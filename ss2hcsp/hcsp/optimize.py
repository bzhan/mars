"""Optimization of HCSP code."""

from ss2hcsp.hcsp import hcsp


def is_atomic(hp):
    """Whether hp is an atomic program"""
    return hp.type in ('skip', 'wait', 'assign', 'assert', 'test', 'log',
                       'input_channel', 'output_channel')

def get_read_vars(hp):
    """Obtain set of variables read by the program."""
    if hp.type in ('skip', 'var'):
        return set()
    elif hp.type == 'wait':
        return hp.delay.get_vars()
    elif hp.type == 'assign':
        return hp.expr.get_vars()
    elif hp.type in ('assert', 'test', 'log'):
        return hp.get_vars()
    elif hp.type == 'input_channel':
        return set()
    elif hp.type == 'output_channel':
        return hp.get_vars()
    elif hp.type == 'condition':
        return hp.cond.get_vars()
    elif hp.type == 'ite':
        return set().union(*(if_cond.get_vars() for if_cond, _ in hp.if_hps))
    else:
        raise NotImplementedError

def replace_read_vars(hp, inst):
    """Replace the set of read variables in the program. Return the
    new program.
    
    """
    if hp.type == 'skip':
        return hp
    elif hp.type == 'wait':
        return hcsp.Wait(hp.delay.subst(inst))
    elif hp.type == 'assign':
        return hcsp.Assign(hp.var_name, hp.expr.subst(inst))
    elif hp.type == 'assert':
        return hcsp.Assert(hp.bexpr.subst(inst), [msg.subst(inst) for msg in hp.msgs])
    elif hp.type == 'test':
        return hcsp.Test(hp.bexpr.subst(inst), [msg.subst(inst) for msg in hp.msgs])
    elif hp.type == 'log':
        return hcsp.Log(*(expr.subst(inst) for expr in hp.exprs))
    elif hp.type == 'input_channel':
        return hp
    elif hp.type == 'output_channel':
        if len(hp.ch_name.args) > 0:
            raise NotImplementedError
        if hp.expr is None:
            return hp
        else:
            return hcsp.OutputChannel(hp.ch_name, hp.expr.subst(inst))
    else:
        raise NotImplementedError

def targeted_replace(hp, repls):
    """Make the given list of replacements."""
    def rec(hp, cur_pos):
        if is_atomic(hp):
            if cur_pos in repls:
                return replace_read_vars(hp, repls[cur_pos])
            else:
                return hp
        elif hp.type == 'var':
            return hp
        elif hp.type == 'sequence':
            new_hps = []
            for i, sub_hp in enumerate(hp.hps):
                new_hps.append(rec(sub_hp, cur_pos + (i,)))
            return hcsp.Sequence(*new_hps)
        elif hp.type == 'condition':
            new_sub_hp = rec(hp.hp, cur_pos + (0,))
            if cur_pos in repls:
                return hcsp.Condition(hp.cond.subst(repls[cur_pos]), new_sub_hp)
            else:
                return hcsp.Condition(hp.cond, new_sub_hp)
        elif hp.type == 'ite':
            new_if_hps = []
            for i, (cond, if_hp) in enumerate(hp.if_hps):
                new_if_hp = rec(if_hp, cur_pos + (i,))
                if cur_pos in repls:
                    new_if_hps.append((cond.subst(repls[cur_pos]), new_if_hp))
                else:
                    new_if_hps.append((cond, new_if_hp))
            new_else_hp = rec(hp.else_hp, cur_pos + (len(hp.if_hps),))
            return hcsp.ITE(new_if_hps, new_else_hp)
        elif hp.type == 'loop':
            return hcsp.Loop(rec(hp.hp, cur_pos))
        else:
            raise NotImplementedError
    return rec(hp, tuple())


class LocationInfo:
    """Information for each location obtained during static analysis."""
    def __init__(self, loc, sub_hp):
        self.loc = loc
        self.sub_hp = sub_hp

        # The following are computed at initialization
        self.edges = []
        self.back_edges = []
        self.exits = []

        # Reaching definitions
        self.reach_before = []
        self.reach_after = []

    def __str__(self):
        lines = []
        lines.append("Location %s" % str(self.loc))
        if is_atomic(self.sub_hp):
            lines.append("  Code: %s" % str(self.sub_hp))
        lines.append("  Edges: %s" % (', '.join(str(edge) for edge in self.edges)))
        lines.append("  Edges (rev): %s" % (', '.join(str(edge) for edge in self.back_edges)))
        if self.reach_before:
            lines.append("  Reach before: %s" % (', '.join(str(var) for var in self.reach_before)))
        if self.reach_after:
            lines.append("  Reach after: %s" % (', '.join(str(var) for var in self.reach_after)))
        return '\n'.join(lines)

    def __repr__(self):
        return "LocationInfo(%s,%s,%s,%s)" % (
            repr(self.loc), repr(self.edges), repr(self.back_edges), repr(self.exits))


class HCSPAnalysis:
    def __init__(self, hp):
        self.hp = hp
        self.infos = dict()

        self.all_vars = set()

        self.init_infos()
        self.init_all_vars()
    
    def add_edge(self, loc1, loc2):
        self.infos[loc1].edges.append(loc2)
        self.infos[loc2].back_edges.append(loc1)

    def init_infos(self):
        """Initialize location infos."""
        def rec(hp, cur_pos):
            # Note location names are repeated for loops
            if cur_pos not in self.infos:
                self.infos[cur_pos] = LocationInfo(cur_pos, hp)

            if is_atomic(hp) or hp.type == 'var':
                self.infos[cur_pos].exits.append(cur_pos)

            elif hp.type == 'sequence':
                for i, sub_hp in enumerate(hp.hps):
                    rec(sub_hp, cur_pos + (i,))
                
                # Entry into first command
                self.add_edge(cur_pos, cur_pos + (0,))

                # Entry into remaining commands
                for i in range(1, len(hp.hps)):
                    for exit_loc in self.infos[cur_pos + (i-1,)].exits:
                        self.add_edge(exit_loc, cur_pos + (i,))
    
                # Overall exit
                self.infos[cur_pos].exits = self.infos[cur_pos + (len(hp.hps)-1,)].exits
            
            elif hp.type == 'condition':
                rec(hp.hp, cur_pos + (0,))

                # Path where condition holds
                self.add_edge(cur_pos, cur_pos + (0,))
                self.infos[cur_pos].exits = self.infos[cur_pos + (0,)].exits

                # Path where condition does not hold
                self.infos[cur_pos].exits.append(cur_pos)

            elif hp.type == 'ite':
                for i, (cond, if_hp) in enumerate(hp.if_hps):
                    rec(if_hp, cur_pos + (i,))
                rec(hp.else_hp, cur_pos + (len(hp.if_hps),))

                # Possible entry into each branch
                for i in range(len(hp.if_hps) + 1):
                    self.add_edge(cur_pos, cur_pos + (i,))
                
                # Possible exit from each branch
                for i in range(len(hp.if_hps) + 1):
                    self.infos[cur_pos].exits.extend(self.infos[cur_pos + (i,)].exits)
            
            elif hp.type == 'loop':
                rec(hp.hp, cur_pos)

                # Return from loop
                for exit_loc in self.infos[cur_pos].exits:
                    self.add_edge(exit_loc, cur_pos)

            else:
                raise NotImplementedError

        rec(self.hp, tuple())

    def init_all_vars(self):
        for loc, info in self.infos.items():
            if info.sub_hp.type == 'assign':
                self.all_vars.add(info.sub_hp.var_name.name)

    def compute_reaching_definition(self):
        # Initial definitions
        for var in self.all_vars:
            self.infos[()].reach_before.append((var, None))

        # Assignments
        for loc, info in self.infos.items():
            if info.sub_hp.type == 'assign':
                info.reach_after.append((info.sub_hp.var_name.name, loc))

        # After procedure calls, anything can happen
        for loc, info in self.infos.items():
            if info.sub_hp.type == 'var':
                for var in self.all_vars:
                    self.infos[loc].reach_after.append((var, None))

        # Propagate
        while True:
            found = False
            # Propagate from reach before to reach after
            for _, info in self.infos.items():
                for var, loc in info.reach_before:
                    if (var, loc) not in info.reach_after and \
                        (info.sub_hp.type != "assign" or var != info.sub_hp.var_name.name):
                        found = True
                        info.reach_after.append((var, loc))

            # Propagate from reach after to reach before of successor
            for _, info in self.infos.items():
                for var, loc in info.reach_after:
                    for next_loc in info.edges:
                        if (var, loc) not in self.infos[next_loc].reach_before:
                            found = True
                            self.infos[next_loc].reach_before.append((var, loc))

            if not found:
                break

    def detect_replacement(self):
        """Replacement is possible if a variable occurs in an expression and
        there is only one possible assignment of the variable leading to it.
        
        """
        repls = dict()
        for loc, info in self.infos.items():
            if is_atomic(info.sub_hp) or info.sub_hp.type in ('condition', 'ite'):
                for var in get_read_vars(info.sub_hp):
                    # Count number of occurrences in var
                    reach_defs = [prev_loc for prev_var, prev_loc in info.reach_before if prev_var == var]
                    if len(reach_defs) == 1 and reach_defs[0] is not None:
                        def_hp = self.infos[reach_defs[0]].sub_hp
                        assert def_hp.type == 'assign'
                        if loc not in repls:
                            repls[loc] = dict()
                        repls[loc][var] = def_hp.expr

        return repls


def full_optimize(hp):
    analysis = HCSPAnalysis(hp)
    analysis.compute_reaching_definition()
    repls = analysis.detect_replacement()
    return targeted_replace(hp, repls)
