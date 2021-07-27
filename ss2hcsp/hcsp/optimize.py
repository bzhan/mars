"""Optimization of HCSP code."""

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.expr import AConst, true_expr, false_expr,RelExpr,FunExpr
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import simulator


def is_atomic(hp):
    """Whether hp is an atomic program"""
    return hp.type in ('skip', 'wait', 'assign', 'assert', 'test', 'log',
                       'input_channel', 'output_channel', 'ode')

def simplify_expr(expr):
    if not expr.get_vars():
        if isinstance(expr,RelExpr)  and isinstance(expr.expr1,FunExpr) and expr.expr1.fun_name == "remove_InputMessage":
            return expr
        else:
            b = simulator.eval_expr(expr, dict())
            assert isinstance(b, bool)
            return true_expr if b else false_expr
    else:
        return expr

def simplify(hp):
    """Perform immediate simplifications to HCSP process. This includes:
    
    * Remove extraneous skip from processes.
    * Simplify if true then P else Q to P.
    
    """
    if is_atomic(hp) or hp.type == 'var':
        return hp
    elif hp.type == 'sequence':
        return hcsp.seq([simplify(sub_hp) for sub_hp in hp.hps])
    elif hp.type == 'loop':
        return hcsp.Loop(simplify(hp.hp), hp.constraint)
    elif hp.type == 'condition':
        simp_cond = simplify_expr(hp.cond)
        simp_sub_hp = simplify(hp.hp)
        if  isinstance(simp_cond,RelExpr)  and isinstance(simp_cond.expr1,FunExpr) and simp_cond.expr1.fun_name == "remove_InputMessage":
            return  hcsp.Condition(simp_cond, simp_sub_hp)
        elif simp_sub_hp.type == 'skip'  or simp_cond == false_expr:
            return hcsp.Skip()
        elif simp_cond == true_expr:
            return simp_sub_hp
        else:
            return hcsp.Condition(simp_cond, simp_sub_hp)
    elif hp.type == 'ode':
        return hcsp.ODE(hp.eqs, simplify(hp.constraint), out_hp=simplify(hp.out_hp))
    elif hp.type == 'ode_comm':
        return hcsp.ODE_Comm(hp.eqs, hp.constraint,
                             [(io, simplify(comm_hp)) for io, comm_hp in hp.io_comms])
    elif hp.type == 'select_comm':
        return hcsp.SelectComm(*((io, simplify(comm_hp)) for io, comm_hp in hp.io_comms))
    elif hp.type == 'ite':
        new_if_hps = [(simplify_expr(cond), simplify(if_hp)) for cond, if_hp in hp.if_hps]
        new_else_hp = hp.else_hp
        return hcsp.ite(new_if_hps, new_else_hp)
    else:
        raise NotImplementedError

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
    elif hp.type == 'ode':
        return hp.constraint.get_vars().union(*(eq.get_vars() for _, eq in hp.eqs))
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
        return hcsp.Log(hp.pattern.subst(inst), exprs=[e.subst(inst) for e in hp.exprs])
    elif hp.type == 'input_channel':
        return hp
    elif hp.type == 'output_channel':
        if len(hp.ch_name.args) > 0:
            raise NotImplementedError
        if hp.expr is None:
            return hp
        else:
            return hcsp.OutputChannel(hp.ch_name, hp.expr.subst(inst))
    elif hp.type == 'ode':
        return hcsp.ODE([(var, eq.subst(inst)) for var, eq in hp.eqs], hp.constraint.subst(inst))
    else:
        raise NotImplementedError

def get_write_vars(lname):
    """Given lname of an assignment, return the set of variables written."""
    if lname is None:
        return {}
    elif isinstance(lname, expr.AVar):
        return {lname.name}
    elif isinstance(lname, expr.ArrayIdxExpr):
        return get_write_vars(lname.expr1)
    elif isinstance(lname, expr.FieldNameExpr):
        return get_write_vars(lname.expr)
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
            return hcsp.Loop(rec(hp.hp, cur_pos), hp.constraint)
        elif hp.type == 'select_comm':
            new_io_comms = []
            for i, (comm_hp, out_hp) in enumerate(hp.io_comms):
                new_out_hp = rec(out_hp, cur_pos + (i,))
                new_io_comms.append((comm_hp, new_out_hp))
            return hcsp.SelectComm(*new_io_comms)
        elif hp.type == 'ode_comm':
            new_io_comms = []
            for i, (comm_hp, out_hp) in enumerate(hp.io_comms):
                new_out_hp = rec(out_hp, cur_pos + (i,))
                new_io_comms.append((comm_hp, new_out_hp))
            return hcsp.ODE_Comm(hp.eqs, hp.constraint, new_io_comms)
        else:
            raise NotImplementedError
    return rec(hp, tuple())

def targeted_remove(hp, remove_locs):
    """Remove code at the given location. For simplicity, simply change
    them to Skip.

    """
    def rec(hp, cur_pos):
        if is_atomic(hp):
            if cur_pos in remove_locs:
                return hcsp.Skip()
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
            return hcsp.Condition(hp.cond, new_sub_hp)
        elif hp.type == 'ite':
            new_if_hps = []
            for i, (cond, if_hp) in enumerate(hp.if_hps):
                new_if_hp = rec(if_hp, cur_pos + (i,))
                new_if_hps.append((cond, new_if_hp))
            new_else_hp = rec(hp.else_hp, cur_pos + (len(hp.if_hps),))
            return hcsp.ITE(new_if_hps, new_else_hp)
        elif hp.type == 'loop':
            return hcsp.Loop(rec(hp.hp, cur_pos), hp.constraint)
        elif hp.type == 'select_comm':
            new_io_comms = []
            for i, (comm_hp, out_hp) in enumerate(hp.io_comms):
                new_out_hp = rec(out_hp, cur_pos + (i,))
                new_io_comms.append((comm_hp, new_out_hp))
            return hcsp.SelectComm(*new_io_comms)
        elif hp.type == 'ode_comm':
            new_io_comms = []
            for i, (comm_hp, out_hp) in enumerate(hp.io_comms):
                new_out_hp = rec(out_hp, cur_pos + (i,))
                new_io_comms.append((comm_hp, new_out_hp))
            return hcsp.ODE_Comm(hp.eqs, hp.constraint, new_io_comms)
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
        self.rev_edges = []
        self.exits = []

        # Reaching definitions
        self.reach_before = set()
        self.reach_after = set()

        # Live variables
        self.live_before = set()
        self.live_after = set()

    def __str__(self):
        lines = []
        lines.append("Location %s" % str(self.loc))
        if is_atomic(self.sub_hp):
            lines.append("  Code: %s" % str(self.sub_hp))
        lines.append("  Edges: %s" % (', '.join(str(edge) for edge in self.edges)))
        lines.append("  Edges (rev): %s" % (', '.join(str(edge) for edge in self.rev_edges)))
        return '\n'.join(lines)

    def __repr__(self):
        return "LocationInfo(%s)" % (repr(self.loc), repr(self.sub_hp))


class HCSPAnalysis:
    def __init__(self, hp, *, local_vars=None):
        self.hp = hp
        if local_vars is None:
            local_vars = set()
        self.local_vars = local_vars
        self.infos = dict()

        self.all_vars = set()

        self.init_infos()
        self.init_all_vars()
    
    def add_edge(self, loc1, loc2):
        self.infos[loc1].edges.append(loc2)
        self.infos[loc2].rev_edges.append(loc1)

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

            elif hp.type == 'select_comm' or hp.type == 'ode_comm':
                for i, (comm_hp, out_hp) in enumerate(hp.io_comms):
                    rec(out_hp, cur_pos + (i,))

                # Possible entry into each select
                for i in range(len(hp.io_comms)):
                    self.add_edge(cur_pos, cur_pos + (i,))

                # Possible exit from each branch
                for i in range(len(hp.io_comms)):
                    self.infos[cur_pos].exits.extend(self.infos[cur_pos + (i,)].exits)

            else:
                print(hp.type)
                raise NotImplementedError

        rec(self.hp, tuple())

    def init_all_vars(self):
        for loc, info in self.infos.items():
            if info.sub_hp.type == 'assign':
                self.all_vars = self.all_vars.union(get_write_vars(info.sub_hp.var_name))

    def compute_reaching_definition(self):
        """Reaching definition analysis.

        For each program location, compute the set of assignments that
        can possibly reach this location. Each assignment is given by
        the variable assigned and the location where it occurs.

        Note for assignment to array elements, we keep name of the
        array rather than the specific element. Likewise for assignment
        to field names.

        Reference:
        Nielson et al. Principles of Program Analysis, Section 2.1.2.

        """
        # Propagate from reach_before to reach_after
        def propagate_before_after(info, var, loc):
            if (var, loc) not in info.reach_after and \
                (info.sub_hp.type != "assign" or var not in get_write_vars(info.sub_hp.var_name)):
                info.reach_after.add((var, loc))

        # Initial definitions
        for var in self.all_vars:
            self.infos[()].reach_before.add((var, None))
            propagate_before_after(self.infos[()], var, None)

        # Assignments
        for loc, info in self.infos.items():
            if info.sub_hp.type == 'assign':
                for write_vars in get_write_vars(info.sub_hp.var_name):
                    info.reach_after.add((write_vars, loc))
            elif info.sub_hp.type == 'input_channel':
                for write_vars in get_write_vars(info.sub_hp.var_name):
                    info.reach_after.add((write_vars, loc))
            elif info.sub_hp.type == 'ode':
                for var, eq in info.sub_hp.eqs:
                    info.reach_after.add((var, loc))

        # After procedure calls, anything can happen
        for loc, info in self.infos.items():
            if info.sub_hp.type == 'var':
                for var in self.all_vars:
                    self.infos[loc].reach_after.add((var, None))

        # Use dictionary order as approximation for a good traversal order
        process_order = sorted(self.infos.keys())

        # Propagate reach_after to reach_before of successor
        while True:
            found = False
            for process_loc in process_order:
                info = self.infos[process_loc]
                for var, loc in info.reach_after:
                    for next_loc in info.edges:
                        if (var, loc) not in self.infos[next_loc].reach_before:
                            found = True
                            self.infos[next_loc].reach_before.add((var, loc))
                            propagate_before_after(self.infos[next_loc], var, loc)

            if not found:
                break

    def detect_replacement(self):
        """Replacement is possible if a variable occurs in an
        expression and there is only one possible assignment of the
        variable leading to it.
        
        """
        repls = dict()
        for loc, info in self.infos.items():
            if is_atomic(info.sub_hp) or info.sub_hp.type in ('condition', 'ite'):   
                for var in get_read_vars(info.sub_hp):
                    # Count number of occurrences in var
                    reach_defs = [prev_loc for prev_var, prev_loc in info.reach_before
                                  if prev_var == var]
                    
                    if any(prev_loc is None for prev_loc in reach_defs):
                        continue

                    # Obtain the unique expression assigned to. The replacement
                    # is valid only if all three of the following conditions hold:
                    #   1. all assignments are to constant expressions.
                    #   2. all assignments are the same.
                    #   3. all assignments are to variable itself, rather than to
                    #      some array index or field name.
                    unique_assign = None
                    for prev_loc in reach_defs:
                        def_hp = self.infos[prev_loc].sub_hp
                        if def_hp.type in ('input_channel', 'ode'):
                            unique_assign = None
                            break
                        assert def_hp.type == 'assign'
                        if not isinstance(def_hp.var_name, expr.AVar):
                            unique_assign = None
                            break
                        if not isinstance(def_hp.expr, AConst):
                            unique_assign = None
                            break
                        if unique_assign is not None and def_hp.expr != unique_assign:
                            unique_assign = None
                            break
                        unique_assign = def_hp.expr
                    # If there is a unique assigned value which is a constant,
                    # add to replacement list.
                    if not unique_assign:
                        continue
                    if loc not in repls:
                        repls[loc] = dict()
                    repls[loc][var] = unique_assign
        return repls

    def compute_live_variable(self):
        """Live variable analysis.

        Reference:
        Nielson et al. Principles of Program Analysis, Section 2.1.4

        """
        # Propagate from live_after to live_before. Note propagation
        # is forbidden only if the variable is exactly equal to the
        # left hand side of assignment. Assigning to indices or field
        # names does not count.
        def propagate_after_before(info, var):
            if var not in info.live_before and \
                (info.sub_hp.type != "assign" or expr.AVar(var) != info.sub_hp.var_name):
                info.live_before.add(var)

        # All variables are live at the end, except those in local_vars
        for loc in self.infos[()].exits:
            info = self.infos[loc]
            for var in self.all_vars - self.local_vars:
                info.live_after.add(var)
                propagate_after_before(info, var)

        # Live variables for commands
        for loc, info in self.infos.items():
            if is_atomic(info.sub_hp) or info.sub_hp.type in ('condition', 'ite'):
                for var in get_read_vars(info.sub_hp):
                    self.infos[loc].live_before.add(var)
        
        # Before procedure calls, any variable may be used
        for loc, info in self.infos.items():
            if info.sub_hp.type == 'var':
                for var in self.all_vars - self.local_vars:
                    self.infos[loc].live_before.add(var)

        # Use reverse dictionary order as approximation for good traversal order
        process_order = reversed(sorted(self.infos.keys()))

        # Propagate from reach before to reach after of predecessor
        while True:
            found = False
            for process_loc in process_order:
                info = self.infos[process_loc]
                for var in info.live_before:
                    for prev_loc in info.rev_edges:
                        if var not in self.infos[prev_loc].live_after:
                            found = True
                            self.infos[prev_loc].live_after.add(var)
                            propagate_after_before(self.infos[prev_loc], var)

            if not found:
                break

    def detect_dead_code(self):
        """Dead code are assignments whose variable which is not live afterwards."""
        dead_code = []
        for loc, info in self.infos.items():
            if info.sub_hp.type == 'assign':
                if all(name not in info.live_after for name in get_write_vars(info.sub_hp.var_name)):
                    dead_code.append(loc)
        return dead_code


def full_optimize(hp, *, local_vars=None):
    """Full optimization of a single HCSP program.

    hp : HCSP - program to be optimized.
    local_vars : set[str] - list of local variables.

    """
    while True:
        old_hp = hp

        # Replace constants
        analysis = HCSPAnalysis(hp, local_vars=local_vars)
        analysis.compute_reaching_definition()
        repls = analysis.detect_replacement()
        hp = targeted_replace(hp, repls)

        # Deadcode elimination
        analysis = HCSPAnalysis(hp, local_vars=local_vars)
        analysis.compute_live_variable()
        dead_code = analysis.detect_dead_code()
        hp = targeted_remove(hp, dead_code)

        # Simplification
        hp = simplify(hp)

        if hp == old_hp:
            break
    return hp

def full_optimize_module(procs, hp, *, local_vars=None, local_vars_proc=None):
    """Full optimization of a single HCSP program, along with procedures.

    hp : HCSP - program to be optimized.
    procs : dict[str, HCSP] - dictionary of procedures.
    local_vars : set[str] - list of local variables in hp.
    local_vars_proc : set[str] - list of local variables in procs.

    """
    while True:
        old_hp = hp
        old_procs = dict()
        for name, proc in procs.items():
            old_procs[name] = proc

        hp = hcsp.reduce_procedures(hp, procs)
        hp = full_optimize(hp, local_vars=local_vars)
        for name in procs:
            procs[name] = full_optimize(procs[name], local_vars=local_vars_proc)
        
        if hp == old_hp and len(old_procs) == len(procs) and \
            all(procs[name] == old_procs[name] for name in procs):
            break

    return procs, hp