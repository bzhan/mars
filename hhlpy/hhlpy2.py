"""
Python implementation of Hybrid Hoare Logic.

This version uses data structures that are separate from the main
HCSP program.

"""

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp.simulator import get_pos
from hhlpy.z3wrapper import z3_prove


def compute_diff(e, eqs_dict):
    """Compute differential of an arithmetic or boolean expression."""
    def rec(e):
        if isinstance(e, expr.LogicExpr):
            if e.op == "&&":
                return expr.LogicExpr("&&", rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == "||":
                 return expr.LogicExpr("&&", rec(e.exprs[0]), rec(e.exprs[1]))
        elif isinstance(e, expr.RelExpr):
            if e.op == '<' or e.op == '<=':
                return expr.RelExpr("<=", rec(e.expr1), rec(e.expr2))
            elif e.op == '>' or e.op == '>=':
                return expr.RelExpr(">=", rec(e.expr1), rec(e.expr2))
            elif e.op == '==' or e.op == '!=':
                return expr.RelExpr("==", rec(e.expr1), rec(e.expr2))
            else:
                raise NotImplementedError
        elif isinstance(e, expr.AConst):
            return expr.AConst(0)
        elif isinstance(e, expr.AVar):
            if e.name in eqs_dict:
                return eqs_dict[e.name]
            else:
                return expr.AConst(0)
        elif isinstance(e, expr.OpExpr):
            if len(e.exprs) == 1:
                return expr.OpExpr("-", rec(e.exprs[0]))
            elif e.op == '+':
                return expr.OpExpr("+", rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == '-':
                return expr.OpExpr("-", rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == '*':
                # d(u*v) = u*dv + du*v
                du, dv = rec(e.exprs[0]), rec(e.exprs[1])
                return expr.OpExpr("+", expr.OpExpr("*", e.exprs[0], dv), expr.OpExpr("*", du, e.exprs[1]))
            else:
                raise NotImplementedError
    
    return rec(e)


class CmdInfo:
    """Information associated to each HCSP program."""
    def __init__(self):
        # Pre-condition and post-condition are assertions.
        self.pre = None
        self.post = None

        # List of verification conditions for this command.
        self.vcs = []

        # Invariants for loops.
        self.inv = None

        # HCSP program for this command
        self.hp = None

        # Differential invariants for ODEs.
        self.diff_inv = None

        # Differential cuts for ODES.
        self.diff_cuts = []

        # Ghost invariants for ODEs.
        self.ghost_inv = None

        # Computed differential equations for ghosts.
        self.ghost_eqs = None

    def __str__(self):
        res = ""
        res += "pre = %s\n" % self.pre
        res += "post = %s\n" % self.post
        for vc in self.vcs:
            res += "vc: %s\n" % vc
        if self.inv is not None:
            res += "inv: %s\n" % self.inv
        if self.diff_inv is not None:
            res += "diff_inv: %s\n" % self.diff_inv
        if self.ghost_inv is not None:
            res += "ghost_inv: %s\n" % self.ghost_inv
        if self.ghost_eqs is not None:
            for ghost_var, eq in self.ghost_eqs.items():
                res += "ghost_eq: %s_dot = %s\n" % (ghost_var, str(eq))
        for diff_cut in self.diff_cuts:
            res += "diff_cut: %s\n" % diff_cut

        return res


class CmdVerifier:
    """Contains current state of verification of an HCSP program."""
    def __init__(self, *, pre, hp, post):
        # The HCSP program to be verified.
        self.hp = hp

        # Mapping from program position to CmdInfo objects.
        self.infos = dict()

        # Set of variables that are used
        self.vars = hp.get_vars().union(pre.get_vars()).union(post.get_vars())

        # Initialize info for the root object. Place pre-condition and
        # post-condition.
        root_pos = tuple()
        self.infos[root_pos] = CmdInfo()
        self.infos[root_pos].pre = pre
        self.infos[root_pos].post = post
        self.infos[root_pos].hp = hp

    def __str__(self):
        res = ""
        for pos, info in self.infos.items():
            res += str(pos) + ":\n"
            res += str(info)
        return res
    
    def print_info(self):
        res = ""
        for pos, info in self.infos.items():
            res += "%s:\n%s" % (pos, info)
        return res

    def add_invariant(self, pos, inv):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].inv = inv

    def add_diff_invariant(self, pos, diff_inv):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].diff_inv = diff_inv

    def add_diff_cuts(self, pos, diff_cuts):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].diff_cuts = diff_cuts

    def add_ghost_invariant(self, pos, ghost_inv):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].ghost_inv = ghost_inv

    def compute_wp(self, *, pos=tuple()):
        """Compute weakest-preconditions using the given information."""

        # Obtain the hp at the given position
        cur_hp = get_pos(self.hp, pos)

        # Compute cur_hp for some new created pos, such as pos created in dC and multi invariants, 
        # they don't have corresponding hp by directly using get_pos()
        if cur_hp is None:
            cur_hp = self.infos[pos].hp

        # The post-condition at the given position should already be
        # available.
        assert pos in self.infos and self.infos[pos].post is not None
        post = self.infos[pos].post

        if isinstance(cur_hp, hcsp.Skip):
            # Skip: {P} skip {P}
            pre = post
        
        elif isinstance(cur_hp, hcsp.Assign):
            # Assign: {P[e/v]} v := e {P}
            # Compute pre-condition by replacing var_name by expr in the
            # post-condition.
            if not isinstance(cur_hp.var_name, expr.AVar):
                raise NotImplementedError

            var = cur_hp.var_name.name
            pre = post.subst({var: cur_hp.expr})
        
        elif isinstance(cur_hp, hcsp.RandomAssign):
            # RandomAssign: replace var_name by var_name_new in post and in cur_hp.expr
            #               pre: cur_hp.expr(newvar_name|var_name) --> post(newvar_name|var_name)
            if not isinstance(cur_hp.var_name, expr.AVar):
                raise NotImplementedError

            var_str = cur_hp.var_name.name

            # Create a new var
            i = 0
            newvar_str = var_str + str(i)
            while(newvar_str in self.vars):
                i = i + 1
                newvar_str = var_str + str(i)
            self.vars.add(newvar_str)

            #Compute the pre: hp.expr(newvar_name|var_name) --> post(newvar_name|var_name)
            newvar_name = expr.AVar(newvar_str)
            pre = expr.imp(cur_hp.expr.subst({var_str: newvar_name}), post.subst({var_str: newvar_name}))


        elif isinstance(cur_hp, hcsp.IChoice):
            # IChoice: 
            #   {P1} c1 {Q}    {P2} c2 {Q}
            # ------------------------------
            #     {P1 & P2} c1 ++ c2 {Q}
            # Pre-condition is the conjunction of the two pre-conditions
            # of subprograms.

            pos0, pos1 = pos + (0,), pos + (1,)
            if pos0 not in self.infos:
                self.infos[pos0] = CmdInfo()
            if pos1 not in self.infos:
                self.infos[pos1] = CmdInfo()
            info1 = self.infos[pos0]
            info2 = self.infos[pos1]
            info1.post = post
            info2.post = post
            self.compute_wp(pos=pos0)
            self.compute_wp(pos=pos1)
            pre = expr.conj(self.infos[pos0].pre, self.infos[pos1].pre)
        
        elif isinstance(cur_hp, hcsp.Sequence):
            # Sequence of several commands, apply compute_wp from bottom to top
            cur_post = post
            for i in reversed(range(len(cur_hp.hps))):
                sub_pos = pos + (i,)
                if sub_pos not in self.infos:
                    self.infos[sub_pos] = CmdInfo()
                sub_info = self.infos[sub_pos]
                sub_info.post = cur_post
                self.compute_wp(pos=sub_pos)
                cur_post = sub_info.pre
            pre = cur_post

        elif isinstance(cur_hp, hcsp.Loop):
            # Loop, currently use the invariant that users offered.
            if cur_hp.constraint != expr.true_expr:
                raise NotImplementedError

            if self.infos[pos].inv is None:
                raise AssertionError("Loop invariant at position %s is not set." % str(pos))

            inv = self.infos[pos].inv
            if not isinstance(inv, expr.BExpr):
                raise NotImplementedError('Invalid Invariant for Loop!') 

            # Compute wp for loop body with respect to invariant
            sub_pos = pos + (0,)
            if sub_pos not in self.infos:
                self.infos[sub_pos] = CmdInfo()
            sub_info = self.infos[sub_pos]
            sub_info.post = inv
            self.compute_wp(pos=sub_pos)
            pre_loopbody = sub_info.pre

            # pre is also set to be the invariant
            pre = inv

            # Verification condition is invariant --> pre_loopbody and invariant --> post
            vc1 = expr.imp(inv, pre_loopbody)
            vc2 = expr.imp(inv, post)
            self.infos[pos].vcs = [vc1, vc2]

        elif isinstance(cur_hp, hcsp.ODE):
            # ODE, use the differential invariant rule, differential cut rule and differential ghost rule.
            # Currently assume out_hp is Skip.
            if cur_hp.out_hp != hcsp.Skip():
                raise NotImplementedError
            if self.infos[pos].hp is None:
                self.infos[pos].hp = cur_hp
            constraint = cur_hp.constraint
            eqs = cur_hp.eqs
            
            # Use dI rules
            if self.infos[pos].diff_inv is not None:
                diff_inv = self.infos[pos].diff_inv
                if self.infos[pos].inv is not None:
                    assert diff_inv == self.infos[pos].inv
                if not isinstance(diff_inv, expr.BExpr):
                    raise NotImplementedError('Invalid differential invariant for ODE!') 

                # Construct dictionary corresponding to eqs.
                eqs_dict = dict()
                for name, e in cur_hp.eqs:
                    eqs_dict[name] = e

                # Compute the differential of inv. 
                # One verification condition is the differential of inv must hold. 
                # The second condition is inv --> post.
                differential = compute_diff(diff_inv, eqs_dict=eqs_dict)
                pre = diff_inv
                self.infos[pos].vcs.append(expr.imp(self.infos[pos].hp.constraint, differential))
                self.infos[pos].vcs.append(expr.imp(diff_inv, post))
            
            # Use dC rules
            elif self.infos[pos].diff_cuts:
                diff_cuts = self.infos[pos].diff_cuts

                # Consider every hp with new constraint, which is the conjunction of original constraint and diff_cuts
                # Sub_constraint of the first sub_hp is the same as cur_hp.constraint
                sub_constraint = constraint
                for i in range(len(diff_cuts)):
                    if not isinstance(diff_cuts[i], expr.BExpr):
                        raise NotImplementedError("Invalid differential cut for ODE!")

                    # Create CmdInfo for every hp with new constraint.
                    # Note that sub_pos doesn't exist in hp. 
                    # Question remained: whether sub_pos here will contradict with pos_inv in multi_invariants
                    sub_pos = pos + (i,)
                    self.infos[sub_pos] = CmdInfo()
                    self.infos[sub_pos].diff_inv = diff_cuts[i]
                    self.infos[sub_pos].post = diff_cuts[i]

                    # Cases i == 0, sub_hp is the same with cur_hp
                    if i == 0:
                        self.infos[sub_pos].hp = cur_hp

                    # Cases i > 0, sub_constraint is the conjunction of old constraint of and diff_cuts[i-1]
                    else:
                        sub_constraint = expr.LogicExpr('&&', sub_constraint, diff_cuts[i-1])
                        sub_hp = hcsp.ODE(eqs, sub_constraint)
                        self.infos[sub_pos].hp = sub_hp

                    self.compute_wp(pos=sub_pos)

                pre = diff_cuts[0]

                self.infos[pos].vcs.append(expr.imp(diff_cuts[-1], post))

            # Use dG rules
            elif self.infos[pos].ghost_inv is not None:
                ghost_inv = self.infos[pos].ghost_inv
                inv = self.infos[pos].inv

                if inv is None or not isinstance(inv, expr.BExpr):
                    raise NotImplementedError('Invalid invariant for ODE (ghost mode)!')
                if not isinstance(ghost_inv, expr.BExpr):
                    raise NotImplementedError('Invalid ghost invariant for ODE!')

                all_vars = cur_hp.get_vars()
                ghost_vars = [v for v in ghost_inv.get_vars() if v not in all_vars]
                if len(ghost_vars) != 1:
                    raise AssertionError("Number of ghost variables is not 1.")
                ghost_var = ghost_vars[0]

                # The first condition is: inv implies there exists a value of ghost_var
                # that satisfies ghost_inv.
                vc1 = expr.imp(inv, expr.ExistsExpr(ghost_var, ghost_inv))

                # Second condition: solve for the differential equation that must be
                # satisfied by the ghost variable.
                # First, assert the ghost invariant is in the form g(x,y) == c, where
                # y is the ghost variable, and x are the other variables.

                eqs_dict = dict()
                for name, e in cur_hp.eqs:
                    eqs_dict[name] = e

                # Cases when ghost_inv is a logic Expression.
                # Currently assume op is "&&"
                if isinstance(ghost_inv, expr.LogicExpr) and ghost_inv.op == "&&":
                    ghost_eqs_candidates = []
                    ghost_subinvs = expr.split_conj(ghost_inv)

                    # Ghost_subinv is in the form: g(x,y) op c, where op is an relation operation
                    for ghost_subinv in ghost_subinvs:
                        if not (isinstance(ghost_subinv, expr.RelExpr) and \
                                isinstance(ghost_subinv.expr2, expr.AConst)):
                            raise AssertionError("Wrong ghost invariant form in LogicExpr!")
                        
                        dg_x = compute_diff(ghost_subinv.expr1, eqs_dict=eqs_dict)
                        dgdy = compute_diff(ghost_subinv.expr1, eqs_dict={ghost_var: expr.AConst(1)})

                        # Since dg/dx * dx + dg/dy * dy == 0, so dy = -(dg/dx * dx) / dg/dy
                        dy = expr.OpExpr("-", expr.OpExpr("/", dg_x, dgdy))
                        ghost_eqs_candidates.append({ghost_var: dy})

                    # Currently directly using candidate number == 1
                    ghost_eqs_num = 1
                    self.infos[pos].ghost_eqs = ghost_eqs_candidates[ghost_eqs_num]
                    dghost_var = self.infos[pos].ghost_eqs[ghost_var]

                    # Add ghost_eqs into eqs
                    eqs.append((ghost_var, dghost_var))
                    # Add ghost_eqs into eqs_dict
                    eqs_dict[ghost_var] = dghost_var

                    # Create CmdInfo for every ghost_subinv.
                    # Note that sub_pos doesn't exist in hp. 
                    # Question remained: whether sub_pos here will contradict with those in multi_invariants and dC
                    for i, ghost_subinv in enumerate(ghost_subinvs):
                        if i != ghost_eqs_num:
                            subpos = pos + (i,)

                            if subpos not in self.infos:
                                self.infos[subpos] = CmdInfo()
                            self.infos[subpos].hp = hcsp.ODE(eqs, constraint)
                            self.infos[subpos].inv = ghost_subinv
                            self.infos[subpos].post = ghost_subinv

                            self.compute_wp(pos=subpos)

                # Cases when ghost_inv is in the form g(x,y) == c
                elif isinstance(ghost_inv, expr.RelExpr) and ghost_inv.op == "==" and \
                        isinstance(ghost_inv.expr2, expr.AConst):

                    # Obtain dg/dx * dx
                    dg_x = compute_diff(ghost_inv.expr1, eqs_dict=eqs_dict)

                    # Obtain dg/dy
                    dgdy = compute_diff(ghost_inv.expr1, eqs_dict={ghost_var: expr.AConst(1)})

                    # Since dg/dx * dx + dg/dy * dy == 0, so dy = -(dg/dx * dx) / dg/dy
                    dy = expr.OpExpr("-", expr.OpExpr("/", dg_x, dgdy))
                    self.infos[pos].ghost_eqs = {ghost_var: dy}

                # Third condition
                vc3 = expr.imp(ghost_inv, inv)

                # Fourth condition
                vc4 = expr.imp(inv, post)

                self.infos[pos].vcs = [vc1, vc3, vc4]

                # New precondition is inv
                pre = inv

            # Invariant is a logic expression, such as x > 0 && y > 0, we can compute wp for each sub_inv one by one.
            # Different sub_inv may use different ODE rules
            elif self.infos[pos].inv is not None and isinstance(self.infos[pos].inv, expr.LogicExpr):
                inv = self.infos[pos].inv

                # Currently only consider op is &&
                if inv.op == "&&":
                    sub_invs = expr.split_conj(inv)
                    
                    # Compute wp for each sub_inv
                    for i, sub_inv in enumerate(sub_invs):
                        # Create different CmdInfos for cur_hp with different invariants
                        # We use pos_inv to map different CmdIndos. Note that hp.get_pos(pos=pos_inv) is None
                        pos_inv = pos + (i,)
                        if pos_inv not in self.infos:
                            self.infos[pos_inv] = CmdInfo()
                        self.infos[pos_inv].hp = cur_hp
                        self.infos[pos_inv].post = sub_inv
                        self.infos[pos_inv].inv = sub_inv
                        
                        self.compute_wp(pos=pos_inv)
                pre = inv

            else:
                raise AssertionError("No invariant set at position %s." % str(pos))

        else:
            raise NotImplementedError

        # Assign pre-condition, or create a new verification condition if the
        # pre-condition is already set.
        if self.infos[pos].pre is None:
            self.infos[pos].pre = pre
        else:
            self.infos[pos].vcs.append(expr.imp(self.infos[pos].pre, pre))

    def get_all_vcs(self):
        all_vcs = dict()
        for pos, info in self.infos.items():
            if info.vcs:
                all_vcs[pos] = info.vcs
        return all_vcs

    def verify(self):
        """Verify all VCs in self."""
        all_vcs = self.get_all_vcs()
        for _, vcs in all_vcs.items():
            if not all(z3_prove(vc) for vc in vcs):
                return False
        return True
