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

        # Differential invariants for ODEs.
        self.diff_inv = None

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
        return res


class CmdVerifier:
    """Contains current state of verification of an HCSP program."""
    def __init__(self, *, pre, hp, post):
        # The HCSP program to be verified.
        self.hp = hp

        # Mapping from program position to CmdInfo objects.
        self.infos = dict()

        # Set of variables that are used
        self.vars = hp.get_vars()

        # Initialize info for the root object. Place pre-condition and
        # post-condition.
        root_pos = tuple()
        self.infos[root_pos] = CmdInfo()
        self.infos[root_pos].pre = pre
        self.infos[root_pos].post = post

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

    def add_ghost_invariant(self, pos, ghost_inv):
        if pos not in self.infos:
            self.infos[pos] = CmdInfo()
        self.infos[pos].ghost_inv = ghost_inv

    def compute_wp(self, *, pos=tuple()):
        """Compute weakest-preconditions using the given information."""

        # Obtain the hp at the given position
        cur_hp = get_pos(self.hp, pos)

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
            # ODE, by default use the differential invariant rule.
            # Currently ignore the constraint, and assume out_hp is Skip.
            if cur_hp.out_hp != hcsp.Skip():
                raise NotImplementedError

            if self.infos[pos].diff_inv is not None:
                diff_inv = self.infos[pos].diff_inv
                if not isinstance(diff_inv, expr.BExpr):
                    raise NotImplementedError('Invalid differential invariant for ODE!') 

                # Construct dictionary corresponding to eqs.
                eqs_dict = dict()
                for name, e in cur_hp.eqs:
                    eqs_dict[name] = e

                # Compute the differential of inv. One verification condition is
                # the differential of inv must hold. The second condition is inv --> post.
                differential = compute_diff(diff_inv, eqs_dict=eqs_dict)
                pre = diff_inv
                self.infos[pos].vcs.append(differential)
                self.infos[pos].vcs.append(expr.imp(diff_inv, post))

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
                if not (isinstance(ghost_inv, expr.RelExpr) and ghost_inv.op == "==" and \
                        isinstance(ghost_inv.expr2, expr.AConst)):
                    raise AssertionError("Ghost invariant not in the form g(x,y) == c.")

                # Obtain dg/dx * dx
                eqs_dict = dict()
                for name, e in cur_hp.eqs:
                    eqs_dict[name] = e
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
