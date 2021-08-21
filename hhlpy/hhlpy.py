"""
Python implementation of Hybrid Hoare Logic.
"""

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import hcsp
from hhlpy.z3wrapper import z3_prove


def compute_diff(e, eqs_dict):
    """Compute differential of an arithmetic or boolean expression."""
    def rec(e):
        if isinstance(e, expr.RelExpr):
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


def compute_wp(hp, post):
    """Compute weakest preconditions for a given hybrid program.
    
    hp : HCSP - input hybrid program.
    post : BExpr - postcondition.

    Returns a pair (pre, vcs), where pre is the computed precondition,
    and vcs is a list of verification conditions.

    """
    if isinstance(hp, hcsp.Assign):
        # Assignment: replace var_name by expr in post
        if not isinstance(hp.var_name, expr.AVar):
            raise NotImplementedError
        var = hp.var_name.name
        pre = post.subst({var: hp.expr})
        return pre, []

    elif isinstance(hp, hcsp.IChoice):
        # Internal choice: conjunction of the two preconditions
        pre1, vcs1 = compute_wp(hp.hp1, post)
        pre2, vcs2 = compute_wp(hp.hp2, post)
        pre = expr.conj(pre1, pre2)
        return pre, vcs1 + vcs2

    elif isinstance(hp, hcsp.Sequence):
        # Sequence of several commands, apply compute_wp from bottom to top
        cur_pre = post
        all_vcs = []
        for sub_hp in reversed(hp.hps):
            cur_pre, cur_vcs = compute_wp(sub_hp, cur_pre)
            all_vcs.extend(cur_vcs)
        return cur_pre, all_vcs

    elif isinstance(hp, hcsp.Loop):
        # Loop, currently use postcondition as invariant.
        if hp.constraint != expr.true_expr:
            raise NotImplementedError
        
        # Set invariant to be the postcondition
        inv = post

        # Compute wp for loop body with respect to invariant
        pre, vcs = compute_wp(hp.hp, inv)

        # Verification condition is inv --> pre
        vc = expr.imp(inv, pre)
        return inv, vcs + [vc]

    elif isinstance(hp, hcsp.ODE):
        # ODE, by default use the differential invariant rule.
        # Currently ignore the constraint, and assume out_hp is Skip.
        if hp.out_hp != hcsp.Skip():
            raise NotImplementedError
        
        # Assume the postcondition is the differential invariant.
        inv = post

        # Construct dictionary corresponding to eqs.
        eqs_dict = dict()
        for name, e in hp.eqs:
            eqs_dict[name] = e

        # Compute the differential of inv.
        inv_diff = compute_diff(inv, eqs_dict=eqs_dict)
        return inv, [inv_diff]

    else:
        raise NotImplementedError

def compute_vcs(pre, hp, post):
    wp, vcs = compute_wp(hp, post)
    return vcs + [expr.imp(pre, wp)]

def verify(pre, hp, post):
    vcs = compute_vcs(pre, hp, post)
    return all(z3_prove(vc) for vc in vcs)
