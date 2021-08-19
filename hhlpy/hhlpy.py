"""
Python implementation of Hybrid Hoare Logic.
"""

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import hcsp


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

    else:
        raise NotImplementedError
