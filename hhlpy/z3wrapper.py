"""Wrapper for Z3 prover."""

import z3

from ss2hcsp.hcsp import expr


def convert(e):
    """Conversion from expression to z3 term."""
    if isinstance(e, expr.AVar):
        return z3.Real(e.name)
    elif isinstance(e, expr.AConst):
        if isinstance(e.value, int):
            return e.value
        else:
            raise NotImplementedError
    elif isinstance(e, expr.LogicExpr):
        if e.op == '-->':
            return z3.Implies(convert(e.exprs[0]), convert(e.exprs[1]))
        elif e.op == '&&':
            return z3.And(convert(e.exprs[0]), convert(e.exprs[1]))
        elif e.op == '||':
            return z3.Or(convert(e.exprs[0]), convert(e.exprs[1]))
        elif e.op == '<-->':
            return convert(e.exprs[0]) == convert(e.exprs[1])
        elif e.op == '~':
            return z3.Not(convert(e.exprs[0]))
        else:
            raise TypeError
    elif isinstance(e, expr.RelExpr):
        if e.op == '<':
            return convert(e.expr1) < convert(e.expr2)
        elif e.op == '<=':
            return convert(e.expr1) <= convert(e.expr2)
        elif e.op == '>':
            return convert(e.expr1) > convert(e.expr2)
        elif e.op == '>=':
            return convert(e.expr1) >= convert(e.expr2)
        elif e.op == '==':
            return convert(e.expr1) == convert(e.expr2)
        elif e.op == '!=':
            return z3.Not(convert(e.expr1) == convert(e.expr2))
    elif isinstance(e, expr.OpExpr):
        if len(e.exprs) == 1:
            return -convert(e.exprs[0])
        elif e.op == '+':
            return convert(e.exprs[0]) + convert(e.exprs[1])
        elif e.op == '-':
            return convert(e.exprs[0]) - convert(e.exprs[1])
        elif e.op == '*':
            return convert(e.exprs[0]) * convert(e.exprs[1])
        elif e.op == '/':
            return convert(e.exprs[0]) / convert(e.exprs[1])
        else:
            raise NotImplementedError
    else:
        raise NotImplementedError

def z3_prove(e):
    """Attempt to prove the given condition."""
    s = z3.Solver()
    s.add(z3.Not(convert(e)))
    if str(s.check()) == 'unsat':
        return True
    else:
        return False
