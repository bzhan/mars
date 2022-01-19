"""Wrapper for Z3 prover."""

from decimal import Decimal
import z3

from ss2hcsp.hcsp import expr


def convert(e):
    """Conversion from expression to z3 term."""
    if isinstance(e, expr.AVar):
        return z3.Real(e.name)
    elif isinstance(e, expr.AConst):
        if isinstance(e.value, int):
            return z3.RealVal(e.value)
        elif isinstance(e.value, Decimal):
            return z3.RealVal(str(e.value))
        else:
            print(e.value, type(e.value))
            raise NotImplementedError
    elif isinstance(e, expr.BConst):
        return z3.BoolVal(e.value)
    elif isinstance(e, expr.FunExpr):
        if len(e.exprs) == 0:  # actually a constant
            return z3.Real(e.fun_name)
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
        elif e.op == '^':
            return convert(e.exprs[0]) ** convert(e.exprs[1])
        else:
            raise NotImplementedError
    
    elif isinstance(e, expr.ExistsExpr):
        if isinstance(e.vars, tuple):
            return z3.Exists(list(convert(var) for var in e.vars), convert(e.expr))
        else:
            return z3.Exists(convert(e.vars), convert(e.expr))
    elif isinstance(e, expr.ForAllExpr):
        if isinstance(e.vars, tuple):
            return z3.ForAll(list(convert(var) for var in e.vars), convert(e.expr))
        else:
            return z3.ForAll(convert(e.vars), convert(e.expr))
    else:
        print(e, type(e))
        raise NotImplementedError

def z3_prove(e):
    """Attempt to prove the given condition."""
    s = z3.Solver()
    s.add(z3.Not(convert(e)))
    if str(s.check()) == 'unsat':
        return True
    else:
        return False
