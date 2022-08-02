"""Wrapper for Z3 prover."""

from decimal import Decimal
from fractions import Fraction
import z3

from ss2hcsp.hcsp import expr

def convert(e, functions):
    """Conversion from expression to z3 term."""
    if isinstance(e, expr.AVar):
        return z3.Real(e.name)
    elif isinstance(e, expr.AConst):
        if isinstance(e.value, int):
            return z3.RealVal(e.value)
        elif isinstance(e.value, (Decimal, Fraction)):
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
            f = functions[e.fun_name]
            return f(*[convert(e, functions) for e in e.exprs])
    elif isinstance(e, expr.LogicExpr):
        if e.op == '->':
            return z3.Implies(convert(e.exprs[0], functions), convert(e.exprs[1], functions))
        elif e.op == '&&':
            return z3.And(convert(e.exprs[0], functions), convert(e.exprs[1], functions))
        elif e.op == '||':
            return z3.Or(convert(e.exprs[0], functions), convert(e.exprs[1], functions))
        elif e.op == '<->':
            return convert(e.exprs[0], functions) == convert(e.exprs[1], functions)
        elif e.op == '!':
            return z3.Not(convert(e.exprs[0], functions))
        else:
            raise TypeError
    elif isinstance(e, expr.RelExpr):
        if e.op == '<':
            return convert(e.expr1, functions) < convert(e.expr2, functions)
        elif e.op == '<=':
            return convert(e.expr1, functions) <= convert(e.expr2, functions)
        elif e.op == '>':
            return convert(e.expr1, functions) > convert(e.expr2, functions)
        elif e.op == '>=':
            return convert(e.expr1, functions) >= convert(e.expr2, functions)
        elif e.op == '==':
            return convert(e.expr1, functions) == convert(e.expr2, functions)
        elif e.op == '!=':
            return z3.Not(convert(e.expr1, functions) == convert(e.expr2, functions))
    elif isinstance(e, expr.OpExpr):
        if len(e.exprs) == 1:
            return -convert(e.exprs[0], functions)
        elif e.op == '+':
            return convert(e.exprs[0], functions) + convert(e.exprs[1], functions)
        elif e.op == '-':
            return convert(e.exprs[0], functions) - convert(e.exprs[1], functions)
        elif e.op == '*':
            return convert(e.exprs[0], functions) * convert(e.exprs[1], functions)
        elif e.op == '/':
            return convert(e.exprs[0], functions) / convert(e.exprs[1], functions)
        elif e.op == '^':
            return convert(e.exprs[0], functions) ** convert(e.exprs[1], functions)
        else:
            raise NotImplementedError
    
    elif isinstance(e, expr.ExistsExpr):
        if isinstance(e.vars, tuple):
            return z3.Exists(list(convert(var, functions) for var in e.vars), convert(e.expr, functions))
        else:
            return z3.Exists(convert(e.vars, functions), convert(e.expr, functions))
    elif isinstance(e, expr.ForAllExpr):
        if isinstance(e.vars, tuple):
            return z3.ForAll(list(convert(var, functions) for var in e.vars), convert(e.expr, functions))
        else:
            return z3.ForAll(convert(e.vars, functions), convert(e.expr, functions))
    elif isinstance(e, expr.IfExpr):
        return z3.If(convert(e.cond, functions), convert(e.expr1, functions), convert(e.expr2, functions))
    else:
        print(e, type(e))
        raise NotImplementedError

def convertFunDecl(funDecl, z3functions):
    convertedBody = convert(funDecl.expr, z3functions)
    f = z3.Function(funDecl.name, *[z3.RealSort() for v in funDecl.vars], convertedBody.sort())
    vars = [z3.Real(v) for v in funDecl.vars]
    return (f, z3.ForAll(vars, f(vars) == convertedBody))

def z3_prove(e, functions=dict()):
    """Attempt to prove the given condition."""
    s = z3.Solver()
    z3functions = {}
    for f in functions:
        z3fun, faxiom = convertFunDecl(functions[f], z3functions)
        s.add(faxiom)
        z3functions[f] = z3fun
    s.add(z3.Not(convert(e, z3functions)))
    if str(s.check()) == 'unsat':
        return True
    else:
        return False
