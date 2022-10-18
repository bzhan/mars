"""Wrapper for SymPy"""

from decimal import Decimal
from fractions import Fraction

import sympy
from sympy.logic.boolalg import BooleanFunction, BooleanAtom, BooleanTrue, BooleanFalse

from ss2hcsp.hcsp import expr

def toSpexpr(e, functions):
    """Conversion from hcsp expression to sympy expression"""
    def rec(e):
        if isinstance(e, expr.AVar):
            return sympy.symbols(e.name)
        elif isinstance(e, expr.AConst):
            if isinstance(e.value, Decimal):
                return sympy.Rational(str(e.value))
            elif isinstance(e.value, (int, float, Fraction)):
                return sympy.sympify(e.value)
            else:
                raise NotImplementedError
        elif isinstance(e, expr.BConst):
            return sympy.sympify(e.value) 
        elif isinstance(e, expr.FunExpr):
            if len(e.exprs) == 0:          
                return sympy.symbols(str(e))
            elif e.fun_name in functions:
                return rec(expr.replace_function(e, functions))
            else:
                raise NotImplementedError
        elif isinstance(e, expr.OpExpr):
            if e.op == '+':
                return sympy.Add(rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == '-':
                if len(e.exprs) == 1:
                    return sympy.Mul(sympy.S.NegativeOne, rec(e.exprs[0]))
                else:
                    return sympy.Add(rec(e.exprs[0]), 
                                    sympy.Mul(sympy.S.NegativeOne, rec(e.exprs[1])))
            elif e.op == '*':
                return sympy.Mul(rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == '/':
                return sympy.Mul(rec(e.exprs[0]),
                                sympy.Pow(rec(e.exprs[1]), sympy.S.NegativeOne))
            elif e.op == '^':
                return sympy.Pow(rec(e.exprs[0]), rec(e.exprs[1]))
            else:
                raise NotImplementedError
        elif isinstance(e, expr.RelExpr):
            if e.op == '<':
                return sympy.Rel(rec(e.expr1), rec(e.expr2), '<')
            elif e.op == '<=':
                return sympy.Rel(rec(e.expr1), rec(e.expr2), '<=')
            elif e.op == '>':
                return sympy.Rel(rec(e.expr1), rec(e.expr2), '>')
            elif e.op == '>=':
                return sympy.Rel(rec(e.expr1), rec(e.expr2), '>=')
            elif e.op == '==':
                return sympy.Rel(rec(e.expr1), rec(e.expr2), '==')
            elif e.op == '!=':
                return sympy.Rel(rec(e.expr1), rec(e.expr2), '!=')
            else:
                raise NotImplementedError
        elif isinstance(e, expr.LogicExpr):
            if e.op == '&&':
                return sympy.And(rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == '||':
                return sympy.Or(rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == '!':
                return sympy.Not(rec(e.exprs[0]))
            elif e.op == '->':
                return sympy.Implies(rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == '<->':
                return sympy.Equivalent(rec(e.exprs[0]), rec(e.exprs[1]))
            else:
                raise NotImplementedError
        else:
            raise NotImplementedError

    return rec(e)

def toHcsp(e):
    """Conversion from sympy expression to hcsp expression"""
    if isinstance(e, sympy.Symbol):
        return expr.AVar(e.name)
    elif isinstance(e, sympy.Number):
        if isinstance(e, sympy.Float):
            return expr.AConst(float(e))
        elif isinstance(e, sympy.Rational):
            if isinstance(e, sympy.Integer):
                return expr.AConst(int(e))
            # sympy.Raitonal(2, 3)
            else:
                return expr.AConst(Fraction(e.p, e.q))
        else:
            raise NotImplementedError
    elif isinstance(e, BooleanAtom):
        if isinstance(e, BooleanTrue):
            return expr.true_expr
        else:
            return expr.false_expr
    elif isinstance(e, sympy.Rel):
        if e.rel_op == '<':
            return expr.RelExpr('<', toHcsp(e.args[0]), toHcsp(e.args[1]))
        elif e.rel_op == '<=':
            return expr.RelExpr('<=', toHcsp(e.args[0]), toHcsp(e.args[1]))
        elif e.rel_op == '>':
            return expr.RelExpr('>', toHcsp(e.args[0]), toHcsp(e.args[1]))
        elif e.rel_op == '>=':
            return expr.RelExpr('>=', toHcsp(e.args[0]), toHcsp(e.args[1]))
        elif e.rel_op == '==':
            return expr.RelExpr('==', toHcsp(e.args[0]), toHcsp(e.args[1]))
        elif e.rel_op == '!=':
            return expr.RelExpr('!=', toHcsp(e.args[0]), toHcsp(e.args[1]))
    
    elif isinstance(e, sympy.Add):
        return expr.list_add(*(toHcsp(arg) for arg in e.args))
    elif isinstance(e, sympy.Mul):
        return expr.list_mul(*(toHcsp(arg) for arg in e.args))
    elif isinstance(e, sympy.Pow):
        assert len(e.args) == 2
        return expr.OpExpr('^', toHcsp(e.args[0]), toHcsp(e.args[1]))

    elif isinstance(e, BooleanFunction):
        if isinstance(e, sympy.And):
            return expr.list_conj(*(toHcsp(arg) for arg in e.args))
        elif isinstance(e, sympy.Or):
            return expr.list_disj(*(toHcsp(arg) for arg in e.args))
        elif isinstance(e, sympy.Not):
            assert len(e.args) == 1
            return expr.LogicExpr('!', toHcsp(e.args[0]))
        elif isinstance(e, sympy.Implies):
            assert len(e.args) == 2
            return expr.LogicExpr('->', toHcsp(e.args[0]), toHcsp(e.args[1]))
        elif isinstance(e, sympy.Equivalent):
            assert len(e.args) == 2
            return expr.LogicExpr('<->', toHcsp(e.args[0]), toHcsp(e.args[1]))
        else:
            raise NotImplementedError

def sp_simplify(e, functions=dict()):
    """Simplify the given expression by sympy"""
    sp_expr = toSpexpr(e, functions)
    sp_expr = sympy.simplify(sp_expr)
    hcsp_expr = toHcsp(sp_expr)

    return hcsp_expr

def sp_polynomial_div(p, q, functions=dict()):
    """Compute the quotient and remainder of polynomial p and q"""
    p = toSpexpr(p, functions)
    q = toSpexpr(q, functions)
    quot, remain = sympy.div(p, q)

    quot = toHcsp(quot)
    remain = toHcsp(remain)
    quot_remains = dict()
    quot_remains[quot] = remain

    return quot_remains

def sp_is_polynomial(e, constants=set(), functions=dict()):
    """Return True if the given expression is a polynomial and False otherwise"""
    vars = e.get_vars().difference(constants)
    vars = {sympy.Symbol(var) for var in vars}

    e = toSpexpr(e, functions)

    result = e.is_polynomial(*vars)

    return result