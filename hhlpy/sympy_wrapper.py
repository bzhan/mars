"""Wrapper for SymPy"""

from decimal import Decimal
from fractions import Fraction

import sympy
from sympy.logic.boolalg import BooleanFunction, BooleanAtom, BooleanTrue, BooleanFalse

from ss2hcsp.hcsp import expr

def toSpexpr(e):
    """Conversion from hcsp expression to sympy expression"""
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
            return sympy.symbols(e.fun_name)
        else:
            raise NotImplementedError
    elif isinstance(e, expr.OpExpr):
        if e.op == '+':
            return sympy.Add(toSpexpr(e.exprs[0]), toSpexpr(e.exprs[1]))
        elif e.op == '-':
            if len(e.exprs) == 1:
                return sympy.Mul(sympy.S.NegativeOne, toSpexpr(e.exprs[0]))
            else:
                return sympy.Add(toSpexpr(e.exprs[0]), 
                                 sympy.Mul(sympy.S.NegativeOne, toSpexpr(e.exprs[1])))
        elif e.op == '*':
            return sympy.Mul(toSpexpr(e.exprs[0]), toSpexpr(e.exprs[1]))
        elif e.op == '/':
            return sympy.Mul(toSpexpr(e.exprs[0]),
                             sympy.Pow(toSpexpr(e.exprs[1]), sympy.S.NegativeOne))
        elif e.op == '^':
            return sympy.Pow(toSpexpr(e.exprs[0]), toSpexpr(e.exprs[1]))
    elif isinstance(e, expr.RelExpr):
        if e.op == '<':
            return sympy.Rel(toSpexpr(e.expr1), toSpexpr(e.expr2), '<')
        elif e.op == '<=':
            return sympy.Rel(toSpexpr(e.expr1), toSpexpr(e.expr2), '<=')
        elif e.op == '>':
            return sympy.Rel(toSpexpr(e.expr1), toSpexpr(e.expr2), '>')
        elif e.op == '>=':
            return sympy.Rel(toSpexpr(e.expr1), toSpexpr(e.expr2), '>=')
        elif e.op == '==':
            return sympy.Rel(toSpexpr(e.expr1), toSpexpr(e.expr2), '==')
        elif e.op == '!=':
            return sympy.Rel(toSpexpr(e.expr1), toSpexpr(e.expr2), '!=')
    elif isinstance(e, expr.LogicExpr):
        if e.op == '&&':
            return sympy.And(toSpexpr(e.exprs[0]), toSpexpr(e.exprs[1]))
        elif e.op == '||':
            return sympy.Or(toSpexpr(e.exprs[0]), toSpexpr(e.exprs[1]))
        elif e.op == '~':
            return sympy.Not(toSpexpr(e.exprs[0]))
        elif e.op == '-->':
            return sympy.Implies(toSpexpr(e.exprs[0]), toSpexpr(e.exprs[1]))
        elif e.op == '<-->':
            return sympy.Equivalent(toSpexpr(e.exprs[0]), toSpexpr(e.exprs[1]))
    else:
        raise NotImplementedError

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
            return expr.LogicExpr('~', toHcsp(e.args[0]))
        elif isinstance(e, sympy.Implies):
            assert len(e.args) == 2
            return expr.LogicExpr('-->', toHcsp(e.args[0]), toHcsp(e.args[1]))
        elif isinstance(e, sympy.Equivalent):
            assert len(e.args) == 2
            return expr.LogicExpr('<-->', toHcsp(e.args[0]), toHcsp(e.args[1]))
        else:
            raise NotImplementedError

def sp_simplify(e):
    """Simplify the given expression by sympy"""
    sp_expr = toSpexpr(e)
    sp_expr = sympy.simplify(sp_expr)
    hcsp_expr = toHcsp(sp_expr)

    return hcsp_expr
    