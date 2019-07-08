"""Parser for expressions."""

from lark import Lark, Transformer, v_args, exceptions
from ss2hcsp.hcsp import expr


grammar = r"""
    ?expr: CNAME -> var_expr
        | INT -> num_expr
        | expr "+" expr -> plus_expr
        | expr "-" expr -> minus_expr
        | expr "*" expr -> times_expr
        | "(" expr ")"

    ?atom_cond: expr "==" expr -> eq_cond
        | expr "!=" expr -> ineq_cond
        | expr "<=" expr -> less_eq_cond
        | expr "<" expr -> less_cond
        | expr ">=" expr -> greater_eq_cond
        | expr ">" expr -> greater_cond
        | "true" -> true_cond
        | "false" -> false_cond
        | "(" cond ")"
    
    ?conj: atom_cond "&&" conj | atom_cond     // Conjunction: priority 35

    ?disj: conj "||" disj | conj   // Disjunction: priority 30

    ?imp: disj "-->" imp | disj  // Implies: priority 25

    ?cond: imp

    %import common.CNAME
    %import common.WS
    %import common.INT

    %ignore WS
"""

@v_args(inline=True)
class HPTransformer(Transformer):
    def __init__(self):
        pass

    def var_expr(self, s):
        return expr.AVar(str(s))

    def num_expr(self, v):
        return expr.AConst(int(v))

    def plus_expr(self, e1, e2):
        return expr.PlusExpr(["+", "+"], [e1, e2])

    def minus_expr(self, e1, e2):
        return expr.PlusExpr(["+", "-"], [e1, e2])

    def times_expr(self, e1, e2):
        return expr.TimesExpr(["*", "*"], [e1, e2])

    def eq_cond(self, e1, e2):
        return expr.RelExpr("==", e1, e2)

    def ineq_cond(self, e1, e2):
        return expr.RelExpr("!=", e1, e2)

    def less_eq_cond(self, e1, e2):
        return expr.RelExpr("<=", e1, e2)

    def less_cond(self, e1, e2):
        return expr.RelExpr("<", e1, e2)

    def greater_eq_cond(self, e1, e2):
        return expr.RelExpr(">=", e1, e2)

    def greater_cond(self, e1, e2):
        return expr.RelExpr(">", e1, e2)

    def true_cond(self):
        return expr.BConst(True)

    def false_cond(self):
        return expr.BConst(False)

    def conj(self, b1, b2):
        return expr.conj(b1, b2)

    def disj(self, b1, b2):
        return expr.disj(b1, b2)

    def imp(self, b1, b2):
        return expr.imp(b1, b2)

aexpr_parser = Lark(grammar, start="expr", parser="lalr", transformer=HPTransformer())
bexpr_parser = Lark(grammar, start="cond", parser="lalr", transformer=HPTransformer())
