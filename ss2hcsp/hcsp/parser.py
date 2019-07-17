"""Parser for expressions."""

from lark import Lark, Transformer, v_args, exceptions
from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import hcsp

grammar = r"""
    ?expr: CNAME -> var_expr
        | INT -> num_expr
        | expr "+" expr -> plus_expr
        | expr "-" expr -> minus_expr
        | expr "*" expr -> times_expr
        | expr "%" expr -> mod_expr
        | "min" "(" expr "," expr ")" -> min_expr
        | "max" "(" expr "," expr ")" -> max_expr
        | "gcd" "(" expr ("," expr)+ ")" -> gcd_expr
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

    ?comm_cmd: CNAME "?" CNAME -> input_cmd
        | CNAME "!" expr -> output_cmd

    ?ode_seq: CNAME "=" expr ("," CNAME "=" expr)*

    ?interrupt: comm_cmd "-->" cmd ("," comm_cmd "-->" cmd)*

    ?cmd: "skip" -> skip_cmd
        | "wait" "(" INT ")" -> wait_cmd
        | CNAME ":=" expr -> assign_cmd
        | cmd ";" cmd -> seq_cmd
        | comm_cmd
        | "(" cmd ")*" -> repeat_cmd
        | "<" ode_seq "&" cond ">" -> ode
        | "<" ode_seq "&" cond ">" "|>" "[]" "(" interrupt ")" -> ode_comm
        | cond "->" "(" cmd ")" -> cond_cmd

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

    def min_expr(self, e1, e2):
        return expr.FunExpr("min", [e1, e2])

    def max_expr(self, e1, e2):
        return expr.FunExpr("max", [e1, e2])

    def mod_expr(self, e1, e2):
        return expr.ModExpr(e1, e2)

    def gcd_expr(self, *exprs):
        return expr.FunExpr(fun_name="gcd", exprs=exprs)

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

    def skip_cmd(self):
        return hcsp.Skip()

    def wait_cmd(self, delay):
        return hcsp.Wait(int(delay))

    def assign_cmd(self, var, expr):
        return hcsp.Assign(var, expr)

    def seq_cmd(self, c1, c2):
        if c2.type == "sequence":
            return hcsp.Sequence(*([c1] + c2.hps))
        else:
            return hcsp.Sequence(c1, c2)

    def input_cmd(self, ch_name, var_name):
        ch_name = str(ch_name)
        var_name = str(var_name)
        return hcsp.InputChannel(ch_name, var_name)

    def output_cmd(self, ch_name, expr):
        ch_name = str(ch_name)
        return hcsp.OutputChannel(ch_name, expr)

    def repeat_cmd(self, cmd):
        return hcsp.Loop(cmd)

    def ode_seq(self, *args):
        res = []
        for i in range(0,len(args),2):
            assert args[i].endswith("_dot")
            res.append((args[i][:-4], args[i+1]))
        return res

    def interrupt(self, *args):
        res = []
        for i in range(0,len(args),2):
            res.append((args[i], args[i+1]))
        return res

    def ode(self, eqs, constraint):
        return hcsp.ODE(eqs, constraint)

    def ode_comm(self, eqs, constraint, io_comms):
        return hcsp.ODE_Comm(eqs, constraint, io_comms)

    def cond_cmd(self, cond, cmd):
        return hcsp.Condition(cond=cond, hp=cmd)


aexpr_parser = Lark(grammar, start="expr", parser="lalr", transformer=HPTransformer())
bexpr_parser = Lark(grammar, start="cond", parser="lalr", transformer=HPTransformer())
hp_parser = Lark(grammar, start="cmd", parser="lalr", transformer=HPTransformer())
