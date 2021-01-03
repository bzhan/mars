"""Parsing for matlab functions."""

from lark import Lark, Transformer, v_args, exceptions

from ss2hcsp.matlab import function


grammar = r"""
    ?lname: CNAME -> var_expr

    ?atom_expr: lname
        | SIGNED_NUMBER -> num_expr
        | ESCAPED_STRING -> string_expr
        
    ?times_expr: times_expr "*" atom_expr -> times_expr
        | atom_expr

    ?plus_expr: plus_expr "+" times_expr -> plus_expr
        | times_expr

    ?expr: plus_expr

    ?assign_cmd: lname "=" expr ";" -> assign_cmd

    ?print_cmd: "fprintf" "(" expr ")" ";" -> print_cmd

    ?cmd: assign_cmd | print_cmd

    ?function: "function" CNAME (cmd)* -> function

    %import common.CNAME
    %import common.WS
    %import common.INT
    %import common.DECIMAL
    %import common.NUMBER
    %import common.SIGNED_NUMBER
    %import common.ESCAPED_STRING

    %ignore WS
"""

@v_args(inline=True)
class MatlabTransformer(Transformer):
    def __init__(self):
        pass

    def var_expr(self, s):
        return function.Var(str(s))

    def num_expr(self, v):
        return function.Const(float(v) if '.' in v or 'e' in v else int(v))

    def string_expr(self, s):
        return function.Const(str(s))

    def times_expr(self, e1, e2):
        return function.FunExpr('*', e1, e2)
    
    def plus_expr(self, e1, e2):
        return function.FunExpr('+', e1, e2)

    def assign_cmd(self, var_name, expr):
        return function.Assign(var_name, expr)

    def print_cmd(self, expr):
        return function.Print(expr)

    def function(self, *args):
        # First argument is name of the function
        # Remaining arguments are commands
        name, cmds = args[0], args[1:]
        return function.Function(name, cmds)


function_parser = Lark(grammar, start="function", parser="lalr", transformer=MatlabTransformer())
