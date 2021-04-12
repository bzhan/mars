"""Parsing for matlab functions."""

from lark import Lark, Transformer, v_args, exceptions

from ss2hcsp.matlab import function
from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import hcsp


grammar = r"""
    ?lname: CNAME -> var_expr
        
    ?return_var:"[" CNAME ("," CNAME)* "]" -> return_var
        | lname 

    ?atom_expr: lname
        | SIGNED_NUMBER -> num_expr
        | ESCAPED_STRING -> string_expr
        | "(" expr ")"
        | "min" "(" expr "," expr ")" -> min_expr
        | "max" "(" expr "," expr ")" -> max_expr
        | "gcd" "(" expr ("," expr)+ ")" -> gcd_expr
      
   
        
    ?times_expr: times_expr "*" atom_expr -> times_expr
        | times_expr "/" atom_expr -> divide_expr
        | times_expr "%" atom_expr -> mod_expr
        | atom_expr
        | "(" times_expr ")"
       
    

    ?plus_expr: plus_expr "+" times_expr -> plus_expr
        | plus_expr "-" times_expr -> minus_expr
        | "-" times_expr -> uminus_expr
        | times_expr

       

    ?expr: plus_expr

    ?assign_cmd: ("int" | "float")? return_var "=" expr ";" -> assign_cmd
        | ("int" | "float")? return_var "=" lname "(" atom_expr ("," atom_expr)*")" (";")?-> func_has_pra
        | ("int" | "float")? return_var  "="  lname "(" ")" (";")? -> func_no_pra
        | ("int" | "float")? return_var  "="  lname  (";")? -> func_no_pra

    ?assign_func: assign_cmd
        | lname
        | func_cmd

    ?print_cmd: "fprintf" "(" expr ")" ";" -> print_cmd

    ?func_cmd: lname "(" atom_expr ("," atom_expr)*")" (";")?-> func_has_pra_cmd
            | lname "(" ")" (";")?-> func_no_pra_cmd
            

    ?cmd: assign_cmd | print_cmd | func_cmd | ite_cmd

    ?seq_cmd: cmd (cmd)* 

    ?atom_cond: expr "==" expr -> eq_cond
        | expr "!=" expr -> ineq_cond
        | expr "<=" expr -> less_eq_cond
        | expr "<" expr -> less_cond
        | expr ">=" expr -> greater_eq_cond
        | expr ">" expr -> greater_cond
        | "~" cond -> not_cond
        | "true" -> true_cond
        | "false" -> false_cond
        | "(" cond ")"
    
    ?conj: atom_cond "&&" conj | atom_cond     // Conjunction: priority 35

    ?disj: conj "||" disj | conj   // Disjunction: priority 30

    ?cond: disj

    ?ite_cmd:"if" cond seq_cmd (ite_cmd)* "else" seq_cmd (ite_cmd)* "end" -> ite_cmd

    ?function: "function" assign_func (cmd)* -> function

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

    def return_var(self, *args):
        if all(isinstance(arg, function.Var) for arg in args):
            return function.ListExpr(list(arg.value for arg in args))
        else:
            return function.ListExpr(*list(function.Var(arg.value) for arg in args))

    def num_expr(self, v):
        return function.Const(float(v) if '.' in v or 'e' in v else int(v))

    def string_expr(self, s):
        return function.Const(str(s))

    def times_expr(self, e1, e2):
        return function.TimesExpr(["*", "*"], [e1, e2])

    def divide_expr(self, e1, e2):
        return function.TimesExpr(["*", "/"], [e1, e2])

    def minus_expr(self, e1, e2):
        return function.PlusExpr(["+", "-"], [e1, e2])

    def uminus_expr(self, e):
        return function.PlusExpr(["-"], [e])

    def mod_expr(self, e1, e2):
        return function.ModExpr(e1, e2)
    
    def plus_expr(self, e1, e2):
        signs, exprs = [], []
        if isinstance(e1, expr.PlusExpr):
            signs.extend(e1.signs)
            exprs.extend(e1.exprs)
        else:
            signs.append('+')
            exprs.append(e1)
        if isinstance(e2, expr.PlusExpr):
            signs.extend(e2.signs)
            exprs.extend(e2.exprs)
        else:
            signs.append('+')
            exprs.append(e2)
        return function.PlusExpr(signs, exprs)

    def min_expr(self, e1, e2):
        return function.FunExpr("min", [e1, e2])

    def max_expr(self, e1, e2):
        return function.FunExpr("max", [e1, e2])
    def gcd_expr(self, *exprs):
        return function.FunExpr(fun_name="gcd", exprs=exprs)

    def fun_expr(self, fun_name, *exprs):
        return function.FunExpr(fun_name, exprs)
    # def first_used(self,e1):
    #     return function.FunExpr('+',e1, function.Const(1)) 

    # def first_plus(self,e1):
    #     return function.FunExpr('+',e1, function.Const(1))                                                                                                         

    def assign_cmd(self, var_name, expr):
        return function.Assign(var_name, expr)

    def print_cmd(self, expr):
        return function.Print(expr)

    def function(self, *args):
        # First argument is name of the function
        # Remaining arguments are commands
        name, cmds = args[0], args[1:]
        return function.Function(name, cmds)

    def func_no_pra(self,return_var, fun_name,*exprs):
        return function.matFunExpr(return_var,fun_name,"")

    def func_has_pra(self,return_var,fun_name,*exprs):
        return function.matFunExpr(return_var, fun_name, exprs)

    # def func_no_pra1(self,return_var, fun_name):
    #     return function.matFunExpr(return_var,fun_name)

    # def func_has_pra1(self,return_var,fun_name,*args):
    #     return function.matFunExpr(return_var,fun_name,args)

    def func_has_pra_cmd(self,fun_name, *exprs):
        return function.FunExpr(fun_name, exprs)

    def func_no_pra_cmd(self,fun_name,*exprs):

        return function.FunExpr(fun_name,"")

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

    def not_cond(self, e):
        return expr.NegExpr(e)

    def true_cond(self):
        return expr.BConst(True)

    def false_cond(self):
        return expr.BConst(False)

    def conj(self, b1, b2):
        return expr.LogicExpr("&&", b1, b2)

    def disj(self, b1, b2):
        return expr.LogicExpr("||", b1, b2)

    def ite_cmd(self, *args):
        assert len(args) % 2 == 1 and len(args) >= 3
        if_hps = []
        for i in range(0, len(args)-1, 2):
            if_hps.append((args[i], args[i+1]))
        else_hp = args[-1]
        return hcsp.ITE(if_hps, else_hp)
    def seq_cmd(self, *args):
        if len(args) == 1:
            return args[0]
        else:
            return hcsp.Sequence(*args)


function_parser = Lark(grammar, start="function", parser="lalr", transformer=MatlabTransformer())
