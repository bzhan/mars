from lark import Lark, Transformer, v_args, exceptions
from ss2hcsp.matlab import function
from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import hcsp
from ss2hcsp.sf.sf_parser import cond_tran

grammar = r"""
    ?lname: CNAME -> var_expr
        | func_cmd
       
    ?atom_expr: lname
        | SIGNED_NUMBER -> num_expr
        | ESCAPED_STRING -> string_expr
        | lname ("." lname)+ -> direct_name

    ?return_var: "[" lname ("," lname)* "]" -> return_var
        | lname

    ?times_expr: times_expr "*" atom_expr -> times_expr
        | times_expr "/" atom_expr -> divide_expr
        | times_expr "%" atom_expr -> mod_expr
        | atom_expr

    ?plus_expr: plus_expr "+" times_expr -> plus_expr
        | plus_expr "-" times_expr -> minus_expr
        | "-" times_expr -> uminus_expr
        | times_expr

    ?expr: plus_expr

    ?assign_cmd: return_var "=" expr -> assign_cmd

    ?func_cmd: CNAME "(" expr ("," expr)*")" (";")? -> func_has_pra_cmd
            | CNAME "(" ")" (";")? -> func_no_pra_cmd 

    ?event: lname 

    ?cmd: assign_cmd | event

    ?seq_cmd: cmd (";" cmd)* (";")? -> seq_cmd

    ?boolean_expr: "true" -> true_cond
        | "false" -> false_cond
        | atom_expr

    ?atom_cond: expr "==" expr -> eq_cond
        | expr "!=" expr -> ineq_cond
        | expr "<=" expr -> less_eq_cond
        | expr "<" expr -> less_cond
        | expr ">=" expr -> greater_eq_cond
        | expr ">" expr -> greater_cond
        | "~" cond -> not_cond
        | boolean_expr
        | "(" cond ")"
        | func_cmd "==" expr  ->func_cmd_cond
    
    ?conj: atom_cond "&&" conj | atom_cond     // Conjunction: priority 35

    ?disj: conj "||" disj | conj   // Disjunction: priority 30

    ?cond: disj

    ?cond_tran: event "[" cond "]" "{" seq_cmd "}" "/{" seq_cmd "}" -> cond_tran
        | "[" cond "]" "{" seq_cmd "}" "/{" seq_cmd "}" -> cond_tran1
        | event "{" seq_cmd "}" "/{" seq_cmd "}" -> cond_tran2
        | event "{" seq_cmd "}" -> cond_tran3
        | event "/{" seq_cmd "}" -> cond_tran4
        | "{" seq_cmd "}" "/{" seq_cmd "}" -> cond_tran5
        | "/{" seq_cmd "}" -> cond_tran6
        | "[" cond "]" "{" seq_cmd "}" -> cond_tran7
        | "[" cond "]" "/{" seq_cmd "}" -> cond_tran8
        | "{" seq_cmd "}" -> cond_tran9
        | event "[" cond "]" "{" seq_cmd "}" -> cond_tran10
        | "[" cond "]" ->cond_tran11
        | event -> cond_tran12
        | event "[" cond "]" -> cond_tran13

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
        return cond_tran.AVar(str(s))

    def return_var(self, *args):
        if all(isinstance(arg, (cond_tran.AVar,cond_tran.FunExpr)) for arg in args):
            return cond_tran.ListExpr(list(arg for arg in args))
        else:
            return cond_tran.ListExpr(*list(cond_tran.AVar(arg) for arg in args))

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

    def func_cmd_cond(self,e1,e2):
        return cond_tran.CondExpr('==',e1,e2) 

    def cond_tran(self,event,cond,cond_act,tran_act):
        return cond_tran.CondTran(event,cond,cond_act,tran_act)
    def cond_tran1(self,cond,cond_act,tran_act):
        return cond_tran.CondTran('',cond,cond_act,tran_act)    
    def cond_tran2(self,event,cond_act,tran_act):
        return cond_tran.CondTran(event,'',cond_act,tran_act)  
    def cond_tran3(self,event,cond_act):
        return cond_tran.CondTran(event,'',cond_act,'')
    def cond_tran4(self,event,tran_act):
        return cond_tran.CondTran(event,'','',tran_act)
    def cond_tran5(self,cond_act,tran_act):
        return cond_tran.CondTran('','',cond_act,tran_act)
    def cond_tran6(self,tran_act):
        return cond_tran.CondTran('','','',tran_act)
    def cond_tran7(self,cond,cond_act):
        return cond_tran.CondTran('',cond,cond_act,'')    
    def cond_tran8(self,cond,tran_act):
        return cond_tran.CondTran('',cond,'',tran_act)                                                                              
    def cond_tran9(self,cond_act):
        return cond_tran.CondTran('','',cond_act,'') 
    def cond_tran10(self,event,cond,cond_act):
        return cond_tran.CondTran(event,cond,cond_act,'') 
    def cond_tran11(self,cond):
        return cond_tran.CondTran('',cond,'','') 
    def cond_tran12(self,event):
        return cond_tran.CondTran(event,'','','') 
    def cond_tran13(self,event,cond):
        return cond_tran.CondTran(event,cond,'','') 
    def assign_cmd(self, var_name, expr):
        return function.Assign(var_name, expr)
    
    def direct_name(self,*expr):
        return cond_tran.DirectName(expr)

    def func_no_pra(self,return_var, fun_name):
        return cond_tran.matFunExpr(return_var,fun_name)

    def func_has_pra(self,return_var,fun_name,*args):
        return cond_tran.matFunExpr(return_var,fun_name,args)

    # def func_no_pra1(self,return_var, fun_name):
    #     return function.matFunExpr(return_var,fun_name)

    # def func_has_pra1(self,return_var,fun_name,*args):
    #     return function.matFunExpr(return_var,fun_name,args)

    def func_has_pra_cmd(self, fun_name, *exprs):
        return cond_tran.FunExpr(fun_name, exprs)

    def func_no_pra_cmd(self, fun_name, *exprs):
        return cond_tran.FunExpr(fun_name, "")

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

    def seq_cmd(self, *args):
        if len(args) == 1:
            return args[0]
        else:
            return hcsp.Sequence(*args)
    def array_idx_expr1(self, a, i):
        return cond_tran.ArrayIdxExpr(cond_tran.AVar(str(a)), i)

    def array_idx_expr1_2(self, a, i,j):
        return cond_tran.ArrayIdxExpr(cond_tran.ArrayIdxExpr(cond_tran.AVar(str(a)), i), j)

    def array_idx_expr1_3(self, a, i,j,k):
        return cond_tran.ArrayIdxExpr(cond_tran.ArrayIdxExpr(cond_tran.ArrayIdxExpr(cond_tran.AVar(str(a)), i), j),k)

transition_parser = Lark(grammar, start="cond_tran", parser="lalr", transformer=MatlabTransformer())
condition_parser = Lark(grammar, start="cond", parser="lalr", transformer=MatlabTransformer())
