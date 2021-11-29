"""Parsing for matlab functions."""

from lark import Lark, Transformer, v_args, exceptions

from ss2hcsp.matlab import function
from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import hcsp


grammar = r"""
    // Expressions
    ?arr_num: expr ((",")? expr)* -> arr_num

    ?string: /'.*?(?<!\\)'/ -> string_expr

    ?atom_expr: CNAME -> var_expr
        | NUMBER -> num_expr
        | ESCAPED_STRING -> string_expr
        | string
        | CNAME "(" ")" -> fun_expr
        | CNAME "(" expr ("," expr)* ")" -> fun_expr
        | "[" "]" -> list_expr
        | "[" expr ((",")? expr)* "]" -> list_expr
        | "[" arr_num (";" arr_num)* "]" -> list_expr2
        | "(" expr ")"
        | CNAME ("." CNAME)+ -> direct_name

    ?times_expr: times_expr "*" atom_expr -> times_expr
        | times_expr "/" atom_expr -> divide_expr
        | times_expr "%" atom_expr -> mod_expr
        | atom_expr

    ?plus_expr: plus_expr "+" times_expr -> plus_expr
        | plus_expr "-" times_expr -> minus_expr
        | "-" times_expr -> uminus_expr
        | times_expr

    ?expr: plus_expr

    // Conditions (boolean expressions)

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
        | "after" "(" expr "," event ")"  -> after_event
        | "before" "(" expr "," event ")"  -> before_event
        | "at" "(" expr "," event ")"  -> at_event
        | "every" "(" expr "," event ")"  -> every_event
        | expr


    
    ?conj: atom_cond "&&" conj | atom_cond     // Conjunction: priority 35

    ?disj: conj "||" disj | conj               // Disjunction: priority 30

    ?cond: disj 

    // Commands

    ?lname: CNAME -> var_lname
        | CNAME "(" expr ("," expr)* ")" -> fun_lname
        | "[" lname ("," lname)* "]" -> list_lname
        | CNAME ("." CNAME)+ -> direct_name
    
    // Assignment command includes possible type declarations
    ?assign_cmd: ("int" | "float")? lname "=" expr (";")?

    // Function call is also a command (this includes fprintf calls)
    ?func_cmd: CNAME "(" expr ("," expr)* ")" (";")? -> func_cmd_has_param
        | CNAME "(" ")" (";")?                       -> func_cmd_no_param

    ?ite_cmd: "if" cond cmd ("end")?("else" cmd ("end")?)? -> ite_cmd

    ?event: CNAME -> event
        | CNAME "." event -> directed_event
        | "after" "(" expr "," event ")"  -> after_event
        | "before" "(" expr "," event ")"  -> before_event
        | "at" "(" expr "," event ")"  -> at_event
        | "every" "(" expr "," event ")"  -> every_event

    ?event_cmd: event (";")? -> event_cmd

    ?atom_cmd: assign_cmd | func_cmd | event_cmd | ite_cmd

    ?seq_cmd: atom_cmd | atom_cmd seq_cmd

    ?cmd: seq_cmd

    // Definition of functions

    // Return value is either an CNAME or a list of CNAMEs
    ?return_var: "[" CNAME ("," CNAME)* "]" -> return_var
        | CNAME                             -> return_var_single

    // Signature of functions can be of three types: func, func(args) and x=func(args)
    ?func_sig: CNAME                                      -> func_sig_name
        | CNAME "(" ")"                                   -> func_sig_no_param
        | CNAME "(" CNAME ("," CNAME)* ")"                -> func_sig_has_param
        | return_var "=" CNAME                            -> func_sig_return_name
        | return_var "=" CNAME "(" ")"                    -> func_sig_return_no_param
        | return_var "=" CNAME "(" CNAME ("," CNAME)* ")" -> func_sig_return_has_param

    ?function: "function" func_sig cmd ("end")? -> function

    // Transitions

    ?cond_act: cmd -> cond_act
    ?tran_act: cmd -> tran_act
    ?transition: (event)? ("[" cond "]")? ("{" cond_act "}")? ("/{" tran_act "}")? -> transition

    ?entry_op: ("en" | "entry") ":" cmd -> entry_op
    ?during_op: ("du" | "during") ":" cmd ->during_op
    ?exit_op: ("ex" | "exit") ":" cmd  ->exit_op

    ?state_op: lname (entry_op)? (during_op)? (exit_op)? -> state_op
        | lname cmd  -> state_op

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
        if s == "true":
            return function.AConst(1)
        elif s == "false":
            return function.AConst(0)
        else:
            return function.Var(str(s))

    def num_expr(self, v):
        return function.AConst(float(v) if '.' in v or 'e' in v else int(v))

    def string_expr(self, s):
        return function.AConst(str(s)[1:-1])  # remo

    def fun_expr(self, fun_name, *exprs):
        return function.FunExpr(str(fun_name), *exprs)

    def list_expr(self, *args):
        return function.ListExpr(*args)

    def arr_num(self, *args):
        return function.ListExpr(*args)

    def list_expr2(self, *args):
        return function.ListExpr(*args)

    def num_expr(self, v):
        return function.AConst(float(v) if '.' in v or 'e' in v else int(v))

    def string_expr(self, s):
        # Remove quotes
        return function.AConst(str(s)[1:-1])

    def times_expr(self, e1, e2):
        return function.OpExpr("*", e1, e2)

    def divide_expr(self, e1, e2):
        return function.OpExpr("/", e1, e2)

    def mod_expr(self, e1, e2):
        return function.OpExpr("%", e1, e2)
    
    def plus_expr(self, e1, e2):
        return function.OpExpr("+", e1, e2)

    def minus_expr(self, e1, e2):
        return function.OpExpr("-", e1, e2)

    def uminus_expr(self, e):
        return function.OpExpr("-", e)

    def eq_cond(self, e1, e2):
        return function.RelExpr("==", e1, e2)

    def ineq_cond(self, e1, e2):
        return function.RelExpr("!=", e1, e2)

    def less_eq_cond(self, e1, e2):
        return function.RelExpr("<=", e1, e2)

    def less_cond(self, e1, e2):
        return function.RelExpr("<", e1, e2)

    def greater_eq_cond(self, e1, e2):
        return function.RelExpr(">=", e1, e2)

    def greater_cond(self, e1, e2):
        return function.RelExpr(">", e1, e2)

    def not_cond(self, e):
        return function.LogicExpr("~", e)

    def true_cond(self):
        return function.BConst(True)

    def false_cond(self):
        return function.BConst(False)

    def conj(self, b1, b2):
        return function.LogicExpr("&&", b1, b2)

    def disj(self, b1, b2):
        return function.LogicExpr("||", b1, b2)

    def var_lname(self, s):
        return function.Var(str(s))

    def fun_lname(self, fun_name, *exprs):
        return function.FunExpr(str(fun_name), *exprs)

    def list_lname(self, *args):
        return function.ListExpr(*args)

    def assign_cmd(self, lname, expr):
        return function.Assign(lname, expr)

    def func_cmd_has_param(self, name, *params):
        return function.FunctionCall(str(name), *params)

    def func_cmd_no_param(self, name):
        return function.FunctionCall(str(name))

    def ite_cmd(self,*args):
        cond, cmd1, cmd2=None,None,None
        if len(args) == 3:
            cond=args[0]
            cmd1=args[1]
            cmd2=args[2]
        elif len(args) == 2:
            cond=args[0]
            cmd1=args[1]
        return function.IfElse(cond, cmd1, cmd2)

    def seq_cmd(self, cmd1, cmd2):
        return function.Sequence(cmd1, cmd2)

    def event(self, name):
        name = str(name)
        if name in ('tick', 'wakeup'):
            return function.ImplicitEvent(name)
        elif name in ('sec', 'msec', 'usec'):
            return function.AbsoluteTimeEvent(name)
        else:
            return function.BroadcastEvent(name)

    def directed_event(self, state_name, event):
        return function.DirectedEvent(str(state_name), event)

    def after_event(self, expr, event):
        return function.TemporalEvent('after', expr, event)

    def before_event(self, expr, event):
        return function.TemporalEvent('before', expr, event)

    def at_event(self, expr, event):
        return function.TemporalEvent('at', expr, event)

    def every_event(self, expr, event):
        return function.TemporalEvent('every', expr, event)

    def event_cmd(self, event):
        return function.RaiseEvent(event)

    def return_var(self, *args):
        return tuple(str(arg) for arg in args)

    def return_var_single(self, arg):
        return str(arg)

    def func_sig_name(self, name):
        return str(name), (), None

    def func_sig_no_param(self, name):
        return str(name), (), None

    def func_sig_has_param(self, name, *params):
        return str(name), tuple(str(param) for param in params), None

    def func_sig_return_name(self, return_var, name):
        return str(name), (), return_var

    def func_sig_return_no_param(self, return_var, name):
        return str(name), (), return_var

    def func_sig_return_has_param(self, return_var, name, *params):
        return str(name), tuple(str(param) for param in params), return_var

    def function(self, func_sig, cmd):
        # First argument gives name and parameter of the function
        # Second argument is the function body
        name, params, return_var = func_sig
        return function.Function(name, params, cmd, return_var)

    def cond_act(self, cmd):
        return ("cond_act", cmd)

    def tran_act(self, cmd):
        return ("tran_act", cmd)

    def transition(self, *args):
        # There are at most four arguments, of type Event, BExpr, Command.
        # Both cond_act and tran_act are commands, so they are distinguished
        # by inserting "cond_act" and "tran_act" at the front.
        event, cond, cond_act, tran_act = None, None, None, None
        for arg in args:
            if isinstance(arg, function.Event):
                event = arg
            elif isinstance(arg, (function.BExpr,function.FunExpr)):
                cond = arg
            elif isinstance(arg, tuple) and arg[0] == "cond_act":
                cond_act = arg[1]
            elif isinstance(arg, tuple) and arg[0] == "tran_act":
                tran_act = arg[1]
            else:
                raise TypeError
        return function.TransitionLabel(event, cond, cond_act, tran_act)

    def direct_name(self,*expr):
        return function.DirectName([str(e) for e in expr])

    def entry_op(self,cmd):
        return function.StateInnerOperate("en",cmd)

    def during_op(self,cmd):
        return function.StateInnerOperate("du",cmd)

    def exit_op(self,cmd):
        return function.StateInnerOperate("ex",cmd)

    def state_op(self,*args):
        name, en_op, du_op, ex_op = None, None, None, None
        for arg in args:
            if isinstance(arg, function.Var):
                name = arg
            elif isinstance(arg, function.StateInnerOperate):
                if arg.name == "en":
                    en_op = arg
                elif arg.name == "du":
                    du_op=arg
                elif arg.name == "ex":
                    ex_op=arg
            elif isinstance(arg,function.Sequence):
                en_op=function.StateInnerOperate("en",arg)
        return function.StateOperate(name, en_op, du_op, ex_op)
   
       


expr_parser = Lark(grammar, start="expr", parser="lalr", transformer=MatlabTransformer())
cond_parser = Lark(grammar, start="cond", parser="lalr", transformer=MatlabTransformer())
cmd_parser = Lark(grammar, start="cmd", parser="lalr", transformer=MatlabTransformer())
event_parser = Lark(grammar, start="event", parser="lalr", transformer=MatlabTransformer())
func_sig_parser = Lark(grammar, start="func_sig", parser="lalr", transformer=MatlabTransformer())
function_parser = Lark(grammar, start="function", parser="lalr", transformer=MatlabTransformer())
transition_parser = Lark(grammar, start="transition", parser="lalr", transformer=MatlabTransformer())
state_op_parser=Lark(grammar, start="state_op", parser="lalr", transformer=MatlabTransformer())