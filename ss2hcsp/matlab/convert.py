"""Conversion from Matlab functions to HCSP."""

from ss2hcsp.matlab import function
from ss2hcsp.hcsp import expr, hcsp
from ss2hcsp.sf.sf_state import GraphicalFunction


def subtract_one(e):
    assert isinstance(e, expr.AExpr)
    if isinstance(e, expr.AConst):
        return expr.AConst(e.value - 1)
    else:
        return expr.PlusExpr(["+", "-"], [e, expr.AConst(1)])

def convert_expr(e, *, procedures=None, arrays=None,array_value=None,messages=None):

    """Convert a Matlab expression to HCSP.

    Since there are possibly functions that should be evaluated,
    part of the expression may be converted to procedures. Hence,
    the return value is a pair (pre_act, expr).
    
    arrays - set(str): names that should be interpreted as arrays (instead of functions).

    """
    if arrays is None:
        arrays = set()
    
    pre_acts = []

    def rec(e):
        if isinstance(e, function.Var):
            return expr.AVar(e.name)
        elif isinstance(e, function.ListExpr):
            return expr.ListExpr(*(rec(arg) for arg in e.args))
        elif isinstance(e, (function.AConst, int, str)):
            if isinstance(e, (int, str)):
                return expr.AConst(e)
            else:
                return expr.AConst(e.value)
        elif isinstance(e,function.DirectName):
            sname=e.exprs[0]
            if str(sname) in messages.keys():
                pre_acts.append(hcsp.Assign(expr.AVar(str(e)),messages[str(sname)].data))
            return expr.AVar(str(e))    
        elif isinstance(e, function.OpExpr):
            if e.op_name == '-' and len(e.exprs) == 1:
                return expr.PlusExpr(['-'], [rec(e.exprs[0])])
            elif e.op_name == '+':
                return expr.PlusExpr(['+', '+'], [rec(e.exprs[0]), rec(e.exprs[1])])
            elif e.op_name == '-':
                return expr.PlusExpr(['+', '-'], [rec(e.exprs[0]), rec(e.exprs[1])])
            elif e.op_name == '*':
                return expr.TimesExpr(['*', '*'], [rec(e.exprs[0]), rec(e.exprs[1])])
            elif e.op_name == '/':
                return expr.TimesExpr(['*', '/'], [rec(e.exprs[0]), rec(e.exprs[1])])
            elif e.op_name == '%':
                return expr.ModExpr(rec(e.exprs[0]), rec(e.exprs[1]))
            else:
                raise NotImplementedError("Unknown operator %s" % e.op_name)
        elif isinstance(e, function.FunExpr):
            if e.fun_name == 'rand':
                if len(e.exprs) == 0:
                    return expr.FunExpr('uniform', [expr.AConst(0), expr.AConst(1)])
                else:
                    raise NotImplementedError("Function rand: argument not supported")
            elif e.fun_name in arrays:
                # Subtract one since indexing in Matlab is 1-based while indexing
                # in HCSP is 0-based.
                if len(e.exprs) == 1:
                    return expr.ArrayIdxExpr(e.fun_name, [subtract_one(rec(arg)) for arg in e.exprs])
                elif len(e.exprs) == 2:
                    return expr.ArrayIdxExpr(expr.ArrayIdxExpr(expr.AVar(e.fun_name),subtract_one(rec(e.exprs[0]))),subtract_one(rec(e.exprs[1])))
                elif len(e.exprs) == 3:
                    return expr.ArrayIdxExpr(expr.ArrayIdxExpr(expr.ArrayIdxExpr(expr.AVar(e.fun_name),subtract_one(rec(e.exprs[0]))),subtract_one(rec(e.exprs[1]))),subtract_one(rec(e.exprs[2])))
            elif procedures is not None and e.fun_name in procedures:
                proc = procedures[e.fun_name]
                if isinstance(proc, GraphicalFunction):
                    if len(e.exprs) > 0:
                        for index in range(0,len(e.exprs)):
                            pre_acts.append(hcsp.Assign(expr.AVar(proc.params[index]),rec(e.exprs[index])))
                    pre_acts.append(hcsp.Var(e.fun_name))
                    if isinstance(proc.return_var,str):
                        pre_acts.append(hcsp.Assign(expr.AVar(e.fun_name+"_"+proc.return_var),expr.AVar(proc.return_var)))
                        return expr.AVar(str(e.fun_name)+"_"+proc.return_var)
                    elif isinstance(proc.return_var,tuple):
                        return expr.ListExpr(*( expr.AVar(arg) for arg in proc.return_var))
                else:
                    pre_acts.append(convert_cmd(proc.instantiate(), procedures=procedures, arrays=arrays))
                    return expr.AVar(proc.return_var)
            else:
                return expr.FunExpr(e.fun_name, [rec(ex) for ex in e.exprs])
        elif isinstance(e, function.BConst):
            if e.value:
                return expr.AConst("1")
            else:
                return expr.AConst("0")
        elif isinstance(e, function.LogicExpr):
            if e.op_name == '~':
                return expr.NegExpr(rec(e.exprs[0]))
            else:
                return expr.LogicExpr(e.op_name, rec(e.exprs[0]), rec(e.exprs[1]))
        elif isinstance(e, function.RelExpr):
            return expr.RelExpr(e.op, rec(e.expr1), rec(e.expr2))
        else:
            raise NotImplementedError("Unrecognized matlab expression: %s" % str(e))

    res = rec(e)
    return hcsp.seq(pre_acts), res


def convert_cmd(cmd, *, raise_event=None, procedures=None, still_there=None, arrays=None,array_value=None,events=None,messages=None):

    """Convert a Matlab command to HCSP.
    
    raise_event : Event -> HCSP - specifies translation for raising events.
        If this is set to None, then an error is raised whenever cmd contains
        RaiseEvent. Otherwise, this function is used to convert raising the event
        into an HCSP program.

    procedures : dict(str, Procedure) - mapping from procedure names to
        procedure objects.

    still_there : expr.BExpr - continue execution only if this condition holds.

    arrays : set(str) - names that should be interpreted as arrays (instead of functions).

    There are three possible options for converting procedure calls:
    1. splice the body of the procedure into the code.
    2. for procedures without arguments, insert call to procedure.
    3. for procedures with arguments, insert call, using a stack to keep track
       of arguments.
    Currently we choose option 2 for procedures without arguments, and option 1
    for procedures with arguments.

    """
    def conv_expr(e):
        return convert_expr(e, procedures=procedures, arrays=arrays,array_value=array_value,messages=messages)


    def conv_exprs(es):
        # Convert a list of expressions
        pre_acts, res = [], []
        for e in es:
            pre_act, hp_e = conv_expr(e)
            pre_acts.append(pre_act)
            res.append(hp_e)
        return hcsp.seq(pre_acts), res

    def convert_lname(lname,val):
        if isinstance(lname, function.Var):
            return expr.AVar(lname.name)
        elif isinstance(lname, function.FunExpr):
            # Subtract one since indexing in Matlab is 1-based while indexing
            # in HCSP is 0-based.
            pre_act, args = conv_exprs(lname.exprs)
            assert pre_act == hcsp.Skip(), "convert_lname"
            if len(lname.exprs) == 1:
                pre_act, hp_e = conv_expr(lname.exprs[0])
                return expr.ArrayIdxExpr(
                    expr.AVar(lname.fun_name), [subtract_one(hp_e)])
            elif len(lname.exprs) == 2:
                _, hp_e1 = conv_expr(lname.exprs[0])
                _, hp_e2 = conv_expr(lname.exprs[1])
                return expr.ArrayIdxExpr(expr.ArrayIdxExpr(expr.AVar(lname.fun_name),subtract_one(hp_e1)),subtract_one(hp_e2))
            elif len(lname.exprs) == 3:
                _, hp_e1 = conv_expr(lname.exprs[0])
                _, hp_e2 = conv_expr(lname.exprs[1])
                _, hp_e3 = conv_expr(lname.exprs[2])
                return expr.ArrayIdxExpr(expr.ArrayIdxExpr(expr.ArrayIdxExpr(expr.AVar(lname.fun_name),subtract_one(hp_e1)),subtract_one(hp_e2)),subtract_one(hp_e3))
        elif isinstance(lname, function.ListExpr):
            return [convert_lname(arg,val) for arg in lname.args]
        elif isinstance(lname,function.DirectName):
            sname=lname.exprs[0]
            if str(sname) in messages.keys():
                message=messages[str(sname)]
                message.data=conv_expr(val)[1]
                messages[str(sname)]=message
            return lname

        else:
            raise NotImplementedError

    def get_directed_event(state_name,event):
        if len(state_name) == 1:
            return function.DirectedEvent(str(state_name[0]),function.BroadcastEvent(str(event)))
        st_name=str(state_name[0])
        
        return function.DirectedEvent(st_name,get_directed_event(state_name[1:],event))

    def convert(cmd):
        if isinstance(cmd,list):
            lists=list()
            for c in cmd:
                lists.append(convert(c))
            return hcsp.seq(lists)
        if isinstance(cmd, function.Assign):
            pre_act, hp_expr = conv_expr(cmd.expr)
# <<<<<<< HEAD
#             name_set=set()
#             vars_set=set()
#             assign_name=convert_lname(cmd.lname)
#             if isinstance(assign_name,list):
#                 for i in range(0,len(assign_name)):
#                     name_set=name_set.union(assign_name[i].get_vars())
#                 vars_set=hp_expr.get_vars()
#             else:
#                 name_set=name_set.union(assign_name.get_vars())
#                 if hp_expr is not None:
#                     vars_set=hp_expr.get_vars()
# =======
            # name_set=set()
            assign_name=convert_lname(cmd.lname,cmd.expr)
            # if isinstance(assign_name,list):
            #     for i in range(0,len(assign_name)):
            #         name_set=name_set.union(assign_name[i].get_vars())
            #     vars_set=hp_expr.get_vars()
            # else:
            #     name_set=name_set.union(assign_name.get_vars())
            #     vars_set=hp_expr.get_vars()
# >>>>>>> adef5ed30bdf662c1ddf5756ac1dc0d4943be7ef
            cmd_list=list()
            cmd_list.append(pre_act)
            # if arrays is not None:
            #     for var in vars_set:
            #         if var in arrays:
            #             data=array_value[var]
            #             if data.scope == "DATA_STORE_MEMORY_DATA":
            #                 cmd_list.append(hcsp.InputChannel('read_' + str(var), expr.AVar(var)))
            if isinstance(assign_name,list):
                if isinstance(hp_expr,expr.ListExpr) and len(hp_expr)>=1:
                    for index in range(0,len(assign_name)):
                        cmd_list.append(hcsp.Assign(assign_name[index], hp_expr[index]))
                elif isinstance(hp_expr, expr.AVar):
                    cmd_list.append(hcsp.Assign(assign_name[0], hp_expr))
            else:
                cmd_list.append(hcsp.Assign(assign_name, hp_expr))
            return hcsp.seq(cmd_list)

        elif isinstance(cmd, function.FunctionCall):
            if cmd.func_name == 'fprintf':
                pre_act, hp_exprs = conv_exprs(cmd.args)
                return hcsp.seq([pre_act, hcsp.Log(hp_exprs[0], exprs=hp_exprs[1:])])
            elif cmd.func_name == 'send':
                args=cmd.args
                if len(args) >1:
                    event,direct_name=args[0],args[1]
                    if isinstance(direct_name,function.DirectName):
                        exprs=direct_name.exprs
                        event_name=get_directed_event(exprs,event)
                    elif isinstance(direct_name,function.Var) :
                        event_name=function.DirectedEvent(str(direct_name),function.BroadcastEvent(str(event)))

                elif len(args) == 1:
                    if isinstance(args[0],function.DirectName):
                        exprs=args[0].exprs
                        event,state_name=exprs[-1],exprs[:len(exprs)-1]
                        event_name=get_directed_event(state_name,event)
                    elif isinstance(args[0],function.Var) and args[0] in events:
                        event_name=args[0]
                    elif isinstance(args[0],function.Var) and args[0] not in events:
                        event_name=function.Message(str(args[0]))
                return raise_event(event_name)
            else:
                assert procedures is not None and cmd.func_name in procedures, \
                    "convert_cmd: procedure %s not found" % cmd.func_name
                if isinstance(procedures[cmd.func_name], function.Function):
                    return convert(procedures[cmd.func_name].instantiate(cmd.args))
                elif isinstance(procedures[cmd.func_name], GraphicalFunction):
                    proc=procedures[cmd.func_name]
                    expr_list=list()
                    if len(cmd.args) > 0:
                        for index in range(0,len(cmd.args)):
                            _,val=conv_expr(cmd.args[index])
                            expr_list.append(hcsp.Assign(expr.AVar(proc.params[index]),val))

                    return hcsp.seq([*expr_list,hcsp.Var(cmd.func_name)])

        elif isinstance(cmd, function.Sequence):
            if isinstance(cmd.cmd1, function.RaiseEvent) and still_there is not None:
                return hcsp.Sequence(convert(cmd.cmd1), hcsp.Condition(still_there, convert(cmd.cmd2)))
            else:
                return hcsp.Sequence(convert(cmd.cmd1), convert(cmd.cmd2))

        elif isinstance(cmd, function.IfElse):
            pre_act, hp_cond = conv_expr(cmd.cond)
            return hcsp.seq([pre_act, hcsp.ITE([(hp_cond, convert(cmd.cmd1))], convert(cmd.cmd2))])

        elif isinstance(cmd, function.RaiseEvent):
            assert raise_event is not None, "convert_cmd: raise_event not set."
            return raise_event(cmd.event)

        else:
            raise NotImplementedError

    return convert(cmd)
