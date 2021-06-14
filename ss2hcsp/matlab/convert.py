"""Conversion from Matlab functions to HCSP."""

from ss2hcsp.matlab import function
from ss2hcsp.hcsp import expr, hcsp


def convert_expr(e, *, arrays=None):
    """Convert a Matlab expression to HCSP.
    
    arrays - set(str): names that should be interpreted as arrays (instead of functions).

    """
    if arrays is None:
        arrays = set()

    def rec(e):
        if isinstance(e, function.Var):
            return expr.AVar(e.name)
        elif isinstance(e, function.ListExpr):
            return expr.ListExpr(*(rec(arg) for arg in e.args))
        elif isinstance(e, function.AConst):
            return expr.AConst(e.value)
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
                return expr.ArrayIdxExpr(e.fun_name, [rec(ex) for ex in e.exprs])
            else:
                return expr.FunExpr(e.fun_name, [rec(ex) for ex in e.exprs])
        elif isinstance(e, function.BConst):
            return expr.BConst(e.value)
        elif isinstance(e, function.LogicExpr):
            if e.op_name == '~':
                return expr.NegExpr(rec(e.exprs[0]))
            else:
                return expr.LogicExpr(e.op_name, rec(e.exprs[0]), rec(e.exprs[1]))
        elif isinstance(e, function.RelExpr):
            return expr.RelExpr(e.op, rec(e.expr1), rec(e.expr2))
        else:
            raise NotImplementedError("Unrecognized matlab expression: %s" % str(e))

    return rec(e)

def convert_cmd(cmd, *, raise_event=None, procedures=None, still_there=None, arrays=None):
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
    def convert_lname(lname):
        if isinstance(lname, function.Var):
            return expr.AVar(lname.name)
        elif isinstance(lname, function.FunExpr):
            return expr.ArrayIdxExpr(
                expr.AVar(lname.fun_name),
                [convert_expr(arg, arrays=arrays) for arg in lname.exprs])
        elif isinstance(lname, function.ListExpr):
            return [convert_lname(arg) for arg in lname.args]
        else:
            raise NotImplementedError

    def convert(cmd):
        if isinstance(cmd, function.Assign):
            return hcsp.Assign(convert_lname(cmd.lname), convert_expr(cmd.expr, arrays=arrays))

        elif isinstance(cmd, function.FunctionCall):
            if cmd.func_name == 'fprintf':
                assert len(cmd.args) == 1, "convert_cmd: fprintf should have exactly one argument."
                return hcsp.Log(convert_expr(cmd.args[0], arrays=arrays))
            else:
                assert procedures is not None and cmd.func_name in procedures, \
                    "convert_cmd: procedure %s not found" % cmd.func_name
                if len(cmd.args) == 0:
                    return hcsp.Var(cmd.func_name)
                else:
                    return convert_function(procedures[cmd.func_name], cmd.args)

        elif isinstance(cmd, function.Sequence):
            if isinstance(cmd.cmd1, function.RaiseEvent) and still_there is not None:
                return hcsp.Sequence(convert(cmd.cmd1), hcsp.Condition(still_there, convert(cmd.cmd2)))
            else:
                return hcsp.Sequence(convert(cmd.cmd1), convert(cmd.cmd2))

        elif isinstance(cmd, function.IfElse):
            return hcsp.ITE([(convert_expr(cmd.cond, arrays=arrays), convert(cmd.cmd1))], convert(cmd.cmd2))

        elif isinstance(cmd, function.RaiseEvent):
            assert raise_event is not None, "convert_cmd: raise_event not set."
            return raise_event(cmd.event)

        else:
            raise NotImplementedError

    return convert(cmd)

def convert_function(func, vals=None):
    """Convert a function call with the given arguments to an HCSP program.

    func : Function - Matlab function to be called.
    vals : [None, List[Expr]] - list of expressions as input values.

    """
    cmd = func.instantiate(vals)
    return convert_cmd(cmd)
