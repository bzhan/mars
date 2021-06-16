"""Conversion from Matlab functions to HCSP."""

from ss2hcsp.matlab import function
from ss2hcsp.hcsp import expr, hcsp


def convert_expr(e):
    """Convert a Matlab expression to HCSP."""
    if isinstance(e, function.Var):
        return expr.AVar(e.name)
    elif isinstance(e, function.ListExpr):
        return expr.ListExpr(*(convert_expr(arg) for arg in e.args))
    elif isinstance(e, function.AConst):
        return expr.AConst(e.value)
    elif isinstance(e, function.OpExpr):
        if e.op_name == '-' and len(e.exprs) == 1:
            return expr.PlusExpr(['-'], [convert_expr(e.exprs[0])])
        elif e.op_name == '+':
            return expr.PlusExpr(['+', '+'], [convert_expr(e.exprs[0]), convert_expr(e.exprs[1])])
        elif e.op_name == '-':
            return expr.PlusExpr(['+', '-'], [convert_expr(e.exprs[0]), convert_expr(e.exprs[1])])
        elif e.op_name == '*':
            return expr.TimesExpr(['*', '*'], [convert_expr(e.exprs[0]), convert_expr(e.exprs[1])])
        elif e.op_name == '/':
            return expr.TimesExpr(['*', '/'], [convert_expr(e.exprs[0]), convert_expr(e.exprs[1])])
        elif e.op_name == '%':
            return expr.ModExpr(convert_expr(e.exprs[0]), convert_expr(e.exprs[1]))
        else:
            raise NotImplementedError("Unknown operator %s" % e.op_name)
    elif isinstance(e, function.FunctionCall):
        if e.func_name == 'rand':
            if len(e.args) == 0:
                return expr.FunExpr('uniform', [expr.AConst(0), expr.AConst(1)])
            else:
                raise NotImplementedError("Function rand: argument not supported")
        else:
            return expr.FunExpr(e.func_name, [convert_expr(ex) for ex in e.args])
    elif isinstance(e, function.BConst):
        return expr.BConst(e.value)
    elif isinstance(e, function.LogicExpr):
        if e.op_name == '~':
            return expr.NegExpr(convert_expr(e.exprs[0]))
        else:
            return expr.LogicExpr(e.op_name, convert_expr(e.exprs[0]), convert_expr(e.exprs[1]))
    elif isinstance(e, function.RelExpr):
        return expr.RelExpr(e.op, convert_expr(e.expr1), convert_expr(e.expr2))
    else:
        raise NotImplementedError("Unrecognized matlab expression: %s" % str(e))

def convert_cmd(cmd, *, raise_event=None, procedures=None):
    """Convert a Matlab command to HCSP.
    
    raise_event : Event -> HCSP - specifies translation for raising events.
        If this is set to None, then an error is raised whenever cmd contains
        RaiseEvent. Otherwise, this function is used to convert raising the event
        into an HCSP program.

    procedures : dict(str, Procedure) - mapping from procedure names to
        procedure objects.

    There are three possible options for converting procedure calls:
    1. splice the body of the procedure into the code.
    2. for procedures without arguments, insert call to procedure.
    3. for procedures with arguments, insert call, using a stack to keep track
       of arguments.
    Currently we choose option 2 for procedures without arguments, and option 1
    for procedures with arguments.

    """
    def convert(cmd):
        if isinstance(cmd, function.Assign):
            return hcsp.Assign(cmd.return_vars, convert_expr(cmd.expr))

        elif isinstance(cmd, function.FunctionCall):
            if cmd.func_name == 'fprintf':
                assert len(cmd.args) == 1, "convert_cmd: fprintf should have exactly one argument."
                return hcsp.Log(convert_expr(cmd.args[0]))
            else:
                assert procedures is not None and cmd.func_name in procedures, \
                    "convert_cmd: procedure %s not found" % cmd.func_name
                if len(cmd.args) == 0:
                    return hcsp.Var(cmd.func_name)
                else:
                    return convert_function(procedures[cmd.func_name], cmd.args)

        elif isinstance(cmd, function.Sequence):
            return hcsp.Sequence(convert(cmd.cmd1), convert(cmd.cmd2))

        elif isinstance(cmd, function.IfElse):
            return hcsp.ITE([(convert_expr(cmd.cond), convert(cmd.cmd1))], convert(cmd.cmd2))

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
