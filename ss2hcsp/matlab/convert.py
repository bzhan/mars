"""Conversion from matlab functions to HCSP."""


from ss2hcsp.matlab import function
from ss2hcsp.hcsp import expr, hcsp


def convert_expr(e):
    """Convert a matlab expression to HCSP."""
    if isinstance(e, function.Var):
        return expr.AVar(e.name)

    elif isinstance(e, function.Const):
        return expr.AConst(e.value)

    elif isinstance(e, function.FunExpr):
        if e.fun_name == '+':
            return expr.PlusExpr(['+', '+'], e.args)
        elif e.fun_name == '*':
            return expr.TimesExpr(['*', '*'], e.args)
        else:
            return expr.FunExpr(e.fun_name, e.args)
    elif isinstance(e,function.Function):
        return e
    else:
        raise NotImplementedError

def split_plus(e):
    """Split all plus operation in a matlab expression."""
    if isinstance(e, function.FunExpr) and e.fun_name == '+':
        return split_plus(e.args[0]) + split_plus(e.args[1])
    else:
        return [e]

def convert_cmd(cmd):
    """Convert a matlab command to HCSP."""
    if isinstance(cmd, function.Assign):
        return hcsp.Assign(convert_expr(cmd.var_name), convert_expr(cmd.expr))

    elif isinstance(cmd, function.Print):
        args = [convert_expr(arg) for arg in split_plus(cmd.expr)]
        return hcsp.Log(*args)

    elif isinstance(cmd,hcsp.ITE):
        return cmd
    elif isinstance(cmd,function.FunExpr):

        return cmd
    else:
        # raise NotImplementedError
        return cmd

def convert_function(func):
    cmds = [convert_cmd(cmd) for cmd in func.commands]
    return hcsp.Sequence(*cmds)
