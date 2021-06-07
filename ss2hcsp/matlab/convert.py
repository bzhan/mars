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
    elif isinstance(e, function.FunExpr):
        if e.fun_name == 'rand':
            if len(e.exprs) == 0:
                return expr.FunExpr('uniform', [expr.AConst(0), expr.AConst(1)])
            else:
                raise NotImplementedError("Function rand: argument not supported")
        else:
            return expr.FunExpr(e.fun_name, [convert_expr(ex) for ex in e.exprs])
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

def convert_cmd(cmd):
    """Convert a Matlab command to HCSP."""
    if isinstance(cmd, function.Assign):
        return hcsp.Assign(cmd.return_vars, convert_expr(cmd.expr))

    elif isinstance(cmd, function.FunctionCall):
        if cmd.func_name == 'fprintf':
            if len(cmd.args) == 1:
                return hcsp.Log(convert_expr(cmd.args[0]))
            else:
                raise NotImplementedError
        else:
            raise NotImplementedError

    elif isinstance(cmd, function.Sequence):
        return hcsp.Sequence(convert_cmd(cmd.cmd1), convert_cmd(cmd.cmd2))

    elif isinstance(cmd, function.IfElse):
        return hcsp.ITE([(convert_expr(cmd.cond), convert_cmd(cmd.cmd1))],
                        convert_cmd(cmd.cmd2))
    else:
        raise NotImplementedError

def convert_function(func, vals=None):
    """Convert a function call with the given arguments to an HCSP program.

    func : Function - Matlab function to be called.
    vals : [None, List[Expr]] - list of expressions as input values.

    """
    cmd = func.instantiate(vals)
    return convert_cmd(cmd)
