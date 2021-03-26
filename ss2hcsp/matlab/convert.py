"""Conversion from matlab functions to HCSP."""


from ss2hcsp.matlab import function
from ss2hcsp.hcsp import expr, hcsp


def convert_expr(e):
    """Convert a matlab expression to HCSP."""
    if isinstance(e, function.Var):
        return expr.AVar(e.name)

    elif isinstance(e, function.Const):
        return expr.AConst(e.value)

    elif isinstance(e, (function.TimesExpr,function.PlusExpr,function.FunExpr,function.ModExpr)):
        return e
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

        return hcsp.Function("",cmd.fun_name,cmd.exprs)
    elif isinstance(cmd,function.matFunExpr):
        return hcsp.Function(cmd.return_vars,cmd.fun_name,cmd.exprs)

    else:
        raise NotImplementedError

def convert_function(func):
    cmds = [convert_cmd(cmd) for cmd in func.commands]
    if isinstance(func.name,function.matFunExpr):
        hp=hcsp.Sequence(*cmds)
        func.commands_hp=[hp]
        var_set=hp.get_vars()
        var_set.update(func.name.get_vars())
        if isinstance(func.name,function.matFunExpr):
            if isinstance(func.name.return_vars,function.ListExpr):
                for return_var in func.name.return_vars:
                    for var in var_set:
                        if str(return_var) == str(var):
                            func.returnVars.append(var)                          
            else:
                for var in var_set:
                    if str(func.name.return_vars) == str(var):
                        func.returnVars.append(var)
    return hcsp.Sequence(*cmds)
# def get_vars(self):
#         return set().union(*(expr.get_vars() for expr in [hcsp.Sequence(self.commands)]))