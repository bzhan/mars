"""Classes for matlab functions"""


class Expr:
    """Base class for matlab expressions."""
    pass


class Var(Expr):
    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name


class Const(Expr):
    def __init__(self, value):
        assert isinstance(value, (int, float, str))
        self.value = value

    def __str__(self):
        return str(self.value)

    def __repr__(self):
        return str(self)


class FunExpr(Expr):
    def __init__(self, fun_name, *args):
        self.fun_name = fun_name
        self.args = args

    def __str__(self):
        if self.fun_name in ("+", "*"):
            return "%s %s %s" % (self.args[0], self.fun_name, self.args[1])
        else:
            return "%s(%s)" % (self.fun_name, ",".join(str(arg) for arg in self.args))

    def __repr__(self):
        return "Fun(%s,%s)" % (self.fun_name, ",".join(repr(arg) for arg in self.args))


class Command:
    """Base class for matlab commands."""
    pass


class Assign(Command):
    def __init__(self, var_name, expr):
        self.var_name = var_name
        self.expr = expr

    def __str__(self):
        return "%s = %s;" % (self.var_name, self.expr)

    def __repr__(self):
        return "Assign(%s,%s)" % (self.var_name, repr(self.expr))

    
class Print(Command):
    def __init__(self, expr):
        self.expr = expr

    def __str__(self):
        return "fprintf(%s);" % self.expr

    def __repr__(self):
        return "Print(%s)" % repr(self.expr)


class Function:
    def __init__(self, name, commands):
        self.name = name
        self.commands = commands

    def __str__(self):
        return "function %s\n%s" % (self.name, '\n'.join('  ' + str(cmd) for cmd in self.commands))

    def __repr__(self):
        return "Function(%s,%s)" % (self.name, ','.join(repr(cmd) for cmd in self.commands))
