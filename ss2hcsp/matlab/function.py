"""Classes for matlab functions"""
from ss2hcsp.hcsp.expr import AExpr

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
        if self.fun_name in ("+", "*","/","%"):
            return "%s %s %s" % (self.args[0], self.fun_name, self.args[1])
        else:
            return "%s(%s)" % (self.fun_name, ",".join(str(arg) for arg in self.args))

    def __repr__(self):
        return "Fun(%s,%s)" % (self.fun_name, ",".join(repr(arg) for arg in self.args))

class matFunExpr(Expr):
    def __init__(self,return_vars,fun_name,*args):
        self.return_vars=return_vars
        self.fun_name = fun_name
        self.args = args

    def __str__(self):
        if isinstance(self.return_vars,list) and len(self.return_vars) >1:
            return "[%s] = %s(%s)" % (",".join(str(return_var) for return_var in self.return_vars),self.fun_name, ",".join(str(arg) for arg in self.args)) 
        else:
            return "%s = %s(%s)" % (self.return_vars,self.fun_name, ",".join(str(arg) for arg in self.args))
           
    def __repr__(self):
        if isinstance(self.return_vars,list) and len(self.return_vars) >1:
            return "[%s] = Fun(%s,%s)" % (",".join(str(return_var) for return_var in self.return_vars),self.fun_name, ",".join(repr(arg) for arg in self.args))
        else:
            return "%s = Fun(%s,%s)" % (self.return_vars,self.fun_name,",".join(repr(arg) for arg in self.args))


class Command:
    """Base class for matlab commands."""
    pass


class Assign(Command):
    def __init__(self, var_name, expr):
        super(Assign, self).__init__()
        self.var_name = var_name
        self.expr = expr  # AExpr

    def __eq__(self, other):
        return self.type == other.type and self.var_name == other.var_name and self.expr == other.expr

    def __str__(self):
        return self.var_name + " = " + str(self.expr)

    def __repr__(self):
        return "Assign(%s,%s)" % (self.var_name, str(self.expr))


    
class Print(Command):
    def __init__(self, expr):
        self.expr = expr

    def __str__(self):
        return "fprintf(%s);" % self.expr

    def __repr__(self):
        return "Print(%s)" % repr(self.expr)


class Function:
    def __init__(self,name, commands):
        self.name = name
        self.commands = commands
     

    def __str__(self):
       
            return "function %s\n%s" % (self.name, '\n'.join('  ' + str(cmd) for cmd in self.commands))
       
    def __repr__(self):
 

            return "Function(%s,%s)" % (self.name, ','.join(repr(cmd) for cmd in self.commands))
       
