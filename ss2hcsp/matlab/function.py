"""Classes for matlab functions"""
class Expr:
    """Base class for matlab expressions."""
    def __init__(self):
        pass

    def get_vars(self):
        """Returns set of variables in the expression."""
        raise NotImplementedError

    def subst(self, inst):
        """inst is a dictionary mapping variable names to expressions."""
        raise NotImplementedError


class Var(Expr):
    def __init__(self, name):
        super(Var, self).__init__()
        assert isinstance(name, str)
        self.name = name

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name
    
    def get_vars(self):
        return {self.name}

    def __eq__(self, other):
        return isinstance(other, Var) and self.name == other.name

    def __hash__(self):
        return hash(("Var", self.name))

    def subst(self, inst):
        if self.name in inst:
            return inst[self.name]
        else:
            return self

class ListExpr(Expr):
    """List expressions."""
    def __init__(self, *args):
        super(ListExpr, self).__init__()
        # assert all(isinstance(arg,Var) for arg in args)
        self.args = args
        self.count=0

    def __repr__(self):
        return "List(%s)" % (','.join(repr(arg) for arg in self.args))

    def __str__(self):
        return "[%s]" % (','.join(str(arg) for arg in self.args))

    def __eq__(self, other):
        return isinstance(other, ListExpr) and self.args == other.args

    def __hash__(self):
        return hash(("List", self.args))

    def __iter__(self):
        return self

    def __len__(self):
      
       return len(self.args)
    def __getitem__(self,key):
            return self.args[key]

    def __next__(self):
        # 获取下一个数
        if self.count < len(self.args):
            result = self.args[self.count]
            self.count += 1
            return result
        else:
            raise StopIteration

    def get_vars(self):
        return set().union(*(arg.get_vars() for arg in self.args))

    def subst(self, inst):
        return ListExpr(expr.subst(inst) for expr in self.args)

class Const(Expr):
    def __init__(self, value):
        assert isinstance(value, (int, float, str))
        self.value = value

    def __str__(self):
        return str(self.value)

    def __repr__(self):
        return str(self)

    def get_vars(self):
        return set()

    def subst(self, inst):
        return self

class PlusExpr(Expr):
    def __init__(self, signs, exprs):
        super(PlusExpr, self).__init__()
        self.signs = signs
        self.exprs = exprs

    def __repr__(self):
        val = ", ".join(sign + repr(expr) for sign, expr in zip(self.signs, self.exprs))
        return "Plus(%s)" % val

    def __str__(self):
        res = str(self.exprs[0])
        if self.signs[0] == "-":
            if str(self.exprs[0]).startswith("-") or isinstance(self.exprs[0], PlusExpr):
                res = "-(" + res + ")"
            else:
                res = "-" + res
        for sign, expr in zip(self.signs[1:], self.exprs[1:]):
            if str(expr).startswith("-") or (sign == "-" and isinstance(expr, PlusExpr)):
                res += sign + "(" + str(expr) + ")"
            else:
                res += sign + str(expr)
        return res

    def __eq__(self, other):
        return isinstance(other, PlusExpr) and "".join(self.signs) == "".join(other.signs) and \
               list(self.exprs) == list(other.exprs)

    def __hash__(self):
        return hash(("Plus", tuple(self.signs), tuple(self.exprs)))

    def get_vars(self):
        return set().union(*(expr.get_vars() for expr in self.exprs))

    def subst(self, inst):
        return PlusExpr(self.signs, [expr.subst(inst) for expr in self.exprs])


class TimesExpr(Expr):
    def __init__(self, signs, exprs):
        super(TimesExpr, self).__init__()
        self.signs = signs
        self.exprs = exprs

    def __repr__(self):
        val = ", ".join(sign + repr(expr) for sign, expr in zip(self.signs, self.exprs))
        return "Times(%s)" % val

    def __str__(self):
        res = str(self.exprs[0])
        if isinstance(self.exprs[0], PlusExpr) or (self.signs[0] == "/" and isinstance(self.exprs[0], TimesExpr)):
            res = "(" + res + ")"
        if self.signs[0] == "/":
            res = "1/" + res
        for sign, expr in zip(self.signs[1:], self.exprs[1:]):
            if isinstance(expr, PlusExpr) or (sign == "/" and isinstance(expr, TimesExpr)) \
                    or (sign == "*" and str(expr).startswith("-")):
                res += sign + "(" + str(expr) + ")"
            else:
                res += sign + str(expr)
        return res

    def __eq__(self, other):
        return isinstance(other, TimesExpr) and "".join(self.signs) == "".join(other.signs) and \
               list(self.exprs) == list(other.exprs)

    def __hash__(self):
        return hash(("Times", tuple(self.signs), tuple(self.exprs)))

    def get_vars(self):
        return set().union(*(expr.get_vars() for expr in self.exprs))

    def subst(self, inst):
        return TimesExpr(self.signs, [expr.subst(inst) for expr in self.exprs])
class ModExpr(Expr):
    def __init__(self, expr1, expr2):
        super(ModExpr, self).__init__()
        assert isinstance(expr1, AExpr) and isinstance(expr2, AExpr)
        self.expr1 = expr1
        self.expr2 = expr2

    def __repr__(self):
        return "Mod(%s, %s)" % (repr(self.expr1), str(repr(self.expr2)))

    def __str__(self):
        s1, s2 = str(self.expr1), str(self.expr2)
        if isinstance(self.expr1, PlusExpr):
            s1 = '(' + s1 + ')'
        if isinstance(self.expr2, PlusExpr):
            s2 = '(' + s2 + ')'
        return "%s%%%s" % (s1, s2)

    def __eq__(self, other):
        return isinstance(other, ModExpr) and self.expr1 == other.expr1 and self.expr2 == other.expr2

    def __hash__(self):
        return hash(("Mod", self.expr1, self.expr2))

    def get_vars(self):
        return self.expr1.get_vars().union(self.expr2.get_vars())

    def subst(self, inst):
        return ModExpr(expr1=self.expr1.subst(inst), expr2=self.expr2.subst(inst))



class FunExpr(Expr):
    def __init__(self, fun_name, exprs):
        super(FunExpr, self).__init__()
        # assert fun_name in [
        #     "min", "max", "abs", "gcd", "delay", "sqrt", "div",
        #     "push", "pop", "top", "get", "bottom", "len", "get_max", "pop_max","get_min", "pop_min",
        #     "bernoulli", "uniform"]
        self.fun_name = fun_name
        exprs = tuple(exprs)
        # assert all(isinstance(expr, AExpr) for expr in exprs)
        self.exprs = exprs
    def priority(self):
            return 100
    def __repr__(self):
        return "Fun(%s, %s)" % (self.fun_name, ", ".join(repr(expr) for expr in self.exprs))

    def __str__(self):
        return "%s(%s)" % (self.fun_name, ", ".join(str(expr) for expr in self.exprs))

    def __eq__(self, other):
        return isinstance(other, FunExpr) and self.fun_name == other.fun_name and \
               self.exprs == other.exprs

    def __hash__(self):
        return hash(("Fun", self.fun_name, self.exprs))

    def get_vars(self):
        return set().union(*(expr.get_vars() for expr in self.exprs))

    def subst(self, inst):
        return FunExpr(self.fun_name, [expr.subst(inst) for expr in self.exprs])
class matFunExpr(Expr):
    def __init__(self,return_vars,fun_name,exprs):
        super(matFunExpr, self).__init__()
        self.return_vars=return_vars
        exprs = tuple(exprs)
        self.exprs = exprs
        if str(fun_name) == 'rand':
            self.fun_name = "uniform"
        else:
            self.fun_name = fun_name
    def get_vars(self):
        if isinstance(self.return_vars,list) and len(self.return_vars) >1:
            var_set=set().union(return_var.get_vars() for return_var in self.return_vars)
        else:
            var_set=set().union(self.return_vars.get_vars())
        for expr in self.exprs:
            if isinstance(expr,tuple):
                for expr1 in expr:
                    var_set.update(expr1.get_vars())
            else:
                var_set.update(expr.get_vars())
        return var_set

    def __str__(self):
        if isinstance(self.return_vars,list) and len(self.return_vars) >1:
            return "[%s] := %s(%s)" % (",".join(str(return_var) for return_var in self.return_vars),self.fun_name, ",".join(str(arg) for arg in self.exprs)) 
        else:
           
            return "%s := %s(%s)" % (self.return_vars,self.fun_name, ", ".join(str(expr) for expr in self.exprs))
           
    def __repr__(self):
        if isinstance(self.return_vars,list) and len(self.return_vars) >1:
            return "Assign([%s] ,Fun(%s,%s))" % (",".join(repr(return_var) for return_var in self.return_vars),self.fun_name, ",".join(repr(arg) for arg in self.exprs))
        else:
            if self.fun_name == "uniform" and len(self.exprs) == 0:
                return "Assign(%s,Fun(%s,(0,1)))" % (self.return_vars,self.fun_name)
            else:
                return "Assign(%s,Fun(%s,%s))" % (self.return_vars,self.fun_name,",".join(repr(arg) for arg in self.exprs))
    def priority(self):
        
        return 100

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
        return  "%s := %s" %(self.var_name , self.expr)

    def __repr__(self):
        return "Assign(%s,%s)" % (self.var_name, str(self.expr))
    def priority(self):
            return 100
    def get_vars(self):
        if isinstance(self.var_name,Expr):
            var_set = {str(self.var_name)}
        else:
            var_set = set(str(n) for n in self.var_name)
        return var_set.union(self.expr.get_vars())


    
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
        self.returnVars=list()
        self.commands_hp=None
    

    def __str__(self):
       
            return "function %s\n%s" % (self.name, '\n'.join('  ' + str(cmd) for cmd in self.commands))
       
    def __repr__(self):
 

            return "Function(%s,%s)" % (self.name, ','.join(repr(cmd) for cmd in self.commands))
       
