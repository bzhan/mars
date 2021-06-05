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

class AVar(Expr):
    def __init__(self, name):
        super(AVar, self).__init__()
        assert isinstance(name, str)
        self.name = name

    def __repr__(self):
        return "AVar(%s)" % self.name

    def __str__(self):
        return self.name

    def __eq__(self, other):
        return isinstance(other, AVar) and self.name == other.name

    def __hash__(self):
        return hash(("AVar", self.name))

    def get_vars(self):
        return {self.name}

    def subst(self, inst):
        if self.name in inst:
            return inst[self.name]
        else:
            return self

class CondTran:
    """Information for a transition.
    
    There are four parts to specify a transition:
    event - event trigger for the transition.
    cond - condition trigger for the transition.
    cond_act - action performed when checking conditions.
    tran_act - action performed at the end of transition.

    """
    def __init__(self, event, cond, cond_act, tran_act):
        self.event = event
        self.cond = cond
        self.cond_act = cond_act
        self.tran_act = tran_act
    
    def __str__(self):
        return "%s[%s]{%s}/{%s}" % (self.event,self.cond,self.cond_act,self.tran_act)

    def __repr__(self):
        return "CondTrans(%s, %s, %s, %s)" % (self.event,self.cond,self.cond_act,self.tran_act)



class CondExpr:
    def __init__(self, op, expr1, expr2):
        self.op = op
        self.expr1 = expr1
        self.expr2 = expr2
    def __repr__(self):
        return "Rel(%s, %s, %s)" % (self.op, repr(self.expr1), repr(self.expr2))

    def __str__(self):
        return str(self.expr1) + " " + self.op + " " + str(self.expr2)

    def __eq__(self, other):
        return isinstance(other, RelExpr) and self.op == other.op and \
            self.expr1 == other.expr1 and self.expr2 == other.expr2

    def __hash__(self):
        return hash(("Rel", self.op, self.expr1, self.expr2))

    def neg(self):
        return RelExpr(RelExpr.neg_table[self.op], self.expr1, self.expr2)

    def get_vars(self):
        return self.expr1.get_vars().union(self.expr2.get_vars())

    def subst(self, inst):
        return RelExpr(self.op, self.expr1.subst(inst), self.expr2.subst(inst))
class DirectName:
    """docstring for ClassName"""
    def __init__(self, expr):
        self.exprs = expr

    def __str__(self):
        return str(".".join(str(arg) for arg in self.exprs))

    def __repr__(self):
        return "str(%s)" %(".".join(repr(arg) for arg in self.exprs))

class ArrayIdxExpr(Expr):
    """Expressions of the form a[i], where a evaluates to a list and i
    evaluates to an integer.
    
    """
    def __init__(self, expr1, expr2):
        super(ArrayIdxExpr, self).__init__()
        # assert isinstance(expr1, Expr) and isinstance(expr2, Expr)
        self.expr1 = expr1
        self.expr2 = expr2

    def __repr__(self):
        return "ArrayIdxExpr(%s,%s)" % (repr(self.expr1), repr(self.expr2))

    def __str__(self):
        return "%s[%s]" % (str(self.expr1), str(self.expr2)+"-1")

    def __eq__(self, other):
        return isinstance(other, ArrayIdxExpr) and self.expr1 == other.expr1 and self.expr2 == other.expr2

    def __hash__(self):
        return hash(("ArrayIdx", self.expr1, self.expr2))

    def get_vars(self):
        return self.expr1.get_vars().union(self.expr2.get_vars())

    def subst(self, inst):
        return ArrayIdxExpr(expr1=self.expr1.subst(inst), expr2=self.expr2.subst(inst))
class FunExpr(Expr):
    def __init__(self, fun_name, exprs):
        super(FunExpr, self).__init__()
        self.fun_name = fun_name
        exprs = tuple(exprs)
        self.exprs = exprs
    def priority(self):
            return 100
    def __repr__(self):
        return "%s(%s)" % (self.fun_name, ",".join(repr(expr) for expr in self.exprs))

    def __str__(self):
        return "%s(%s)" % (self.fun_name, ",".join(str(expr) for expr in self.exprs))

    def __eq__(self, other):
        return isinstance(other, FunExpr) and self.fun_name == other.fun_name and \
               self.exprs == other.exprs

    def __hash__(self):
        return hash(("str", self.fun_name, self.exprs))

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
           
            return "%s := %s(%s)" % (self.return_vars,self.fun_name, ",".join(str(expr) for expr in self.exprs))
           
    def __repr__(self):
        if isinstance(self.return_vars,list) and len(self.return_vars) >1:
            return "Assign([%s],%s(%s))" % (",".join(repr(return_var) for return_var in self.return_vars),self.fun_name, ",".join(repr(arg) for arg in self.exprs))
        else:
            
            return "Assign(%s,%s(%s))" % (self.return_vars,self.fun_name,",".join(repr(arg) for arg in self.exprs))
    def priority(self):
        
        return 100
class ListExpr(Expr):
    """List expressions."""
    def __init__(self, *args):
        super(ListExpr, self).__init__()
        # assert all(isinstance(arg,Var) for arg in args)
        self.args = args
        self.count=0

    def __repr__(self):
        return "[%s]" % (','.join(repr(arg) for arg in self.args))

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

        