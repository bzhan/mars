"""Classes for Matlab functions"""

class Expr:
    """Base class for Matlab (non-boolean) expressions."""
    def __init__(self):
        pass

    def priority(self):
        """Priority of expression during printing."""
        raise NotImplementedError

    def get_vars(self):
        """Returns set of variables in the expression."""
        raise NotImplementedError

    def subst(self, inst):
        """inst is a dictionary mapping variable names to expressions."""
        raise NotImplementedError


class Var(Expr):
    """Matlab variables."""
    def __init__(self, name):
        super(Var, self).__init__()
        assert isinstance(name, str)
        self.name = name

    def __repr__(self):
        return "Var(%s)" % repr(self.name)

    def __str__(self):
        return self.name
    
    def __eq__(self, other):
        return isinstance(other, Var) and self.name == other.name

    def __hash__(self):
        return hash(("Var", self.name))

    def priority(self):
        return 100

    def get_vars(self):
        return {self.name}

    def subst(self, inst):
        if self.name in inst:
            return inst[self.name]
        else:
            return self


class ListExpr(Expr):
    """List expressions."""
    def __init__(self, *args):
        super(ListExpr, self).__init__()
        assert all(isinstance(arg, Expr) for arg in args)
        self.args = args

    def __repr__(self):
        return "ListExpr(%s)" % (','.join(repr(arg) for arg in self.args))

    def __str__(self):
        return "[%s]" % (','.join(str(arg) for arg in self.args))

    def __eq__(self, other):
        return isinstance(other, ListExpr) and self.args == other.args

    def __hash__(self):
        return hash(("ListExpr", self.args))

    def priority(self):
        return 100

    def get_vars(self):
        return set().union(*(arg.get_vars() for arg in self.args))

    def subst(self, inst):
        return ListExpr(expr.subst(inst) for expr in self.args)


class AConst(Expr):
    """Matlab constants."""
    def __init__(self, value):
        super(AConst, self).__init__()
        assert isinstance(value, (int, float, str))
        self.value = value

    def __repr__(self):
        return "AConst(%s)" % repr(self.value)

    def __str__(self):
        if isinstance(self.value, str):
            return "\"" + self.value + "\""
        else:
            return str(self.value)

    def __eq__(self, other):
        return isinstance(other, AConst) and self.value == other.value

    def __hash__(self):
        return hash(("AConst", self.value))

    def priority(self):
        return 100

    def get_vars(self):
        return set()

    def subst(self, inst):
        return self


class OpExpr(Expr):
    """Arithmetic operations."""
    def __init__(self, op_name, *exprs):
        super(OpExpr, self).__init__()
        assert op_name in ['+', '-', '*', '/', '%']
        assert (op_name == '-' and len(exprs) == 1) or len(exprs) == 2
        self.op_name = op_name
        self.exprs = tuple(exprs)

    def __repr__(self):
        return "OpExpr(%s,%s)" % (repr(self.op_name), ','.join(repr(expr) for expr in self.exprs))

    def __str__(self):
        if self.op_name == '-' and len(self.exprs) == 1:
            s = str(self.exprs[0])
            if self.exprs[0].priority() < self.priority():
                s = '(' + s + ')'
            return '-' + s

        else:
            s1, s2 = str(self.exprs[0]), str(self.exprs[1])
            if self.exprs[0].priority() < self.priority():
                s1 = '(' + s1 + ')'
            if self.exprs[1].priority() <= self.priority():
                s2 = '(' + s2 + ')'
            return '%s %s %s' % (s1, self.op_name, s2)
    
    def __eq__(self, other):
        return isinstance(other, OpExpr) and self.op_name == other.op_name and self.exprs == other.exprs

    def __hash__(self):
        return hash(("OpExpr", self.op_name, self.exprs))

    def priority(self):
        if self.op_name == '-' and len(self.exprs) == 1:
            return 80  # priority of unary minus
        elif self.op_name in ('+', '-'):
            return 65
        elif self.op_name in ('*', '/', '%'):
            return 70
        else:
            raise NotImplementedError

    def get_vars(self):
        return set().union(*(expr.get_vars() for expr in self.exprs))

    def subst(self, inst):
        return OpExpr(self.op_name, *(expr.subst(inst) for expr in self.exprs))


class FunExpr(Expr):
    def __init__(self, fun_name, *exprs):
        super(FunExpr, self).__init__()
        assert isinstance(fun_name, str)
        self.fun_name = fun_name
        assert all(isinstance(expr, Expr) for expr in exprs)
        self.exprs = tuple(exprs)

    def __repr__(self):
        return "FunExpr(%s,%s)" % (repr(self.fun_name), ",".join(repr(expr) for expr in self.exprs))

    def __str__(self):
        return "%s(%s)" % (self.fun_name, ",".join(str(expr) for expr in self.exprs))

    def __eq__(self, other):
        return isinstance(other, FunExpr) and self.fun_name == other.fun_name and \
               self.exprs == other.exprs

    def __hash__(self):
        return hash(("FunExpr", self.fun_name, self.exprs))

    def priority(self):
        return 100

    def get_vars(self):
        return set().union(*(expr.get_vars() for expr in self.exprs))

    def subst(self, inst):
        return FunExpr(self.fun_name, *(expr.subst(inst) for expr in self.exprs))


class BExpr:
    """Base class for Matlab boolean expressions."""
    def __init__(self):
        pass

    def priority(self):
        raise NotImplementedError

    def get_vars(self):
        raise NotImplementedError

    def subst(self, inst):
        raise NotImplementedError


class BConst(BExpr):
    """Boolean constants (true or false)."""
    def __init__(self, value):
        super(BConst, self).__init__()
        assert isinstance(value, bool)
        self.value = value

    def __repr__(self):
        return "BConst(%s)" % str(self.value)

    def __str__(self):
        return "true" if self.value else "false"

    def __eq__(self, other):
        return isinstance(other, BConst) and self.value == other.value

    def __hash__(self):
        return hash(("BConst", self.value))

    def priority(self):
        return 100

    def get_vars(self):
        return set()

    def subst(self, inst):
        return self


class LogicExpr(BExpr):
    """Boolean operations."""
    def __init__(self, op_name, *exprs):
        super(LogicExpr, self).__init__()
        assert op_name in ["~", "&&", "||", "-->", "<-->"]
        assert (op_name == "~" and len(exprs) == 1) or (op_name != "~" and len(exprs) == 2)
        self.op_name = op_name
        self.exprs = tuple(exprs)

    def __repr__(self):
        return "Logic(%s,%s)" % (repr(self.op_name), ','.join(repr(expr) for expr in self.exprs))

    def __str__(self):
        if self.op_name == '~':
            s = str(self.exprs[0])
            if self.exprs[0].priority() < self.priority():
                s = '(' + s + ')'
            return '~' + s

        else:
            s1, s2 = str(self.exprs[0]), str(self.exprs[1])
            if self.exprs[0].priority() < self.priority():
                s1 = '(' + s1 + ')'
            if self.exprs[1].priority() <= self.priority():
                s2 = '(' + s2 + ')'
            return '%s %s %s' % (s1, self.op_name, s2)

    def __eq__(self, other):
        return isinstance(other, LogicExpr) and self.op_name == other.op_name and self.exprs == other.exprs

    def __hash__(self):
        return hash(("LogicExpr", self.op, self.exprs))

    def priority(self):
        if self.op_name == '~':
            return 40
        elif self.op_name == '&&':
            return 35
        elif self.op_name == '||':
            return 30
        elif self.op_name == '<-->':
            return 25
        elif self.op_name == '-->':
            return 20
        else:
            raise NotImplementedError

    def get_vars(self):
        return set().union(*(expr.get_vars() for expr in self.exprs))

    def subst(self, inst):
        return OpExpr(self.op_name, *(expr.subst(inst) for expr in self.exprs))


class RelExpr(BExpr):
    neg_table = {"<": ">=", ">": "<=", "==": "!=", "!=": "==", ">=": "<", "<=": ">"}

    def __init__(self, op, expr1, expr2):
        super(RelExpr, self).__init__()
        assert op in ["<", ">", "==", "!=", ">=", "<="]
        assert isinstance(expr1, Expr) and isinstance(expr2, Expr)
        self.op = op
        self.expr1 = expr1
        self.expr2 = expr2

    def __repr__(self):
        return "Rel(%s,%s,%s)" % (repr(self.op), repr(self.expr1), repr(self.expr2))

    def __str__(self):
        return str(self.expr1) + " " + self.op + " " + str(self.expr2)

    def __eq__(self, other):
        return isinstance(other, RelExpr) and self.op == other.op and \
            self.expr1 == other.expr1 and self.expr2 == other.expr2

    def __hash__(self):
        return hash(("RelExpr", self.op, self.expr1, self.expr2))

    def get_vars(self):
        return self.expr1.get_vars().union(self.expr2.get_vars())

    def subst(self, inst):
        return RelExpr(self.op, self.expr1.subst(inst), self.expr2.subst(inst))


class Command:
    """Base class for Matlab commands."""
    def __init__(self):
        pass

    def subst(self, inst):
        """inst is a dictionary mapping variable names to expressions."""
        raise NotImplementedError


class Assign(Command):
    """Assignment command.

    This command evaluates expr, which should return either a value or a list
    of values. The returned value is assigned to one or more return variables.

    """
    def __init__(self, return_vars, expr):
        super(Assign, self).__init__()
        assert isinstance(expr, Expr)
        if isinstance(return_vars, str):
            self.return_vars = return_vars
        else:
            self.return_vars = tuple(return_vars)
        self.expr = expr

    def __str__(self):
        if isinstance(self.return_vars, str):
            return "%s = %s" % (self.return_vars, self.expr)
        else:
            return "[%s] = %s" % (','.join(self.return_vars), self.expr)

    def __repr__(self):
        return "Assign(%s,%s)" % (repr(self.return_vars), repr(self.expr))

    def __eq__(self, other):
        return isinstance(other, Assign) and self.return_vars == other.return_vars and \
            self.expr == other.expr

    def subst(self, inst):
        # Disallow instantiating return values
        for var in self.return_vars:
            assert var not in inst, "Cannot instantiate return value %s" % var
        
        return Assign(self.return_vars, self.expr.subst(inst))


class FunctionCall(Command):
    """Function call as a single command.
    
    This includes both Matlab functions and graphical functions defined in
    Stateflow diagrams.

    """
    def __init__(self, func_name, *args):
        super(FunctionCall, self).__init__()
        self.func_name = func_name
        self.args = tuple(args)

    def __str__(self):
        return "%s(%s)" % (self.func_name, ','.join(str(arg) for arg in self.args))

    def __repr__(self):
        if self.args:
            return "FunctionCall(%s,%s)" % (repr(self.func_name), ','.join(repr(arg) for arg in self.args))
        else:
            return "FunctionCall(%s)" % repr(self.func_name)

    def __eq__(self, other):
        return isinstance(other, FunctionCall) and self.func_name == other.func_name and \
            self.args == other.args

    def subst(self, inst):
        return FunctionCall(self.func_name, *(arg.subst(inst) for arg in self.args))


class Sequence(Command):
    """Sequential commands."""
    def __init__(self, cmd1, cmd2):
        super(Sequence, self).__init__()
        assert isinstance(cmd1, Command) and isinstance(cmd2, Command)
        self.cmd1 = cmd1
        self.cmd2 = cmd2

    def __str__(self):
        return "%s;\n%s" % (str(self.cmd1), str(self.cmd2))

    def __repr__(self):
        return "Sequence(%s,%s)" % (repr(self.cmd1), repr(self.cmd2))

    def __eq__(self, other):
        return isinstance(other, Sequence) and self.cmd1 == other.cmd1 and self.cmd2 == other.cmd2

    def subst(self, inst):
        return Sequence(self.cmd1.subst(inst), self.cmd2.subst(inst))


class IfElse(Command):
    """If-Else commands."""
    def __init__(self, cond, cmd1, cmd2):
        super(IfElse, self).__init__()
        assert isinstance(cond, BExpr) and isinstance(cmd1, Command) and isinstance(cmd2, Command)
        self.cond = cond
        self.cmd1 = cmd1
        self.cmd2 = cmd2

    def __str__(self):
        if_str = str(self.cmd1)
        else_str = str(self.cmd2)
        res = "if %s\n" % self.cond
        res += '\n'.join('  ' + line for line in if_str.split('\n'))
        res += '\nelse\n'
        res += '\n'.join('  ' + line for line in else_str.split('\n'))
        return res

    def __repr__(self):
        return "IfElse(%s,%s,%s)" % (repr(self.cond), repr(self.cmd1), repr(self.cmd2))

    def __eq__(self, other):
        return isinstance(other, IfElse) and self.cond == other.cond and self.cmd1 == other.cmd1 and \
            self.cmd2 == other.cmd2

    def subst(self, inst):
        return IfElse(self.cond.subst(inst), self.cmd1.subst(inst), self.cmd2.subst(inst))


class Function:
    """Function declarations in Matlab.
    
    name : str - name of the function.
    params : List[str] - list of parameter names.
    cmd : Command - body of the function.
    return_vars : List[str] - list of return variables.

    """
    def __init__(self, name, params, cmd, return_vars):
        assert isinstance(cmd, Command)
        self.name = name
        self.params = tuple(params)
        self.cmd = cmd

        if return_vars is None or isinstance(return_vars, str):
            self.return_vars = return_vars
        else:
            self.return_vars = tuple(return_vars)

    def __str__(self):
        if self.return_vars is None:
            str_return_vars = ""
        elif isinstance(self.return_vars, str):
            str_return_vars = self.return_vars + "="
        else:
            str_return_vars = "[" + ','.join(self.return_vars) + "]="

        func_sig = str_return_vars + self.name + "(" + ",".join(self.params) + ")"
        str_cmd = '\n'.join('  ' + line for line in str(self.cmd).split('\n'))
        return "function %s\n%s" % (func_sig, str_cmd)

    def __repr__(self):
        return "Function(%s,%s,%s,%s)" % (repr(self.name), repr(self.params), repr(self.cmd), repr(self.return_vars))

    def __eq__(self, other):
        return isinstance(other, Function) and self.name == other.name and self.params == other.params and \
            self.cmd == other.cmd and self.return_vars == other.return_vars

    def instantiate(self, vals=None):
        """Instantiate a procedure with given values for parameters.

        vals : [None, List[Expr]] - list of expressions as input values.
            Default to None if no input values.

        Returns Command - instantiated command.
        
        This works by replacing occurrence of parameters in the body of
        the function with the given values.
 
        """
        if vals is None:
            vals = tuple()

        assert len(self.params) == len(vals), "Function instantiation: wrong number of inputs"
        inst = dict(zip(self.params, vals))
        return self.cmd.subst(inst)
