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
        return "Var(%s)" % self.name

    def __str__(self):
        return str(self.name)
    
    def __eq__(self, other):
        return isinstance(other, Var) and self.name == other.name

    def __hash__(self):
        return hash(("Var", str(self.name)))

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
            if isinstance(self.exprs[0],OpExpr) or isinstance(self.exprs[1],OpExpr):
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
        assert all(isinstance(expr, (Expr,DirectName)) for expr in exprs)
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
        self.expr1=self.exprs[0]
        if len(exprs) != 1:
            self.expr2=self.exprs[1]
        

    def __repr__(self):
        return "Logic(%s,%s)" % (repr(self.op_name), ','.join(repr(expr) for expr in self.exprs))

    def __str__(self):
        if self.op_name == '~':
            s = str(self.expr1)
            if self.expr1.priority() < self.priority():
                s = '(' + s + ')'
            return '~' + s

        else:
            s1, s2 = str(self.expr1), str(self.expr2)
            if isinstance(self.expr1,LogicExpr) or isinstance(self.expr2,LogicExpr):
                if self.expr1.priority() < self.priority():
                    s1 = '(' + s1 + ')'
                if self.expr2.priority() <= self.priority():
                    s2 = '(' + s2 + ')'
            return '%s %s %s' % (s1, self.op_name, s2)

    def __eq__(self, other):
        return isinstance(other, LogicExpr) and self.op_name == other.op_name and self.exprs == other.exprs

    def __hash__(self):
        return hash(("LogicExpr", self.op_name, self.exprs))

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
        return LogicExpr(self.op_name, *(expr.subst(inst) for expr in self.exprs))


class RelExpr(BExpr):
    neg_table = {"<": ">=", ">": "<=", "==": "!=", "!=": "==", ">=": "<", "<=": ">"}

    def __init__(self, op, expr1, expr2):
        super(RelExpr, self).__init__()
        assert op in ["<", ">", "==", "!=", ">=", "<="]
        assert isinstance(expr1, (Expr,FunctionCall,DirectName)) and isinstance(expr2, (Expr,FunctionCall,AConst))
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

    def priority(self):
        return 50

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


class Skip(Command):
    """Skip command."""
    def __init__(self):
        super(Skip, self).__init__()

    def __str__(self):
        return "skip"

    def __repr__(self):
        return "Skip()"

    def __eq__(self, other):
        return isinstance(other, Skip)

    def __hash__(self):
        return hash("SKIP")

    def priority(self):
        return 100

    def subst(self, inst):
        return self


class Assign(Command):
    """Assignment command.

    This command evaluates expr, which should return either a value or a list
    of values. The resulting value is assigned to one or more lnames.

    """
    def __init__(self, lname, expr):
        super(Assign, self).__init__()
        assert isinstance(expr, Expr)
        assert isinstance(lname, (Var, FunExpr, ListExpr, DirectName))
        self.lname = lname
        self.expr = expr

    def __str__(self):
        return "%s = %s" % (self.lname, self.expr)

    def __repr__(self):
        return "Assign(%s,%s)" % (repr(self.lname), repr(self.expr))

    def __eq__(self, other):
        return isinstance(other, Assign) and self.lname == other.lname and \
            self.expr == other.expr

    def __hash__(self):
        return hash(("ASSIGN", self.lname, self.expr))

    def priority(self):
        return 100

    def contain_hp(self, name):
        return False

    def subst(self, inst):
        # Disallow instantiating lname
        assert self.lname not in inst, "Cannot instantiate lname %s" % self.lname
        return Assign(self.lname, self.expr.subst(inst))


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

    def __hash__(self):
        return hash(("FUNCTION_CALL", self.func_name, self.args))

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
        return "%s; %s" % (str(self.cmd1), Sequence(self.cmd2.cmd1,self.cmd2.cmd2) if isinstance(self.cmd2,Sequence) else str(self.cmd2))

    def __repr__(self):
        return "Sequence(%s,%s)" % (repr(self.cmd1), Sequence(self.cmd2.cmd1,self.cmd2.cmd2) if isinstance(self.cmd2,Sequence) else repr(self.cmd2) )

    def __eq__(self, other):
        return isinstance(other, Sequence) and self.cmd1 == other.cmd1 and self.cmd2 == other.cmd2

    def __hash__(self):
        return hash(("SEQUENCE", self.cmd1, self.cmd2))

    def subst(self, inst):
        return Sequence(self.cmd1.subst(inst), self.cmd2.subst(inst))

    def priority(self):
        return 70

    def contain_hp(self, name):
        return False

def flatten(args):
    """Expand any Sequence in list of commands."""
    res = []
    for arg in args:
        if isinstance(arg, Sequence):
            res.extend(flatten([arg.cmd1]))
            res.extend(flatten([arg.cmd2]))
        else:
            res.append(arg)
    return res

def rec_seq(args):
    if len(args) == 0:
        return Skip()
    elif len(args) == 1:
        return args[0]
    else:
        return Sequence(args[0], rec_seq(args[1:]))

def seq(args):
    args = [arg for arg in flatten(args) if arg != Skip()]
    return rec_seq(args)


class IfElse(Command):
    """If-Else commands."""
    def __init__(self, cond, cmd1, cmd2):
        super(IfElse, self).__init__()
        assert isinstance(cond, BExpr) and isinstance(cmd1, Command) 
        self.cond = cond
        self.cmd1 = cmd1
        self.cmd2 = cmd2

    def __str__(self):
        if_str = str(self.cmd1)
        else_str = str(self.cmd2) if self.cmd2 is not None else ""
        res = "if %s " % self.cond
        res += ''.join(' ' + line for line in if_str.split('\n'))
        if  self.cmd2 is not None:
            res += ' else'
            res += ''.join(' ' + line for line in else_str.split('\n'))
        return res

    def __repr__(self):
        return "IfElse(%s,%s,%s)" % (repr(self.cond), repr(self.cmd1), repr(self.cmd2))

    def __eq__(self, other):
        return isinstance(other, IfElse) and self.cond == other.cond and self.cmd1 == other.cmd1 and \
            self.cmd2 == other.cmd2

    def __hash__(self):
        return hash(("IFELSE", self.cond, self.cmd1, self.cmd2))

    def subst(self, inst):
        return IfElse(self.cond.subst(inst), self.cmd1.subst(inst), self.cmd2.subst(inst)) if self.cmd2 is not None \
                else IfElse(self.cond.subst(inst), self.cmd1.subst(inst), None)


class Event:
    """Base class for events in Matlab."""
    pass

class BroadcastEvent(Event):
    """Broadcast event in Matlab.
    
    Event can serve as either conditions (require this event to be active)
    or as commands (raise this event).
    
    """
    def __init__(self, name):
        assert isinstance(name, str)
        self.name = name

    def __str__(self):
        return self.name

    def __repr__(self):
        return "BroadcastEvent(%s)" % repr(self.name)

    def __eq__(self, other):
        return isinstance(other, BroadcastEvent) and self.name == other.name

    def __hash__(self):
        return hash(("BROADCAST_EVENT", self.name))

class DirectedEvent(Event):
    """Sending event to particular state."""
    def __init__(self, state_name, event):
        assert isinstance(state_name, str) and isinstance(event, (BroadcastEvent, DirectedEvent))
        self.state_name = state_name
        self.event = event

    def __str__(self):
        return self.state_name + "." + str(self.event)

    def __repr__(self):
        return "DirectedEvent(%s,%s)" % (repr(self.state_name), repr(self.event))

    def __eq__(self, other):
        return isinstance(other, DirectedEvent) and self.state_name == other.state_name and \
            self.event == other.event

    def __hash__(self):
        return hash(("DIRECTED_EVENT", self.state_name, self.event))

class ImplicitEvent(Event):
    """Implicit events in Matlab."""
    def __init__(self, name):
        assert name in ('tick', 'wakeup')
        self.name = name

    def __str__(self):
        return self.name

    def __repr__(self):
        return "ImplicitEvent(%s)" % repr(self.name)

    def __eq__(self, other):
        return isinstance(other, ImplicitEvent) and self.name == other.name

    def __hash__(self):
        return hash(("IMPLICIT_EVENT", self.name))

class AbsoluteTimeEvent(Event):
    """Absolute time events in Matlab."""
    def __init__(self, name):
        assert name in ('sec', 'msec', 'usec')
        self.name = name

    def __str__(self):
        return self.name

    def __repr__(self):
        return "AbsoluteTimeEvent(%s)" % repr(self.name)

    def __eq__(self, other):
        return isinstance(other, AbsoluteTimeEvent) and self.name == other.name

    def __hash__(self):
        return hash(("ABSOLUTE_TIME_EVENT", self.name))

class TemporalEvent(Event):
    """Temporal logic events in Matlab."""
    def __init__(self, temp_op, expr, event):
        assert temp_op in ('after', 'before', 'at', 'every')
        assert isinstance(event, Event)
        # assert isinstance(expr, Expr)
        self.temp_op = temp_op
        self.expr = expr
        self.event = event

    def __str__(self):
        return "%s(%s,%s)" % (self.temp_op, str(self.expr), str(self.event))

    def __repr__(self):
        return "TemporalEvent(%s,%s,%s)" % (repr(self.temp_op), repr(self.expr), repr(self.event))

    def __eq__(self, other):
        return isinstance(other, TemporalEvent) and self.temp_op == other.temp_op and \
            self.expr == other.expr and self.event == other.event

    def __hash__(self):
        return hash(("TEMPORAL_EVENT", self.temp_op, self.expr, self.event))


class RaiseEvent(Command):
    """Command for raising an event."""
    def __init__(self, event):
        assert isinstance(event, (BroadcastEvent, DirectedEvent))
        self.event = event

    def __str__(self):
        return str(self.event)

    def __repr__(self):
        return "RaiseEvent(%s)" % repr(self.event)

    def __eq__(self, other):
        return isinstance(other, RaiseEvent) and self.event == other.event

    def __hash__(self):
        return hash(("RAISE_EVENT", self.event))

    def subst(self, inst):
        return self


class Message(Command):
    """Command for raising an event."""
    def __init__(self, message):
        assert isinstance(message, str)
        self.message = str(message)

    def __str__(self):
        return self.message

    def __repr__(self):
        return "RaiseEvent(%s)" % repr(self.message)

    def __eq__(self, other):
        return self.message == other.message

    def __hash__(self):
        return hash(("MESSAGE", self.message))

    def subst(self, inst):
        return self


class Function:
    """Function declarations in Matlab.
    
    name : str - name of the function.
    params : List[str] - list of parameter names.
    cmd : Command - body of the function.
    return_var : [str, List[str]] - return variables.

    """
    def __init__(self, name, params, cmd, return_var):
        assert isinstance(cmd, Command)
        self.name = name
        self.params = tuple(params)
        self.cmd = cmd
        self.type = "MATLAB_FUNCTION"
        if return_var is None or isinstance(return_var, str):
            self.return_var = return_var
        else:
            self.return_var = tuple(return_var)

    def __str__(self):
        if self.return_var is None:
            str_return_var = ""
        elif isinstance(self.return_var, str):
            str_return_var = self.return_var + "="
        else:
            str_return_var = "[" + ','.join(self.return_var) + "]="

        func_sig = str_return_var + self.name + "(" + ",".join(self.params) + ")"
        str_cmd = '\n'.join('  ' + line for line in str(self.cmd).split('\n'))
        return "function %s\n%s" % (func_sig, str_cmd)

    def __repr__(self):
        return "Function(%s,%s,%s,%s)" % (repr(self.name), repr(self.params), repr(self.cmd), repr(self.return_var))

    def __eq__(self, other):
        return isinstance(other, Function) and self.name == other.name and self.params == other.params and \
            self.cmd == other.cmd and self.return_var == other.return_var

    
    def get_Sequence(self,lists):
        if len(lists) == 1:
            return lists[0]
        else:
           return Sequence(lists[0],Sequence(self.get_Sequence(lists[1:])))
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
       
        paramsList=list()
        for i in range(0,len(self.params)):
            paramsList.append(Assign(Var(self.params[i]),vals[i]))
        # return self.cmd.subst(inst),list()
        return self.cmd,paramsList


class TransitionLabel:
    """Label on transitions.

    There are four parts to specify a transition:
    event : [None, Event] - event trigger for the transition.
    cond : [None, BExpr] - condition trigger for the transition.
    cond_act : [None, Command] - action performed when checking conditions.
    tran_act : [None, Command] - action performed at the end of transition.

    """
    def __init__(self, event, cond, cond_act, tran_act):
        assert event is None or isinstance(event, Event)
        assert cond is None or isinstance(cond, (BExpr,FunExpr))
        if cond_act is None:
            cond_act = Skip()
        if tran_act is None:
            tran_act = Skip()
        assert isinstance(cond_act, Command)
        assert isinstance(tran_act, Command)

        self.event = event
        self.cond = cond
        self.cond_act = cond_act
        self.tran_act = tran_act

    def __str__(self):
        event_str = str(self.event) if self.event else ""
        cond_str = '[' + str(self.cond) + ']' if self.cond else ""
        cond_act_str = '{' + str(self.cond_act) + '}' if self.cond_act != Skip() else ""
        tran_act_str = '/{' + str(self.tran_act) + '}' if self.tran_act != Skip() else ""
        return event_str + cond_str + cond_act_str + tran_act_str

    def __repr__(self):
        return "TransitionLabel(%s,%s,%s,%s)" % (
            repr(self.event), repr(self.cond), repr(self.cond_act), repr(self.tran_act))

    def __eq__(self, other):
        return isinstance(other, TransitionLabel) and self.event == other.event and \
            self.cond == other.cond and self.cond_act == other.cond_act and self.tran_act == other.tran_act

class DirectName:
    """Directed name."""
    def __init__(self, expr):
        self.exprs = expr

    def __str__(self):
        return str(".".join(str(arg) for arg in self.exprs))

    def __repr__(self):
        return "str(%s)" %(".".join(repr(arg) for arg in self.exprs))


class StateInnerOperate:
    def __init__(self, name, op):
        self.name = name
        self.op = op

    def __str__(self):
        return self.name + ":" + self.op

    def __repr__(self):
        return "StateInnerOperate(%s,%s)" % (self.name, self.op)

class StateOperate:
    def __init__(self, name, en_op, du_op, ex_op):
        self.name = name
        self.en_op = en_op
        self.du_op = du_op
        self.ex_op = ex_op

    def __str__(self):
        state_name = self.name + "\n"
        state_en_op = self.en_op.name + " : " + self.op + "\n"
        state_du_op = self.du_op.name + " : " + self.op + "\n"
        state_ex_op = self.ex_op.name + " : " + self.op + "\n"
        return state_name + state_en_op + state_du_op + state_ex_op

    def __repr__(self):
        return "StateOperate(%s,%s,%s,%s)" % (self.name, self.en_op, self.du_op, self.ex_op)
