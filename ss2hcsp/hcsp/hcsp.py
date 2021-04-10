"""Hybrid programs"""

from collections import OrderedDict
from ss2hcsp.hcsp.expr import AExpr, AVar, AConst, BExpr, true_expr, RelExpr
from ss2hcsp.matlab.function import Expr
import re


class Channel:
    """Models a channel identifier. It is a string followed by a list
    of integer or variable arguments.

    The usual channel is modeled by a string without arguments. Further
    arguments can be given for parameterized channels. Parameters that
    are already decided are indicated by integers. Those that still need
    to be matched are indicated by variables.

    """
    def __init__(self, name, args=None):
        assert isinstance(name, str)
        if args is None:
            args = tuple()

        # Each argument is either integer, (unevaluated) expression, or variable
        assert isinstance(args, tuple) and all(isinstance(arg, (AExpr, int, str)) for arg in args)

        self.name = name
        self.args = args

    def __str__(self):
        def str_arg(arg):
            if isinstance(arg, str):
                return repr(arg)
            elif isinstance(arg, AConst) and isinstance(arg.value, str):
                return repr(arg.value)
            else:
                return str(arg)
        return self.name + ''.join('[' + str_arg(arg) + ']' for arg in self.args)
    
    def __repr__(self):
        if self.args:
            return "Channel(%s,%s)" % (self.name, ','.join(str(arg) for arg in self.args))
        else:
            return "Channel(%s)" % self.name

    def __hash__(self):
        return hash(("CHANNEL", self.name, self.args))

    def __eq__(self, other):
        return self.name == other.name and self.args == other.args

    def __le__(self, other):
        return (self.name, self.args) <= (other.name, other.args)

    def __lt__(self, other):
        return (self.name, self.args) < (other.name, other.args)

    def subst(self, inst):
        if self.name in inst:
            target = inst[self.name]
            assert isinstance(target, Channel)
            return Channel(target.name, tuple(arg if isinstance(arg, (int, str)) else arg.subst(inst)
                                              for arg in target.args + self.args))
        else:
            return Channel(self.name, tuple(arg if isinstance(arg, (int, str)) else arg.subst(inst)
                                            for arg in self.args))


class HCSP:
    def __init__(self):
        self.type = None

    def sc_str(self):
        """
        The HCSP form that can be accepted by HCSP2SC,
        the program translating HCSP into SystemC.
        """
        return str(self)

    def get_vars(self):
        return set()

    def get_chs(self):
        return set()

    def priority(self):
        if self.type == "parallel":
            return 30
        elif self.type == "select_comm":
            return 50
        elif self.type == "sequence":
            return 70
        elif self.type == "condition":
            return 90
        else:
            return 100

    def contain_hp(self, name):
        # return if it contains an hcsp named name
        if self == Var(name):
            return True
        elif isinstance(self, (Sequence, Parallel)):
            for sub_hp in self.hps:
                if sub_hp.contain_hp(name):
                    return True
        elif isinstance(self, (Loop, Condition, Recursion)):
            return self.hp.contain_hp(name)
        elif isinstance(self, ODE):
            return self.out_hp.contain_hp(name)
        elif isinstance(self, (ODE_Comm, SelectComm)):
            for io_comm in self.io_comms:
                if io_comm[1].contain_hp(name):
                    return True
        elif isinstance(self, ITE):
            if self.else_hp.contain_hp(name):
                return True
            for sub_hp in [_hp for _cond, _hp in self.if_hps]:
                if sub_hp.contain_hp(name):
                    return True
        return False

    def subst_comm(self, inst):
        def subst_io_comm(io_comm):
            return (io_comm[0].subst_comm(inst), io_comm[1].subst_comm(inst))

        def subst_if_hp(if_hp):
            return (if_hp[0].subst(inst), if_hp[1].subst_comm(inst))

        def subst_ode_eq(ode_eq):
            return (ode_eq[0], ode_eq[1].subst(inst))

        if self.type in ('var', 'skip'):
            return self
        elif self.type == 'wait':
            return Wait(self.delay.subst(inst))
        elif self.type == 'assign':
            return Assign(self.var_name, self.expr.subst(inst))
        elif self.type == 'assert':
            return Assert(self.bexpr.subst(inst), [expr.subst(inst) for expr in self.msgs])
        elif self.type == 'test':
            return Test(self.bexpr.subst(inst), [expr.subst(inst) for expr in self.msgs])
        elif self.type == 'log':
            return Log(*[expr.subst(inst) for expr in self.exprs])
        elif self.type == 'input_channel':
            return InputChannel(self.ch_name.subst(inst), self.var_name)
        elif self.type == 'output_channel':
            if self.expr is None:
                return OutputChannel(self.ch_name.subst(inst))
            else:
                return OutputChannel(self.ch_name.subst(inst), self.expr.subst(inst))
        elif self.type == 'sequence':
            return Sequence(*(hp.subst_comm(inst) for hp in self.hps))
        elif self.type == 'ode':
            return ODE([subst_ode_eq(eq) for eq in self.eqs],
                       self.constraint.subst(inst), out_hp=self.out_hp.subst_comm(inst))
        elif self.type == 'ode_comm':
            return ODE_Comm([subst_ode_eq(eq) for eq in self.eqs],
                            self.constraint.subst(inst),
                            [subst_io_comm(io_comm) for io_comm in self.io_comms])
        elif self.type == 'loop':
            return Loop(self.hp.subst_comm(inst), constraint=self.constraint)
        elif self.type == 'condition':
            return Condition(self.cond.subst(inst), self.hp.subst_comm(inst))
        elif self.type == 'select_comm':
            return SelectComm(*(subst_io_comm(io_comm) for io_comm in self.io_comms))
        elif self.type == 'recursion':
            return Recursion(self.hp.subst_comm(inst), entry=self.entry)
        elif self.type == 'ite':
            return ITE([subst_if_hp(if_hp) for if_hp in self.if_hps], self.else_hp.subst_comm(inst))
        else:
            print(self.type)
            raise NotImplementedError


class Var(HCSP):
    def __init__(self, name):
        super(Var, self).__init__()
        self.type = "var" 
        self.name = name

    def __eq__(self, other):
        return self.type == other.type and self.name == other.name

    def __repr__(self):
        return "Var(%s)" % self.name

    def __str__(self):
        return "@" + self.name

    def sc_str(self):
        return self.name


class Skip(HCSP):
    def __init__(self):
        super(Skip, self).__init__()
        self.type = "skip"

    def __eq__(self, other):
        return self.type == other.type

    def __repr__(self):
        return "Skip()"

    def __str__(self):
        return "skip"


class Wait(HCSP):
    def __init__(self, delay):
        super(Wait, self).__init__()
        assert isinstance(delay, AExpr)
        self.type = "wait"
        self.delay = delay

    def __eq__(self, other):
        return self.type == other.type and self.delay == other.delay

    def __repr__(self):
        return "Wait(%s)" % str(self.delay)

    def __str__(self):
        return "wait(%s)" % str(self.delay)


class Assign(HCSP):
    """Assignment command.

    Left side is an expression that can serve as a lname. This includes
    variables, array indices, and field names.

    """
    def __init__(self, var_name, expr):
        super(Assign, self).__init__()
        self.type = "assign"
        assert isinstance(expr, (AExpr,Expr))
        if isinstance(var_name, str):
            var_name = AVar(var_name)
        if isinstance(var_name, AExpr):
            self.var_name = var_name
        else:
            var_name = tuple(var_name)
            assert len(var_name) >= 2 and all(isinstance(name, (str, AExpr)) for name in var_name)
            self.var_name = [AVar(n) if isinstance(n, str) else n for n in var_name]
        self.expr = expr  # AExpr

    def __eq__(self, other):
        return self.type == other.type and self.var_name == other.var_name and self.expr == other.expr

    def __repr__(self):
        if isinstance(self.var_name, AExpr):
            var_str = str(self.var_name)
        else:
            var_str = "[%s]" % (','.join(str(n) for n in self.var_name))
        return "Assign(%s,%s)" % (var_str, str(self.expr))

    def __str__(self):
        if isinstance(self.var_name, AExpr):
            var_str = str(self.var_name)
        else:
            var_str = "(%s)" % (', '.join(str(n) for n in self.var_name))
        return var_str + " := " + str(self.expr)

    def get_vars(self):
        if isinstance(self.var_name, AExpr):
            var_set = {str(self.var_name)}
        else:
            var_set = set(str(n) for n in self.var_name)
        return var_set.union(self.expr.get_vars())

    def sc_str(self):
        return re.sub(pattern=":=", repl="=", string=str(self))


class Assert(HCSP):
    def __init__(self, bexpr, msgs):
        super(Assert, self).__init__()
        self.type = "assert"
        assert isinstance(bexpr, BExpr)
        self.bexpr = bexpr
        msgs = tuple(msgs)
        assert all(isinstance(msg, AExpr) for msg in msgs)
        self.msgs = msgs

    def __eq__(self, other):
        return self.type == other.type and self.bexpr == other.bexpr and self.msgs == other.msgs

    def __repr__(self):
        if self.msgs:
            return "Assert(%s,%s)" % (repr(self.bexpr), ','.join(repr(msg) for msg in self.msgs))
        else:
            return "Assert(%s)" % repr(self.bexpr)

    def __str__(self):
        if self.msgs:
            return "assert(%s,%s)" % (self.bexpr, ','.join(str(msg) for msg in self.msgs))
        else:
            return "assert(%s)" % self.bexpr

    def get_vars(self):
        var_set = self.bexpr.get_vars()
        for msg in self.msgs:
            var_set.update(msg.get_vars())
        return var_set


class Test(HCSP):
    def __init__(self, bexpr, msgs):
        super(Test, self).__init__()
        self.type = "test"
        assert isinstance(bexpr, BExpr)
        self.bexpr = bexpr
        msgs = tuple(msgs)
        assert all(isinstance(msg, AExpr) for msg in msgs)
        self.msgs = msgs

    def __eq__(self, other):
        return self.type == other.type and self.bexpr == other.bexpr and self.msgs == other.msgs

    def __repr__(self):
        if self.msgs:
            return "Test(%s,%s)" % (repr(self.bexpr), ','.join(repr(msg) for msg in self.msgs))
        else:
            return "Test(%s)" % repr(self.bexpr)

    def __str__(self):
        if self.msgs:
            return "test(%s,%s)" % (self.bexpr, ','.join(str(msg) for msg in self.msgs))
        else:
            return "test(%s)" % self.bexpr

    def get_vars(self):
        var_set = self.bexpr.get_vars()
        for msg in self.msgs:
            var_set.update(msg.get_vars())
        return var_set


class Log(HCSP):
    def __init__(self, *exprs):
        super(Log, self).__init__()
        self.type = "log"
        exprs = tuple(exprs)
        assert all(isinstance(expr, (AExpr,Expr)) for expr in exprs)
        self.exprs = tuple(exprs)

    def __eq__(self, other):
        return self.type == other.type and self.exprs == other.exprs

    def __repr__(self):
        return "Log(%s)" % (','.join(repr(expr) for expr in self.exprs))

    def __str__(self):
        return "log(%s)" % (','.join(str(expr) for expr in self.exprs))

    def get_vars(self):
        var_set = set()
        for expr in self.exprs:
            var_set.update(expr.get_vars())
        return var_set

    
class InputChannel(HCSP):
    def __init__(self, ch_name, var_name=None):
        super(InputChannel, self).__init__()
        self.type = "input_channel"
        if isinstance(ch_name, str):
            ch_name = Channel(ch_name)
        assert isinstance(ch_name, Channel)
        if isinstance(var_name, str):
            var_name = AVar(str(var_name))
        assert var_name is None or isinstance(var_name, AExpr)
        self.ch_name = ch_name  # Channel
        self.var_name = var_name  # AExpr or None

    def __eq__(self, other):
        return self.type == other.type and self.ch_name == other.ch_name and \
            self.var_name == other.var_name

    def __repr__(self):
        if self.var_name:
            return "InputC(%s,%s)" % (self.ch_name, self.var_name)
        else:
            return "InputC(%s)" % self.ch_name

    def __str__(self):
        if self.var_name:
            return str(self.ch_name) + "?" + str(self.var_name)
        else:
            return str(self.ch_name) + "?"

    def get_vars(self):
        if self.var_name:
            return {str(self.var_name)}
        return set()

    def get_chs(self):
        return {self.ch_name}

    def sc_str(self):
        return re.sub(pattern="\\?", repl="??", string=str(self))


class OutputChannel(HCSP):
    def __init__(self, ch_name, expr=None):
        super(OutputChannel, self).__init__()
        self.type = "output_channel"
        if isinstance(ch_name, str):
            ch_name = Channel(ch_name)
        assert isinstance(ch_name, Channel)
        assert expr is None or isinstance(expr, AExpr)
        self.ch_name = ch_name  # Channel
        self.expr = expr  # AExpr or None

    def __eq__(self, other):
        return self.type == other.type and self.expr == other.expr and self.ch_name == other.ch_name

    def __repr__(self):
        if isinstance(self.expr, AExpr):
            return "OutputC(%s,%s)" % (self.ch_name, self.expr)
        else:
            return "OutputC(%s)" % self.ch_name

    def __str__(self):
        if self.expr:
            return str(self.ch_name) + "!" + str(self.expr)
        else:
            return str(self.ch_name) + "!"

    def get_vars(self):
        if self.expr:
            return self.expr.get_vars()
        return set()

    def get_chs(self):
        return {self.ch_name}

    def sc_str(self):
        return re.sub(pattern="!", repl="!!", string=str(self))


def is_comm_channel(hp):
    return hp.type == "input_channel" or hp.type == "output_channel"

class Function(HCSP):
    def __init__(self, return_vars,fun_name,exprs):
        super(Function, self).__init__()
        self.type = "function"
        self.return_vars = return_vars  # Channel
         # AExpr or None
        self.exprs = exprs
       
        self.fun_name = fun_name

    def __eq__(self, other):
        return self.type == other.type and self.return_var == other.return_var and self.fun_name == other.fun_name and self.exprs == other.exprs

    def __repr__(self):
        if self.return_vars == "":
            return "Fun(%s,%s)" % (self.fun_name, ",".join(str(arg) for arg in self.exprs))
        elif isinstance(self.return_vars,list) and len(self.return_vars) >1:
            return "Assign([%s],Fun(%s,%s))" % (",".join(str(return_var) for return_var in self.return_vars),self.fun_name, ",".join(repr(arg) for arg in self.exprs))
        else:
            if self.fun_name == "uniform" and len(self.exprs) == 0:
                return "Assign(%s,Fun(%s,(0,1)))" % (self.return_vars,self.fun_name)
            else:
                return "Assign(%s,Fun(%s,%s))" % (self.return_vars,self.fun_name,",".join(repr(arg) for arg in self.exprs))


    def __str__(self):
        if self.return_vars == "":
            return "%s(%s)" % (self.fun_name, ",".join(repr(arg) for arg in self.exprs))
        elif isinstance(self.return_vars,list) and len(self.return_vars) >1:
            return "[%s] := %s(%s)" % (",".join(str(return_var) for return_var in self.return_vars),self.fun_name, ",".join(str(arg) for arg in self.exprs)) 
        else:
            if self.fun_name == "uniform" and len(self.exprs) == 0:
                return "%s := %s(0,1)" % (self.return_vars,self.fun_name)
            else:
                return "%s := %s(%s)" % (self.return_vars,self.fun_name, ",".join(str(arg) for arg in self.exprs))

    def get_vars(self):
        if self.return_vars == "":
            var_set =set()
        else:
            var_set=set().union(self.return_vars.get_vars())
        for expr in self.exprs:
            if isinstance(expr,tuple):
                for expr1 in expr:
                    var_set.update(expr1.get_vars())
            else:
                var_set.update(expr.get_vars())
        return var_set

    def sc_str(self):
        if self.return_vars == "":
            if self.fun_name == "uniform" and len(self.exprs) == 0:
                return "%s(0,1)" %(self.func_name)
            else:
                return "%s(%s)" %(self.func_name,",".join(str(arg) for arg in self.exprs))

        else:
            if self.fun_name == "uniform" and len(self.exprs) == 0:
                return "%s := %s(0,1)" %(self.return_vars,self.func_name)
            else:
                return  "%s := %s(%s)" %(self.return_vars,self.func_name,",".join(str(arg) for arg in self.exprs))



class Sequence(HCSP):
    def __init__(self, *hps):
        super(Sequence, self).__init__()
        """hps is a list of hybrid programs."""
        self.type = "sequence"
        #assert all(isinstance(hp, HCSP) for hp in hps)
        #assert len(hps) >= 2
        self.hps = []
        for hp in hps:
            if isinstance(hp, Sequence):
                self.hps.extend(hp.hps)
            else:
                self.hps.append(hp)

    def __eq__(self, other):
        return self.type == other.type and self.hps == other.hps

    def __repr__(self):
        return "Seq(%s)" % ", ".join(repr(hp) for hp in self.hps)

    def __str__(self):
        return "; ".join(
            str(hp) if hp.priority() > self.priority() else "(" + str(hp) + ")"
            for hp in self.hps)

    def sc_str(self):
        return "; ".join(
            hp.sc_str() if hp.priority() > self.priority() else "(" + hp.sc_str() + ")"
            for hp in self.hps)

    def get_vars(self):  # in assignments
        var_set = set()
        for hp in self.hps:
            # if isinstance(hp, Assign):
            # var_set = var_set.union(hp.get_vars())
            var_set.update(hp.get_vars())
        return var_set

    def get_chs(self):
        ch_set = set()
        for hp in self.hps:
            # ch_set = ch_set.union(hp.get_chs())
            ch_set.update(hp.get_chs())
        return ch_set


class ODE(HCSP):
    """Represents an ODE program of the form

    <F(s',s) = 0 & B> |> Q

    """
    def __init__(self, eqs, constraint, *, out_hp=Skip()):
        """Each equation is of the form (var_name, expr), where var_name
        is the name of the variable, and expr is its derivative.

        constraint is a boolean formula.

        """
        super(ODE, self).__init__()
        assert isinstance(eqs, list)
        for eq in eqs:
            assert isinstance(eq, tuple) and len(eq) == 2
            assert isinstance(eq[0], str) and isinstance(eq[1], AExpr)
        assert isinstance(constraint, BExpr)
        assert not out_hp or isinstance(out_hp, HCSP)

        self.type = "ode"
        self.eqs = eqs  # list of tuples (string, AExpr)
        self.constraint = constraint  # BExpr
        self.out_hp = out_hp  # None or hcsp

    def __eq__(self, other):
        return self.type == other.type and self.eqs == other.eqs and \
               self.constraint == other.constraint and self.out_hp == other.out_hp

    def __str__(self):
        str_eqs = ", ".join(var_name + "_dot = " + str(expr) for var_name, expr in self.eqs)
        str_out_hp = "" if isinstance(self.out_hp, Skip) else " |> " + str(self.out_hp)
        return "<" + str_eqs + " & " + str(self.constraint) + ">" + str_out_hp

    def get_vars(self):
        var_set = set()
        for variable, expression in self.eqs:
            var_set.add(variable)
            var_set.update(expression.get_vars())
        var_set.update(self.constraint.get_vars())
        var_set.update(self.out_hp.get_vars())
        return var_set

    def get_chs(self):
        return self.out_hp.get_chs()


class ODE_Comm(HCSP):
    """Represents an ODE program that can be interrupted by
    communications, of the form

    <F(s',s) = 0 & B> |> [] (io_i --> Q_i)

    """
    def __init__(self, eqs, constraint, io_comms):
        """Each equation is of the form (var_name, expr). Each element
        of io_comms is of the form (comm_hp, out_hp), where comm_hp
        is a communication process (either InputChannel or OutputChannel).
        Whenever one of comm_hp is received, the ODE stops and performs
        out_hp.

        """
        super(ODE_Comm, self).__init__()
        assert isinstance(eqs, list)
        for eq in eqs:
            assert isinstance(eq, tuple) and len(eq) == 2
            assert isinstance(eq[0], str) and isinstance(eq[1], AExpr)
        assert isinstance(constraint, BExpr)
        assert isinstance(io_comms, list)
        for io_comm in io_comms:
            assert isinstance(io_comm, tuple) and len(io_comm) == 2
            assert is_comm_channel(io_comm[0]) and isinstance(io_comm[1], HCSP)

        self.type = "ode_comm"
        self.eqs = eqs  # list
        self.constraint = constraint  # BExpr
        self.io_comms = io_comms  # list

    def __eq__(self, other):
        return self.type == other.type and self.eqs == other.eqs and \
               self.constraint == other.constraint and self.io_comms == other.io_comms

    def __str__(self):
        str_eqs = ", ".join(var_name + "_dot = " + str(expr) for var_name, expr in self.eqs)
        str_io_comms = ", ".join(str(comm_hp) + " --> " + str(out_hp) for comm_hp, out_hp in self.io_comms)
        return "<" + str_eqs + " & " + str(self.constraint) + "> |> [] (" + str_io_comms + ")"

    def __repr__(self):
        str_eqs = ", ".join(var_name + ", " + str(expr) for var_name, expr in self.eqs)
        str_io_comms = ", ".join(str(comm_hp) + ", " + str(out_hp) for comm_hp, out_hp in self.io_comms)
        return "ODEComm(%s, %s, %s)" % (str_eqs, str(self.constraint), str_io_comms)

    def sc_str(self):
        derivatives = "DOT(" + ", ".join(var_name for var_name, _ in self.eqs) + ")"
        expressions = "{" + ", ".join(str(expr) for _, expr in self.eqs) + "}"
        domain = "DOMAIN(" + ("TRUE" if self.constraint == true_expr else str(self.constraint)) + ")"
        assert all(isinstance(out_hp, Var) for _, out_hp in self.io_comms)
        interupt = "INTERRUPT({" + ", ".join(comm_hp.sc_str() for comm_hp, _ in self.io_comms) + "}{" \
                   + ", ".join(out_hp.sc_str() for _, out_hp in self.io_comms) + "})"
        return derivatives + "=" + expressions + " " + domain + " " + interupt

    def get_vars(self):
        var_set = set()
        for variable, expression in self.eqs:
            var_set.add(variable)
            var_set.update(expression.get_vars())
        var_set.update(self.constraint.get_vars())
        for ch, out_hp in self.io_comms:
            var_set.update(ch.get_vars())
            var_set.update(out_hp.get_vars())
        return var_set

    def get_chs(self):
        ch_set = set()
        for ch, out_hp in self.io_comms:
            ch_set.update(ch.get_chs())
            ch_set.update(out_hp.get_chs())
        return ch_set


class Loop(HCSP):
    """Represents an infinite loop of a program."""
    def __init__(self, hp, constraint=true_expr):
        super(Loop, self).__init__()
        self.type = 'loop'
        assert isinstance(hp, HCSP)
        self.hp = hp  # hcsp
        self.constraint = constraint

    def __eq__(self, other):
        return self.type == other.type and self.hp == other.hp and self.constraint == other.constraint

    def __repr__(self):
        if self.constraint == true_expr:
            return "Loop(%s)" % repr(self.hp)
        else:
            return "Loop(%s, %s)" % (repr(self.hp), self.constraint)

    def __str__(self):
        if self.constraint == true_expr:
            return "(%s)**" % str(self.hp)
        else:
            return "(%s){%s}**" % (str(self.hp), str(self.constraint))

    def sc_str(self):
        assert isinstance(self.hp, Var)
        return self.hp.sc_str() + "**"

    def get_vars(self):
        return self.hp.get_vars()

    def get_chs(self):
        return self.hp.get_chs()


class Condition(HCSP):
    """The alternative cond -> hp behaves as hp if cond is true;
     otherwise, it terminates immediately."""
    def __init__(self, cond, hp):
        super(Condition, self).__init__()
        assert isinstance(cond, (BExpr,RelExpr)) and isinstance(hp, HCSP)
        self.type = "condition"
        self.cond = cond  # BExpr
        self.hp = hp  # HCSP

    def __eq__(self, other):
        return self.type == other.type and self.cond == other.cond and self.hp == other.hp

    def __repr__(self):
        return "Condition(%s, %s)" % (str(self.cond), repr(self.hp))

    def __str__(self):
        return str(self.cond) + " -> " + \
            (str(self.hp) if self.hp.priority() > self.priority() else "(" + str(self.hp) + ")")

    def sc_str(self):
        assert isinstance(self.hp, Var)
        if_hps = ((self.cond, self.hp),)
        else_hp = Skip()
        return ITE(if_hps, else_hp).sc_str()

    def get_vars(self):
        return self.cond.get_vars().union(self.hp.get_vars())

    def get_chs(self):
        return self.hp.get_chs()


class Parallel(HCSP):
    def __init__(self, *hps):
        """hps is a list of hybrid programs."""
        super(Parallel, self).__init__()
        self.type = "parallel"
        assert all(isinstance(hp, HCSP) for hp in hps)
        assert len(hps) >= 2
        # self.hps = list(hps)  # type(hps) == tuple
        self.hps = []
        for hp in hps:
            if hp.type == "parallel":
                self.hps.extend(hp.hps)
            else:
                self.hps.append(hp)

    def __eq__(self, other):
        return self.type == other.type and self.hps == other.hps

    def __repr__(self):
        return "Parallel(%s)" % (", ".join(repr(hp) for hp in self.hps))

    def __str__(self):
        return " || ".join(
            str(hp) if hp.priority() > self.priority() else "(" + str(hp) + ")"
            for hp in self.hps)

    def sc_str(self):
        return " || ".join(
            hp.sc_str() if hp.priority() > self.priority() else "(" + hp.sc_str() + ")"
            for hp in self.hps)

    def get_vars(self):
        var_set = set()
        for hp in self.hps:
            var_set.update(hp.get_vars())
        return var_set

    def get_chs(self):
        ch_set = set()
        for hp in self.hps:
            ch_set.update(hp.get_chs())
        return ch_set


class SelectComm(HCSP):
    def __init__(self, *io_comms):
        """io_comms is a list of pairs, where the first element of each
        pair must be a communication, and the second entry can be
        any program.
        
        """
        super(SelectComm, self).__init__()
        self.type = "select_comm"
        assert len(io_comms) >= 2

        assert all(is_comm_channel(comm_hp) and isinstance(out_hp, HCSP)
                   for comm_hp, out_hp in io_comms)
        self.io_comms = tuple(io_comms)

    def __eq__(self, other):
        return self.type == other.type and self.io_comms == other.io_comms

    def __repr__(self):
        return "SelectComm(%s)" % (",".join("%s,%s" % (repr(comm_hp), repr(out_hp))
                                            for comm_hp, out_hp in self.io_comms))

    def __str__(self):
        return " $ ".join(
            "%s --> %s" % (comm_hp, out_hp) if out_hp.priority() > self.priority() else
            "%s --> (%s)" % (comm_hp, out_hp)
            for comm_hp, out_hp in self.io_comms)

    def sc_str(self):
        return " [[ ".join("(%s; %s)" % (comm_hp.sc_str(), out_hp.sc_str()) if out_hp.priority() > self.priority()
                           else "(%s; (%s))" % (comm_hp.sc_str(), out_hp.sc_str()) for comm_hp, out_hp in self.io_comms)

    def get_vars(self):
        var_set = set()
        for ch, out_hp in self.io_comms:
            var_set.update(ch.get_vars())
            var_set.update(out_hp.get_vars())
        return var_set

    def get_chs(self):
        ch_set = set()
        for ch, out_hp in self.io_comms:
            ch_set.update(ch.get_chs())
            ch_set.update(out_hp.get_chs())
        return ch_set


class Recursion(HCSP):
    def __init__(self, hp, entry="X"):
        super(Recursion, self).__init__()
        assert isinstance(entry, str) and isinstance(hp, HCSP)
        self.type = "recursion"
        self.entry = entry
        self.hp = hp

    def __eq__(self, other):
        return self.type == other.type and self.entry == other.entry and self.hp == other.hp

    def __repr__(self):
        return "Recursion(%s, %s)" % (self.entry, repr(self.hp))

    def __str__(self):
        return "rec " + self.entry + ".(" + str(self.hp) + ")"

    def get_vars(self):
        return self.hp.get_vars()

    def get_chs(self):
        return self.hp.get_chs()


class ITE(HCSP):
    def __init__(self, if_hps, else_hp):
        """if-then-else statements.

        if_hps is a list of condition-program pairs. else_hp is a program.
        The program associated to the first true condition in if_hps will
        be executed. If no condition is true, else_hp is executed.

        """
        super(ITE, self).__init__()
        #assert all(isinstance(cond, BExpr) and isinstance(hp, HCSP) for cond, hp in if_hps)
        #assert isinstance(else_hp, HCSP)
        self.type = "ite"
        self.if_hps = tuple(tuple(p) for p in if_hps)
        self.else_hp = else_hp

    def __eq__(self, other):
        return self.type == other.type and self.if_hps == other.if_hps and self.else_hp == other.else_hp

    def __repr__(self):
        if_hps_strs = ", ".join("%s, %s" % (cond, repr(hp)) for cond, hp in self.if_hps)
        return "ITE(%s, %s)" % (if_hps_strs, repr(self.else_hp))

    def __str__(self):
        res = "if %s then %s " % (self.if_hps[0][0], self.if_hps[0][1])
        for cond, hp in self.if_hps[1:]:
            res += "elif %s then %s " % (cond, hp)
        res += "else %s endif" % self.else_hp
        return res

    def sc_str(self):
        assert len(self.if_hps) == 1 and isinstance(self.if_hps[0][1], Var) and isinstance(self.else_hp, (Skip, Var))
        return "if %s then %s else %s" % (self.if_hps[0][0], self.if_hps[0][1].sc_str(), self.else_hp.sc_str())

    def get_vars(self):
        var_set = set()
        for cond, hp in self.if_hps:
            var_set.update(cond.get_vars())
            var_set.update(hp.get_vars())
        var_set.update(self.else_hp.get_vars())
        return var_set

    def get_chs(self):
        ch_set = set()
        for _, hp in self.if_hps:
            ch_set.update(hp.get_chs())
        ch_set.update(self.else_hp.get_chs())
        return ch_set


def get_comm_chs(hp):
    """Returns the list of communication channels for the given program.
    
    Result is a list of pairs (ch_name, '?'/'!').
    
    """
    assert isinstance(hp, HCSP)
    collect = []

    def rec(_hp):
        if _hp.type == 'input_channel':
            collect.append((_hp.ch_name, '?'))
        elif _hp.type == 'output_channel':
            collect.append((_hp.ch_name, '!'))
        elif _hp.type == 'sequence':
            for arg in _hp.hps:
                rec(arg)
        elif _hp.type == 'ode':
            if _hp.out_hp:
                rec(_hp.out_hp)
        elif _hp.type in ('ode_comm', 'select_comm'):
            for comm_hp, out_hp in _hp.io_comms:
                rec(comm_hp)
                rec(out_hp)
        elif _hp.type in ('loop', 'condition', 'recursion'):
            rec(_hp.hp)
        elif _hp.type == 'ite':
            for _, sub_hp in _hp.if_hps:
                rec(sub_hp)
            rec(_hp.else_hp)
    
    rec(hp)
    return list(OrderedDict.fromkeys(collect))


class HCSPInfo:
    """HCSP process with extra information."""
    def __init__(self, name, hp, *, outputs=None):
        self.name = name
        self.hp = hp
        
        # List of output variables, None indicates output everything
        self.outputs = outputs

    def __str__(self):
        return self.name + ' ::=\n' + str(self.hp)

    def __repr__(self):
        return "HCSPInfo(%s, %s)" % (self.name, str(self.hp))

    def __eq__(self, other):
        return self.name == other.name and self.hp == other.hp

def HCSP_subst(hp, inst):
    """Substitution of program variables for their instantiations."""
    assert isinstance(hp, HCSP)
    if isinstance(hp, Var):
        if hp.name in inst:
            return inst[hp.name]
        else:
            return hp
    elif isinstance(hp, (Loop, Recursion, Condition)):
        hp.hp = HCSP_subst(hp.hp, inst)
        return hp
    elif isinstance(hp, Sequence):
        hps = [HCSP_subst(sub_hp, inst) for sub_hp in hp.hps]
        return Sequence(*hps)
    elif isinstance(hp, ODE):
        hp.out_hp = HCSP_subst(hp.out_hp, inst)
        return hp
    elif isinstance(hp, (ODE_Comm, SelectComm)):
        hp.io_comms = tuple((io_comm[0], HCSP_subst(io_comm[1], inst)) for io_comm in hp.io_comms)
        return hp
    elif isinstance(hp, ITE):
        hp.if_hps = tuple((e[0], HCSP_subst(e[1], inst)) for e in hp.if_hps)
        hp.else_hp = HCSP_subst(hp.else_hp, inst)
        return hp
    elif isinstance(hp, (Skip, Assign, Wait, InputChannel, OutputChannel)):
        return hp
    else:
        print(hp)
        raise NotImplementedError


class HCSPProcess:
    """System of HCSP processes. Input is a list of (name, HCSP) pairs."""
    def __init__(self, hps=None):
        """Initialize with an optional list of definitions."""

        # List of (name, HCSP) pairs.
        self.hps = []
        if hps:
            for name, hp in hps:
                self.hps.append((name, hp))

    def add(self, name, hp):
        """Insert (name, hp) at the end."""
        self.hps.append((name, hp))

    def extend(self, lst):
        """Insert list of (name, hp) at the end."""
        if isinstance(lst, HCSPProcess):
            self.hps.extend(lst.hps)
        else:
            self.hps.extend(lst)

    def insert(self, n, name, hp):
        """Insert (name, hp) at position n."""
        self.hps.insert(n, (name, hp))

    def substitute(self):
        """Substitute program variables for their definitions."""
        def _substitute(_hp):
            assert isinstance(_hp, HCSP)
            if isinstance(_hp, Var):
                _name = _hp.name
                if _name in substituted.keys():
                    _hp = substituted[_name]
                elif _name in hps_dict:
                    _hp = _substitute(hps_dict[_name])
                    substituted[_name] = _hp
                    del hps_dict[_name]
            elif isinstance(_hp, (Loop, Recursion, Condition)):
                _hp.hp = _substitute(_hp.hp)
            elif isinstance(_hp, Sequence):
                _hps = [_substitute(sub_hp) for sub_hp in _hp.hps]
                _hp = Sequence(*_hps)
                # _hp = Sequence(tuple(_substitute(sub_hp) for sub_hp in _hp.hps))
            elif isinstance(_hp, ODE):
                _hp.out_hp = _substitute(_hp.out_hp)
            elif isinstance(_hp, (ODE_Comm, SelectComm)):
                _hp.io_comms = tuple((io_comm[0], _substitute(io_comm[1])) for io_comm in _hp.io_comms)
            elif isinstance(_hp, ITE):
                _hp.if_hps = tuple((e[0], _substitute(e[1])) for e in _hp.if_hps)
                _hp.else_hp = _substitute(_hp.else_hp)
            return _hp

        hps_dict = {name: hp for name, hp in self.hps}
        #assert len(hps_dict) == len(self.hps)
        substituted = dict()
        while hps_dict:
            name, hp = hps_dict.popitem()
            assert name not in substituted
            substituted[name] = _substitute(hp)
        assert set(substituted.keys()) == set(name for name, _ in self.hps)

        return substituted

    def __str__(self):
        return "\n".join("%s ::= %s" % (name, str(hp)) for name, hp in self.hps)

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        return self.hps == other.hps

    def sc_str(self):
        assert len([_ for _, hp in self.hps if isinstance(hp, Parallel)]) == 1
        system, process = None, None
        for name, hp in self.hps:
            if isinstance(hp, Parallel):
                system, process = name, hp
                break
        sys_def = "systemDef " + system + " ::= " + process.sc_str() + "\n\n"
        var_def = "variableDef ::= " + ("; ".join(self.get_vars())) + "\n\n"
        ch_def = "channelDef ::= " + ("; ".join([ch.name for ch in self.get_chs()])) + "\n\n"
        hp_def = "\n".join("processDef " + "%s ::= %s" % (name, hp.sc_str()) for name, hp in self.hps
                           if not isinstance(hp, Parallel))
        return sys_def + var_def + ch_def + hp_def

    def get_vars(self):
        var_set = set()
        for _, hp in self.hps:
            var_set.update(hp.get_vars())
        return var_set

    def get_chs(self):
        ch_set = set()
        for _, hp in self.hps:
            ch_set.update(hp.get_chs())
        return ch_set
