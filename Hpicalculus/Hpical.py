"""Hybrid programs"""

from collections import OrderedDict
from Hpicalculus.expr import AExpr, AVar, AConst, BExpr, true_expr, false_expr, RelExpr, LogicExpr
from ss2hcsp.matlab import function
from ss2hcsp.util.topsort import topological_sort
import re


class Channel:
    """Models a channel identifier. It is a string followed by a list
    of integer or variable arguments.

    The usual channel is modeled by a string without arguments. Further
    arguments can be given for parameterized channels. Parameters that
    are already decided are indicated by integers. Those that still need
    to be matched are indicated by variables.

    """

    def __init__(self, name, args=None, meta=None):
        assert isinstance(name, str)
        if args is None:
            args = tuple()

        # Each argument is either integer, (unevaluated) expression, or variable
        assert isinstance(args, tuple) and all(
            isinstance(arg, (AExpr, int, str)) for arg in args)

        self.name = name
        self.args = args
        self.meta = meta

    def __str__(self):
        def str_arg(arg):
            # if isinstance(arg, str):
            #     return repr(arg)
            if isinstance(arg, AConst) and isinstance(arg.value, str) and arg.value[0] != "\"":
                return "\"" + arg.value + "\""
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


class HPiCal:
    def __init__(self):
        self.type = None
        self.ses_in = list()

    def sc_str(self):
        """
        The HPiCal form that can be accepted by HPiCal2SC,
        the program translating HPiCal into SystemC.
        """
        return str(self)

    def get_vars(self):
        return set()

    def get_funs(self):
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
        elif self.type == "ichoice":
            return 80
        elif self.type == "condition":
            return 90
        else:
            return 100

    def size(self):
        """Returns size of HPiCal program."""
        if isinstance(self, (Var, Skip, Wait, Assign, Assert, Test, Log,
                             )):
            return 1
        elif isinstance(self, (Sequence, Parallel)):
            return 1 + sum([hp.size() for hp in self.hps])
        elif isinstance(self, (Loop, Condition, Recursion)):
            return 1 + self.hp.size()
        elif isinstance(self, ODE):
            return 1
        elif isinstance(self, (ODE_Comm, SelectComm)):
            return 1 + sum([1 + out_hp.size() for comm_hp, out_hp in self.io_comms])
        elif isinstance(self, ITE):
            return 1 + sum([1 + hp.size() for cond, hp in self.if_hps]) + self.else_hp.size()
        else:
            raise NotImplementedError

    def contain_hp(self, name):
        """Returns whether the given HPiCal program contains Var(name)."""
        if isinstance(self, Var):
            return self.name == name
        elif isinstance(self, (Skip, Wait, Assign, Assert, Test, Log, InputChannel, OutputChannel)):
            return False
        elif isinstance(self, (Sequence, Parallel)):
            for sub_hp in self.hps:
                if sub_hp.contain_hp(name):
                    return True
        elif isinstance(self, (Loop, Condition, Recursion)):
            # Note the test for Recursion is imprecise.
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
            for sub_hp in [hp for cond, hp in self.if_hps]:
                if sub_hp.contain_hp(name):
                    return True
        else:
            raise NotImplementedError

    def get_contain_hps(self):
        """Returns the set of Var calls contained in self."""
        if isinstance(self, Var):
            return {self.name}
        elif isinstance(self, (Skip, Wait, Assign, Assert, Test, Log, InputChannel, OutputChannel)):
            return set()
        elif isinstance(self, (Sequence, Parallel)):
            return set().union(*(hp.get_contain_hps() for hp in self.hps))
        elif isinstance(self, (Loop, Condition, Recursion)):
            # Note the test for Recursion is imprecise.
            return self.hp.get_contain_hps()
        elif isinstance(self, ODE):
            return self.out_hp.get_contain_hps()
        elif isinstance(self, (ODE_Comm, SelectComm)):
            return set().union(*(io_comm[1].get_contain_hps() for io_comm in self.io_comms))
        elif isinstance(self, ITE):
            return self.else_hp.get_contain_hps().union(*(hp.get_contain_hps() for cond, hp in self.if_hps))
        else:
            raise NotImplementedError

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
            return Log(self.pattern.subst(inst), exprs=[expr.subst(inst) for expr in self.exprs])
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


class Restriction(HPiCal):
    def __init__(self, name, expr, meta=None):
        super(Restriction, self).__init__()
        self.type = "Restriction"
        assert isinstance(name, str)
        self.name = str(name)
        self.expr = expr
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.name == other.name and self.expr == other.expr

    def __repr__(self):
        return "Retriction %s<%s>" % (self.name, self.expr)

    def __str__(self):
        return "%s!<%s>" % (self.name, self.expr)

    def __hash__(self):
        return hash(("Restricion", self.name, self.expr))


class Replication(HPiCal):
    def __init__(self, name, expr, meta=None):
        super(Replication, self).__init__()
        self.type = "Replication"
        assert isinstance(name, str)
        self.name = str(name)
        self.expr = expr
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.name == other.name and self.expr == other.expr

    def __repr__(self):
        return "Replication %s(%s)" % (self.name, self.expr)

    def __str__(self):
        return "!%s(%s)" % (self.name, self.expr)

    def __hash__(self):
        return hash(("Replication", self.name, self.expr))


class Oplus(HPiCal):

    def __init__(self, eqs, constraint, name, c1, c2, meta):
        """Each equation is of the form (var_name, expr), where var_name
        is the name of the variable, and expr is its derivative.

        constraint is a boolean formula.

        """
        super(Oplus, self).__init__()
        assert isinstance(eqs, list)
        for eq in eqs:
            assert isinstance(eq, tuple) and len(eq) == 2
            assert isinstance(eq[0], str) and isinstance(eq[1], AExpr)
        assert isinstance(constraint, BExpr)

        self.type = "Oplus"
        self.eqs = eqs  # list of tuples (string, AExpr)
        self.constraint = constraint  # BExpr

        self.meta = meta
        self.name = name
        self.c1 = c1
        self.c2 = c2

    def __eq__(self, other):
        return self.type == other.type and self.eqs == other.eqs and \
            self.constraint == other.constraint and self.c1 == other.c1 and \
            self.c2 == other.c2

    def __str__(self):
        str_eqs = ", ".join(var_name + "_dot = " + str(expr)
                            for var_name, expr in self.eqs)
        return "<" + str_eqs + " & " + str(self.constraint) + ">" + \
            "|>OPLUS(" + str(self.name) + \
            "{" + str(self.c1) + "}, " + str(self.c2) + ")"

    def __repr__(self):
        return "OPLUS<%s, %s>(%s{%s}%s)" % (repr(self.eqs), repr(self.constraint), repr(self.name), repr(self.c1), repr(self.c2))

    def __hash__(self):
        return hash(("OPLUS", self.eqs, self.constraint, self.name, self.c1, self.c2))


class And(HPiCal):

    def __init__(self, eqs, constraint, name, c1, c2, c3, meta):
        """Each equation is of the form (var_name, expr), where var_name
        is the name of the variable, and expr is its derivative.

        constraint is a boolean formula.

        """
        super(And, self).__init__()
        assert isinstance(eqs, list)
        for eq in eqs:
            assert isinstance(eq, tuple) and len(eq) == 2
            assert isinstance(eq[0], str) and isinstance(eq[1], AExpr)
        assert isinstance(constraint, BExpr)

        self.type = "And"
        self.eqs = eqs  # list of tuples (string, AExpr)
        self.constraint = constraint  # BExpr

        self.meta = meta
        self.name = name
        self.c1 = c1
        self.c2 = c2
        self.c3 = c3

    def __eq__(self, other):
        return self.type == other.type and self.eqs == other.eqs and \
            self.constraint == other.constraint and self.c1 == other.c1 and \
            self.c2 == other.c2 and self.c3 == other.c3

    def __str__(self):
        str_eqs = ", ".join(var_name + "_dot = " + str(expr)
                            for var_name, expr in self.eqs)
        return "<" + str_eqs + " & " + str(self.constraint) + ">" + \
            "|>AND(" + str(self.name) + "{" + str(self.c1) + \
            "," + str(self.c2) + "}, " + str(self.c3) + ")"

    def __repr__(self):
        return "AND<%s, %s>(%s{%s,%s}%s)" % (repr(self.eqs), repr(self.constraint), repr(self.name), repr(self.c1), repr(self.c2), repr(self.c3))

    def __hash__(self):
        return hash(("AND", self.eqs, self.constraint, self.name, self.c1, self.c2, self.c3))


class Var(HPiCal):
    def __init__(self, name, meta=None):
        super(Var, self).__init__()
        self.type = "var"
        assert isinstance(name, str)
        self.name = name
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.name == other.name

    def __repr__(self):
        return "Var(%s)" % self.name

    def __str__(self):
        return "@" + self.name

    def __hash__(self):
        return hash(("VAR", self.name))

    def sc_str(self):
        return self.name


class Skip(HPiCal):
    def __init__(self, meta=None):
        super(Skip, self).__init__()
        self.type = "skip"
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type

    def __repr__(self):
        return "Skip()"

    def __str__(self):
        return "skip"

    def __hash__(self):
        return hash("Skip")


class Wait(HPiCal):
    def __init__(self, delay, meta=None):
        super(Wait, self).__init__()
        assert isinstance(delay, AExpr)
        self.type = "wait"
        self.delay = delay
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.delay == other.delay

    def __repr__(self):
        return "Wait(%s)" % str(self.delay)

    def __str__(self):
        return "wait(%s)" % str(self.delay)

    def __hash__(self):
        return hash(("Wait", self.delay))


class End(HPiCal):
    def __init__(self, meta=None):
        super(End, self).__init__()
        self.type = "end"
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type

    def __repr__(self):
        return "end"

    def __str__(self):
        return "end"

    def __hash__(self):
        return hash("end")


class Assign(HPiCal):
    """Assignment command.

    var_name : AExpr - variable to be assigned, one of AVar (e.g. x),
        ArrayIdxExpr (e.g. a[0]), and FieldNameExpr (e.g. a.field1).
    expr : AExpr - value to be assigned.

    Left side is an expression that can serve as a lname. This includes
    variables, array indices, and field names.

    """

    def __init__(self, var_name, expr, meta=None):
        super(Assign, self).__init__()
        self.type = "assign"
        assert isinstance(expr, (AExpr, str, int))
        if isinstance(var_name, str):
            var_name = AVar(str(var_name))
        if isinstance(var_name, AExpr):
            self.var_name = var_name
        elif isinstance(var_name, function.DirectName):
            self.var_name = var_name
        else:
            var_name = tuple(var_name)
            assert len(var_name) >= 2 and all(isinstance(
                name, (str, AExpr)) for name in var_name)
            self.var_name = [AVar(n) if isinstance(
                n, str) else n for n in var_name]
        self.expr = expr
        self.meta = meta

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
        elif isinstance(self.var_name, function.DirectName):
            var_str = str(self.var_name)
        else:
            var_str = "(%s)" % (', '.join(str(n) for n in self.var_name))
        return "%s := %s" % (var_str, self.expr)

    def __hash__(self):
        return hash(("Assign", self.var_name, self.expr))

    def get_vars(self):
        if isinstance(self.var_name, AExpr):
            var_set = {str(self.var_name)}
        else:
            var_set = set(str(n) for n in self.var_name)
        return var_set.union(self.expr.get_vars())

    def get_funs(self):
        return set().union(self.expr.get_funs())

    def sc_str(self):
        return re.sub(pattern=":=", repl="=", string=str(self))

    def priority(self):
        return 100


class RandomAssign(HPiCal):
    """Random Assignment commend.

    x := {x >= 1}

    var_name : AExpr - variable to be assigned, one of AVar (e.g. x), ArrayIdxExpr (e.g. a[0]), and FieldNameExpr (e.g. a.field1).
    expr : BExpr - the range value to be randomly choose from.

    Left side is an expression that can serve as a lname. This includes
    variables, array indices, and field names.

    """

    def __init__(self, var_name, expr, meta=None):
        super(RandomAssign, self).__init__()
        self.type = "randomassign"
        assert isinstance(expr, BExpr)
        if isinstance(var_name, str):
            var_name = AVar(str(var_name))
        if isinstance(var_name, AExpr):
            self.var_name = var_name
        elif isinstance(var_name, function.DirectName):
            self.var_name = var_name
        else:
            var_name = tuple(var_name)
            assert len(var_name) <= 2 and all(
                isinstance(name, (str, AExpr))for name in var_name)
            self.var_name = [AVar(n) if isinstance(
                n, str) else n for n in var_name]
        self.expr = expr
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.var_name == other.var_name and self.expr == other.expr

    def __repr__(self):
        if isinstance(self.var_name, AExpr):
            var_str = str(self.var_name)
        else:
            var_str = "[%s]" % (','.join(str(n) for n in self.var_name))
        return "RandomAssign(%s, %s)" % (var_str, str(self.expr))

    def __str__(self):
        if isinstance(self.var_name, AExpr):
            var_str = str(self.var_name)
        elif isinstance(self.var_name, function.DirectName):
            var_str = str(self.var_name)
        else:
            var_str = "(%s)" % (', '.join(str(n) for n in self.var_name))
        return var_str + " := " + "{" + str(self.expr) + "}"

    def __hash__(self):
        return hash(("RandomAssign", self.var_name, self.expr))

    def get_vars(self):
        if isinstance(self.var_name, AExpr):
            var_set = {str(self.var_name)}
        else:
            var_set = set(str(n) for n in self.var_name)
        return var_set.union(self.expr.get_vars())

    def get_funs(self):
        return set.union(self.expr.get_funs())

    def priority(self):
        return 100


class Assert(HPiCal):
    def __init__(self, bexpr, msgs, meta=None):
        super(Assert, self).__init__()
        self.type = "assert"
        assert isinstance(bexpr, BExpr)
        self.bexpr = bexpr
        msgs = tuple(msgs)
        assert all(isinstance(msg, AExpr) for msg in msgs)
        self.msgs = msgs
        self.meta = meta

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

    def __hash__(self):
        return hash(("Assert", self.bexpr, self.msgs))

    def get_vars(self):
        var_set = self.bexpr.get_vars()
        for msg in self.msgs:
            var_set.update(msg.get_vars())
        return var_set

    def get_funs(self):
        fun_set = self.bexpr.get_funs()
        for msg in self.msgs:
            fun_set.update(msg.get_funs())
        return fun_set


class Test(HPiCal):
    def __init__(self, bexpr, msgs, meta=None):
        super(Test, self).__init__()
        self.type = "test"
        assert isinstance(bexpr, BExpr)
        self.bexpr = bexpr
        msgs = tuple(msgs)
        assert all(isinstance(msg, AExpr) for msg in msgs)
        self.msgs = msgs
        self.meta = meta

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

    def __hash__(self):
        return hash(("Test", self.bexpr, self.msgs))

    def get_vars(self):
        var_set = self.bexpr.get_vars()
        for msg in self.msgs:
            var_set.update(msg.get_vars())
        return var_set

    def get_funs(self):
        fun_set = self.bexpr.get_funs()
        for msg in self.msgs:
            fun_set.update(msg.get_funs())
        return fun_set


class Log(HPiCal):
    def __init__(self, pattern, *, exprs=None, meta=None):
        super(Log, self).__init__()
        self.type = "log"
        assert isinstance(pattern, AExpr)
        self.pattern = pattern
        if exprs is None:
            exprs = tuple()
        else:
            exprs = tuple(exprs)
        assert all(isinstance(expr, AExpr) for expr in exprs)
        self.exprs = exprs
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.pattern == other.pattern and self.exprs == other.exprs

    def __repr__(self):
        if self.exprs:
            return "Log(%s,%s)" % (repr(self.pattern), ','.join(repr(expr) for expr in self.exprs))
        else:
            return "Log(%s)" % repr(self.pattern)

    def __str__(self):
        if self.exprs:
            return "log(%s,%s)" % (self.pattern, ','.join(str(expr) for expr in self.exprs))
        else:
            return "log(%s)" % self.pattern

    def __hash__(self):
        return hash(("Log", self.pattern, self.exprs))

    def get_vars(self):
        var_set = self.pattern.get_vars()
        for expr in self.exprs:
            var_set.update(expr.get_vars())
        return var_set

    def get_funs(self):
        fun_set = self.pattern.get_funs()
        for expr in self.exprs:
            fun_set.update(expr.get_funs())
        return fun_set


class Outputmsg(HPiCal):
    def __init__(self, ouput_name, *, exprs=None, meta=None):
        super(Outputmsg, self).__init__()
        self.type = "Outputmsg"
        assert isinstance(ouput_name, str)
        self.ouput_name = ouput_name
        if exprs is None:
            exprs = tuple()
        else:
            exprs = tuple(exprs)
        assert all(isinstance(expr, AExpr) for expr in exprs)
        self.exprs = exprs
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.ouput_name == other.ouput_name and self.exprs == other.exprs

    def __repr__(self):
        if self.exprs:
            return "Outputmsg(%s,%s)" % (repr(self.ouput_name), ','.join(repr(expr) for expr in self.exprs))
        else:
            return "Outputmsg(%s)" % repr(self.ouput_name)

    def __str__(self):
        if self.exprs:
            return "%s-<%s>" % (self.ouput_name, ','.join(str(expr) for expr in self.exprs))
        else:
            return "%s-<>" % self.ouput_name

    def __hash__(self):
        return hash(("Outputmsg", self.ouput_name, self.exprs))


class Inputmsg(HPiCal):
    def __init__(self, input_name, *, exprs=None, meta=None):
        super(Inputmsg, self).__init__()
        self.type = "Inputmsg"
        assert isinstance(input_name, str)
        self.input_name = input_name
        if exprs is None:
            exprs = tuple()
        else:
            exprs = tuple(exprs)
        assert all(isinstance(expr, AExpr) for expr in exprs)
        self.exprs = exprs
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.input_name == other.input_name and self.exprs == other.exprs

    def __repr__(self):
        if self.exprs:
            return "Intputmsg(%s,%s)" % (repr(self.input_name), ','.join(repr(expr) for expr in self.exprs))
        else:
            return "Intputmsg(%s)" % repr(self.input_name)

    def __str__(self):
        if self.exprs:
            return "%s-(%s)" % (self.input_name, ','.join(str(expr) for expr in self.exprs))
        else:
            return "%s-()" % self.input_name

    def __hash__(self):
        return hash(("Inputmsg", self.input_name, self.exprs))


class Sequence(HPiCal):
    def __init__(self, *hps, meta=None):
        """hps is a list of hybrid programs."""
        super(Sequence, self).__init__()
        self.type = "sequence"
        assert all(isinstance(hp, HPiCal) for hp in hps)
        assert len(hps) >= 1
        self.hps = []
        for hp in hps:
            if isinstance(hp, Sequence):
                self.hps.extend(hp.hps)
            else:
                self.hps.append(hp)
        self.hps = tuple(self.hps)
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.hps == other.hps

    def __repr__(self):
        return "Seq(%s)" % ", ".join(repr(hp) for hp in self.hps)

    def __str__(self):
        return "; ".join(
            str(hp) if hp.priority() > self.priority() else "(" + str(hp) + ")"
            for hp in self.hps)

    def __hash__(self):
        return hash(("Sequence", self.hps))

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

    def get_funs(self):
        fun_set = set()
        for hp in self.hps:
            fun_set.update(hp.get_funs())
        return fun_set

    def get_chs(self):
        ch_set = set()
        for hp in self.hps:
            # ch_set = ch_set.union(hp.get_chs())
            ch_set.update(hp.get_chs())
        return ch_set


def seq(hps):
    """Returns the sequential composition of hps. Special case when hps has
    length 0 or 1.

    """
    assert all(isinstance(hp, HPiCal) for hp in hps)
    hps = [hp for hp in hps if hp != Skip()]
    if len(hps) == 0:
        return Skip()
    elif len(hps) == 1:
        return hps[0]
    else:
        return Sequence(*hps)


class IChoice(HPiCal):
    """Represents internal choice of the form P ++ Q."""

    def __init__(self, hp1, hp2, meta=None):
        super(IChoice, self).__init__()
        self.type = "ichoice"
        assert isinstance(hp1, HPiCal) and isinstance(hp2, HPiCal)
        self.hp1 = hp1
        self.hp2 = hp2
        self.meta = meta

    def __eq__(self, other):
        return self.hp1 == other.hp1 and self.hp2 == other.hp2

    def __str__(self):
        return "%s ++ %s" % (str(self.hp1), str(self.hp2))

    def __repr__(self):
        return "IChoice(%s,%s)" % (repr(self.hp1), repr(self.hp2))

    def __hash__(self):
        return hash(("ICHOICE", self.hp1, self.hp2))

    def get_vars(self):
        return self.hp1.get_vars().union(self.hp2.get_vars())

    def get_funs(self):
        return self.hp1.get_funs().union(self.hp2.get_funs())


class ODE(HPiCal):
    """Represents an ODE program of the form

    <F(s',s) = 0 & B> |> Q

    """

    def __init__(self, eqs, constraint, *, out_hp=Skip(), meta=None, inv=None):
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
        assert not out_hp or isinstance(out_hp, HPiCal)

        self.type = "ode"
        self.eqs = eqs  # list of tuples (string, AExpr)
        self.constraint = constraint  # BExpr
        self.out_hp = out_hp  # None or HPiCal
        self.meta = meta
        self.inv = inv

    def __eq__(self, other):
        return self.type == other.type and self.eqs == other.eqs and \
            self.constraint == other.constraint and self.out_hp == other.out_hp

    def __str__(self):
        str_eqs = ", ".join(var_name + "_dot = " + str(expr)
                            for var_name, expr in self.eqs)
        str_out_hp = "" if isinstance(
            self.out_hp, Skip) else " |> " + str(self.out_hp)
        return "<" + str_eqs + " & " + str(self.constraint) + ">" + str_out_hp

    def __repr__(self):
        if self.out_hp == Skip():
            return "ODE(%s, %s)" % (repr(self.eqs), repr(self.constraint))
        else:
            return "ODE(%s, %s, out_hp=%s)" % (repr(self.eqs), repr(self.constraint), repr(self.out_hp))

    def __hash__(self):
        return hash(("ODE", self.eqs, self.constraint, self.out_hp))

    def get_vars(self):
        var_set = set()
        for variable, expression in self.eqs:
            var_set.add(variable)
            var_set.update(expression.get_vars())
        var_set.update(self.constraint.get_vars())
        var_set.update(self.out_hp.get_vars())
        return var_set

    def get_funs(self):
        fun_set = set()
        for _, expression in self.eqs:
            fun_set.update(expression.get_funs())
        fun_set.update(self.constraint.get_funs())
        fun_set.update(self.out_hp.get_funs())
        return fun_set

    def get_chs(self):
        return self.out_hp.get_chs()


class ODE_Comm(HPiCal):
    """Represents an ODE program that can be interrupted by
    communications, of the form

    <F(s',s) = 0 & B> |> [] (io_i --> Q_i)

    """

    def __init__(self, eqs, constraint, io_comms, meta=None):
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
            assert is_comm_channel(
                io_comm[0]) and isinstance(io_comm[1], HPiCal)

        self.type = "ode_comm"
        self.eqs = eqs  # list
        self.constraint = constraint  # BExpr
        self.io_comms = io_comms  # list
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.eqs == other.eqs and \
            self.constraint == other.constraint and self.io_comms == other.io_comms

    def __str__(self):
        str_eqs = ", ".join(var_name + "_dot = " + str(expr)
                            for var_name, expr in self.eqs)
        str_io_comms = ", ".join(str(comm_hp) + " --> " + str(out_hp)
                                 for comm_hp, out_hp in self.io_comms)
        return "<" + str_eqs + " & " + str(self.constraint) + "> |> [] (" + str_io_comms + ")"

    def __repr__(self):
        str_eqs = ", ".join(var_name + ", " + str(expr)
                            for var_name, expr in self.eqs)
        str_io_comms = ", ".join(str(comm_hp) + ", " + str(out_hp)
                                 for comm_hp, out_hp in self.io_comms)
        return "ODEComm(%s, %s, %s)" % (str_eqs, str(self.constraint), str_io_comms)

    def __hash__(self):
        return hash(("ODE_Comm", self.eqs, self.constraint, self.io_comms))

    def sc_str(self):
        derivatives = "DOT(" + ", ".join(var_name for var_name,
                                         _ in self.eqs) + ")"
        expressions = "{" + ", ".join(str(expr) for _, expr in self.eqs) + "}"
        domain = "DOMAIN(" + ("TRUE" if self.constraint ==
                              true_expr else str(self.constraint)) + ")"
        assert all(isinstance(out_hp, Var) for _, out_hp in self.io_comms)
        interupt = "INTERRUPT({" + ", ".join(comm_hp.sc_str() for comm_hp, _ in self.io_comms) + "}{" \
                   + ", ".join(out_hp.sc_str()
                               for _, out_hp in self.io_comms) + "})"
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

    def get_funs(self):
        fun_set = set()
        for _, expression in self.eqs:
            fun_set.update(expression.get_funs())
        fun_set.update(self.constraint.get_funs())
        for ch, out_hp in self.io_comms:
            fun_set.update(ch.get_funs())
            fun_set.update(out_hp.get_funs())
        return fun_set

    def get_chs(self):
        ch_set = set()
        for ch, out_hp in self.io_comms:
            ch_set.update(ch.get_chs())
            ch_set.update(out_hp.get_chs())
        return ch_set


class Loop(HPiCal):
    """Represents an infinite loop of a program.

    hp : HPiCal - body of the loop.
    constraint : BExpr - loop condition, default to true.
    inv : list of BExpr - invariants

    """

    def __init__(self, hp, *, inv=None, constraint=true_expr, meta=None):
        super(Loop, self).__init__()
        self.type = 'loop'
        assert isinstance(hp, HPiCal)
        self.hp = hp
        self.inv = inv
        self.constraint = constraint
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.hp == other.hp and \
            self.constraint == other.constraint and self.inv == other.inv

    def __repr__(self):
        if self.constraint == true_expr:
            return "Loop(%s)" % (repr(self.hp))
        else:
            return "Loop(%s, %s)" % (repr(self.hp), str(self.constraint))

    def __str__(self):
        if self.constraint == true_expr:
            return "(%s)**" % str(self.hp)
        else:
            return "(%s){%s}**" % (str(self.hp), str(self.constraint))

    def __hash__(self):
        return hash(("Loop", self.hp, self.constraint))

    def sc_str(self):
        assert isinstance(self.hp, Var)
        return self.hp.sc_str() + "**"

    def get_vars(self):
        return self.hp.get_vars()

    def get_funs(self):
        return self.hp.get_funs()

    def get_chs(self):
        return self.hp.get_chs()


class Condition(HPiCal):
    """The alternative cond -> hp behaves as hp if cond is true, otherwise,
    it terminates immediately.

    """

    def __init__(self, cond, hp, meta=None):
        super(Condition, self).__init__()
        assert isinstance(cond, BExpr) and isinstance(hp, HPiCal)
        self.type = "condition"
        self.cond = cond
        self.hp = hp
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.cond == other.cond and self.hp == other.hp

    def __repr__(self):
        return "Condition(%s, %s)" % (str(self.cond), repr(self.hp))

    def __str__(self):
        return str(self.cond) + " -> " + \
            (str(self.hp) if self.hp.priority() >
             self.priority() else "(" + str(self.hp) + ")")

    def __hash__(self):
        return hash(("Condition", self.cond, self.hp))

    def sc_str(self):
        assert isinstance(self.hp, Var)
        if_hps = ((self.cond, self.hp),)
        else_hp = Skip()
        return ITE(if_hps, else_hp).sc_str()

    def get_vars(self):
        return self.cond.get_vars().union(self.hp.get_vars())

    def get_funs(self):
        return self.cond.get_funs().union(self.hp.get_funs())

    def get_chs(self):
        return self.hp.get_chs()


class Parallel(HPiCal):
    def __init__(self, *hps, meta=None):
        """hps is a list of hybrid programs."""
        super(Parallel, self).__init__()
        self.type = "parallel"
        assert all(isinstance(hp, HPiCal) for hp in hps)
        assert len(hps) >= 2
        # self.hps = list(hps)  # type(hps) == tuple
        self.hps = []
        for hp in hps:
            if hp.type == "parallel":
                self.hps.extend(hp.hps)
            else:
                self.hps.append(hp)
        self.hps = tuple(self.hps)
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.hps == other.hps

    def __repr__(self):
        return "Parallel(%s)" % (", ".join(repr(hp) for hp in self.hps))

    def __str__(self):
        return " || ".join(
            str(hp) if hp.priority() > self.priority() else "(" + str(hp) + ")"
            for hp in self.hps)

    def __hash__(self):
        return hash(("Parallel", self.hps))

    def sc_str(self):
        return " || ".join(
            hp.sc_str() if hp.priority() > self.priority() else "(" + hp.sc_str() + ")"
            for hp in self.hps)

    def get_vars(self):
        var_set = set()
        for hp in self.hps:
            var_set.update(hp.get_vars())
        return var_set

    def get_funs(self):
        fun_set = set()
        for hp in self.hps:
            fun_set.update(hp.get_vars())
        return fun_set

    def get_chs(self):
        ch_set = set()
        for hp in self.hps:
            ch_set.update(hp.get_chs())
        return ch_set


class SelectComm(HPiCal):
    def __init__(self, *io_comms, meta=None):
        """io_comms is a list of pairs, where the first element of each
        pair must be a communication, and the second entry can be
        any program.

        """
        super(SelectComm, self).__init__()
        self.type = "select_comm"
        assert len(io_comms) >= 2

        assert all(is_comm_channel(comm_hp) and isinstance(out_hp, HPiCal)
                   for comm_hp, out_hp in io_comms)
        self.io_comms = tuple(io_comms)
        self.meta = meta

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

    def __hash__(self):
        return hash(("SelectComm", self.io_comms))

    def sc_str(self):
        return " [[ ".join("(%s; %s)" % (comm_hp.sc_str(), out_hp.sc_str()) if out_hp.priority() > self.priority()
                           else "(%s; (%s))" % (comm_hp.sc_str(), out_hp.sc_str()) for comm_hp, out_hp in self.io_comms)

    def get_vars(self):
        var_set = set()
        for ch, out_hp in self.io_comms:
            var_set.update(ch.get_vars())
            var_set.update(out_hp.get_vars())
        return var_set

    def get_funs(self):
        fun_set = set()
        for ch, out_hp in self.io_comms:
            fun_set.update(ch.get_funs())
            fun_set.update(out_hp.get_funs())
        return fun_set

    def get_chs(self):
        ch_set = set()
        for ch, out_hp in self.io_comms:
            ch_set.update(ch.get_chs())
            ch_set.update(out_hp.get_chs())
        return ch_set


class Recursion(HPiCal):
    def __init__(self, hp, entry="X", meta=None):
        super(Recursion, self).__init__()
        assert isinstance(entry, str) and isinstance(hp, HPiCal)
        self.type = "recursion"
        self.entry = entry
        self.hp = hp
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.entry == other.entry and self.hp == other.hp

    def __repr__(self):
        return "Recursion(%s, %s)" % (self.entry, repr(self.hp))

    def __str__(self):
        return "rec " + self.entry + ".(" + str(self.hp) + ")"

    def __hash__(self):
        return hash(("Recursion", self.entry, self.hp))

    def get_vars(self):
        return self.hp.get_vars()

    def get_funs(self):
        return self.hp.get_funs()

    def get_chs(self):
        return self.hp.get_chs()


class ITE(HPiCal):
    def __init__(self, if_hps, else_hp=None, meta=None):
        """if-then-else statements.

        if_hps : List[Tuple[BExpr, HPiCal]] - list of condition-program pairs.
        else_hp : [None, HPiCal]

        The program associated to the first true condition in if_hps will
        be executed. If no condition is true, else_hp is executed.

        """
        super(ITE, self).__init__()
#         assert all(isinstance(cond, BExpr) and isinstance(hp, (HPiCal,function.Assign)) for cond, hp in if_hps)
        assert all(isinstance(cond, (BExpr, LogicExpr, RelExpr)) and isinstance(
            hp, (HPiCal, function.Assign)) for cond, hp in if_hps)
        # assert all(isinstance(cond, BExpr) and isinstance(hp, HPiCal) for cond, hp in if_hps)
        assert len(if_hps) > 0, "ITE: must have at least one if branch"
        if else_hp is None:
            else_hp = Skip()
        assert isinstance(else_hp, HPiCal)
        self.type = "ite"
        self.if_hps = tuple(tuple(p) for p in if_hps)
        self.else_hp = else_hp
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.if_hps == other.if_hps and self.else_hp == other.else_hp

    def __repr__(self):
        if_hps_strs = ", ".join("%s, %s" % (cond, repr(hp))
                                for cond, hp in self.if_hps)
        return "ITE(%s, %s)" % (if_hps_strs, repr(self.else_hp))

    def __str__(self):
        res = "if %s then %s " % (self.if_hps[0][0], self.if_hps[0][1])
        for cond, hp in self.if_hps[1:]:
            res += "elif %s then %s " % (cond, hp)
        res += "else %s endif" % self.else_hp
        return res

    def __hash__(self):
        return hash(("ITE", self.if_hps, self.else_hp))

    def sc_str(self):
        assert len(self.if_hps) == 1 and isinstance(
            self.if_hps[0][1], Var) and isinstance(self.else_hp, (Skip, Var))
        return "if %s then %s else %s" % (self.if_hps[0][0], self.if_hps[0][1].sc_str(), self.else_hp.sc_str())

    def get_vars(self):
        var_set = set()
        for cond, hp in self.if_hps:
            var_set.update(cond.get_vars())
            var_set.update(hp.get_vars())
        var_set.update(self.else_hp.get_vars())
        return var_set

    def get_funs(self):
        fun_set = set()
        for cond, hp in self.if_hps:
            fun_set.update(cond.get_funs())
            fun_set.update(hp.get_funs())
        fun_set.update(self.else_hp.get_funs())
        return fun_set

    def get_chs(self):
        ch_set = set()
        for _, hp in self.if_hps:
            ch_set.update(hp.get_chs())
        ch_set.update(self.else_hp.get_chs())
        return ch_set


def ite(if_hps, else_hp):
    """Construction of if-then-else with simplifications."""
    new_if_hps, new_else_hp = [], else_hp
    for cond, if_hp in if_hps:
        if cond == true_expr:
            new_else_hp = if_hp
            break
        elif cond == false_expr:
            continue
        else:
            new_if_hps.append((cond, if_hp))
    if len(new_if_hps) == 0:
        return new_else_hp
    else:
        return ITE(new_if_hps, new_else_hp)


def get_comm_chs(hp):
    """Returns the list of communication channels for the given program.

    Result is a list of pairs (ch_name, '?'/'!').

    """
    assert isinstance(hp, HPiCal)
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


def ses_handlesub(hp, name, change_name):
    if str(name) in hp.ses_in:
        change_name = True
    if hasattr(hp, 'hp'):
        ses_handlesub(hp.hp, name, change_name)
    if hasattr(hp, 'hps'):
        for next_hp in hp.hps:
            ses_handlesub(next_hp, name, change_name)
    if hasattr(hp, 'c1'):
        ses_handlesub(hp.c1, name, change_name)
    if hasattr(hp, 'c2'):
        ses_handlesub(hp.c2, name, change_name)
    if hasattr(hp, 'c3'):
        ses_handlesub(hp.c3, name, change_name)
    if hasattr(hp, 'hp1'):
        ses_handlesub(hp.hp1, name, change_name)
    if hasattr(hp, 'hp2'):
        ses_handlesub(hp.hp2, name, change_name)
    if hasattr(hp, 'out_hp'):
        ses_handlesub(hp.out_hp, name, change_name)
    if hasattr(hp, 'if_hps'):
        for p in hp.if_hps:
            ses_handlesub(p, name, change_name)
    if hasattr(hp, 'else_hp'):
        ses_handlesub(hp.else_hp, name, change_name)

    if change_name :
        if hp.type == 'Restriction':
            hp.name = hp.name + '.1'
        if hp.type == 'Replication':
            hp.name = hp.name + '.1'
    else:
        hp.ses_in.append(str(name))
    return hp


class Session(HPiCal):
    def __init__(self, name, hp, meta=None):
        self.type = "Session"
        self.name = name
        hp = ses_handlesub(hp, name, False)
        self.hp = hp
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.name == other.name and self.hp == other.hp

    def __repr__(self):
        return "Session %s(%s)" % (self.name, repr(self.hp))

    def __str__(self):
        return "(new %s)(%s)" % (self.name, str(self.hp))

    def __hash__(self):
        return hash(("Session", self.name, self.hp))

    def sc_str(self):
        return self.name


class parallelSession(Session):

    def __init__(self, name, hps, meta=None):
        assert all(isinstance(hp, HPiCal) for hp in hps)
        assert len(hps) >= 2
        # self.hps = list(hps)  # type(hps) == tuple
        self.name = name
        self.hps = []
        for hp in hps:
            hp = ses_handlesub(hp, name, False)
            if hp.type == "parallel":
                self.hps.extend(hp.hps)
            else:
                self.hps.append(hp)
        self.hps = tuple(self.hps)
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.name == other.name and self.hps == other.hps

    def __repr__(self):
        return "Session %s(%s)" % (self.name, ", ".join(repr(hp) for hp in self.hps))

    def __str__(self):
        return "(new %s)(%s)" % (self.name,
                                 " || ".join(
                                     str(hp) if hp.priority() > self.priority(
                                     ) else "(" + str(hp) + ")"
                                     for hp in self.hps)
                                 )

    def __hash__(self):
        return hash(("Session", self.name, self.hps))

    def sc_str(self):
        return self.name


class Procedure:
    """Declared procedure within a process."""

    def __init__(self, name, hp, meta=None):
        self.name = name
        if isinstance(hp, str):
            from ss2hcsp.hcsp.parser import hp_parser
            hp = hp_parser.parse(hp)
        self.hp = hp
        self.meta = meta

    def __eq__(self, other):
        return self.name == other.name and self.hp == other.hp

    def __repr__(self):
        return "Procedure(%s,%s)" % (self.name, repr(self.hp))

    def __str__(self):
        return "procedure %s begin %s end" % (self.name, str(self.hp))


class HPiCalInfo:
    """HPiCal process with extra information."""

    def __init__(self, name, hp, *, outputs=None, procedures=None):
        self.name = name
        self.hp = hp

        # List of output variables, None indicates output everything
        self.outputs = outputs

        # List of declared procedures
        if procedures is None:
            procedures = []
        self.procedures = procedures

    def __str__(self):
        res = self.name + ' ::=\n'
        for procedure in self.procedures:
            res += str(procedure) + '\n'
        res += str(self.hp)
        return res

    def __repr__(self):
        return "HPiCalInfo(%s, %s)" % (self.name, str(self.hp))

    def __eq__(self, other):
        return self.name == other.name and self.hp == other.hp


def subst_comm_all(hp, inst):
    """Perform all substitutions given in inst. Detect cycles.

    First compute a topological sort of dependency in inst, which will
    provide the order of substitution.

    """
    # Set of all variables to be substituted
    all_vars = set(inst.keys())

    # Mapping variable to its dependencies
    dep_order = dict()
    for var in all_vars:
        dep_order[var] = list(inst[var].get_vars().intersection(all_vars))

    topo_order = topological_sort(dep_order)
    for var in reversed(topo_order):
        hp = hp.subst_comm({var: inst[var]})
    return hp


def HPiCal_subst(hp, inst):
    """Substitution of program variables for their instantiations."""
    assert isinstance(hp, HPiCal)
    if isinstance(hp, Var):
        if hp.name in inst:
            return inst[hp.name]
        else:
            return hp
    elif isinstance(hp, (Skip, Wait, Assign, Assert, Test, Log, InputChannel, OutputChannel)):
        return hp
    elif isinstance(hp, (Loop, Recursion, Condition)):
        hp.hp = HPiCal_subst(hp.hp, inst)
        return hp
    elif isinstance(hp, Sequence):
        hps = [HPiCal_subst(sub_hp, inst) for sub_hp in hp.hps]
        return Sequence(*hps)
    elif isinstance(hp, ODE):
        hp.out_hp = HPiCal_subst(hp.out_hp, inst)
        return hp
    elif isinstance(hp, (ODE_Comm, SelectComm)):
        hp.io_comms = tuple((io_comm[0], HPiCal_subst(
            io_comm[1], inst)) for io_comm in hp.io_comms)
        return hp
    elif isinstance(hp, ITE):
        hp.if_hps = tuple((e[0], HPiCal_subst(e[1], inst)) for e in hp.if_hps)
        hp.else_hp = HPiCal_subst(hp.else_hp, inst)
        return hp
    else:
        print(hp)
        raise NotImplementedError


def reduce_procedures(hp, procs, strict_protect=None):
    """Reduce number of procedures in the process by inlining.

    hp : HPiCal - input process.
    procs : Dict[str, HPiCal] - mapping from procedure name to procedure body.
    strict_protect : Set[str] - this set of procedures will never be inlined.

    The algorithm for finding which procedures to inline is partly heuristic,
    with settings specified by the various flags. It performs the following steps:

    1. Traverse the procedure definitions to find dependency relations.

    2. Inline any procedure that does not depend on any other procedure (except
       those that are strictly protected).

    3. When step 2 can not find any procedure to inline, remove one of the
       procedures from consideration.

    This function directly modifies procs, and returns the new HPiCal process.

    """
    if strict_protect is None:
        strict_protect = set()

    # First, construct the dependency relation. We use the empty string
    # to represent the toplevel process.
    dep_relation = dict()
    dep_relation[""] = hp.get_contain_hps()
    for name, proc in procs.items():
        dep_relation[name] = proc.get_contain_hps()

    # Construct reverse dependency relation, for heuristic selection of
    # inlined functions
    rev_dep_relation = dict()
    rev_dep_relation[""] = 0
    for name in procs:
        rev_dep_relation[name] = 0
    for name, contains in dep_relation.items():
        for contain in contains:
            rev_dep_relation[contain] += 1

    # Set of procedures to be inlined, in order of removal
    inline_order = []

    # Set of procedures that are kept, initially the toplevel process
    # and the strictly protected processes.
    fixed = {""}.union(strict_protect)

    # Also protect procedures that are too large and invoked too many times
    for name, proc in procs.items():
        if rev_dep_relation[name] >= 2 and proc.size() > 2:
            fixed.add(name)

    # Get the order of inlining
    while True:
        # First, find procedures that only depend on inlined or fixed procedures
        found = False
        for name, dep in dep_relation.items():
            if name not in fixed and name not in inline_order and \
                    dep.issubset(set(inline_order).union(fixed)):
                found = True
                inline_order.append(name)

        # If all procedures are either inlined or fixed, exit the loop
        if len(fixed) + len(inline_order) == len(dep_relation):
            break

        # If some procedure is found, repeat the iteration
        if found:
            continue

        # No procedure is found, move one procedure to fixed
        for name in dep_relation:
            if name not in fixed and name not in inline_order:
                fixed.add(name)
                break

    # Next, recursively perform substitutions
    for inline_name in inline_order:
        for name, dep in dep_relation.items():
            if name == "" and inline_name in dep:
                hp = HPiCal_subst(hp, {inline_name: procs[inline_name]})
            elif inline_name in dep:
                procs[name] = HPiCal_subst(
                    procs[name], {inline_name: procs[inline_name]})
        del procs[inline_name]

    return hp


class HPiCalProcess:
    """System of HPiCal processes. Input is a list of (name, HPiCal) pairs."""

    def __init__(self, hps=None):
        """Initialize with an optional list of definitions."""

        # List of (name, HPiCal) pairs.
        self.hps = []
        if hps:
            for name, hp in hps:
                self.hps.append((name, hp))

    def add(self, name, hp):
        """Insert (name, hp) at the end."""
        self.hps.append((name, hp))

    def extend(self, lst):
        """Insert list of (name, hp) at the end."""
        if isinstance(lst, HPiCalProcess):
            self.hps.extend(lst.hps)
        else:
            self.hps.extend(lst)

    def insert(self, n, name, hp):
        """Insert (name, hp) at position n."""
        self.hps.insert(n, (name, hp))

    def substitute(self):
        """Substitute program variables for their definitions."""
        def _substitute(_hp):
            assert isinstance(_hp, (HPiCal, function.Assign))
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
                _hp.io_comms = tuple((io_comm[0], _substitute(
                    io_comm[1])) for io_comm in _hp.io_comms)
            elif isinstance(_hp, ITE):
                _hp.if_hps = tuple((e[0], _substitute(e[1]))
                                   for e in _hp.if_hps)
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
        ch_def = "channelDef ::= " + \
            ("; ".join([ch.name for ch in self.get_chs()])) + "\n\n"
        hp_def = "\n".join("processDef " + "%s ::= %s" % (name, hp.sc_str()) for name, hp in self.hps
                           if not isinstance(hp, Parallel))
        return sys_def + var_def + ch_def + hp_def

    def get_vars(self):
        var_set = set()
        for _, hp in self.hps:
            var_set.update(hp.get_vars())
        return var_set

    def get_funs(self):
        fun_set = set()
        for _, hp in self.hps:
            fun_set.update(hp.get_funs())
        return fun_set

    def get_chs(self):
        ch_set = set()
        for _, hp in self.hps:
            ch_set.update(hp.get_chs())
        return ch_set
