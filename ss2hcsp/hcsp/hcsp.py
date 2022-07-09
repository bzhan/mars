"""Hybrid programs"""

from collections import OrderedDict
from typing import Union
from ss2hcsp.hcsp.expr import AExpr, AVar, AConst, BExpr, true_expr, false_expr, RelExpr, LogicExpr, AExpr
from ss2hcsp.hcsp.invariant import Invariant, LoopInvariant
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
        assert isinstance(args, tuple) and all(isinstance(arg, (AExpr, int, str)) for arg in args)

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

class Function:
    """Declarations of (pure functions).
    
    Each pure functions is defined by a list of variables and an expression.
    When the function is called, the variables in the expression are
    substituted for the arguments to the function.
    
    """
    def __init__(self, name: str, vars, expr: Union[AExpr, str]):
        assert isinstance(vars, list) and all(isinstance(var, str) for var in vars)
        if isinstance(expr, str):
            from ss2hcsp.hcsp.parser import aexpr_parser
            expr = aexpr_parser.parse(expr)
        assert set(vars) == expr.get_vars()
        self.name = name
        self.vars = vars
        self.expr = expr

    def __str__(self):
        return "%s(%s) = %s" % (self.name, ",".join(var for var in self.vars), self.expr)

    def __repr__(self):
        return "Function(%s, %s, %s)" % (self.name, repr(self.vars), repr(self.expr))


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

    def get_fun_names(self):
        return set()

    def get_zero_arity_funcs(self):
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
        else:
            return 100

    def size(self):
        """Returns size of HCSP program."""
        if isinstance(self, (Var, Skip, Wait, Assign, Assert, Test, Log,
                             InputChannel, OutputChannel)):
            return 1
        elif isinstance(self, (Sequence, Parallel)):
            return 1 + sum([hp.size() for hp in self.hps])
        elif isinstance(self, Loop):
            return 1 + self.hp.size()
        elif isinstance(self, ODE):
            return 1
        elif isinstance(self, (ODE_Comm, SelectComm)):
            return 1 + sum([1 + out_hp.size() for comm_hp, out_hp in self.io_comms])
        elif isinstance(self, ITE):
            return 1 + sum([1 + hp.size() for cond, hp in self.if_hps]) + \
              (self.else_hp.size() if self.else_hp else 0)
        else:
            raise NotImplementedError

    def contain_hp(self, name):
        """Returns whether the given HCSP program contains Var(name)."""
        if isinstance(self, Var):
            return self.name == name
        elif isinstance(self, (Skip, Wait, Assign, Assert, Test, Log, InputChannel, OutputChannel)):
            return False
        elif isinstance(self, (Sequence, Parallel)):
            for sub_hp in self.hps:
                if sub_hp.contain_hp(name):
                    return True
        elif isinstance(self, Loop):
            return self.hp.contain_hp(name)
        elif isinstance(self, ODE):
            return self.out_hp.contain_hp(name)
        elif isinstance(self, (ODE_Comm, SelectComm)):
            for io_comm in self.io_comms:
                if io_comm[1].contain_hp(name):
                    return True
        elif isinstance(self, ITE):
            if self.else_hp.else_hp is not None and self.else_hp.contain_hp(name):
                return True
            for sub_hp in [hp for cond, hp in self.if_hps]:
                if sub_hp.contain_hp(name):
                    return True
        else:
            raise NotImplementedError

    def get_contain_hps_count(self):
        """Returns the dictionary mapping contained hps to number
        of appearances.
        
        """
        res = dict()

        def rec(hp):
            if isinstance(hp, Var):
                if hp.name not in res:
                    res[hp.name] = 0
                res[hp.name] += 1
            elif isinstance(hp, (Skip, Wait, Assign, Assert, Test, Log, InputChannel, OutputChannel)):
                pass
            elif isinstance(hp, (Sequence, Parallel)):
                for sub_hp in hp.hps:
                    rec(sub_hp)
            elif isinstance(hp, Loop):
                rec(hp.hp)
            elif isinstance(hp, ODE):
                rec(hp.out_hp)
            elif isinstance(hp, (ODE_Comm, SelectComm)):
                for _, out_hp in hp.io_comms:
                    rec(out_hp)
            elif isinstance(hp, ITE):
                for _, sub_hp in hp.if_hps:
                    rec(sub_hp)
                if hp.else_hp is not None:
                    rec(hp.else_hp)
            else:
                raise NotImplementedError
        rec(self)
        return res

    def get_contain_hps(self):
        """Returns the set of Var calls contained in self."""
        return set(self.get_contain_hps_count())

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
        elif self.type == 'select_comm':
            return SelectComm(*(subst_io_comm(io_comm) for io_comm in self.io_comms))
        elif self.type == 'ite':
            return ITE([subst_if_hp(if_hp) for if_hp in self.if_hps], 
              self.else_hp.subst_comm(inst) if self.else_hp is not None else None)
        else:
            print(self.type)
            raise NotImplementedError


class Var(HCSP):
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
        return "@" + self.name + ";"

    def __hash__(self):
        return hash(("VAR", self.name))

    def sc_str(self):
        return self.name


class Skip(HCSP):
    def __init__(self, meta=None):
        super(Skip, self).__init__()
        self.type = "skip"
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type

    def __repr__(self):
        return "Skip()"

    def __str__(self):
        return "skip;"

    def __hash__(self):
        return hash("Skip")


class Wait(HCSP):
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
        return "wait(%s);" % str(self.delay)

    def __hash__(self):
        return hash(("Wait", self.delay))


class Assign(HCSP):
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
        elif isinstance(var_name,function.DirectName):
            self.var_name=var_name
        else:
            var_name = tuple(var_name)
            assert len(var_name) >= 2 and all(isinstance(name, (str, AExpr)) for name in var_name)
            self.var_name = [AVar(n) if isinstance(n, str) else n for n in var_name]
        self.expr = expr
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.var_name == other.var_name and self.expr == other.expr

    def __repr__(self):
        if isinstance(self.var_name, AExpr):
            var_str = str(self.var_name)
        else:
            var_str = "[%s]" % (','.join(str(n) for n in self.var_name))
        return  "Assign(%s,%s)" % (var_str, str(self.expr))

    def __str__(self):
        if isinstance(self.var_name, AExpr):
            var_str = str(self.var_name)
        elif isinstance(self.var_name,function.DirectName):
            var_str=str(self.var_name)
        else:
            var_str = "(%s)" % (', '.join(str(n) for n in self.var_name))
        return "%s := %s;" % (var_str, self.expr)

    def __hash__(self):
        return hash(("Assign", self.var_name, self.expr))

    def get_vars(self):
        if isinstance(self.var_name, AExpr):
            var_set = {str(self.var_name)}
        else:
            var_set = set(str(n) for n in self.var_name)
        return var_set.union(self.expr.get_vars())

    def get_fun_names(self):
        return set().union(self.expr.get_fun_names())

    def get_zero_arity_funcs(self):
        return set().union(self.expr.get_zero_arity_funcs())

    def sc_str(self):
        return re.sub(pattern=":=", repl="=", string=str(self))

    def priority(self):
        return 100

class RandomAssign(HCSP):
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
            assert len(var_name) <= 2 and all (isinstance(name, (str, AExpr))for name in var_name)
            self.var_name = [AVar(n) if isinstance(n, str) else n for n in var_name]
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
        elif isinstance(self.var_name,function.DirectName):
            var_str=str(self.var_name)
        else:
            var_str = "(%s)" % (', '.join(str(n) for n in self.var_name))
        return var_str + " := " + "*(" + str(self.expr) + ");"

    def __hash__(self):
        return hash(("RandomAssign", self.var_name, self.expr))

    def get_vars(self):
        if isinstance(self.var_name, AExpr):
            var_set = {str(self.var_name)}
        else:
            var_set = set(str(n) for n in self.var_name)
        return var_set.union(self.expr.get_vars())

    def get_fun_names(self):
        return set.union(self.expr.get_fun_names())

    def get_zero_arity_funcs(self):
        return set.union(self.expr.get_zero_arity_funcs())

    def priority(self):
        return 100

class Assert(HCSP):
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
            return "assert(%s,%s);" % (self.bexpr, ','.join(str(msg) for msg in self.msgs))
        else:
            return "assert(%s);" % self.bexpr

    def __hash__(self):
        return hash(("Assert", self.bexpr, self.msgs))

    def get_vars(self):
        var_set = self.bexpr.get_vars()
        for msg in self.msgs:
            var_set.update(msg.get_vars())
        return var_set

    def get_fun_names(self):
        fun_set = self.bexpr.get_fun_names()
        for msg in self.msgs:
            fun_set.update(msg.get_fun_names())
        return fun_set

    def get_zero_arity_funcs(self):
        fun_set = self.bexpr.get_zero_arity_funcs()
        for msg in self.msgs:
            fun_set.update(msg.get_zero_arity_funcs())
        return fun_set


class Test(HCSP):
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
            return "test(%s,%s);" % (self.bexpr, ','.join(str(msg) for msg in self.msgs))
        else:
            return "test(%s);" % self.bexpr

    def __hash__(self):
        return hash(("Test", self.bexpr, self.msgs))

    def get_vars(self):
        var_set = self.bexpr.get_vars()
        for msg in self.msgs:
            var_set.update(msg.get_vars())
        return var_set

    def get_fun_names(self):
        fun_set = self.bexpr.get_fun_names()
        for msg in self.msgs:
            fun_set.update(msg.get_fun_names())
        return fun_set

    def get_zero_arity_funcs(self):
        fun_set = self.bexpr.get_zero_arity_funcs()
        for msg in self.msgs:
            fun_set.update(msg.get_zero_arity_funcs())
        return fun_set


class Log(HCSP):
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
            return "log(%s,%s);" % (self.pattern, ','.join(str(expr) for expr in self.exprs))
        else:
            return "log(%s);" % self.pattern

    def __hash__(self):
        return hash(("Log", self.pattern, self.exprs))

    def get_vars(self):
        var_set = self.pattern.get_vars()
        for expr in self.exprs:
            var_set.update(expr.get_vars())
        return var_set

    def get_fun_names(self):
        fun_set = self.pattern.get_fun_names()
        for expr in self.exprs:
            fun_set.update(expr.get_fun_names())
        return fun_set

    def get_zero_arity_funcs(self):
        fun_set = self.pattern.get_zero_arity_funcs()
        for expr in self.exprs:
            fun_set.update(expr.get_zero_arity_funcs())
        return fun_set
    
class InputChannel(HCSP):
    def __init__(self, ch_name, var_name=None, meta=None):
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
        self.meta = meta

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
            return str(self.ch_name) + "?" + str(self.var_name) + ";"
        else:
            return str(self.ch_name) + "?" + ";"

    def __hash__(self):
        return hash(("InputChannel", self.ch_name, self.var_name))

    def get_vars(self):
        if self.var_name:
            return {str(self.var_name)}
        return set()

    def get_fun_names(self):
        return set()

    def get_zero_arity_funcs(self):
        return set()

    def get_chs(self):
        return {self.ch_name}

    def sc_str(self):
        return re.sub(pattern="\\?", repl="??", string=str(self))


class ParaInputChannel(InputChannel):
    def __init__(self, ch_name, paras, var_name=None, is_str=False):
        super(ParaInputChannel, self).__init__(ch_name, var_name)
        assert all(isinstance(para, (int, float, str)) for para in paras)
        self.paras = paras
        self.is_str = is_str

    def __str__(self):
        result = str(self.ch_name)
        for para in self.paras:
            if isinstance(para, str) and self.is_str:
                result += "[\"" + str(para) + "\"]"
            else:
                result += "[" + str(para) + "]"
        result += "?"
        if self.var_name:
            result += str(self.var_name)
        result += ";"
        return result


class OutputChannel(HCSP):
    def __init__(self, ch_name, expr=None, meta=None):
        super(OutputChannel, self).__init__()
        self.type = "output_channel"
        if isinstance(ch_name, str):
            ch_name = Channel(ch_name)
        assert isinstance(ch_name, Channel)
        assert expr is None or isinstance(expr, AExpr)
        self.ch_name = ch_name  # Channel
        self.expr = expr  # AExpr or None
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.expr == other.expr and self.ch_name == other.ch_name

    def __repr__(self):
        if isinstance(self.expr, AExpr):
            return "OutputC(%s,%s)" % (self.ch_name, self.expr)
        else:
            return "OutputC(%s)" % self.ch_name

    def __str__(self):
        if self.expr:
            return str(self.ch_name) + "!" + str(self.expr) + ";"
        else:
            return str(self.ch_name) + "!" + ";"

    def __hash__(self):
        return hash(("OutputChannel", self.ch_name, self.expr))

    def get_vars(self):
        if self.expr:
            return self.expr.get_vars()
        return set()

    def get_fun_names(self):
        if self.expr:
            return self.expr.get_fun_names()
        return set()

    def get_zero_arity_funcs(self):
        if self.expr:
            return self.expr.get_zero_arity_funcs()
        return set()

    def get_chs(self):
        return {self.ch_name}

    def sc_str(self):
        return re.sub(pattern="!", repl="!!", string=str(self))


class ParaOutputChannel(OutputChannel):
    def __init__(self, ch_name, paras, expr=None, is_str=False):
        super(ParaOutputChannel, self).__init__(ch_name, expr)
        assert all(isinstance(para, (int, float, str)) for para in paras)
        self.paras = paras
        self.is_str = is_str

    def __str__(self):
        result = str(self.ch_name)
        for para in self.paras:
            if isinstance(para, str) and self.is_str:
                result += "[\"" + str(para) + "\"]"
            else:
                result += "[" + str(para) + "]"
        if self.expr:
            result += str(self.expr)
        result += ";"
        return result


def is_comm_channel(hp):
    return hp.type == "input_channel" or hp.type == "output_channel"


class Sequence(HCSP):
    def __init__(self, *hps, meta=None):
        """hps is a list of hybrid programs."""
        super(Sequence, self).__init__()
        self.type = "sequence"
        assert all(isinstance(hp, HCSP) for hp in hps)
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
        return " ".join(
            str(hp) if hp.priority() > self.priority() else "{" + str(hp) + "}"
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

    def get_fun_names(self):
        fun_set = set()
        for hp in self.hps:
            fun_set.update(hp.get_fun_names())
        return fun_set

    def get_zero_arity_funcs(self):
        fun_set = set()
        for hp in self.hps:
            fun_set.update(hp.get_zero_arity_funcs())
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
    assert all(isinstance(hp, HCSP) for hp in hps)
    hps = [hp for hp in hps if hp != Skip()]
    if len(hps) == 0:
        return Skip()
    elif len(hps) == 1:
        return hps[0]
    else:
        return Sequence(*hps)


class IChoice(HCSP):
    """Represents internal choice of the form P ++ Q ++ N."""
    def __init__(self, *hps, meta=None):
        super(IChoice, self).__init__()
        self.type = "ichoice"
        assert all(isinstance(hp, HCSP) for hp in hps)
        assert len(hps) >= 1
        self.hps = tuple(hps)
        # assert isinstance(hp1, HCSP) and isinstance(hp2, HCSP)
        # self.hp1 = hp1
        # self.hp2 = hp2
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.hps == other.hps

    def __str__(self):
        return " ++ ".join(str(hp) if hp.priority() > self.priority() else "(" + str(hp) + ")"
                for hp in self.hps)

    def __repr__(self):
        return "IChoice(%s)" % ", ".join(repr(hp) for hp in self.hps)

    def __hash__(self):
        return hash(("ICHOICE", self.hps))

    def get_vars(self):
        var_set = set()
        for hp in self.hps:
            var_set.update(hp.get_vars())
        return var_set

    def get_fun_names(self):
        fun_set = set()
        for hp in self.hps:
            fun_set.update(hp.get_fun_names())
        return fun_set

    def get_zero_arity_funcs(self):
        fun_set = set()
        for hp in self.hps:
            fun_set.update(hp.get_zero_arity_funcs())
        return fun_set

class ODE(HCSP):
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
        assert inv is None or isinstance(inv, tuple)
        if isinstance(inv, tuple):
            for sub_inv in inv:
                assert isinstance(sub_inv, Invariant)
        assert not out_hp or isinstance(out_hp, HCSP)

        self.type = "ode"
        self.eqs = eqs  # list of tuples (string, AExpr)
        self.constraint = constraint  # BExpr
        self.out_hp = out_hp  # None or hcsp
        self.meta = meta
        self.inv = inv

    def __eq__(self, other):
        return self.type == other.type and self.eqs == other.eqs and \
               self.constraint == other.constraint and self.out_hp == other.out_hp

    def __str__(self):
        str_eqs = ", ".join(var_name + "_dot = " + str(expr) for var_name, expr in self.eqs)
        str_out_hp = "" if isinstance(self.out_hp, Skip) else " |> " + str(self.out_hp)
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

    def get_fun_names(self):
        fun_set = set()
        for _, expression in self.eqs:
            fun_set.update(expression.get_fun_names())
        fun_set.update(self.constraint.get_fun_names())
        fun_set.update(self.out_hp.get_fun_names())
        return fun_set

    def get_zero_arity_funcs(self):
        fun_set = set()
        for _, expression in self.eqs:
            fun_set.update(expression.get_zero_arity_funcs())
        fun_set.update(self.constraint.get_zero_arity_funcs())
        fun_set.update(self.out_hp.get_zero_arity_funcs())
        return fun_set

    def get_chs(self):
        return self.out_hp.get_chs()


class ODE_Comm(HCSP):
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
            assert is_comm_channel(io_comm[0]) and isinstance(io_comm[1], HCSP)

        self.type = "ode_comm"
        self.eqs = eqs  # list
        self.constraint = constraint  # BExpr
        self.io_comms = io_comms  # list
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.eqs == other.eqs and \
               self.constraint == other.constraint and self.io_comms == other.io_comms

    def __str__(self):
        str_eqs = ", ".join(var_name + "_dot = " + str(expr) for var_name, expr in self.eqs)
        str_io_comms = ", ".join(str(comm_hp)[:-1] + " --> " + str(out_hp) for comm_hp, out_hp in self.io_comms)
        return "<" + str_eqs + " & " + str(self.constraint) + "> |> [] (" + str_io_comms + ")"

    def __repr__(self):
        str_eqs = ", ".join(var_name + ", " + str(expr) for var_name, expr in self.eqs)
        str_io_comms = ", ".join(str(comm_hp)[:-1] + ", " + str(out_hp) for comm_hp, out_hp in self.io_comms)
        return "ODEComm(%s, %s, %s)" % (str_eqs, str(self.constraint), str_io_comms)

    def __hash__(self):
        return hash(("ODE_Comm", self.eqs, self.constraint, self.io_comms))

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

    def get_fun_names(self):
        fun_set = set()
        for _, expression in self.eqs:
            fun_set.update(expression.get_fun_names())
        fun_set.update(self.constraint.get_fun_names())
        for ch, out_hp in self.io_comms:
            fun_set.update(ch.get_fun_names())
            fun_set.update(out_hp.get_fun_names())
        return fun_set

    def get_zero_arity_funcs(self):
        fun_set = set()
        for _, expression in self.eqs:
            fun_set.update(expression.get_zero_arity_funcs())
        fun_set.update(self.constraint.get_zero_arity_funcs())
        for ch, out_hp in self.io_comms:
            fun_set.update(ch.get_zero_arity_funcs())
            fun_set.update(out_hp.get_zero_arity_funcs())
        return fun_set

    def get_chs(self):
        ch_set = set()
        for ch, out_hp in self.io_comms:
            ch_set.update(ch.get_chs())
            ch_set.update(out_hp.get_chs())
        return ch_set


class Loop(HCSP):
    """Represents an infinite loop of a program.
    
    hp : HCSP - body of the loop.
    constraint : BExpr - loop condition, default to true.
    inv : tuple of LoopInvariants - invariants

    """
    def __init__(self, hp, *, inv=None, constraint=true_expr, meta=None):
        super(Loop, self).__init__()
        self.type = 'loop'
        assert isinstance(hp, HCSP)
        if inv is not None:
            assert isinstance(inv, tuple)
            for sub_inv in inv:
                assert isinstance(sub_inv, LoopInvariant)
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
            return "{%s}*" % str(self.hp)
        else:
            return "{%s}*(%s)" % (str(self.hp), str(self.constraint))

    def __hash__(self):
        return hash(("Loop", self.hp, self.constraint))

    def sc_str(self):
        assert isinstance(self.hp, Var)
        return self.hp.sc_str() + "**"

    def get_vars(self):
        return self.hp.get_vars()

    def get_fun_names(self):
        return self.hp.get_fun_names()

    def get_zero_arity_funcs(self):
        return self.hp.get_zero_arity_funcs()

    def get_chs(self):
        return self.hp.get_chs()

class Parallel(HCSP):
    def __init__(self, *hps, meta=None):
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
        self.hps = tuple(self.hps)
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.hps == other.hps

    def __repr__(self):
        return "Parallel(%s)" % (", ".join(repr(hp) for hp in self.hps))

    def __str__(self):
        return " || ".join(
            str(hp) if hp.priority() > self.priority() else "{" + str(hp) + "}"
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

    def get_fun_names(self):
        fun_set = set()
        for hp in self.hps:
            fun_set.update(hp.get_fun_names())
        return fun_set

    def get_zero_arity_funcs(self):
        fun_set = set()
        for hp in self.hps:
            fun_set.update(hp.get_zero_arity_funcs())
        return fun_set


    def get_chs(self):
        ch_set = set()
        for hp in self.hps:
            ch_set.update(hp.get_chs())
        return ch_set


class SelectComm(HCSP):
    def __init__(self, *io_comms, meta=None):
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
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.io_comms == other.io_comms

    def __repr__(self):
        return "SelectComm(%s)" % (",".join("%s,%s" % (repr(comm_hp), repr(out_hp))
                                            for comm_hp, out_hp in self.io_comms))

    def __str__(self):
        return " $ ".join(
            "%s --> %s" % (str(comm_hp)[:-1], out_hp) if out_hp.priority() > self.priority() else
            "%s --> {%s}" % (str(comm_hp)[:-1], out_hp)
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

    def get_fun_names(self):
        fun_set = set()
        for ch, out_hp in self.io_comms:
            fun_set.update(ch.get_fun_names())
            fun_set.update(out_hp.get_fun_names())
        return fun_set

    def get_zero_arity_funcs(self):
        fun_set = set()
        for ch, out_hp in self.io_comms:
            fun_set.update(ch.get_zero_arity_funcs())
            fun_set.update(out_hp.get_zero_arity_funcs())
        return fun_set

    def get_chs(self):
        ch_set = set()
        for ch, out_hp in self.io_comms:
            ch_set.update(ch.get_chs())
            ch_set.update(out_hp.get_chs())
        return ch_set


class ITE(HCSP):
    def __init__(self, if_hps, else_hp=None, meta=None):
        """if-then-else statements.

        if_hps : List[Tuple[BExpr, HCSP]] - list of condition-program pairs.
        else_hp : [None, HCSP]

        The program associated to the first true condition in if_hps will
        be executed. If no condition is true, else_hp is executed.

        """
        super(ITE, self).__init__()
#         assert all(isinstance(cond, BExpr) and isinstance(hp, (HCSP,function.Assign)) for cond, hp in if_hps)   
        assert all(isinstance(cond, (BExpr,LogicExpr,RelExpr)) and isinstance(hp, (HCSP,function.Assign)) for cond, hp in if_hps)
        # assert all(isinstance(cond, BExpr) and isinstance(hp, HCSP) for cond, hp in if_hps)
        assert len(if_hps) > 0, "ITE: must have at least one if branch"
        assert else_hp is None or isinstance(else_hp, HCSP)
        self.type = "ite"
        self.if_hps = tuple(tuple(p) for p in if_hps)
        self.else_hp = else_hp
        self.meta = meta

    def __eq__(self, other):
        return self.type == other.type and self.if_hps == other.if_hps and self.else_hp == other.else_hp

    def __repr__(self):
        if_hps_strs = ", ".join("%s, %s" % (cond, repr(hp)) for cond, hp in self.if_hps)
        return "ITE(%s, %s)" % (if_hps_strs, repr(self.else_hp))

    def __str__(self):
        res = "if (%s) { %s " % (self.if_hps[0][0], self.if_hps[0][1])
        for cond, hp in self.if_hps[1:]:
            res += "} else if (%s) { %s " % (cond, hp)
        if self.else_hp is None:
            res += "}"
        else:
            res += "} else { %s }" % self.else_hp
        return res

    def __hash__(self):
        return hash(("ITE", self.if_hps, self.else_hp))

    def sc_str(self):
        assert len(self.if_hps) == 1 and isinstance(self.if_hps[0][1], Var) and (self.else_hp is None or isinstance(self.else_hp, Var))
        if self.else_hp is None:
            return "if %s then %s" % (self.if_hps[0][0], self.if_hps[0][1].sc_str())
        else:
            return "if %s then %s else %s" % (self.if_hps[0][0], self.if_hps[0][1].sc_str(), self.else_hp.sc_str())

    def get_vars(self):
        var_set = set()
        for cond, hp in self.if_hps:
            var_set.update(cond.get_vars())
            var_set.update(hp.get_vars())
        if self.else_hp is not None:
            var_set.update(self.else_hp.get_vars())
        return var_set

    def get_fun_names(self):
        fun_set = set()
        for cond, hp in self.if_hps:
            fun_set.update(cond.get_fun_names())
            fun_set.update(hp.get_fun_names())
        if self.else_hp is not None:
            fun_set.update(self.else_hp.get_fun_names())
        return fun_set

    def get_zero_arity_funcs(self):
        fun_set = set()
        for cond, hp in self.if_hps:
            fun_set.update(cond.get_zero_arity_funcs())
            fun_set.update(hp.get_zero_arity_funcs())
        if self.else_hp is not None:
            fun_set.update(self.else_hp.get_zero_arity_funcs())
        return fun_set

    def get_chs(self):
        ch_set = set()
        for _, hp in self.if_hps:
            ch_set.update(hp.get_chs())
        if self.else_hp is not None:
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
        if new_else_hp is None:
            return Skip()
        return new_else_hp
    else:
        return ITE(new_if_hps, new_else_hp)

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
        elif _hp.type == 'loop':
            rec(_hp.hp)
        elif _hp.type == 'ite':
            for _, sub_hp in _hp.if_hps:
                rec(sub_hp)
            if _hp.else_hp is not None:
                rec(_hp.else_hp)
    
    rec(hp)
    return list(OrderedDict.fromkeys(collect))

class HoareTriple:
    """A program with pre- and post-conditions"""
    def __init__(self, pre, hp, post, meta=None):
        self.pre = list(pre)
        self.post = list(post)
        self.hp = hp
        self.meta = meta

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


class HCSPInfo:
    """HCSP process with extra information."""
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
        return "HCSPInfo(%s, %s)" % (self.name, str(self.hp))

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

def HCSP_subst(hp, inst):
    """Substitution of program variables for their instantiations."""
    assert isinstance(hp, HCSP)
    if isinstance(hp, Var):
        if hp.name in inst:
            return inst[hp.name]
        else:
            return hp
    elif isinstance(hp, (Skip, Wait, Assign, Assert, Test, Log, InputChannel, OutputChannel)):
        return hp
    elif isinstance(hp, Loop):
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
        if hp.else_hp is not None:
            hp.else_hp = HCSP_subst(hp.else_hp, inst)
        return hp
    else:
        print(hp)
        raise NotImplementedError

def reduce_procedures(hp, procs, strict_protect=None):
    """Reduce number of procedures in the process by inlining.

    hp : HCSP - input process.
    procs : Dict[str, HCSP] - mapping from procedure name to procedure body.
    strict_protect : Set[str] - this set of procedures will never be inlined.

    The algorithm for finding which procedures to inline is partly heuristic,
    with settings specified by the various flags. It performs the following steps:

    1. Traverse the procedure definitions to find dependency relations.

    2. Inline any procedure that does not depend on any other procedure (except
       those that are strictly protected).

    3. When step 2 can not find any procedure to inline, remove one of the
       procedures from consideration.

    This function directly modifies procs, and returns the new HCSP process.

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
    # inlined functions. For each hp
    rev_dep_count = dict()
    for name in procs:
        rev_dep_count[name] = 0
    for name, count in hp.get_contain_hps_count().items():
        rev_dep_count[name] += count
    for _, proc in procs.items():
        for name, count in proc.get_contain_hps_count().items():
            rev_dep_count[name] += count

    # Set of procedures to be inlined, in order of removal
    inline_order = []

    # Set of procedures that are kept, initially the toplevel process
    # and the strictly protected processes.
    fixed = {""}.union(strict_protect)

    # Also protect procedures that are too large and invoked too many times
    for name, proc in procs.items():
        if rev_dep_count[name] >= 2 and proc.size() > 8:
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
                hp = HCSP_subst(hp, {inline_name: procs[inline_name]})
            elif inline_name in dep:
                procs[name] = HCSP_subst(procs[name], {inline_name: procs[inline_name]})
        del procs[inline_name]

    return hp


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
            assert isinstance(_hp, (HCSP,function.Assign))
            if isinstance(_hp, Var):
                _name = _hp.name
                if _name in substituted.keys():
                    _hp = substituted[_name]
                elif _name in hps_dict:
                    _hp = _substitute(hps_dict[_name])
                    substituted[_name] = _hp
                    del hps_dict[_name]
            elif isinstance(_hp, Loop):
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
                if _hp.else_hp is not None:
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

    def get_fun_names(self):
        fun_set = set()
        for _, hp in self.hps:
            fun_set.update(hp.get_fun_names())
        return fun_set

    def get_zero_arity_funcs(self):
        fun_set = set()
        for _, hp in self.hps:
            fun_set.update(hp.get_zero_arity_funcs())
        return fun_set

    def get_chs(self):
        ch_set = set()
        for _, hp in self.hps:
            ch_set.update(hp.get_chs())
        return ch_set
