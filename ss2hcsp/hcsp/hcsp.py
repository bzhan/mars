"""Hybrid programs"""

from collections import OrderedDict
from ss2hcsp.hcsp.expr import AExpr, BExpr, AConst, true_expr


class HCSP:
    def __init__(self):
        self.type = None

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
    def __init__(self, var_name, expr):
        super(Assign, self).__init__()
        self.type = "assign"
        assert isinstance(var_name, str) and isinstance(expr, AExpr)
        self.var_name = var_name  # string
        self.expr = expr  # AExpr

    def __eq__(self, other):
        return self.type == other.type and self.var_name == other.var_name and self.expr == other.expr

    def __repr__(self):
        return "Assign(%s,%s)" % (self.var_name, str(self.expr))

    def __str__(self):
        return self.var_name + " := " + str(self.expr)


class InputChannel(HCSP):
    def __init__(self, ch_name, var_name=None):
        super(InputChannel, self).__init__()
        self.type = "input_channel"
        assert isinstance(ch_name, str)
        assert var_name is None or isinstance(var_name, str)
        self.ch_name = ch_name  # string
        self.var_name = var_name  # string or None

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
            return self.ch_name + "?" + str(self.var_name)
        else:
            return self.ch_name + "?"


class OutputChannel(HCSP):
    def __init__(self, ch_name, expr=None):
        super(OutputChannel, self).__init__()
        self.type = "output_channel"
        assert isinstance(ch_name, str)
        assert expr is None or isinstance(expr, AExpr)
        self.ch_name = ch_name  # string
        self.expr = expr  # AExpr or None

    def __eq__(self, other):
        return self.type == other.type and self.expr == other.expr and self.ch_name == other.ch_name

    def __repr__(self):
        if self.expr == AExpr():
            return "OutputC(%s,%s)" % (self.ch_name, self.expr)
        else:
            return "OutputC(%s)" % self.ch_name

    def __str__(self):
        if self.expr:
            return self.ch_name + "!" + str(self.expr)
        else:
            return self.ch_name + "!"


def is_comm_channel(hp):
    return hp.type == "input_channel" or hp.type == "output_channel"


class Sequence(HCSP):
    def __init__(self, *hps):
        super(Sequence, self).__init__()
        """hps is a list of hybrid programs."""
        self.type = "sequence"
        assert all(isinstance(hp, HCSP) for hp in hps)
        assert len(hps) >= 2
        self.hps = []
        for hp in hps:
            if hp.type == "sequence":
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


class Condition(HCSP):
    """The alternative cond -> hp behaves as hp if cond is true;
     otherwise, it terminates immediately."""
    def __init__(self, cond, hp):
        super(Condition, self).__init__()
        if not (isinstance(cond, BExpr) and isinstance(hp, HCSP)):
            print(hp, type(hp))
        assert isinstance(cond, BExpr)  and isinstance(hp, HCSP)
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


class Parallel(HCSP):
    def __init__(self, *hps):
        """hps is a list of hybrid programs."""
        super(Parallel, self).__init__()
        self.type = "parallel"
        assert all(isinstance(hp, HCSP) for hp in hps)
        assert len(hps) >= 2
        self.hps = list(hps)  # type(hps) == tuple

    def __eq__(self, other):
        return self.type == other.type and self.hps == other.hps

    def __repr__(self):
        return "Parallel(%s)" % (", ".join(repr(hp) for hp in self.hps))

    def __str__(self):
        return " || ".join(
            str(hp) if hp.priority() > self.priority() else "(" + str(hp) + ")"
            for hp in self.hps)


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
            "%s --> %s" % (comm_hp, out_hp) if out_hp.priority() > self.priority() else \
                "%s --> (%s)" % (comm_hp, out_hp) \
            for comm_hp, out_hp in self.io_comms)


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


class ITE(HCSP):
    def __init__(self, if_hps, else_hp):
        """if-then-else statements.

        if_hps is a list of condition-program pairs. else_hp is a program.
        The program associated to the first true condition in if_hps will
        be executed. If no condition is true, else_hp is executed.

        """
        super(ITE, self).__init__()
        assert all(isinstance(cond, BExpr) and isinstance(hp, HCSP) for cond, hp in if_hps)
        assert isinstance(else_hp, HCSP)
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
        assert len(hps_dict) == len(self.hps)
        substituted = dict()
        while hps_dict:
            name, hp = hps_dict.popitem()
            assert name not in substituted
            substituted[name] = _substitute(hp)
        assert set(substituted.keys()) == set(name for name, _ in self.hps)

        # self.hps[0] is the main process
        main_name, main_hp = self.hps[0]
        assert all(isinstance(hp, Var) for hp in main_hp.hps)
        self.hps = [(hp.name, substituted[hp.name]) for hp in main_hp.hps]
        self.hps.insert(0, (main_name, main_hp))

    def __str__(self):
        return "\n".join("%s ::= %s" % (name, str(hp)) for name, hp in self.hps)

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        return self.hps == other.hps
