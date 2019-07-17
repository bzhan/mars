"""Hybrid programs"""

# from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.expr import AExpr, BExpr


class HCSP:
    def __init__(self, name=""):
        self.type = ""
        self.name = name

    def __repr__(self):
        return str(self)

    def __str__(self):
        return self.name


class Skip(HCSP):
    def __init__(self):
        self.type = "skip"

    def __eq__(self, other):
        return self.type == other.type

    def __repr__(self):
        return "Skip()"

    def __str__(self):
        return "skip"


class Wait(HCSP):
    def __init__(self, delay):
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
        self.type = "assign"
        assert isinstance(var_name, str) and isinstance(expr, AExpr)
        self.var_name = var_name  # string
        self.expr = expr  # AExpr

    def __eq__(self, other):
        return self.type == other.type and self.var_name == other.var_name and self.expr == other.expr

    def __repr__(self):
        return "Assign(%s, %s)" % (self.var_name, str(self.expr))

    def __str__(self):
        return self.var_name + " := " + str(self.expr)


class InputChannel(HCSP):
    def __init__(self, ch_name, var_name=None):
        self.type = "input_channel"
        # assert isinstance(ch_name, str) and isinstance(var_name, str)
        assert isinstance(ch_name, str)
        self.ch_name = ch_name  # string
        self.var_name = var_name  # string

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
    def __init__(self, ch_name, expr = None):
        self.type = "output_channel"
        # assert isinstance(ch_name, str) and isinstance(expr, AExpr)
        assert isinstance(ch_name, str)
        self.ch_name = ch_name  # string
        self.expr = expr  # AExpr

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
        """hps is a list of hybrid programs."""
        self.type = "sequence"
        assert all(isinstance(hp, HCSP) for hp in hps)
        self.hps = list(hps)  # type(hps) == tuple

    def __eq__(self, other):
        return self.type == other.type and self.hps == other.hps

    def __repr__(self):
        return "Seq(%s)" % ", ".join(repr(hp) for hp in self.hps)

    def __str__(self):
        return "; ".join(str(hp) for hp in self.hps)


class ODE(HCSP):
    """Represents an ODE program of the form

    <F(s',s) = 0 & B> |> Q

    """
    def __init__(self, eqs, constraint, *, out_hp=Skip()):
        """Each equation is of the form (var_name, expr), where var_name
        is the name of the variable, and expr is its derivative.

        constraint is a boolean formula.

        """
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
        # str_out_hp = " |> " + str(self.out_hp) if self.out_hp else ""
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
    def __init__(self, hp):
        self.type = 'loop'
        assert isinstance(hp, HCSP)
        self.hp = hp  # hcsp

    def __eq__(self, other):
        return self.type == other.type and self.hp == other.hp

    def __repr__(self):
        return "Loop(%s)" % repr(self.hp)

    def __str__(self):
        return "(" + str(self.hp) + ")*"


class Condition(HCSP):
    """The alternative cond -> hp behaves as hp if cond is true;
     otherwise, it terminates immediately."""
    def __init__(self, cond, hp):
        assert isinstance(cond, BExpr) and isinstance(hp, HCSP)
        self.type = "condition"
        self.cond = cond  # BExpr
        self.hp = hp  # HCSP

    def __eq__(self, other):
        return self.type == other.type and self.cond == other.cond and self.hp == other.hp

    def __repr__(self):
        return "Condition(%s, %s)" % (str(self.cond), repr(self.hp))

    def __str__(self):
        return str(self.cond) + " -> (" + str(self.hp) + ")"


class Parallel(HCSP):
    def __init__(self, *hps):
        """hps is a list of hybrid programs."""
        self.type = "parallel"
        assert all(isinstance(hp, HCSP) for hp in hps)
        self.hps = list(hps)  # type(hps) == tuple

    def __eq__(self, other):
        return self.type == other.type and self.hps == other.hps

    def __str__(self):
        return " || ".join(str(hp) for hp in self.hps)


class Definition(HCSP):
    """The alternative hp1 ::= hp2 behaves as hp1 defined by hp2;
    otherwise, it terminates immediately.
    
    """
    def __init__(self, hp1, hp2):
        assert isinstance(hp1, HCSP) and isinstance(hp2, HCSP)
        self.type = "definition"
        self.hp1 = hp1
        self.hp2 = hp2

    def __eq__(self, other):
        return self.type == other.type and self.hp1 == other.hp1

    def __str__(self):
        return str(self.hp1) + " ::= ( " + str(self.hp2) + " ) "


class SelectComm(HCSP):
    def __init__(self, *hps):
        """hps is a list of hybrid programs."""
        self.type = "select_comm"
        assert all(isinstance(hp, HCSP) for hp in hps)
        # assert all(is_comm_channel(hp) for hp in hps)
        self.hps = list(hps)  # type(hps) == tuple

    def __eq__(self, other):
        return self.type == other.type and self.hps == other.hps

    def __str__(self):
        return " { " + " $ ".join(str(hp) for hp in self.hps) + " } "
