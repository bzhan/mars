class HCSP:
    def __init__(self,name):
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

    def __str__(self):
        return "skip"


class Assign(HCSP):
    def __init__(self, var_name, expr):
        self.type = "assign"
        assert isinstance(var_name, str) and isinstance(expr, str)
        self.var_name = var_name  # string
        self.expr = expr  # string

    def __eq__(self, other):
        return self.type == other.type and self.var_name == other.var_name and self.expr == other.expr

    def __str__(self):
        return self.var_name + " := " + self.expr


class InputChannel(HCSP):
    def __init__(self, channel_name , var=None):
        self.type = "input_channel"
        self.channel_name = channel_name  # string
        self.var = var

    def __eq__(self, other):
        return self.type == other.type and self.channel_name == other.channel_name

    def __str__(self):
        if self.var:
            return "ch_" + self.channel_name + "?" + self.var
        else:
            return "ch_" + self.channel_name + "?"


class OutputChannel(HCSP):
    def __init__(self, channel_name , var=None):
        self.type = "output_channel"
        self.channel_name = channel_name  # string
        self.var = var

    def __eq__(self, other):
        return self.type == other.type and self.channel_name == other.channel_name

    def __str__(self):
        if self.var:
            return "ch_" + self.channel_name + "!" + self.var
        else:
            return "ch_" + self.channel_name + "!"



def is_comm_channel(hp):
    return hp.type == "input_channel" or hp.type == "output_channel"


class Sequence(HCSP):
    def __init__(self, *hps):
        """hps is a list of hybrid programs."""
        self.type = "sequence"
       # assert all(isinstance(hp, HCSP) for hp in hps)
        self.hps = list(hps)  # type(hps) == tuple

    def __eq__(self, other):
        return self.type == other.type and self.hps == other.hps

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
        '''
        assert isinstance(eqs, tuple) and len(eqs) == 2
        assert isinstance(out_hp, HCSP)
        self.type = 'ode'
        self.eqs = eqs  # (var_name: string, expr: string)
        self.constraint = constraint  # string
        self.out_hp = out_hp  # hcsp
        '''
        assert isinstance(eqs, list)
        assert all(isinstance(eq, tuple) and len(eq) == 2 for eq in eqs)
        assert not out_hp or isinstance(out_hp, HCSP)
        self.type = "ode"
        self.eqs = eqs  # list of tuples (string, string)
        self.constraint = constraint  # string
        self.out_hp = out_hp  # None or hcsp

    def __eq__(self, other):
        return self.type == other.type and self.eqs == other.eqs and \
               self.constraint == other.constraint and self.out_hp == other.out_hp

    def __str__(self):
        str_eqs = ", ".join(var_name + "_dot = " + expr for var_name, expr in self.eqs)
        # str_out_hp = " |> " + str(self.out_hp) if self.out_hp else ""
        str_out_hp = "" if isinstance(self.out_hp, Skip) else " |> " + str(self.out_hp)
        return "<" + str_eqs + " & " + self.constraint + ">" + str_out_hp


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
        assert all(isinstance(eq, tuple) and len(eq) == 2 for eq in eqs)
        assert isinstance(io_comms, list)
        assert all(isinstance(io_comm, tuple) and len(io_comm) == 2 and
                   is_comm_channel(io_comm[0]) and isinstance(io_comm[1], HCSP)
                   for io_comm in io_comms)
        self.type = "ode_comm"
        self.eqs = eqs  # list
        self.constraint = constraint  # string
        self.io_comms = io_comms  # list

    def __eq__(self, other):
        return self.type == other.type and self.eqs == other.eqs and \
               self.constraint == other.constraint and self.io_comms == other.io_comms

    def __str__(self):
        str_eqs = ", ".join(var_name + "_dot = " + expr for var_name, expr in self.eqs)
        str_io_comms = ", ".join(str(comm_hp) + " --> " + str(out_hp) for comm_hp, out_hp in self.io_comms)
        return "<<" + str_eqs + " & " + self.constraint + " >>|> [] (" + str_io_comms + ")"


class Loop(HCSP):
    """Represents an infinite loop of a program."""
    def __init__(self, hp):
        self.type = 'loop'
        self.hp = hp  # hcsp

    def __eq__(self, other):
        return self.type == other.type and self.hp == other.hp

    def __str__(self):
        return "(" + str(self.hp) + ")*"


class Condition(HCSP):
    """The alternative cond -> hp behaves as hp if cond is true;
     otherwise, it terminates immediately."""
    def __init__(self, cond, hp):
        assert isinstance(cond, str) and isinstance(hp, HCSP)
        self.type = "condition"
        self.cond = cond
        self.hp = hp

    def __eq__(self, other):
        return self.type == other.type and self.hp == other.hp

    def __str__(self):
        return self.cond + " -> (" + str(self.hp) + ")"

### add by Lin
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


class Defination(HCSP):
    """The alternative hp1 ::= hp2 behaves as hp1 defined by hp2;
         otherwise, it terminates immediately."""

    def __init__(self, hp1, hp2):
        assert isinstance(hp1, HCSP) and isinstance(hp2, HCSP)
        self.type = "defination"
        self.hp1 = hp1
        self.hp2 = hp2

    def __eq__(self, other):
        return self.type == other.type and self.hp1 == other.hp1

    def __str__(self):
        return str(self.hp1) + " ::= ( " + str(self.hp2) + " ) "


class Wait(HCSP):
    def __init__(self, time):
        self.type = "wait"
        self.time = time

    def __eq__(self, other):
        return self.type == other.type

    def __str__(self):
        return "wait "+self.time


class SelectComm(HCSP):
    def __init__(self, *hps):
        """hps is a list of hybrid programs."""
        self.type = "select_comm"
        assert all(isinstance(hp, HCSP) for hp in hps)
        #assert all(is_comm_channel(hp) for hp in hps)
        self.hps = list(hps)  # type(hps) == tuple

    def __eq__(self, other):
        return self.type == other.type and self.hps == other.hps

    def __str__(self):
        return " { "+" $ ".join(str(hp) for hp in self.hps) + " } "