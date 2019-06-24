class HCSP:
    def __init__(self):
        self.type = ""

    def __repr__(self):
        return str(self)

class Skip(HCSP):
    def __init__(self):
        self.type = "skip"

    def __eq__(self, other):
        return self.type == other.type

    def __str__(self):
        return "skip"

class Assign(HCSP):
    def __init__(self, var_name, expr):
        self.type = "assign",
        assert isinstance(var_name, str) and isinstance(expr, str)
        self.var_name = var_name
        self.expr = expr

    def __eq__(self, other):
        return self.type == other.type and self.var_name == other.var_name and self.expr == other.expr

    def __str__(self):
        return self.var_name + " := " + self.expr

class InputChannel(HCSP):
    def __init__(self, ch_name, var_name):
        self.type = "input_channel"
        self.ch_name = ch_name
        self.var_name = var_name

    def __eq__(self, other):
        return self.type == other.type and self.ch_name == other.ch_name and self.var_name == other.var_name

    def __str__(self):
        return self.ch_name + "?" + self.var_name

class OutputChannel(HCSP):
    def __init__(self, ch_name, expr):
        self.type = "output_channel"
        self.ch_name = ch_name
        self.expr = expr

    def __eq__(self, other):
        return self.type == other.type and self.ch_name == other.ch_name and self.expr == other.expr

    def __str__(self):
        return self.ch_name + "!" + self.expr

def is_comm_channel(hp):
    return hp.type == 'input_channel' or hp.type == 'output_channel'

class Sequence(HCSP):
    def __init__(self, *hps):
        """hps is a list of hybrid programs."""
        self.type = "sequence"
        assert all(isinstance(hp, HCSP) for hp in hps)
        self.hps = list(hps)

    def __eq__(self, other):
        return self.type == other.type and self.hps == other.hps

    def __str__(self):
        return "; ".join(str(hp) for hp in self.hps)

class ODE(HCSP):
    """Represents an ODE program of the form

    <F(s',s) = 0 & B> |> Q

    """
    def __init__(self, eqs, constraint, out_hp):
        """Each equation is of the form (var_name, expr), where var_name
        is the name of the variable, and expr is its derivative.

        constraint is a boolean formula.

        """
        assert isinstance(eqs, tuple) and len(eqs) == 2
        assert isinstance(out_hp, HCSP)
        self.type = 'ode'
        self.eqs = eqs
        self.constraint = constraint
        self.out_hp = out_hp

    def __eq__(self, other):
        return self.type == other.type and self.eqs == other.eqs and \
               self.constraint == other.constraint and self.out_hp == other.out_hp

    def __str__(self):
        str_eqs = ", ".join(var_name + "_dot = " + expr for var_name, expr in self.eqs)
        return "<" + str_eqs + " & " + self.constraint + "> |> " + self.out_hp

class ODE_Comm(HCSP):
    """Represents an ODE program that can be interrupted by
    communications, of the form

    <F(s',s) = 0 & B> |> [] (io_i --> Q_i)

    """
    def __init__(self, eqs, constraint, out_comms):
        """Each equation is of the form (var_name, expr). Each element
        of out_comms is of the form (comm_hp, out_hp), where comm_hp
        is a communication process (either InputChannel or OutputChannel).
        Whenever one of comm_hp is received, the ODE stops and performs
        out_hp.

        """
        assert isinstance(eqs, list)
        assert all(isinstance(p, tuple) and len(p) == 2 for p in eqs)
        assert isinstance(out_comms, list)
        assert all(isinstance(p, tuple) and len(p) == 2 and \
                   is_comm_channel(p[0]) and isinstance(p[1], HCSP) \
                   for p in out_comms)
        self.type = 'ode_comm'
        self.eqs = eqs
        self.constraint = constraint
        self.out_comms = out_comms

    def __eq__(self, other):
        return self.type == other.type and self.eqs == other.eqs and \
               self.constraint == other.constraint and self.out_comms == other.out_comms

    def __str__(self):
        str_eqs = ", ".join(var_name + "_dot = " + expr for var_name, expr in self.eqs)
        str_out_comms = ", ".join(str(comm_hp) + " --> " + str(out_hp) \
                                  for comm_hp, out_hp in self.out_comms)
        return "<" + str_eqs + " & " + self.constraint + "> |> [] (" + str_out_comms + ")"

class Loop(HCSP):
    """Represents an infinite loop of a program."""
    def __init__(self, hp):
        self.type = 'loop'
        self.hp = hp

    def __eq__(self, other):
        return self.type == other.type and self.hp == other.hp

    def __str__(self):
        return "(" + str(self.hp) + ")*"
