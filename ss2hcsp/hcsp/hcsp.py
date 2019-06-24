class HCSP:
    def __init__(self):
        self.type = ""

class Skip(HCSP):
    def __init__(self):
        self.type = "skip"

class Assign(HCSP):
    def __init__(self, var_name, expr):
        self.type = "assign",
        self.var_name = var_name
        self.expr = expr

class InputChannel(HCSP):
    def __init__(self, ch_name, var_name):
        self.type = "input_channel"
        self.ch_name = ch_name
        self.var_name = var_name

class OutputChannel(HCSP):
    def __init__(self, ch_name, expr):
        self.type = "output_channel"
        self.ch_name = ch_name
        self.expr = expr

def is_comm_channel(hp):
    return hp.type == 'input_channel' or hp.type == 'output_channel'

class Sequence(HCSP):
    def __init__(self, hps):
        """hps is a list of hybrid programs."""
        self.hps = hps

class ODE(HCSP):
    """Represents an ODE program of the form

    <F(s',s) = 0 & B> |> Q

    """
    def __init__(self, eqs, constraint, out_hp):
        """Each equation is of the form (var_name, expr), where var_name
        is the name of the variable, and expr is its derivative.

        constraint is a boolean formula.

        """
        assert isinstance(eqs, Tuple) and len(eqs) == 2
        assert isinstance(out_hp, HCSP)
        self.eqs = eqs
        self.constraint = constraint
        self.out_hp = out_hp

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
        assert isinstance(eqs, Tuple) and len(eqs) == 2
        assert isinstance(out_comms, List)
        assert all(isinstance(p, Tuple) and len(p) == 2 and \
                   is_comm_channel(p[0]) and isinstance(p[1], HCSP) \
                   for p in out_comms)
        self.eqs = eqs
        self.constraint = constraint
        self.out_comms = out_comms

class Loop(HCSP):
    """Represents an infinite loop of a program."""
    def __init__(self, hp):
        self.hp = hp
