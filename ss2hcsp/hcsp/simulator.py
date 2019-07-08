"""Simulation for HCSP programs.

The state is given by a dictionary from variable names to numbers.

"""

from ss2hcsp.hcsp.expr import AVar, AConst, PlusExpr, TimesExpr, FunExpr
from ss2hcsp.hcsp import hcsp

def eval_expr(expr, state):
    """Evaluate the given expression on the given state."""
    if isinstance(expr, AVar):
        # Variable case
        assert expr.name in state
        return state[expr.name]

    elif isinstance(expr, AConst):
        # Constant case
        return expr.value

    elif isinstance(expr, PlusExpr):
        # Sum of expressions
        res = 0
        for s, e in zip(expr.signs, expr.exprs):
            if s == '+':
                res += eval_expr(e, state)
            else:
                res -= eval_expr(e, state)
        return res

    elif isinstance(expr, TimesExpr):
        # Product of expressions
        res = 1
        for s, e in zip(expr.signs, expr.exprs):
            if s == '*':
                res *= eval_expr(e, state)
            else:
                res /= eval_expr(e, state)
        return res

    elif isinstance(expr, FunExpr):
        # Special functions
        if expr.fun_name == "min":
            a, b = expr.exprs
            return min(eval_expr(a, state), eval_expr(b, state))
        else:
            raise NotImplementedError

    else:
        raise NotImplementedError

def exec_step(hp, state):
    """Compute a single process for one step.

    If there is a step to be taken, return ("step", hp2),
    which is the remaining program (state is changed implicitly).

    If there is no step to be taken, return the reason for
    the wait: either the program must delay for some time
    ("delay", d), or it is waiting for one of the communication
    events ("comm", [...]), each communication event is described
    by a channel name and direction (e.g. ("p2c", "!") or ("c2p", "?"))).

    If the program ends, return ("end", None).
    
    """
    if hp.type == "skip":
        return ("end", None)

    elif hp.type == "assign":
        state[hp.var_name] = eval_expr(hp.expr, state)
        return ("step", hcsp.Skip())

    elif hp.type == "loop":
        # Unfold the loop once
        if hp.hp.type == "sequence":
            return ("step", hcsp.Sequence(*(hp.hp.hps + [hp])))
        else:
            return ("step", hcsp.Sequence(hp.hp, hp))

    elif hp.type == "sequence":
        assert len(hp.hps) >= 2
        if hp.hps[0].type == "skip":
            # First part of sequence ends
            if len(hp.hps) == 2:
                return ("step", hp.hps[1])
            else:
                return ("step", hcsp.Sequence(*hp.hps[1:]))
        else:
            # First part of sequence has not ended
            reason, rest = exec_step(hp.hps[0], state)
            if reason == "step":
                hp2 = rest
                return ("step", hcsp.Sequence(*([hp2] + hp.hps[1:])))
            else:
                return reason, rest

    elif hp.type == "input_channel":
        # Waiting for input
        return ("comm", [(hp.ch_name, "?")])

    elif hp.type == "output_channel":
        # Waiting for someone to receive output
        return ("comm", [(hp.var_name, "!")])

    elif hp.type == "wait":
        # Waiting for some number of seconds
        return ("delay", hp.delay)

    elif hp.type == "ode_comm":
        # Run ODE until one of the communication events
        comms = []
        for io_comm, rest in hp.io_comms:
            if io_comm.type == "input_channel":
                comms.append((io_comm.ch_name, "?"))
            else:
                comms.append((io_comm.var_name, "!"))
        return ("comm", comms)

    else:
        raise NotImplementedError

def exec_process(hp, state):
    """Compute a single process, until it must delay for some time,
    or wait for some communication event.

    Returns the pair (hp', state', stop_reason).

    """
    while True:
        reason, rest = exec_step(hp, state)
        if reason == "step":
            # Make hp the new program
            hp = rest
        else:
            return hp, (reason, rest)
