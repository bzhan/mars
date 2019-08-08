"""Simulation for HCSP programs.

The state is given by a dictionary from variable names to numbers.

"""

import itertools

from ss2hcsp.hcsp.expr import AVar, AConst, PlusExpr, TimesExpr, FunExpr, true_expr
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
        return "end", None

    elif hp.type == "assign":
        state[hp.var_name] = eval_expr(hp.expr, state)
        return "step", hcsp.Skip()

    elif hp.type == "loop":
        # Unfold the loop once
        if hp.hp.type == "sequence":
            return "step", hcsp.Sequence(*(hp.hp.hps + [hp]))
        else:
            return "step", hcsp.Sequence(hp.hp, hp)

    elif hp.type == "sequence":
        assert len(hp.hps) >= 2
        if hp.hps[0].type == "skip":
            # First part of sequence ends
            if len(hp.hps) == 2:
                return "step", hp.hps[1]
            else:
                return "step", hcsp.Sequence(*hp.hps[1:])
        else:
            # First part of sequence has not ended
            reason, rest = exec_step(hp.hps[0], state)
            if reason == "step":
                hp2 = rest
                return "step", hcsp.Sequence(*([hp2] + hp.hps[1:]))
            else:
                return reason, rest

    elif hp.type == "input_channel":
        # Waiting for input
        return "comm", [(hp.ch_name, "?")]

    elif hp.type == "output_channel":
        # Waiting for someone to receive output
        return "comm", [(hp.ch_name, "!")]

    elif hp.type == "wait":
        # Waiting for some number of seconds
        return "delay", hp.delay

    elif hp.type == "ode_comm":
        # Run ODE until one of the communication events
        comms = []
        for io_comm, rest in hp.io_comms:
            if io_comm.type == "input_channel":
                comms.append((io_comm.ch_name, "?"))
            else:
                comms.append((io_comm.ch_name, "!"))
        return "comm", comms

    else:
        raise NotImplementedError

def exec_process(hp, state):
    """Compute a single process, until it must delay for some time,
    or wait for some communication event.

    Returns the pair (hp2, stop_reason).

    """
    while True:
        reason, rest = exec_step(hp, state)
        if reason == "step":
            # Make hp the new program
            hp = rest
        else:
            return hp, (reason, rest)

def exec_input_comm(hp, state, ch_name, x):
    """Perform an input communication on a given hybrid program.

    The input communication is specified by the channel name
    and input value.

    Returns the new hybrid program.

    """
    if hp.type == "input_channel":
        assert hp.ch_name == ch_name
        state[hp.var_name] = x
        return hcsp.Skip()

    elif hp.type == "sequence":
        hp2 = exec_input_comm(hp.hps[0], state, ch_name, x)
        return hcsp.Sequence(*([hp2] + hp.hps[1:]))

    elif hp.type == "ode_comm":
        for comm_hp, out_hp in hp.io_comms:
            if comm_hp.type == "input_channel" and comm_hp.ch_name == ch_name:
                state[comm_hp.var_name] = x
                return out_hp
        # Communication must be found among the interrupts
        assert False

    else:
        assert False

def exec_output_comm(hp, state, ch_name):
    """Perform an output communication on a given hybrid program.

    The output communication is specified by the channel name.

    Returns the new hybrid program and the output value.

    """
    if hp.type == "output_channel":
        assert hp.ch_name == ch_name
        return hcsp.Skip(), eval_expr(hp.expr, state)

    elif hp.type == "sequence":
        hp2, val = exec_output_comm(hp.hps[0], state, ch_name)
        return hcsp.Sequence(*([hp2] + hp.hps[1:])), val

    elif hp.type == "ode_comm":
        for comm_hp, out_hp in hp.io_comms:
            if comm_hp.type == "output_channel" and comm_hp.ch_name == ch_name:
                val = eval_expr(comm_hp.expr, state)
                return out_hp, val
        # Communication must be found among the interrupts
        assert False

    else:
        assert False

def exec_delay(hp, state, delay):
    """Perform delay on the hybrid program of the given length.
    
    Return the new hybrid program.
    
    """
    if hp.type in ["skip", "input_channel", "output_channel"]:
        return hp

    elif hp.type == "sequence":
        hp2 = exec_delay(hp.hps[0], state, delay)
        return hcsp.Sequence(*([hp2] + hp.hps[1:]))

    elif hp.type == "wait":
        assert hp.delay >= delay
        if hp.delay == delay:
            return hcsp.Skip()
        else:
            return hcsp.Wait(hp.delay - delay)

    elif hp.type == "ode_comm":
        # Currently, we only consider constant derivatives and
        # no constraints
        assert hp.constraint == true_expr
        for var_name, deriv in hp.eqs:
            assert isinstance(deriv, AConst)
            state[var_name] += delay * deriv.value
        return hp

    else:
        assert False

def exec_parallel(num_steps, hp_states, *, debug=False):
    """Given a list of pairs (hp, state), execute the hybrid programs
    in parallel on their respective states for the given number steps.

    """
    def print_status():
        for hp, state in hp_states:
            print(hp, state)

    num_hp = len(hp_states)

    # Stores the list of events
    trace = []

    if debug:
        print("\nInitial status:")
        print_status()

    for iteration in range(num_steps):
        # List of stopping reasons for each process
        reasons = []

        # Iterate over the processes, update hybrid program and
        # (implicitly) update their states, collect the stopping
        # reasons
        for i in range(num_hp):
            hp, state = hp_states[i]
            hp2, reason = exec_process(hp, state)
            hp_states[i] = hp2, state
            reasons.append(reason)

        if debug:
            print("\nAfter exec_process:")
            print_status()

        # Find matching communication
        id_in, id_out, ch_name = None, None, None
        for i, (reason1, rest1) in enumerate(reasons):
            for j, (reason2, rest2) in enumerate(reasons):
                if reason1 == "comm" and reason2 == "comm":
                    for ch_name1, dir1 in rest1:
                        for ch_name2, dir2 in rest2:
                            if ch_name1 == ch_name2 and dir1 == "!" and dir2 == "?":
                                id_out, id_in, ch_name = i, j, ch_name1

        if id_in is None:
            # No matching communication. Find minimum delay among
            # the processes.
            min_delay = None
            for reason, rest in reasons:
                if reason == "delay":
                    if min_delay is None or min_delay > rest:
                        min_delay = rest

            # If no delay is possible, the system is in a deadlock
            # todo: this deadlock detection does not work well, it will report "deadlock" for ended processes.
            # todo: see testExecParallel3 in simulator_test
            if min_delay is None:
                if debug:
                    print("Deadlock")
                trace.append("deadlock")
                return trace

            # Otherwise, execute the delay.
            if debug:
                print("\nDelay for %s seconds" % str(min_delay))
            trace.append("delay %s" % str(min_delay))
            for i, (hp, state) in enumerate(hp_states):
                hp2 = exec_delay(hp, state, min_delay)
                hp_states[i] = (hp2, state)
            if debug:
                print("... with result")
                print_status()

        else:
            # If there is a matching communication, perform the
            # communication.
            if debug:
                print("\nCommunication from %d to %d on %s" % (id_out, id_in, ch_name))
            hp_in, state_in = hp_states[id_in]
            hp_out, state_out = hp_states[id_out]
            hp_out2, val = exec_output_comm(hp_out, state_out, ch_name)
            hp_in2 = exec_input_comm(hp_in, state_in, ch_name, val)
            hp_states[id_in] = (hp_in2, state_in)
            hp_states[id_out] = (hp_out2, state_out)
            trace.append("IO %s %s" % (ch_name, str(val)))
            if debug:
                print("... %s transfered, with result")
                print_status()

    return trace
