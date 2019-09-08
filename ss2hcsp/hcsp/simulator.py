"""Simulation for HCSP programs.

The state is given by a dictionary from variable names to numbers.

"""

import itertools

from ss2hcsp.hcsp.expr import AVar, AConst, PlusExpr, TimesExpr, FunExpr, true_expr
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import parser


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

def start_pos(hp):
    """Returns the starting position for a given program."""
    if hp.type == 'sequence':
        return (0,) + start_pos(hp.hps[0])
    elif hp.type == 'loop':
        return start_pos(hp.hp)
    elif hp.type == 'wait':
        return (0,)  # Time already spent in delay
    else:
        return tuple()

def get_pos(hp, pos):
    """Obtain the sub-program corresponding to the given position."""
    assert pos is not None, "get_pos: already reached the end."
    if hp.type == 'sequence':
        assert len(pos) > 0 and pos[0] < len(hp.hps)
        return get_pos(hp.hps[pos[0]], pos[1:])
    elif hp.type == 'loop':
        return get_pos(hp.hp, pos)
    elif hp.type == 'wait':
        assert len(pos) == 1
        return hp
    elif hp.type == 'ode_comm':
        if len(pos) == 0:
            return hp
        else:
            _, out_hp = hp.io_comms[pos[0]]
            return get_pos(out_hp, pos[1:])
    else:
        assert len(pos) == 0
        return hp

def step_pos(hp, pos):
    """Execute a (non-communicating) step in the program. Returns the
    new position, or None if steping to the end.
    
    """
    assert pos is not None, "step_pos: already reached the end."
    if hp.type == 'sequence':
        assert len(pos) > 0 and pos[0] < len(hp.hps)
        sub_step = step_pos(hp.hps[pos[0]], pos[1:])
        if sub_step is None:
            if pos[0] == len(hp.hps) - 1:
                return None
            else:
                return (pos[0]+1,) + start_pos(hp.hps[pos[0]+1])
        else:
            return (pos[0],) + sub_step
    elif hp.type == 'loop':
        sub_step = step_pos(hp.hp, pos)
        if sub_step is None:
            return start_pos(hp.hp)
        else:
            return sub_step
    elif hp.type == 'delay':
        assert len(pos) == 1
        return None
    else:
        return None


class HCSPInfo:
    """Represents a (non-parallel) HCSP program together with
    additional information on the current execution position and
    the current state.

    The current execution position is represented by a tuple of numbers,
    or None if execution has reached the end.

    """
    def __init__(self, hp, *, pos=None, state=None):
        """Initializes with starting position as the execution position."""
        if isinstance(hp, str):
            self.hp = parser.hp_parser.parse(hp)
        else:
            self.hp = hp

        if pos is None:
            pos = start_pos(self.hp)
        assert isinstance(pos, tuple)
        self.pos = pos

        if state is None:
            state = dict()
        assert isinstance(state, dict)
        self.state = state

    def exec_step(self):
        """Compute a single process for one step.

        If there is a step to be taken, return "step".

        If there is no step to be taken, return the reason for
        the wait: either the program must delay for some time
        ("delay", d), or it is waiting for one of the communication
        events ("comm", [...]), each communication event is described
        by a channel name and direction (e.g. ("p2c", "!") or ("c2p", "?"))).
        
        """
        cur_hp = get_pos(self.hp, self.pos)

        if cur_hp.type == "skip":
            self.pos = step_pos(self.hp, self.pos)
            return "step"
            
        elif cur_hp.type == "assign":
            # Perform assignment
            self.state[cur_hp.var_name] = eval_expr(cur_hp.expr, self.state)
            self.pos = step_pos(self.hp, self.pos)
            return "step"

        elif cur_hp.type == "input_channel":
            # Waiting for input
            return "comm", [(cur_hp.ch_name, "?")]

        elif cur_hp.type == "output_channel":
            # Waiting for someone to receive output
            return "comm", [(cur_hp.ch_name, "!")]

        elif cur_hp.type == "wait":
            # Waiting for some number of seconds
            return "delay", cur_hp.delay - self.pos[-1]

        elif cur_hp.type == "ode_comm":
            # Run ODE until one of the communication events
            comms = []
            for io_comm, rest in cur_hp.io_comms:
                if io_comm.type == "input_channel":
                    comms.append((io_comm.ch_name, "?"))
                else:
                    comms.append((io_comm.ch_name, "!"))
            return "comm", comms

        elif cur_hp.type == "select_comm":
            # Waiting for one of the input/outputs
            comms = []
            for comm in cur_hp.hps:
                if comm.type == "input_channel":
                    comms.append((comm.ch_name, "?"))
                elif comm.type == "output_channel":
                    comms.append((comm.ch_name, "!"))
                else:
                    raise NotImplementedError
            return "comm", comms

        else:
            raise NotImplementedError

    def exec_process(self):
        """Compute a single process, until it must delay for some time,
        or wait for some communication event.

        Returns the stopping reason, either ("comm", [...]) or ("delay", d)
        or "end" (for end of the program).

        """
        while self.pos is not None:
            res = self.exec_step()
            if res != "step":
                return res

        return "end"

    def exec_input_comm(self, ch_name, x):
        """Perform an input communication on a given hybrid program.

        The input communication is specified by the channel name
        and input value.

        """
        cur_hp = get_pos(self.hp, self.pos)

        if cur_hp.type == "input_channel":
            assert cur_hp.ch_name == ch_name
            self.state[cur_hp.var_name] = x
            self.pos = step_pos(self.hp, self.pos)

        elif cur_hp.type == "ode_comm":
            for i, (comm_hp, out_hp) in enumerate(cur_hp.io_comms):
                if comm_hp.type == "input_channel" and comm_hp.ch_name == ch_name:
                    self.state[comm_hp.var_name] = x
                    self.pos += (i,) + start_pos(out_hp)
                    return

            # Communication must be found among the interrupts
            assert False

        elif cur_hp.type == "select_comm":
            for i, comm in enumerate(cur_hp.hps):
                if comm.type == "input_channel" and comm.ch_name == ch_name:
                    self.state[comm.var_name] = x
                    self.pos = step_pos(self.hp, self.pos)
                    return

            # Communication must be found among the choices
            assert False

        else:
            assert False

    def exec_output_comm(self, ch_name):
        """Perform an output communication on a given hybrid program.

        The output communication is specified by the channel name.

        Returns the output value.

        """
        cur_hp = get_pos(self.hp, self.pos)

        if cur_hp.type == "output_channel":
            assert cur_hp.ch_name == ch_name
            self.pos = step_pos(self.hp, self.pos)
            return eval_expr(cur_hp.expr, self.state)

        elif cur_hp.type == "ode_comm":
            for i, (comm_hp, out_hp) in enumerate(cur_hp.io_comms):
                if comm_hp.type == "output_channel" and comm_hp.ch_name == ch_name:
                    val = eval_expr(comm_hp.expr, self.state)
                    self.pos += (i,) + start_pos(out_hp)
                    return val

            # Communication must be found among the interrupts
            assert False

        elif cur_hp.type == "select_comm":
            for i, comm in enumerate(cur_hp.hps):
                if comm.type == "output_channel" and comm.ch_name == ch_name:
                    self.pos = step_pos(self.hp, self.pos)
                    return eval_expr(comm.expr, self.state)

            # Communication must be found among the choices
            assert False

        else:
            assert False

    def exec_delay(self, delay):
        """Perform delay on the hybrid program of the given length."""

        cur_hp = get_pos(self.hp, self.pos)

        if cur_hp.type in ["skip", "input_channel", "output_channel", "select_comm"]:
            pass

        elif cur_hp.type == "wait":
            delay_left = cur_hp.delay - self.pos[-1]
            assert delay_left >= delay
            if delay_left == delay:
                self.pos = step_pos(self.hp, self.pos)
            else:
                self.pos = self.pos[:-1] + (self.pos[-1] + delay,)

        elif cur_hp.type == "ode_comm":
            # Currently, we only consider constant derivatives and
            # no constraints
            assert cur_hp.constraint == true_expr
            for var_name, deriv in cur_hp.eqs:
                assert isinstance(deriv, AConst)
                self.state[var_name] += delay * deriv.value

        else:
            assert False

def exec_parallel(infos, num_steps, *, debug=False):
    """Given a list of HCSPInfo objects, execute the hybrid programs
    in parallel on their respective states for the given number steps.

    """
    def print_status():
        for info in infos:
            print(info.hp, info.pos, info.state)

    # Stores the list of events
    trace = []

    if debug:
        print("\nInitial status:")
        print_status()

    for iteration in range(num_steps):
        # List of stopping reasons for each process
        reasons = []

        # Iterate over the processes, apply exec_process to each,
        # collect the stopping reasons.
        for info in infos:
            reason = info.exec_process()
            reasons.append(reason)

        if debug:
            print("\nAfter exec_process:")
            print_status()

        # Find matching communication
        id_in, id_out, ch_name = None, None, None
        for i, reason1 in enumerate(reasons):
            for j, reason2 in enumerate(reasons):
                if reason1 != 'end' and reason2 != 'end' and \
                    reason1[0] == 'comm' and reason2[0] == 'comm':
                    for ch_name1, dir1 in reason1[1]:
                        for ch_name2, dir2 in reason2[1]:
                            if ch_name1 == ch_name2 and dir1 == "!" and dir2 == "?":
                                id_out, id_in, ch_name = i, j, ch_name1

        if id_in is None:
            # No matching communication. Find minimum delay among
            # the processes.
            min_delay = None
            for reason in reasons:
                if reason != 'end' and reason[0] == "delay":
                    if min_delay is None or min_delay > reason[1]:
                        min_delay = reason[1]

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
            for info in infos:
                info.exec_delay(min_delay)
            if debug:
                print("... with result")
                print_status()

        else:
            # If there is a matching communication, perform the
            # communication.
            if debug:
                print("\nCommunication from %d to %d on %s" % (id_out, id_in, ch_name))
            val = infos[id_out].exec_output_comm(ch_name)
            infos[id_in].exec_input_comm(ch_name, val)
            trace.append("IO %s %s" % (ch_name, str(val)))
            if debug:
                print("... %s transfered, with result")
                print_status()

    return trace
