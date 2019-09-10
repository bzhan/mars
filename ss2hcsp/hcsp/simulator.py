"""Simulation for HCSP programs.

The state is given by a dictionary from variable names to numbers.

"""

from copy import copy
import itertools
import math

from ss2hcsp.hcsp.expr import AVar, AConst, PlusExpr, TimesExpr, FunExpr, ModExpr, \
    BConst, LogicExpr, RelExpr, true_expr
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
        args = [eval_expr(e, state) for e in expr.exprs]
        if expr.fun_name == "min":
            return min(*args)
        elif expr.fun_name == "max":
            return max(*args)
        elif expr.fun_name == "abs":
            return abs(*args)
        elif expr.fun_name == "gcd":
            return math.gcd(*args)
        elif expr.fun_name == "push":
            a, b = args
            assert isinstance(a, tuple)
            return a + (b,)
        elif expr.fun_name == "pop":
            a, = args
            assert isinstance(a, tuple) and len(a) > 0
            return a[:-1]
        elif expr.fun_name == "top":
            a, = args
            assert isinstance(a, tuple) and len(a) > 0
            return a[-1]
        else:
            raise NotImplementedError

    elif isinstance(expr, ModExpr):
        return eval_expr(expr.expr1, state) % eval_expr(expr.expr2, state)

    elif isinstance(expr, BConst):
        return self.value

    elif isinstance(expr, LogicExpr):
        a = eval_expr(expr.expr1, state)
        b = eval_expr(expr.expr2, state)
        if expr.op == "&&":
            return a and b
        elif expr.op == "||":
            return a or b
        elif expr.op == "-->":
            return (not a) or b
        elif expr.op == "<-->":
            return a == b
        else:
            raise NotImplementedError

    elif isinstance(expr, RelExpr):
        a = eval_expr(expr.expr1, state)
        b = eval_expr(expr.expr2, state)
        if expr.op == "<":
            return a < b
        elif expr.op == ">":
            return a > b
        elif expr.op == "==":
            return a == b
        elif expr.op == "!=":
            return a != b
        elif expr.op == ">=":
            return a >= b
        elif expr.op == "<=":
            return a <= b
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
    elif hp.type == 'condition':
        if len(pos) == 0:
            return hp
        else:
            assert pos[0] == 0
            return get_pos(hp.hp, pos[1:])
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

def parse_pos(hp, pos):
    """Convert pos in string form to internal representation."""
    if pos == 'end':
        return None
    elif pos == 'start':
        return start_pos(hp)
    
    assert len(pos) > 0 and pos[0] == 'p'
    pos = pos[1:].split('.')
    if len(pos) > 0 and pos[-1].startswith('w'):
        pos = tuple([int(p) for p in pos[:-1]] + [int(pos[-1][1:])])
        assert get_pos(hp, pos).type == 'wait'
    else:
        pos = tuple(int(p) for p in pos)

    return pos

def string_of_pos(hp, pos):
    """Convert pos in internal representation to string form."""
    if pos is None:
        return 'end'
    elif get_pos(hp, pos).type != 'wait':
        return 'p' + '.'.join(str(p) for p in pos)
    else:
        return 'p' + '.'.join(str(p) for p in pos[:-1]) + '.w' + str(pos[-1])

class HCSPInfo:
    """Represents a (non-parallel) HCSP program together with
    additional information on the current execution position and
    the current state.

    The current execution position is represented by a tuple of numbers,
    or None if execution has reached the end.

    """
    def __init__(self, hp, *, pos="start", state=None):
        """Initializes with starting position as the execution position."""
        if isinstance(hp, str):
            self.hp = parser.hp_parser.parse(hp)
        else:
            self.hp = hp

        if isinstance(pos, str):
            pos = parse_pos(self.hp, pos)
        else:
            assert isinstance(pos, tuple)
        self.pos = pos

        if state is None:
            state = dict()
        elif isinstance(state, (tuple, list)):
            state = dict({k: v for k, v in state})
        else:
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

        elif cur_hp.type == "condition":
            # Evaluate the condition, either go inside or step to next
            if eval_expr(cur_hp.cond, self.state):
                self.pos = self.pos + (0,)
            else:
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
        if self.pos is None:
            return

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

def extract_event(reasons):
    """From a list of reasons, extract the next event. The returned
    value is one of:

    "deadlock" -> the program has deadlocked.
    ("delay", n) -> delay for n seconds.
    ("comm", id_out, id_in, ch_name) -> communication.

    """
    # First, attempt to find communication
    for i, reason1 in enumerate(reasons):
        for j, reason2 in enumerate(reasons):
            if reason1 != 'end' and reason2 != 'end' and \
                reason1[0] == 'comm' and reason2[0] == 'comm':
                for ch_name1, dir1 in reason1[1]:
                    for ch_name2, dir2 in reason2[1]:
                        if ch_name1 == ch_name2 and dir1 == "!" and dir2 == "?":
                            return ("comm", i, j, ch_name1)

    # If there is no communication, find minimum delay
    min_delay = None
    for reason in reasons:
        if reason != 'end' and reason[0] == "delay":
            if min_delay is None or min_delay > reason[1]:
                min_delay = reason[1]

    if min_delay is not None:
        return ("delay", min_delay)
    else:
        return "deadlock"

def get_log_info(infos):
    """Obtain the logged info."""
    cur_info = []
    for info in infos:
        info_pos = string_of_pos(info.hp, info.pos)
        info_state = sorted([(k, v) for k, v in info.state.items()])
        cur_info.append({'pos': info_pos, 'state': info_state})
    return cur_info

def exec_parallel(infos, num_steps, *, state_log=None, time_series=None):
    """Given a list of HCSPInfo objects, execute the hybrid programs
    in parallel on their respective states for the given number steps.

    If state_log is given (as a list), append the log of states.

    """
    # Stores the list of events
    trace = []

    # Current time
    time = 0

    def log_info():
        if state_log is not None:
            state_log.append(get_log_info(infos))

    def log_time_series():
        if time_series is not None:
            new_entry = {
                "time": time,
                "states": [copy(info.state) for info in infos]
            }
            if len(time_series) == 0 or new_entry != time_series[-1]:
                time_series.append(new_entry)

    # Record state and time series at the beginning
    log_info()
    log_time_series()

    for iteration in range(num_steps):
        # List of stopping reasons for each process
        reasons = []

        # Iterate over the processes, apply exec_process to each,
        # collect the stopping reasons.
        for info in infos:
            reason = info.exec_process()
            reasons.append(reason)

        # Record state after exec_process
        log_info()

        event = extract_event(reasons)
        if event == "deadlock":
            trace.append("deadlock")
            break
        elif event[0] == "delay":
            _, min_delay = event
            trace.append("delay %s" % str(min_delay))
            log_time_series()
            for info in infos:
                info.exec_delay(min_delay)
            time += min_delay
            log_time_series()
        else:
            _, id_out, id_in, ch_name = event
            val = infos[id_out].exec_output_comm(ch_name)
            infos[id_in].exec_input_comm(ch_name, val)
            trace.append("IO %s %s" % (ch_name, str(val)))

    # Log info and time series at the end
    if trace[-1] != 'deadlock':
        log_info()
    log_time_series()

    return trace

def exec_parallel_steps(infos, *, start_event):
    """Execute the programs in infos, until the next event.
    If start_event is True, the infos start at an event, and
    execution continues until the next event. Otherwise, the infos
    start at the beginning.

    Returns the list of states encountered.

    """
    state_log = []
    reasons = []

    if start_event:
        # Find the current event
        for info in infos:
            if info.pos is None:
                reasons.append("end")
            else:
                res = info.exec_step()
                assert res != "step"
                reasons.append(res)
        event = extract_event(reasons)

        # Execute the current event
        if event == "deadlock":
            return []
        elif event[0] == "delay":
            _, min_delay = event
            for info in infos:
                info.exec_delay(min_delay)
        else:
            _, id_out, id_in, ch_name = event
            val = infos[id_out].exec_output_comm(ch_name)
            infos[id_in].exec_input_comm(ch_name, val)

        # Store state immediately after event
        state_log.append(get_log_info(infos))

    for info in infos:
        while True:
            if info.pos is None:
                break
            res = info.exec_step()
            if res == "step":
                state_log.append(get_log_info(infos))
            else:
                break

    return state_log
