"""Simulation for HCSP programs.

The state is given by a dictionary from variable names to numbers.

"""

from copy import copy
import itertools
import math
from scipy.integrate import solve_ivp

from ss2hcsp.hcsp.expr import AVar, AConst, PlusExpr, TimesExpr, FunExpr, ModExpr, \
    BConst, LogicExpr, RelExpr, true_expr, opt_round, get_range
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import parser


class SimulatorException(Exception):
    def __init__(self, error_msg):
        self.error_msg = error_msg


def eval_expr(expr, state):
    """Evaluate the given expression on the given state."""
    if expr is None:
        return None

    elif isinstance(expr, AVar):
        # Variable case
        if expr.name not in state:
            raise SimulatorException("Uninitialized variable: " + expr.name)

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

def get_ode_delay(hp, state):
    """Obtain the delay needed for the given ODE, starting at the
    given state.
    
    """
    assert hp.type == 'ode'

    def ode_fun(t, y):
        res = []
        state2 = copy(state)
        for (var_name, _), yval in zip(hp.eqs, y):
            state2[var_name] = yval
        for var_name, expr in hp.eqs:
            res.append(eval_expr(expr, state2))
        return res

    def event(t, y):
        state2 = copy(state)
        for (var_name, _), yval in zip(hp.eqs, y):
            state2[var_name] = yval

        c = hp.constraint
        if isinstance(c, RelExpr):
            if c.op in ('<', '<='):
                return eval_expr(c.expr1, state2) - eval_expr(c.expr2, state2)
            elif hp.constraint.op in ('>', '>='):
                return eval_expr(c.expr2, state2) - eval_expr(c.expr1, state2)
            else:
                raise NotImplementedError
        else:
            raise NotImplementedError

    event.terminal = True  # Terminate execution when result is 0
    event.direction = 1    # Crossing from negative to positive

    y0 = []
    for var_name, _ in hp.eqs:
        y0.append(state[var_name])

    # Test the differential equation on longer and longer time ranges,
    # return the delay if the ODE solver detects event before the end
    # of the time range.
    delays = [1, 2, 5, 10, 20, 50, 100]
    for delay in delays:
        sol = solve_ivp(ode_fun, [0, delay], y0, events=[event], rtol=1e-4)
        if sol.t[-1] < delay:
            return opt_round(sol.t[-1])

    # Otherwise, return the maximum 100.
    return 100

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
    elif hp.type == 'select_comm':
        if len(pos) == 0:
            return hp
        else:
            _, out_hp = hp.io_comms[pos[0]]
            return get_pos(out_hp, pos[1:])
    elif hp.type == 'recursion':
        if len(pos) == 0:
            return hp
        else:
            return get_pos(hp.hp, pos[1:])
    elif hp.type == 'ite':
        if len(pos) == 0:
            return hp
        elif pos[0] < len(hp.if_hps):
            return get_pos(hp.if_hps[pos[0]][1], pos[1:])
        else:
            assert pos[0] == len(hp.if_hps)
            return get_pos(hp.else_hp, pos[1:])
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
    elif hp.type == 'select_comm':
        assert len(pos) > 0
        _, out_hp = hp.io_comms[pos[0]]
        sub_step = step_pos(out_hp, pos[1:])
        if sub_step is None:
            return None
        else:
            return (pos[0],) + sub_step
    elif hp.type == 'loop':
        sub_step = step_pos(hp.hp, pos)
        if sub_step is None:
            return start_pos(hp.hp)
        else:
            return sub_step
    elif hp.type == 'condition':
        if len(pos) == 0:
            return None
        sub_step = step_pos(hp.hp, pos[1:])
        if sub_step is None:
            return None
        else:
            return (0,) + sub_step
    elif hp.type == 'delay':
        assert len(pos) == 1
        return None
    elif hp.type == 'recursion':
        sub_step = step_pos(hp.hp, pos[1:])
        if sub_step is None:
            return None
        else:
            return (0,) + sub_step
    elif hp.type == 'ode_comm':
        assert len(pos) > 0
        _, out_hp = hp.io_comms[pos[0]]
        sub_step = step_pos(out_hp, pos[1:])
        if sub_step is None:
            return None
        else:
            return (pos[0],) + sub_step
    elif hp.type == 'ite':
        assert len(pos) > 0
        if pos[0] < len(hp.if_hps):
            _, sub_hp = hp.if_hps[pos[0]]
            sub_step = step_pos(sub_hp, pos[1:])
        else:
            assert pos[0] == len(hp.if_hps)
            sub_step = step_pos(hp.else_hp, pos[1:])
    
        if sub_step is None:
            return None
        else:
            return (pos[0],) + sub_step
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
    def __init__(self, name, hp, *, pos="start", state=None):
        """Initializes with starting position as the execution position."""
        assert isinstance(name, str)
        self.name = name

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
                self.pos += (0,) + start_pos(cur_hp.hp)
            else:
                self.pos = step_pos(self.hp, self.pos)
            return "step"

        elif cur_hp.type == "recursion":
            # Enter into recursion
            self.pos = self.pos + (0,) + start_pos(cur_hp.hp)
            return "step"            

        elif cur_hp.type == "var":
            # Return to body of recursion
            for i in range(len(self.pos)):
                try:
                    hp = get_pos(self.hp, self.pos[:i])
                except AssertionError:
                    pass
                else:
                    if hp.type == 'recursion' and hp.entry == cur_hp.name:
                        self.pos = self.pos[:i]
                        return "step"

            # Otherwise, not a recursion variable
            raise SimulatorException("Unrecognized process variable: " + cur_hp.name)

        elif cur_hp.type == "input_channel":
            # Waiting for input
            return "comm", [(cur_hp.ch_name, "?")]

        elif cur_hp.type == "output_channel":
            # Waiting for someone to receive output
            return "comm", [(cur_hp.ch_name, "!")]

        elif cur_hp.type == "wait":
            # Waiting for some number of seconds
            return "delay", eval_expr(cur_hp.delay, self.state) - self.pos[-1]

        elif cur_hp.type == "ode":
            # Find delay of ODE
            return "delay", get_ode_delay(cur_hp, self.state)

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
            for comm_hp, out_hp in cur_hp.io_comms:
                if comm_hp.type == "input_channel":
                    comms.append((comm_hp.ch_name, "?"))
                elif comm_hp.type == "output_channel":
                    comms.append((comm_hp.ch_name, "!"))
                else:
                    raise NotImplementedError
            return "comm", comms

        elif cur_hp.type == 'ite':
            # Find the first condition that evaluates to true
            for i, (cond, sub_hp) in enumerate(cur_hp.if_hps):
                if eval_expr(cond, self.state):
                    self.pos += (i,) + start_pos(sub_hp)
                    return "step"

            # Otherwise, go to the else branch
            self.pos += (len(cur_hp.if_hps),) + start_pos(cur_hp.else_hp)
            return "step"

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
            if cur_hp.var_name is None:
                assert x is None
            else:
                assert x is not None
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
            for i, (comm_hp, out_hp) in enumerate(cur_hp.io_comms):
                if comm_hp.type == "input_channel" and comm_hp.ch_name == ch_name:
                    if comm_hp.var_name is None:
                        assert x is None
                    else:
                        assert x is not None
                        self.state[comm_hp.var_name] = x
                    self.pos += (i,) + start_pos(out_hp)
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
            for i, (comm_hp, out_hp) in enumerate(cur_hp.io_comms):
                if comm_hp.type == "output_channel" and comm_hp.ch_name == ch_name:
                    self.pos += (i,) + start_pos(out_hp)
                    return eval_expr(comm_hp.expr, self.state)

            # Communication must be found among the choices
            assert False

        else:
            assert False

    def exec_delay(self, delay, *, time_series=None):
        """Perform delay on the hybrid program of the given length."""
        if self.pos is None:
            return

        cur_hp = get_pos(self.hp, self.pos)
        if cur_hp.type in ["input_channel", "output_channel", "select_comm"]:
            pass

        elif cur_hp.type == "wait":
            delay_left = eval_expr(cur_hp.delay, self.state) - self.pos[-1]
            assert delay_left >= delay
            if delay_left == delay:
                self.pos = step_pos(self.hp, self.pos)
            else:
                self.pos = self.pos[:-1] + (self.pos[-1] + delay,)

        elif cur_hp.type == "ode_comm" or cur_hp.type == "ode":
            finish_ode = False
            if cur_hp.type == "ode_comm":
                assert cur_hp.constraint == true_expr
            else:
                # Test whether this finishes the ODE.
                ode_delay = get_ode_delay(cur_hp, self.state)
                assert delay <= ode_delay
                if delay == ode_delay:
                    finish_ode = True

            if delay == 0.0:
                return
            else:
                def ode_fun(t, y):
                    res = []
                    state2 = copy(self.state)
                    for (var_name, _), yval in zip(cur_hp.eqs, y):
                        state2[var_name] = yval
                    for var_name, expr in cur_hp.eqs:
                        res.append(eval_expr(expr, state2))
                    return res
                
                y0 = []
                for var_name, _ in cur_hp.eqs:
                    y0.append(self.state[var_name])

                t_eval = [x for x in get_range(0, delay)]
                sol = solve_ivp(ode_fun, [0, delay], y0, t_eval=t_eval, rtol=1e-5, atol=1e-7)

                # Store time series
                if time_series is not None:
                    for i in range(len(sol.t)):
                        for (var_name, _), yval in zip(cur_hp.eqs, sol.y):
                            self.state[var_name] = opt_round(yval[i])
                        time_series.append({'time': t_eval[i], 'state': copy(self.state)})

                # Update state with values at the end
                for i, (var_name, _) in enumerate(cur_hp.eqs):
                    self.state[var_name] = opt_round(sol.y[i][-1])

            if finish_ode:
                self.pos = step_pos(self.hp, self.pos)

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
    cur_info = dict()
    for info in infos:
        info_pos = string_of_pos(info.hp, info.pos)
        cur_info[info.name] = {'pos': info_pos, 'state': copy(info.state)}
    return cur_info

def exec_parallel(infos, *, num_io_events=100, num_steps=400):
    """Given a list of HCSPInfo objects, execute the hybrid programs
    in parallel on their respective states for the given number steps.

    The returned result is a dictionary containing the result of the
    run. The entries are:

    time - total time spent in the model.

    trace - list of events. Each event contains information about the
        event, as well as the current state *before* executing the event.
    time_series - records evolution of variables in each program by time.
        This is a dictionary indexed by names of programs.

    """
    # Overall returned result
    res = {
        'time': 0,    # Current time
        'trace': [],  # List of events
        'time_series': {}  # Evolution of variables, indexed by program
    }

    end_run = False

    for info in infos:
        res['time_series'][info.name] = []

    def log_event(**xargs):
        """Log the given event, starting with the given event info."""
        nonlocal end_run
        new_event = xargs
        new_event['time'] = res['time']
        new_event['infos'] = get_log_info(infos)
        res['trace'].append(new_event)
        if len(res['trace']) > num_steps:
            end_run = True

    def log_time_series(name, time, state):
        """Log the given time series for program with the given name."""
        new_entry = {
            "time": time,
            "state": copy(state),
        }
        series = res['time_series'][name]
        if len(series) == 0 or new_entry != series[-1]:
            series.append(new_entry)

    # Record event and time series at the beginning.
    log_event(type="start", str="start")
    for info in infos:
        log_time_series(info.name, 0, info.state)

    for iteration in range(num_io_events):
        # List of stopping reasons for each process
        reasons = []

        # Iterate over the processes, apply exec_process to each,
        # collect the stopping reasons.
        for info in infos:
            while info.pos is not None and not end_run:
                reason = info.exec_step()
                if reason == "step":
                    log_event(type="step", str="step")
                    log_time_series(info.name, res['time'], info.state)
                else:
                    break
            if info.pos is None:
                reason = "end"
            reasons.append(reason)

        if end_run:
            break

        event = extract_event(reasons)
        if event == "deadlock":
            log_event(type="deadlock", str="deadlock")
            break
        elif event[0] == "delay":
            _, min_delay = event
            trace_str = "delay %s" % str(round(min_delay, 3))
            all_series = []
            for info in infos:
                series = []
                info.exec_delay(min_delay, time_series=series)
                for entry in series:
                    log_time_series(info.name, res['time'] + entry['time'], entry['state'])
                log_time_series(info.name, res['time'] + min_delay, info.state)
            log_event(type="delay", delay_time=min_delay, str=trace_str)
            res['time'] += min_delay
        else:
            _, id_out, id_in, ch_name = event
            val = infos[id_out].exec_output_comm(ch_name)
            infos[id_in].exec_input_comm(ch_name, val)
            if val is None:
                val_str = ""
            elif isinstance(val, float):
                val_str = " " + str(round(val, 3))
            else:
                val_str = " " + str(val)
            trace_str = "IO %s%s" % (ch_name, val_str)
            log_event(type="comm", ch_name=ch_name, val=val, str=trace_str)
            log_time_series(infos[id_in].name, res['time'], infos[id_in].state)

        # Overflow detection
        has_overflow = False
        for info in infos:
            for k, v in info.state.items():
                if isinstance(v, (int, float)) and abs(v) > 1e10:
                    has_overflow = True

        if has_overflow:
            log_event(type="overflow", str="overflow")
            break

    return res
