"""Simulation for HCSP programs.

The state is given by a dictionary from variable names to numbers.

"""

import copy
import itertools
import math
import random
from scipy.integrate import solve_ivp
import matplotlib.pyplot as plt

from ss2hcsp.hcsp.expr import AExpr, AVar, AConst, PlusExpr, TimesExpr, FunExpr, ModExpr, \
    ListExpr, DictExpr, ArrayIdxExpr, FieldNameExpr, BConst, LogicExpr, NegExpr, \
    RelExpr, true_expr, false_expr, opt_round, get_range, split_disj
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import parser
from ss2hcsp.hcsp import pprint
from ss2hcsp.hcsp import graph_plot


class SimulatorException(Exception):
    def __init__(self, error_msg):
        self.error_msg = error_msg

class SimulatorAssertionException(Exception):
    def __init__(self, expr, error_msg):
        self.expr = expr
        self.error_msg = error_msg

    def __str__(self):
        res = 'Test %s failed' % self.expr
        if self.error_msg:
            res += ' (%s)' % self.error_msg
        return res


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
        try:
            res = 0
            for s, e in zip(expr.signs, expr.exprs):
                if s == '+':
                    res += eval_expr(e, state)
                else:
                    res -= eval_expr(e, state)
            return res
        except TypeError:
            raise SimulatorException("Type error when evaluating %s" % expr)

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
        elif expr.fun_name == "div":
            a, b = args
            return int(a) // int(b)
        elif expr.fun_name == "push":
            a, b = args
            assert isinstance(a, list)
            if isinstance(b, list):
                return a + b
            else:
                return a + [b]
        elif expr.fun_name == "pop":
            a, = args
            assert isinstance(a, list)
            if len(a) == 0:
                raise SimulatorException('When evaluating %s: argument is empty' % expr)
            return a[:-1]
        elif expr.fun_name == "top":
            a, = args
            assert isinstance(a, list)
            if len(a) == 0:
                raise SimulatorException('When evaluating %s: argument is empty' % expr)
            return a[-1]
        elif expr.fun_name == "bottom":
            a, = args
            assert isinstance(a, list)
            if len(a) == 0:
                raise SimulatorException('When evaluating %s: argument is empty' % expr)
            return a[0]
        elif expr.fun_name == "get":
            a, = args
            assert isinstance(a, list)
            if len(a) == 0:
                raise SimulatorException('When evaluating %s: argument is empty' % expr)
            return a[1:]
        elif expr.fun_name == "len":
            a, = args
            assert isinstance(a, list)
            return len(a)
        elif expr.fun_name == "get_max":
            a, = args
            assert isinstance(a, list)
            if len(a) == 0:
                raise SimulatorException('When evaluating %s: argument is empty' % expr)
            return max(a)
        elif expr.fun_name == "pop_max":
            a, = args
            assert isinstance(a, list)
            if len(a) == 0:
                raise SimulatorException('When evaluating %s: argument is empty' % expr)
            b = list(a)
            try:
                b.remove(max(a))
            except TypeError as e:
                print('value is:', a)
                raise e
            return list(b)
        elif expr.fun_name == "sqrt":
            assert len(args) == 1
            if args[0] < 0:
                raise SimulatorException('When evaluating %s: argument %s less than zero' % (expr, args[0]))
            return math.sqrt(args[0])
        elif expr.fun_name == "bernoulli":
            assert len(args) == 1
            if not (args[0] >= 0 and args[0] <= 1):
                raise SimulatorException('When evaluating %s: argument %s not in range' % (expr, args[0]))
            if random.uniform(0,1) <= args[0]:
                return 1
            else:
                return 0
        elif expr.fun_name == "uniform":
            assert len(args) == 2
            if args[0] > args[1]:
                raise SimulatorException('When evaluating %s: %s > %s' % (expr, args[0], args[1]))
            return random.uniform(args[0], args[1])
        else:
            raise NotImplementedError

    elif isinstance(expr, ModExpr):
        return eval_expr(expr.expr1, state) % eval_expr(expr.expr2, state)

    elif isinstance(expr, ListExpr):
        return list(eval_expr(arg, state) for arg in expr.args)

    elif isinstance(expr, DictExpr):
        return dict((k, eval_expr(v, state)) for k, v in expr.dict.items())

    elif isinstance(expr, ArrayIdxExpr):
        a = eval_expr(expr.expr1, state)
        i = eval_expr(expr.expr2, state)
        if not (isinstance(a, list) and isinstance(i, int)):
            raise SimulatorException('When evaluating %s: type error' % expr)
        if not i < len(a):
            raise SimulatorException('When evaluating %s: array out of bounds error' % expr)
        return a[i]

    elif isinstance(expr, FieldNameExpr):
        a = eval_expr(expr.expr, state)
        if expr.field not in a:
            raise SimulatorException('When evaluating %s: field not found' % expr)
        return a[expr.field]

    elif isinstance(expr, BConst):
        return expr.value

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

    elif isinstance(expr, NegExpr):
        a = eval_expr(expr.expr, state)
        return (not a)

    elif isinstance(expr, RelExpr):
        a = eval_expr(expr.expr1, state)
        b = eval_expr(expr.expr2, state)
        if expr.op == "<":
            return b - a > 1e-7
        elif expr.op == ">":
            return a - b > 1e-7
        elif expr.op == "==":
            if isinstance(a, (int, float)) and isinstance(b, (int, float)):
                return abs(a - b) < 1e-7
            else:
                return a == b
        elif expr.op == "!=":
            if isinstance(a, (int, float)) and isinstance(b, (int, float)):
                return abs(a - b) > 1e-7
            else:
                return a != b
        elif expr.op == ">=":
            return a - b > -1e-7
        elif expr.op == "<=":
            return b - a > -1e-7
        else:
            raise NotImplementedError

    else:
        print('When evaluating %s' % expr)
        raise NotImplementedError

def eval_channel(ch_name, state):
    args = tuple(int(eval_expr(arg, state)) for arg in ch_name.args)
    return hcsp.Channel(ch_name.name, args)

def get_ode_delay(hp, state):
    """Obtain the delay needed for the given ODE, starting at the
    given state.
    
    """
    assert hp.type in ('ode', 'ode_comm')

    if hp.constraint == false_expr:
        return 0.0

    if not eval_expr(hp.constraint, state):
        return 0.0

    def ode_fun(t, y):
        res = []
        state2 = copy.copy(state)
        for (var_name, _), yval in zip(hp.eqs, y):
            state2[var_name] = yval
        for var_name, expr in hp.eqs:
            res.append(eval_expr(expr, state2))
        return res

    def event_gen(t, y, c):
        # Here c is the constraint
        state2 = copy.copy(state)
        for (var_name, _), yval in zip(hp.eqs, y):
            state2[var_name] = yval
        if isinstance(c, RelExpr):
            if c.op in ('<', '<='):
                return eval_expr(c.expr1, state2) - eval_expr(c.expr2, state2)
            elif c.op in ('>', '>='):
                return eval_expr(c.expr2, state2) - eval_expr(c.expr1, state2)
            else:
                print('!!!!!')
                raise NotImplementedError
        else:
            print('!!!!!')
            raise NotImplementedError

    # Compute set of variables that remain zero
    zero_vars = []

    def is_zero(t):
        """Whether the given expression simplifies to 0."""
        if isinstance(t, TimesExpr):
            return any(t.signs[i] == '*' and is_zero(t.exprs[i]) for i in range(len(t.exprs)))
        elif isinstance(t, AConst):
            return t.value == 0
        elif isinstance(t, AVar):
            return t.name in zero_vars
        else:
            return False
    
    def is_zero_deriv(name):
        """Whether the derivative of variable simplifies to 0."""
        for var_name, eq in hp.eqs:
            if var_name == name and not is_zero(eq):
                return False
        return True

    found = True
    while found:
        found = False
        for name in state:
            if name not in zero_vars and is_zero_deriv(name) and state[name] == 0:
                zero_vars.append(name)
                found = True

    changed_vars = []
    for var_name, eq in hp.eqs:
        if not is_zero(eq):
            changed_vars.append(var_name)

    def occur_var(e, var_name):
        if isinstance(e, RelExpr):
            return occur_var(e.expr1, var_name) or occur_var(e.expr2, var_name)
        if isinstance(e, AVar):
            return e.name == var_name
        elif isinstance(e, AConst):
            return False
        elif isinstance(e, PlusExpr):
            return any(occur_var(sub_e, var_name) for sub_e in e.exprs)
        elif isinstance(e, (PlusExpr, TimesExpr, FunExpr)):
            return any(occur_var(sub_e, var_name) for sub_e in e.exprs)
        else:
            print('occur_var:', e)
            raise NotImplementedError

    def expr_unchanged(e):
        return all(not occur_var(e, var_name) for var_name in changed_vars)

    def test_cond(e):
        if isinstance(e, LogicExpr) and e.op == '||':
            delay1 = test_cond(e.expr1)
            delay2 = test_cond(e.expr2)
            return max(delay1, delay2)
        
        if isinstance(e, LogicExpr) and e.op == '&&':
            delay1 = test_cond(e.expr1)
            delay2 = test_cond(e.expr2)
            return min(delay1, delay2)

        # Condition never changes
        if expr_unchanged(e):
            if eval_expr(e, state):
                return 100
            else:
                return 0

        # Condition of the form t < constant
        if isinstance(e, RelExpr) and e.op in ('<', '<=') and \
            isinstance(e.expr1, AVar) and expr_unchanged(e.expr2):
            for var_name, deriv in hp.eqs:
                if var_name == e.expr1.name and expr_unchanged(deriv):
                    diff = eval_expr(e.expr2, state) - eval_expr(e.expr1, state)
                    return min(diff / eval_expr(deriv, state), 100.0)

        if not eval_expr(e, state):
            return 0

        y0 = []
        for var_name, _ in hp.eqs:
            y0.append(state[var_name])

        # Test the differential equation on longer and longer time ranges,
        # return the delay if the ODE solver detects event before the end
        # of the time range.
        min_delay = 100

        event = lambda t, y: event_gen(t, y, e)
        event.terminal = True  # Terminate execution when result is 0
        event.direction = 1    # Crossing from negative to positive

        delays = [1, 2, 5, 10, 20, 50, 100]
        cur_delay = 100
        for delay in delays:
            sol = solve_ivp(ode_fun, [0, delay], y0, events=[event], rtol=1e-5, atol=1e-7)
            if sol.t[-1] < delay:
                cur_delay = opt_round(sol.t[-1])
                break

        if cur_delay < min_delay:
            min_delay = cur_delay

        return min_delay

    return test_cond(hp.constraint)

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

def get_pos(hp, pos, rec_vars=None):
    """Obtain the sub-program corresponding to the given position."""
    assert pos is not None, "get_pos: already reached the end."
    if rec_vars is None:
        rec_vars = dict()
    if hp.type == 'sequence':
        if len(pos) == 0:
            return hp
        return get_pos(hp.hps[pos[0]], pos[1:], rec_vars)
    elif hp.type == 'loop':
        return get_pos(hp.hp, pos, rec_vars)
    elif hp.type == 'wait':
        # assert len(pos) == 1
        return hp
    elif hp.type == 'ode_comm':
        if len(pos) == 0:
            return hp
        else:
            _, out_hp = hp.io_comms[pos[0]]
            return get_pos(out_hp, pos[1:], rec_vars)
    elif hp.type == 'condition':
        if len(pos) == 0:
            return hp
        else:
            assert pos[0] == 0
            return get_pos(hp.hp, pos[1:], rec_vars)
    elif hp.type == 'select_comm':
        if len(pos) == 0:
            return hp
        else:
            _, out_hp = hp.io_comms[pos[0]]
            return get_pos(out_hp, pos[1:], rec_vars)
    elif hp.type == 'recursion':
        if len(pos) == 0:
            return hp
        else:
            rec_vars[hp.entry] = hp
            return get_pos(hp.hp, pos[1:], rec_vars)
    elif hp.type == 'ite':
        if len(pos) == 0:
            return hp
        elif pos[0] < len(hp.if_hps):
            return get_pos(hp.if_hps[pos[0]][1], pos[1:], rec_vars)
        else:
            assert pos[0] == len(hp.if_hps)
            return get_pos(hp.else_hp, pos[1:], rec_vars)
    elif hp.type == 'var':
        if len(pos) == 0:
            return hp
        assert pos[0] == 0

        if hp.name not in rec_vars:
            raise SimulatorException("Unrecognized process variable: " + hp.name)

        rec_hp = rec_vars[hp.name]
        return get_pos(rec_hp, pos[1:], rec_vars)
    else:
        assert len(pos) == 0
        return hp

def step_pos(hp, pos, state, rec_vars=None):
    """Execute a (non-communicating) step in the program. Returns the
    new position, or None if steping to the end.
    
    """
    if rec_vars is None:
        rec_vars = dict()

    def helper(hp, pos):
        assert pos is not None, "step_pos: already reached the end."
        if hp.type == 'sequence':
            assert len(pos) > 0 and pos[0] < len(hp.hps)
            sub_step = helper(hp.hps[pos[0]], pos[1:])
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
            sub_step = helper(out_hp, pos[1:])
            if sub_step is None:
                return None
            else:
                return (pos[0],) + sub_step
        elif hp.type == 'loop':
            sub_step = helper(hp.hp, pos)
            if sub_step is None:
                if hp.constraint != true_expr and not eval_expr(hp.constraint, state):
                    return None
                else:
                    return start_pos(hp.hp)
            else:
                return sub_step
        elif hp.type == 'condition':
            if len(pos) == 0:
                return None
            sub_step = helper(hp.hp, pos[1:])
            if sub_step is None:
                return None
            else:
                return (0,) + sub_step
        elif hp.type == 'delay':
            assert len(pos) == 1
            return None
        elif hp.type == 'recursion':
            rec_vars[hp.entry] = hp
            sub_step = helper(hp.hp, pos[1:])
            if sub_step is None:
                return None
            else:
                return (0,) + sub_step
        elif hp.type == 'var':
            if hp.name not in rec_vars:
                raise SimulatorException("Unrecognized process variable: " + hp.name)

            rec_hp = rec_vars[hp.name]
            sub_step = helper(rec_hp, pos[1:])
            if sub_step is None:
                return None
            else:
                return (0,) + sub_step
        elif hp.type == 'ode_comm':
            if len(pos) == 0:
                return None

            _, out_hp = hp.io_comms[pos[0]]
            sub_step = helper(out_hp, pos[1:])
            if sub_step is None:
                return None
            else:
                return (pos[0],) + sub_step
        elif hp.type == 'ite':
            assert len(pos) > 0
            if pos[0] < len(hp.if_hps):
                _, sub_hp = hp.if_hps[pos[0]]
                sub_step = helper(sub_hp, pos[1:])
            else:
                assert pos[0] == len(hp.if_hps)
                sub_step = helper(hp.else_hp, pos[1:])
        
            if sub_step is None:
                return None
            else:
                return (pos[0],) + sub_step
        else:
            return None

    return helper(hp, pos)

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

def remove_rec(hp, pos, rec_vars=None):
    """Given a position in a program possibly with recursion,
    return the simplest expression for the same position in the program
    (removing recursion). This simpler position is used for display
    in user interface.

    """
    if pos is None:
        return None

    rec_list = []
    for i in range(len(pos)+1):
        sub_hp = get_pos(hp, pos[:i])
        if sub_hp.type == 'recursion':
            rec_list.append(i)

    if len(rec_list) >= 2:
        pos = pos[:rec_list[0]] + pos[rec_list[-1]:]
    return pos

def string_of_pos(hp, pos):
    """Convert pos in internal representation to string form."""
    if pos is None:
        return 'end'
    elif get_pos(hp, pos).type != 'wait':
        return 'p' + '.'.join(str(p) for p in pos)
    else:
        return 'p' + '.'.join(str(p) for p in pos[:-1])

class SimInfo:
    """Represents a (non-parallel) HCSP program together with
    additional information on the current execution position and
    the current state.

    The current execution position is represented by a tuple of numbers,
    or None if execution has reached the end.

    """
    def __init__(self, name, hp, *, outputs=None, pos="start", state=None):
        """Initializes with starting position as the execution position."""

        # Name of the program
        assert isinstance(name, str)
        self.name = name

        # Code for the program
        if isinstance(hp, str):
            self.hp = parser.hp_parser.parse(hp)
        else:
            self.hp = hp

        # List of output variables, None indicates output everything.
        self.outputs = outputs

        # Current position of execution
        if isinstance(pos, str):
            pos = parse_pos(self.hp, pos)
        else:
            assert isinstance(pos, tuple)
        self.pos = pos

        # Current state
        if state is None:
            state = dict()
        elif isinstance(state, (tuple, list)):
            state = dict({k: v for k, v in state})
        else:
            assert isinstance(state, dict)
        self.state = state

        # What the program is currently waiting for. None means not
        # currently waiting. If not None, then it is a dictionary with
        # possible keys 'comm' and 'delay'.
        self.reason = None

        # Last step at which the state is changed. Used during simulation.
        self.last_change = 0

    def __str__(self):
        return str({'name': self.name, 'hp': self.hp, 'pos': self.pos, 'state': self.state, 'reason': self.reason})

    def exec_assign(self, lname, val, hp):
        """Make the copy of val into lname. Note deep-copy need to be
        used to avoid aliasing.

        """
        if isinstance(lname, AVar):
            self.state[lname.name] = copy.deepcopy(val)
        elif isinstance(lname, ArrayIdxExpr):
            v = eval_expr(lname.expr1, self.state)
            idx = eval_expr(lname.expr2, self.state)
            if idx >= len(v):
                raise SimulatorException('Array index %s out of bounds, when executing %s' % (idx, hp))
            v[idx] = copy.deepcopy(val)
        elif isinstance(lname, FieldNameExpr):
            v = eval_expr(lname.expr, self.state)
            if lname.field not in v:
                raise SimulatorException('Field %s does not exist, when executing %s' % (lname.field, hp))
            v[lname.field] = copy.deepcopy(val)
        else:
            raise NotImplementedError

    def exec_step(self):
        """Compute a single process for one step.

        If there is a step to be taken, return "step".

        If there is no step to be taken, return the reason for
        the wait: either the program must delay for some time
        ("delay", d), or it is waiting for one of the communication
        events ("comm", [...]), each communication event is described
        by a channel name and direction (e.g. ("p2c", "!") or ("c2p", "?"))).
        
        """
        rec_vars = dict()
        cur_hp = get_pos(self.hp, self.pos, rec_vars)

        if cur_hp.type == "skip":
            self.pos = step_pos(self.hp, self.pos, self.state, rec_vars)
            self.reason = None
            
        elif cur_hp.type == "assign":
            # Perform assignment
            if isinstance(cur_hp.var_name, AExpr):
                self.exec_assign(cur_hp.var_name, eval_expr(cur_hp.expr, self.state), cur_hp)
            else:
                # Multiple assignment
                val = eval_expr(cur_hp.expr, self.state)
                assert isinstance(val, list) and len(val) == len(cur_hp.var_name), \
                    "Multiple assignment: value not a list or of the wrong length."
                for i, s in enumerate(cur_hp.var_name):
                    if s != AVar('_'):
                        self.exec_assign(s, val[i], cur_hp)

            self.pos = step_pos(self.hp, self.pos, self.state, rec_vars)
            self.reason = None

        elif cur_hp.type == "assert":
            # Evaluate an assertion. If fails, immediate stop the execution
            # (like a runtime error).
            if not eval_expr(cur_hp.bexpr, self.state):
                error_msg = ''
                for msg in cur_hp.msgs:
                    val = eval_expr(msg, self.state)
                    if isinstance(val, str):
                        error_msg += val[1:-1]
                    else:
                        error_msg += str(val)
                raise SimulatorException(error_msg)
            else:
                self.pos = step_pos(self.hp, self.pos, self.state, rec_vars)
                self.reason = None

        elif cur_hp.type == "test":
            # Evaluate a test. If fails, output a warning but do not stop
            # the execution.
            self.pos = step_pos(self.hp, self.pos, self.state, rec_vars)
            self.reason = None
            if not eval_expr(cur_hp.bexpr, self.state):
                warning_expr = ''
                for msg in cur_hp.msgs:
                    val = eval_expr(msg, self.state)
                    if isinstance(val, str):
                        warning_expr += val[1:-1]
                    else:
                        warning_expr += str(val)
                raise SimulatorAssertionException(cur_hp.bexpr, warning_expr)

        elif cur_hp.type == "log":
            # Output a log item to the simulator
            self.pos = step_pos(self.hp, self.pos, self.state, rec_vars)
            log_expr = ''
            for expr in cur_hp.exprs:
                val = eval_expr(expr, self.state)
                if isinstance(val, str):
                    log_expr += val[1:-1]
                else:
                    log_expr += str(val)
            self.reason = {"log": log_expr}

        elif cur_hp.type == "condition":
            # Evaluate the condition, either go inside or step to next
            if eval_expr(cur_hp.cond, self.state):
                self.pos += (0,) + start_pos(cur_hp.hp)
            else:
                self.pos = step_pos(self.hp, self.pos, self.state, rec_vars)
            self.reason = None

        elif cur_hp.type == "recursion":
            # Enter into recursion
            self.pos += (0,) + start_pos(cur_hp.hp)
            self.reason = None

        elif cur_hp.type == "var":
            # Return to body of recursion
            for i in range(len(self.pos)):
                hp = get_pos(self.hp, self.pos[:i])
                if hp.type == 'recursion' and hp.entry == cur_hp.name:
                    self.pos += (0,) + start_pos(hp)
                    self.reason = None
                    return

            # Otherwise, not a recursion variable
            raise SimulatorException("Unrecognized process variable: " + cur_hp.name)

        elif cur_hp.type == "input_channel":
            # Waiting for input
            self.reason = {"comm": [(eval_channel(cur_hp.ch_name, self.state), "?")]}

        elif cur_hp.type == "output_channel":
            # Waiting for someone to receive output
            self.reason = {"comm": [(eval_channel(cur_hp.ch_name, self.state), "!")]}

        elif cur_hp.type == "wait":
            # Waiting for some number of seconds
            self.reason = {"delay": eval_expr(cur_hp.delay, self.state) - self.pos[-1]}

        elif cur_hp.type == "ode":
            # Find delay of ODE
            self.reason = {"delay": get_ode_delay(cur_hp, self.state)}

        elif cur_hp.type == "ode_comm":
            # Run ODE until one of the communication events (or the boundary)
            comms = []
            for io_comm, rest in cur_hp.io_comms:
                if io_comm.type == "input_channel":
                    comms.append((eval_channel(io_comm.ch_name, self.state), "?"))
                else:
                    comms.append((eval_channel(io_comm.ch_name, self.state), "!"))
            self.reason = {"comm": comms}
            if cur_hp.constraint != true_expr:
                self.reason["delay"] = get_ode_delay(cur_hp, self.state)

        elif cur_hp.type == "select_comm":
            # Waiting for one of the input/outputs
            comms = []
            for comm_hp, out_hp in cur_hp.io_comms:
                if comm_hp.type == "input_channel":
                    comms.append((eval_channel(comm_hp.ch_name, self.state), "?"))
                elif comm_hp.type == "output_channel":
                    comms.append((eval_channel(comm_hp.ch_name, self.state), "!"))
                else:
                    raise NotImplementedError
            self.reason = {"comm": comms}

        elif cur_hp.type == 'ite':
            # Find the first condition that evaluates to true
            for i, (cond, sub_hp) in enumerate(cur_hp.if_hps):
                if eval_expr(cond, self.state):
                    self.pos += (i,) + start_pos(sub_hp)
                    self.reason = None
                    return

            # Otherwise, go to the else branch
            self.pos += (len(cur_hp.if_hps),) + start_pos(cur_hp.else_hp)
            self.reason = None

        else:
            raise NotImplementedError

    def exec_input_comm(self, ch_name, x):
        """Perform an input communication on a given hybrid program.

        The input communication is specified by the channel name
        and input value.

        """
        rec_vars = dict()
        cur_hp = get_pos(self.hp, self.pos, rec_vars)

        if cur_hp.type == "input_channel":
            assert eval_channel(cur_hp.ch_name, self.state) == ch_name
            if cur_hp.var_name is None:
                assert x is None
            else:
                assert x is not None
                self.exec_assign(cur_hp.var_name, x, cur_hp)
            self.pos = step_pos(self.hp, self.pos, self.state, rec_vars)

        elif cur_hp.type == "ode_comm":
            for i, (comm_hp, out_hp) in enumerate(cur_hp.io_comms):
                if comm_hp.type == "input_channel" and eval_channel(comm_hp.ch_name, self.state) == ch_name:
                    self.exec_assign(comm_hp.var_name, x, comm_hp)
                    self.pos += (i,) + start_pos(out_hp)
                    return

            # Communication must be found among the interrupts
            assert False

        elif cur_hp.type == "select_comm":
            for i, (comm_hp, out_hp) in enumerate(cur_hp.io_comms):
                if comm_hp.type == "input_channel" and eval_channel(comm_hp.ch_name, self.state) == ch_name:
                    if comm_hp.var_name is None:
                        assert x is None
                    else:
                        assert x is not None
                        self.exec_assign(comm_hp.var_name, x, comm_hp)
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
        rec_vars = dict()
        cur_hp = get_pos(self.hp, self.pos, rec_vars)

        if cur_hp.type == "output_channel":
            assert eval_channel(cur_hp.ch_name, self.state) == ch_name
            self.pos = step_pos(self.hp, self.pos, self.state, rec_vars)
            return eval_expr(cur_hp.expr, self.state)

        elif cur_hp.type == "ode_comm":
            for i, (comm_hp, out_hp) in enumerate(cur_hp.io_comms):
                if comm_hp.type == "output_channel" and eval_channel(comm_hp.ch_name, self.state) == ch_name:
                    val = eval_expr(comm_hp.expr, self.state)
                    self.pos += (i,) + start_pos(out_hp)
                    return val

            # Communication must be found among the interrupts
            assert False

        elif cur_hp.type == "select_comm":
            for i, (comm_hp, out_hp) in enumerate(cur_hp.io_comms):
                if comm_hp.type == "output_channel" and eval_channel(comm_hp.ch_name, self.state) == ch_name:
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

        rec_vars = dict()
        cur_hp = get_pos(self.hp, self.pos, rec_vars)
        if cur_hp.type in ["input_channel", "output_channel", "select_comm"]:
            pass

        elif cur_hp.type == "wait":
            assert 'delay' in self.reason
            assert self.reason['delay'] >= delay
            if self.reason['delay'] == delay:
                self.pos = step_pos(self.hp, self.pos, self.state, rec_vars)
            else:
                self.pos = self.pos[:-1] + (self.pos[-1] + delay,)

            self.reason['delay'] -= delay

        elif cur_hp.type == "ode_comm" or cur_hp.type == "ode":
            finish_ode = False

            if cur_hp.constraint != true_expr:
                # Test whether this finishes the ODE.
                assert 'delay' in self.reason and delay <= self.reason['delay']
                if delay == self.reason['delay']:
                    finish_ode = True

            if delay != 0.0:
                def ode_fun(t, y):
                    res = []
                    state2 = copy.copy(self.state)
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
                        time_series.append({'time': t_eval[i], 'state': copy.copy(self.state)})

                # Update state with values at the end
                for i, (var_name, _) in enumerate(cur_hp.eqs):
                    self.state[var_name] = opt_round(sol.y[i][-1])

            if finish_ode:
                self.pos = step_pos(self.hp, self.pos, self.state, rec_vars)
            else:
                if 'delay' in self.reason:
                    self.reason['delay'] -= delay

        else:
            assert False

def extract_event(infos):
    """From a list of infos, extract the next event. The returned
    value is one of:

    "deadlock" -> the program has deadlocked.
    ("warning", msg) -> warning message.
    ("error", msg) -> error message.
    ("delay", n) -> delay for n seconds.
    ("comm", id_out, id_in, ch_name) -> communication.

    """
    # If any process has a warning or error, return it
    for i, info in enumerate(infos):
        if 'warning' in info.reason:
            return ('warning', info.reason['warning'])
        if 'error' in info.reason:
            return ('error', info.reason['error'])

    # First, attempt to find communication
    # We keep two dictionaries: out-ready events and in-ready events
    out_ready = dict()
    in_ready = dict()
    for i, info in enumerate(infos):
        if 'comm' in info.reason:
            for ch_name, direction in info.reason['comm']:
                if direction == '!':
                    out_ready[ch_name] = i
                elif direction == '?':
                    in_ready[ch_name] = i
                else:
                    raise TypeError
    for ch_name in out_ready:
        if ch_name in in_ready:
            return ('comm', out_ready[ch_name], in_ready[ch_name], ch_name)

    # If there is no communication, find minimum delay
    min_delay, delay_pos = None, []
    for i, info in enumerate(infos):
        if 'delay' in info.reason:
            if min_delay is None or min_delay > info.reason['delay']:
                min_delay = info.reason['delay']
                delay_pos = [i]
            elif min_delay == info.reason['delay']:
                delay_pos.append(i)

    if min_delay is not None:
        return ("delay", min_delay, delay_pos)
    else:
        return "deadlock"

def exec_parallel(infos, *, num_io_events=100, num_steps=400, num_show=None):
    """Given a list of SimInfo objects, execute the hybrid programs
    in parallel on their respective states for the given number steps.

    The returned result is a dictionary containing the result of the
    run. The entries are:

    time - total time spent in the model.

    trace - list of events. Each event contains information about the
        event, as well as the current state after executing the event.

    time_series - records evolution of variables in each program by time.
        This is a dictionary indexed by names of programs.

    """
    # Overall returned result
    res = {
        'time': 0,    # Current time
        'trace': [],  # List of events
        'time_series': {},  # Evolution of variables, indexed by program
        'events': []  # Concise list of event strings
    }

    # Number of steps so far.
    num_event = 0

    for info in infos:
        if info.outputs is None or len(info.outputs) > 0:
            # Has some variable to output
            res['time_series'][info.name] = []

    def log_event(ori_pos, **xargs):
        """Log the given event, starting with the given event info."""
        nonlocal num_event
        num_event += 1
        if num_event % 10000 == 0:
            print('i:', num_event)

        new_event = xargs
        new_event['time'] = res['time']
        new_event['ori_pos'] = ori_pos
        res['events'].append(new_event['str'])

        if new_event['type'] != 'error' and num_show is not None and len(res['trace']) >= num_show + 1:
            return

        cur_info = dict()
        for info in infos:
            if new_event['type'] == 'error' or info.name in ori_pos:
                info_pos = string_of_pos(info.hp, remove_rec(info.hp, info.pos))
                cur_info[info.name] = {'pos': info_pos, 'state': copy.copy(info.state)}
                info.last_change = len(res['trace'])
            else:
                cur_info[info.name] = info.last_change

        new_event['infos'] = cur_info
        res['trace'].append(new_event)

    def log_time_series(info, time, state):
        """Log the given time series for program with the given name."""
        if info.name not in res['time_series']:
            return

        new_entry = {
            "time": time,
            "event": len(res['trace']),
            "state": dict()
        }
        for k, v in state.items():
            if (info.outputs is None or any(k in output for output in info.outputs)) and \
                isinstance(v, (int, float)):
                new_entry['state'][k] = v
        series = res['time_series'][info.name]
        if len(series) == 0 or new_entry != series[-1]:
            series.append(new_entry)

    # List of processes that have been updated in the last round.
    updated = [info.name for info in infos]

    # Record event and time series at the beginning.
    log_event(ori_pos=updated, type="start", str="start")
    for info in infos:
        log_time_series(info, 0, info.state)

    for iteration in range(num_io_events):
        # Iterate over the processes, apply exec_step to each until
        # stuck, find the stopping reasons.
        for info in infos:
            if info.name not in updated:
                continue

            while info.pos is not None and not num_event > num_steps:
                try:
                    info.exec_step()
                except SimulatorAssertionException as e:
                    if 'warning' not in res:
                        info.reason = {'warning': str(e)}
                        res['warning'] = (res['time'], str(e))
                except SimulatorException as e:
                    info.reason = {'error': str(e)}
                    res['warning'] = (res['time'], str(e))

                if info.reason is None:
                    log_event(ori_pos=[info.name], type="step", str="step")
                    log_time_series(info, res['time'], info.state)
                elif 'log' in info.reason:
                    log_event(ori_pos=[info.name], type="log", str='-- ' + info.reason['log'] + ' --')
                elif 'warning' in info.reason:
                    log_event(ori_pos=[info.name], type="warning", str="warning: " + info.reason['warning'])
                elif 'error' in info.reason:
                    log_event(ori_pos=[info.name], type="error", str="error: " + info.reason['error'])
                    break
                else:
                    break

            if info.pos is None:
                info.reason = {'end': None}

        if num_event > num_steps:
            break

        event = extract_event(infos)
        if event == "deadlock":
            log_event(ori_pos=[], type="deadlock", str="deadlock")
            break
        elif event[0] == "error":
            break
        elif event[0] == "delay":
            _, min_delay, delay_pos = event
            trace_str = "delay %s" % str(round(min_delay, 3))
            all_series = []
            for info in infos:
                series = []
                info.exec_delay(min_delay, time_series=series)
                for entry in series:
                    log_time_series(info, res['time'] + entry['time'], entry['state'])
                log_time_series(info, res['time'] + min_delay, info.state)

            updated = [infos[p].name for p in delay_pos]
            log_event(ori_pos=updated, type="delay", delay_time=min_delay, str=trace_str)
            res['time'] += min_delay
        else:
            _, id_out, id_in, ch_name = event
            val = infos[id_out].exec_output_comm(ch_name)
            infos[id_in].exec_input_comm(ch_name, val)
            if val is None:
                val_str = ""
            elif isinstance(val, float):
                val_str = " " + str(round(val, 3))
            elif isinstance(val, dict):
                val_str = " {%s}" % (','.join(k + ':' + str(v) for k, v in val.items()))
            elif isinstance(val, list):
                val_str = " [%s]" % (','.join(str(v) for v in val))
            else:
                val_str = " " + str(val)

            updated = [infos[id_in].name, infos[id_out].name]
            trace_str = "IO %s%s" % (ch_name, val_str)
            log_event(ori_pos=updated, inproc=infos[id_in].name, outproc=infos[id_out].name,
                      type="comm", ch_name=str(ch_name), val=val, str=trace_str)
            log_time_series(infos[id_in], res['time'], infos[id_in].state)

        # Overflow detection
        has_overflow = False
        for info in infos:
            for k, v in info.state.items():
                if isinstance(v, (int, float)) and abs(v) > 1e10:
                    has_overflow = True

        if has_overflow:
            log_event(ori_pos=[], type="overflow", str="overflow")
            break
        
    return res

def graph(res, proc_name, tkplot=False, separate=True, variables=None):
    DataState = {}
    temp = res.get("time_series")
    lst = temp.get(proc_name)
    for t in lst:
        state = t.get("state")
        for key in state.keys():
            if variables is not None and key not in variables:
                continue
            if key not in DataState.keys():
                DataState.update({key:([],[])})
            DataState.get(key)[0].append(state.get(key))
            DataState.get(key)[1].append(t.get('time'))
                
    if tkplot:
        app = graph_plot.Graphapp(res)
        app.mainloop()
    else:
        if separate:
            for t in DataState.keys():
                x = DataState.get(t)[1]
                y = DataState.get(t)[0]
                plt.plot(x, y, label=t)
                plt.show()
        else:
            for t in DataState.keys():
                x = DataState.get(t)[1]
                y = DataState.get(t)[0]
                plt.plot(x, y, label=t)
                plt.legend()


def check_comms(infos):
    """Given a list of HCSP infos, check for potential mismatch of
    communication channels.

    """
    # Map communication channels to processes containing them
    comm_in_map, comm_out_map = dict(), dict()
    warnings = []
    for info in infos:
        if info.hp.type == 'parallel':
            continue

        for ch_name, direction in hcsp.get_comm_chs(info.hp):
            if len(ch_name.args) > 0:  # do not check parameterized channels
                continue
            if direction == '?':
                if ch_name not in comm_in_map:
                    comm_in_map[ch_name] = []
                comm_in_map[ch_name].append(info.name)
            else:
                if ch_name not in comm_out_map:
                    comm_out_map[ch_name] = []
                comm_out_map[ch_name].append(info.name)

    for ch_name, hp_names in comm_in_map.items():
        if len(hp_names) >= 2:
            warnings.append("Warning: input %s used in more than one process: %s" % (ch_name, ', '.join(hp_names)))
        if ch_name not in comm_out_map:
            warnings.append("Warning: input channel %s has no corresponding output" % ch_name)
        elif hp_names[0] in comm_out_map[ch_name]:
            warnings.append("Warning: input and output channel %s in the same process" % ch_name)

    for ch_name, hp_names in comm_out_map.items():
        if len(hp_names) >= 2:            
            warnings.append("Warning: output %s used in more than one process: %s" % (ch_name, ', '.join(hp_names)))
        if ch_name not in comm_in_map:
            warnings.append("Warning: output channel %s has no corresponding input" % ch_name)

    return warnings
