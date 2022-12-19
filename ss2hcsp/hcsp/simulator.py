"""Simulation for HCSP programs.

The state is given by a dictionary from variable names to numbers.

"""

import copy
import ast
import math
import random
from decimal import Decimal
from typing import Dict, List, Optional
from scipy.integrate import solve_ivp
from ss2hcsp.hcsp.expr import Expr, AVar, AConst, OpExpr, FunExpr, IfExpr, \
    ListExpr, DictExpr, ArrayIdxExpr, FieldNameExpr, BConst, LogicExpr, \
    RelExpr, true_expr, false_expr, opt_round, get_range, str_of_val
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import parser
import numpy as np

class SimulatorException(Exception):
    """Exception raised during simulation. Indicates an error in the
    HCSP program.
    
    """
    def __init__(self, error_msg):
        self.error_msg = error_msg

class SimulatorAssertionException(Exception):
    """Failure of a test in the HCSP program."""
    def __init__(self, expr, error_msg):
        self.expr = expr
        self.error_msg = error_msg

    def __str__(self):
        res = 'Test %s failed' % self.expr
        if self.error_msg:
            res += ' (%s)' % self.error_msg
        return res


class Frame:
    """Represents a frame on the call stack."""
    def __init__(self, pos, proc_name):
        # Location within the program or procedure
        self.pos = pos

        # Name of the process to be called. Can be None for the main process
        self.proc_name = proc_name

        # Inner position, use for display
        self.innerpos = pos


class Callstack:
    """Represents current call stack during simulation."""
    def __init__(self, pos):
        self.callstack = [Frame(pos, None)]

    def renewinnerpos(self, hp, procs):
        if self.callstack[-1].pos is None:
            self.callstack[-1].innerpos = copy.deepcopy(self.callstack[-1].pos)
        else:
            self.callstack[-1].innerpos = copy.deepcopy(self.callstack[-1].pos)
            # if has procedure, renew cur-place by deleting heads of pos
            if len(self.callstack) > 1:
                curpos = self.callstack[-1].pos
                lastpos = self.callstack[-2].pos
                if curpos is None:
                    self.callstack[-1].innerpos = None
                elif lastpos is None:
                    self.callstack[-1].innerpos = curpos
                else:
                    self.callstack[-1].innerpos = curpos[len(lastpos)+1:]
            # if has recursion, renew cur-place by deleting inner recursion cycles
            pos = self.callstack[-1].pos
            rec_list = []
            length = len(self.callstack[-1].innerpos)
            for i in range(len(pos)-length, len(pos)+1):
                sub_hp = get_pos(hp, pos[:i], procs)
                if sub_hp.type == "recursion":
                    rec_list.append(i)
            if len(rec_list) >= 2:
                self.callstack[-1].innerpos = pos[:rec_list[0]] + pos[rec_list[-1]:]
                self.callstack[-1].innerpos = self.callstack[-1].innerpos[(len(pos)-length):]
 
    def push(self, pos, proc_name):
        # when procedure shift occur, push
        self.callstack.append(Frame(pos, proc_name))
    
    def renew(self, pos):
        # renew pos in same procedure or main part
        self.callstack[-1].pos = pos

    def pop(self):
        if self.callstack:
            self.callstack.pop()
        else:
            raise LookupError('callstack is empty!')

    def top_pos(self):
        return self.callstack[-1].pos

    def top_procname(self):
        return self.callstack[-1].proc_name

    def getinfo(self, hp, procs):
        self.renewinnerpos(hp, procs)
        callstack_info = {
            'innerpos': [],
            'procedure':[]
        }
        index = len(self.callstack) - 1
        while index >= 0:
            innerpos = self.callstack[index].innerpos
            if innerpos is None:
                callstack_info['innerpos'].append('end')
            elif get_pos(hp, self.callstack[-1].pos, procs).type != 'wait':
                callstack_info['innerpos'].append('p' + ','.join(str(p) for p in innerpos))   
            else:
                callstack_info['innerpos'].append('p' + ','.join(str(p) for p in innerpos[:-1]))         
            if self.callstack[index].proc_name is None:
                callstack_info['procedure'].append(self.callstack[index].proc_name)
            else:
                callstack_info['procedure'].append(self.callstack[index].proc_name)
            index = index - 1
        return callstack_info


def start_pos(hp):
    """Returns the starting position for a given program."""
    if hp.type == 'sequence':
        return (0,) + start_pos(hp.hps[0])
    elif hp.type == 'loop':
        return (0,) + start_pos(hp.hp)
    elif hp.type == 'wait':
        return (0,)  # Time already spent in delay
    else:
        return tuple()

def get_pos(hp, pos, procs=None):
    """Obtain the sub-program corresponding to the given position.
    
    procs: mapping from procedure names to HCSP processes.

    """
    assert pos is not None, "get_pos: already reached the end."

    if procs is None:
        procs = dict()

    if hp.type == 'sequence':
        if len(pos) == 0:
            return hp
        return get_pos(hp.hps[pos[0]], pos[1:], procs)
    elif hp.type == 'loop':
        if len(pos) == 0:
            return hp
        else:
            assert pos[0] == 0
        return get_pos(hp.hp, pos[1:], procs)
    elif hp.type == 'wait':
        # assert len(pos) == 1
        return hp
    elif hp.type == 'ode_comm':
        if len(pos) == 0:
            return hp
        else:
            _, out_hp = hp.io_comms[pos[0]]
            return get_pos(out_hp, pos[1:], procs)
    elif hp.type == 'select_comm':
        if len(pos) == 0:
            return hp
        else:
            _, out_hp = hp.io_comms[pos[0]]
            return get_pos(out_hp, pos[1:], procs)
    elif hp.type == 'ite':
        if len(pos) == 0:
            return hp
        elif pos[0] < len(hp.if_hps):
            return get_pos(hp.if_hps[pos[0]][1], pos[1:], procs)
        else:
            assert pos[0] == len(hp.if_hps) and hp.else_hp is not None
            return get_pos(hp.else_hp, pos[1:], procs)
    elif hp.type == 'var':
        if len(pos) == 0:
            return hp
        assert pos[0] == 0
        if hp.name in procs:
            rec_hp = procs[hp.name].hp
            return get_pos(rec_hp, pos[1:], procs)
        else:
            raise SimulatorException("Unrecognized process variable: " + hp.name)
    elif hp.type == 'ichoice':
        if len(pos) == 0:
            return hp
        return get_pos(hp.hps[pos[0]], pos[1:], procs)
    else:
        assert len(pos) == 0
        return hp

def parse_pos(hp, pos):
    """Convert pos in string form to internal representation."""
    if pos == 'end':
        return None
    elif pos == 'start':
        return start_pos(hp)
    
    assert len(pos) > 0 and pos[0] == 'p'
    pos = pos[1:].split(',')
    if len(pos) > 0 and pos[-1].startswith('w'):
        pos = tuple([int(p) for p in pos[:-1]] + [float(pos[-1][1:])])
        assert get_pos(hp, pos).type == 'wait'
    else:
        pos = tuple(int(p) for p in pos)

    return pos

def disp_of_callstack(info):
    return info.callstack.getinfo(info.hp, info.procedures)

class SimInfo:
    """Represents a (non-parallel) HCSP program together with
    additional information on the current execution position and
    the current state.

    The current execution position is represented by a tuple of numbers,
    or None if execution has reached the end.

    """
    def __init__(self, name: str, hp: hcsp.HCSP, *,
                 outputs: Optional[List[hcsp.HCSPOutput]] = None,
                 procedures: Optional[Dict[str, hcsp.Procedure]] = None,
                 functions: Optional[Dict[str, hcsp.Function]] = None,
                 pos="start",
                 state=None):
        """Initializes with starting position as the execution position."""

        # Name of the program
        assert isinstance(name, str)
        self.name: str = name

        # Code for the program
        self.hp: hcsp.HCSP
        if isinstance(hp, str):
            self.hp = parser.hp_parser.parse(hp)
        else:
            self.hp = hp

        # List of output variables
        self.outputs: List[hcsp.HCSPOutput] = []
        if outputs is not None:
            self.outputs = outputs

        # Dictionary of procedure declarations
        if procedures is None:
            procedures = dict()
        assert isinstance(procedures, dict)
        for k, v in procedures.items():
            assert isinstance(k, str) and isinstance(v, hcsp.Procedure)
        self.procedures: Dict[str, hcsp.Procedure] = procedures

        # Dictionary of function declarations
        if functions is None:
            functions = dict()
        assert isinstance(functions, dict)
        for k, v in functions.items():
            assert isinstance(k, str) and isinstance(v, hcsp.Function)
        self.functions: Dict[str, hcsp.Function] = functions
    
        # Current position of execution
        if isinstance(pos, str):
            pos = parse_pos(self.hp, pos)
        else:
            assert isinstance(pos, tuple)
        
        self.callstack = Callstack(pos)

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

    def __str__(self):
        return str({'name': self.name, 'hp': self.hp, 'pos': self.callstack.top_pos(), 'state': self.state, 'reason': self.reason})

    def eval_expr(self, expr):
        """Evaluate the given expression on the current state."""
        if expr is None:
            return None

        if isinstance(expr, AVar):
            # Variable case
            if expr.name not in self.state:
                raise SimulatorException("Uninitialized variable: " + expr.name)

            return self.state[expr.name]

        elif isinstance(expr, AConst):
            # Constant case
            if isinstance(expr.value, Decimal):
                return float(expr.value)
            else:
                return expr.value

        elif isinstance(expr, OpExpr):
            # Arithmetic operations
            if len(expr.exprs) == 1:
                return -self.eval_expr(expr.exprs[0])
            else:
                e1, e2 = self.eval_expr(expr.exprs[0]), self.eval_expr(expr.exprs[1])
                if expr.op == '+':
                    return e1 + e2
                elif expr.op == '-':
                    return e1 - e2
                elif expr.op == '*':
                    return e1 * e2
                elif expr.op == '/':
                    return e1 / e2
                elif expr.op == '%':
                    if isinstance(e2, Decimal):
                        if e2 != int(e2):
                            raise SimulatorException("When evaluating %s: %s is not an integer" % (expr, e2))
                        return round(e1) % int(e2)
                    else:
                        return round(e1) % e2
                elif expr.op == '^':
                    return e1 ** e2
                else:
                    raise SimulatorException("Unrecognized operator %s" % expr.op)

        elif isinstance(expr, FunExpr):
            # Special functions
            args = [self.eval_expr(e) for e in expr.exprs]
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
            elif expr.fun_name == "sin":
                return math.sin(args[0])
            elif expr.fun_name == "push":
                a, b = args
                if not isinstance(a, list):
                    a = [a]
                if not isinstance(b, list):
                    b = [b]
                return a + b
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
            elif expr.fun_name == "del":
                a, b = args
                assert isinstance(a, list)
                del a[b]
                return a
            elif expr.fun_name == "del0":
                a, b = args
                assert isinstance(a, list)
                assert isinstance(b, str)
                procs = []
                for e in a:
                    assert isinstance(e, list) and len(e) == 2  # [prior, process]
                    if e[1] == b:
                        procs.append(e)
                assert len(procs) <= 1
                if len(procs) == 1:
                    c = list(a)
                    c.remove(procs[0])
                    a = list(c)
                return a
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
            elif expr.fun_name == "unidrnd":
                assert len(args) == 1
                if args[0] <= 0:
                    raise SimulatorException('When evaluating %s: %s <= 0' % (expr, args[0]))
                return random.randint(1, args[0])
            elif expr.fun_name == "zeros":
                return np.zeros(tuple(args), dtype=int).tolist()
            elif expr.fun_name == "pi":
                return math.pi

            # Custom functions
            elif expr.fun_name in self.functions:
                f = self.functions[expr.fun_name]
                if len(args) != len(f.vars):
                    raise SimulatorException("When evaluating %s: wrong number of arguments" % expr)
                inst = dict()
                for (var, arg) in zip(f.vars, args):
                    inst[var] = AConst(arg)
                expr2 = f.expr.subst(inst)
                return self.eval_expr(expr2)

            # elif expr.fun_name == "protected_curve":
            #     # assert len(args) == 4
            #     # obs_pos, veh_pos, max_v, min_a = args
            #     a, = args
            #     assert len(a) == 4
            #     obs_pos, veh_pos, max_v, min_a = a
            #     if obs_pos <= 0:
            #         return max_v
            #     assert min_a < 0
            #     distance = obs_pos - veh_pos
            #     if distance > max_v * max_v / (-2 * min_a):
            #         return max_v
            #     elif distance >= 0:
            #         return math.sqrt(-2 * min_a * distance)
            #     else:
            #         return 0
            else:
                raise SimulatorException("When evaluating %s: unrecognized function" % expr)

        elif isinstance(expr, IfExpr):
            cond = self.eval_expr(expr.cond)
            if cond:
                return self.eval_expr(expr.expr1)
            else:
                return self.eval_expr(expr.expr2)

        elif isinstance(expr, ListExpr):
            return list(self.eval_expr(arg) for arg in expr.args)

        elif isinstance(expr, DictExpr):
            return dict((k, self.eval_expr(v)) for k, v in expr.dict.items())

        elif isinstance(expr, ArrayIdxExpr):
            a = self.eval_expr(expr.expr1)
            i = self.eval_expr(expr.expr2)
            if not (isinstance(a, list) and isinstance(i, int)):
                raise SimulatorException('When evaluating %s: type error' % expr)
            if not i < len(a):
                raise SimulatorException('When evaluating %s: array out of bounds error' % expr)
            return a[i]

        elif isinstance(expr, FieldNameExpr):
            a = self.eval_expr(expr.expr)
            if not isinstance(a, dict) or expr.field not in a:
                raise SimulatorException('When evaluating %s: field not found' % expr)
            return a[expr.field]

        elif isinstance(expr, BConst):
            return expr.value

        elif isinstance(expr, LogicExpr):
            if expr.op == "&&":
                return self.eval_expr(expr.exprs[0]) and self.eval_expr(expr.exprs[1])
            elif expr.op == "||":
                return self.eval_expr(expr.exprs[0]) or self.eval_expr(expr.exprs[1])
            elif expr.op == "->":
                return (not self.eval_expr(expr.exprs[0])) or self.eval_expr(expr.exprs[1])
            elif expr.op == "<->":
                return self.eval_expr(expr.exprs[0]) == self.eval_expr(expr.exprs[1])
            elif expr.op == "!":
                return not self.eval_expr(expr.exprs[0])
            else:
                raise NotImplementedError

        elif isinstance(expr, RelExpr):
            a, b = self.eval_expr(expr.expr1), self.eval_expr(expr.expr2)
            if expr.op == "<":
                return a < b
            elif expr.op == ">":
                return a > b
            elif expr.op == "==":
                if isinstance(a, float) or isinstance(b, float):
                    return abs(a - b) < 1e-10
                else:
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
            print('When evaluating %s' % expr)
            raise NotImplementedError

    def eval_channel(self, ch_name):
        """Evaluate channel ch_name at the given state.

        A special case is when one or more indices of the communication
        channel is a bound variable (indicated by variable name starting
        with '_'). In this case we do not modify the index.

        """
        args = []
        for arg in ch_name.args:
            if isinstance(arg, AVar) and arg.name.startswith("_"):
                args.append(arg)
            else:
                args.append(self.eval_expr(arg))
        return hcsp.Channel(ch_name.name, tuple(args))

    def get_ode_delay(self, hp):
        """Obtain the delay needed for the given ODE, starting at the
        given state.
        
        """
        assert hp.type in ('ode', 'ode_comm')

        if hp.constraint == false_expr:
            return 0.0

        if not self.eval_expr(hp.constraint):
            return 0.0

        def get_deriv(name):
            """Returns the derivative of a variable."""
            for var_name, eq in hp.eqs:
                if var_name == name:
                    return eq
            return AConst(0)
            
        def ode_fun(t, y):
            res = []
            # Store previous state
            ori_state = dict()
            for (var_name, _), yval in zip(hp.eqs, y):
                ori_state[var_name] = self.state[var_name]
                self.state[var_name] = yval
            for var_name, expr in hp.eqs:
                res.append(self.eval_expr(expr))
            # Recover previous state
            for var_name, val in ori_state.items():
                self.state[var_name] = val
            return res

        def event_gen(t, y, c):
            # Here c is the constraint.
            # Store previou sstate
            ori_state = dict()
            for (var_name, _), yval in zip(hp.eqs, y):
                ori_state[var_name] = self.state[var_name]
                self.state[var_name] = yval
            if isinstance(c, RelExpr):
                if c.op in ('<', '<='):
                    res = self.eval_expr(c.expr1) - self.eval_expr(c.expr2)
                elif c.op in ('>', '>='):
                    res = self.eval_expr(c.expr2) - self.eval_expr(c.expr1)
                else:
                    print('get_ode_delay: cannot handle constraint %s' % c)
                    raise NotImplementedError
            else:
                print('get_ode_delay: cannot handle constraint %s' % c)
                raise NotImplementedError
            # Recover previous state
            for var_name, val in ori_state.items():
                self.state[var_name] = val
            return res

        # Compute set of variables that remain zero
        zero_vars = []

        def is_zero(t):
            """Whether the given expression simplifies to 0."""
            if isinstance(t, OpExpr) and t.op == '*':
                return is_zero(t.exprs[0]) or is_zero(t.exprs[1])
            elif isinstance(t, OpExpr) and t.op == '/':
                return is_zero(t.exprs[0])
            elif isinstance(t, AConst):
                return t.value == 0
            elif isinstance(t, AVar):
                return t.name in zero_vars
            else:
                return False

        # List of variables that are guaranteed to stay zero.
        found = True
        while found:
            found = False
            for name in self.state:
                if name not in zero_vars and is_zero(get_deriv(name)) and self.state[name] == 0:
                    zero_vars.append(name)
                    found = True

        # List of variables that are changed.
        changed_vars = [var_name for var_name, eq in hp.eqs if not is_zero(eq)]

        def occur_var(e, var_name):
            if isinstance(e, RelExpr):
                return occur_var(e.expr1, var_name) or occur_var(e.expr2, var_name)
            if isinstance(e, AVar):
                return e.name == var_name
            elif isinstance(e, AConst):
                return False
            elif isinstance(e, (OpExpr, LogicExpr, FunExpr)):
                return any(occur_var(sub_e, var_name) for sub_e in e.exprs)
            else:
                print('occur_var:', e)
                raise NotImplementedError

        def expr_unchanged(e):
            # The expression does not change in the ODE
            return all(not occur_var(e, var_name) for var_name in changed_vars)

        def test_cond(e):
            # Case where the condition is a disjunction: take the maximum of
            # two delays
            if isinstance(e, LogicExpr) and e.op == '||':
                delay1 = test_cond(e.exprs[0])
                delay2 = test_cond(e.exprs[1])
                return max(delay1, delay2)
            
            # Case where the condition is a conjunction: take the minimum of
            # two delays
            if isinstance(e, LogicExpr) and e.op == '&&':
                delay1 = test_cond(e.exprs[0])
                delay2 = test_cond(e.exprs[1])
                return min(delay1, delay2)

            # Condition never changes
            if expr_unchanged(e):
                if self.eval_expr(e):
                    return 100
                else:
                    return 0

            # Condition comparing a variable to a constant, where the derivative
            # of the variable is also a constant.
            if (isinstance(e, RelExpr) and e.op in ('<', '<=', '>', '>=') and
                isinstance(e.expr1, AVar) and expr_unchanged(e.expr2) and
                expr_unchanged(get_deriv(e.expr1.name))):
                deriv = self.eval_expr(get_deriv(e.expr1.name))
                diff = self.eval_expr(e.expr2) - self.eval_expr(e.expr1)
                if e.op in ('<', '<='):
                    if diff < 0:
                        return 0.0
                    return min(diff / deriv, 100.0) if deriv > 0 else 100.0
                else:
                    if diff > 0:
                        return 0.0
                    return min(diff / deriv, 100.0) if deriv < 0 else 100.0        

            # If the condition is false initially, return 0
            if not self.eval_expr(e):
                return 0

            y0 = []
            for var_name, _ in hp.eqs:
                y0.append(self.state[var_name])

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

    def step_pos(self):
        """Execute a (non-communicating) step in the program. Returns the
        new position, or None if steping to the end.
        
        """
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
                assert len(pos) > 0
                # Step inside the loop
                assert pos[0] == 0
                sub_step = helper(hp.hp, pos[1:])
                if sub_step is None:
                    if hp.constraint != true_expr and not self.eval_expr(hp.constraint):
                        return None
                    else:
                        return (0,) + start_pos(hp.hp)
                else:
                    return (0,) + sub_step
            elif hp.type == 'delay':
                assert len(pos) == 1
                return None
            elif hp.type == 'var':
                if hp.name in self.procedures:
                    rec_hp = self.procedures[hp.name].hp
                else:
                    raise SimulatorException("Unrecognized process variable: " + hp.name)

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
                if len(pos) == 0:
                    return None
                if pos[0] < len(hp.if_hps):
                    _, sub_hp = hp.if_hps[pos[0]]
                    sub_step = helper(sub_hp, pos[1:])
                else:
                    assert pos[0] == len(hp.if_hps) and hp.else_hp is not None
                    sub_step = helper(hp.else_hp, pos[1:])
            
                if sub_step is None:
                    return None
                else:
                    return (pos[0],) + sub_step
            else:
                return None

        pos = helper(self.hp, self.callstack.top_pos())
        if self.callstack.top_procname() is not None:
            self.callstack.pop()
        self.callstack.renew(pos)

    def exec_assign(self, lname, val, hp):
        """Make the copy of val into lname. Note deep-copy need to be
        used to avoid aliasing.

        """
        if isinstance(lname, AVar):
            self.state[lname.name] = copy.deepcopy(val)
        elif isinstance(lname, ArrayIdxExpr):
            v = self.eval_expr(lname.expr1)
            idx = self.eval_expr(lname.expr2)
            if not isinstance(v, list):
                raise SimulatorException('%s is not a list, when executing %s' % (v, hp))
            if idx >= len(v):
                raise SimulatorException('Array index %s out of bounds, when executing %s' % (idx, hp))
            v[idx] = copy.deepcopy(val)
        elif isinstance(lname, FieldNameExpr):
            v = self.eval_expr(lname.expr)
            if lname.field not in v:
                raise SimulatorException('Field %s does not exist, when executing %s' % (lname.field, hp))
            v[lname.field] = copy.deepcopy(val)
        elif lname is None:
            pass
        else:
            raise SimulatorException('Evaluating assignment %s := %s: not implemented' % (lname, val))

    def exec_step(self,infos):
        """Compute a single process for one step.

        If there is a step to be taken, return "step".

        If there is no step to be taken, return the reason for
        the wait: either the program must delay for some time
        ("delay", d), or it is waiting for one of the communication
        events ("comm", [...]), each communication event is described
        by a channel name and direction (e.g. ("p2c", "!") or ("c2p", "?"))).
        
        """

        procedures_list = {}
        for info in infos:
            procedures_list.update(info.procedures)
         
        cur_hp = get_pos(self.hp, self.callstack.top_pos(), procedures_list)
        if cur_hp.type == "skip":
            self.step_pos()
            self.reason = None
            
        elif cur_hp.type == "assign":
            # Perform assignment
            if isinstance(cur_hp.var_name, Expr):
                self.exec_assign(cur_hp.var_name, self.eval_expr(cur_hp.expr), cur_hp)
            else:
                # Multiple assignment
                val = self.eval_expr(cur_hp.expr)
                assert isinstance(val, list) and len(val) == len(cur_hp.var_name), \
                    "Multiple assignment: value not a list or of the wrong length."
                for i, s in enumerate(cur_hp.var_name):
                    if s != AVar('_'):
                        self.exec_assign(s, val[i], cur_hp)
            
            self.step_pos()
            self.reason = None

        elif cur_hp.type == "assert":
            # Evaluate an assertion. If fails, immediate stop the execution
            # (like a runtime error).
            if not self.eval_expr(cur_hp.bexpr):
                error_msg = ''
                for msg in cur_hp.msgs:
                    val = self.eval_expr(msg)
                    error_msg += str(val)
                raise SimulatorException(error_msg)
            else:
                self.step_pos()
                self.reason = None

        elif cur_hp.type == "test":
            # Evaluate a test. If fails, output a warning but do not stop
            # the execution.
            self.step_pos()
            self.reason = None
            if not self.eval_expr(cur_hp.bexpr):
                warning_expr = ''
                for msg in cur_hp.msgs:
                    val = self.eval_expr(msg)
                    warning_expr += str(val)
                raise SimulatorAssertionException(cur_hp.bexpr, warning_expr)

        elif cur_hp.type == "log":
            # Output a log item to the simulator
            self.step_pos()
            str_pat = self.eval_expr(cur_hp.pattern)
            if not isinstance(str_pat, str):
                str_pat = str(str_pat)
            vals = tuple(self.eval_expr(e) for e in cur_hp.exprs)
            try:
                log_expr = str_pat % vals
            except TypeError:
                raise SimulatorException("When evaluating %s %% %s, wrong number of arguments" \
                    % (str_pat, vals))
            self.reason = {"log": log_expr}

        elif cur_hp.type == "recursion":
            # Enter into recursion
            pos=self.callstack.top_pos() + (0,) + start_pos(cur_hp.hp)
            self.callstack.renew(pos)
            self.reason = None

        elif cur_hp.type == "var":
            # Return to body of recursion
            for i in range(len(self.callstack.top_pos())):
                hp = get_pos(self.hp, self.callstack.top_pos()[:i], procedures_list)
                if hp.type == 'recursion' and hp.entry == cur_hp.name:
                    pos = self.callstack.top_pos() + (0,) + start_pos(hp)
                    self.callstack.renew(pos)
                    self.reason = None
                    return

            # Otherwise, enter code of procedure
            if cur_hp.name in procedures_list:
                proc = procedures_list[cur_hp.name]
                pos = self.callstack.top_pos() + (0,) + start_pos(proc.hp)
                self.callstack.push(pos, cur_hp.name)
                self.reason = None
                return

            # Otherwise, not a recursion or procedure call
            raise SimulatorException("Unrecognized process variable: " + cur_hp.name)

        elif cur_hp.type == "input_channel":
            # Waiting for input
            self.reason = {"comm": [(self.eval_channel(cur_hp.ch_name), "?")]}

        elif cur_hp.type == "output_channel":
            # Waiting for someone to receive output
            self.reason = {"comm": [(self.eval_channel(cur_hp.ch_name), "!")]}

        elif cur_hp.type == "wait":
            # Waiting for some number of seconds
            delay = self.eval_expr(cur_hp.delay) - self.callstack.top_pos()[-1]
            if delay < 0:
                raise SimulatorException("When executing %s: delay %s less than zero" % (cur_hp, delay))
            self.reason = {"delay": delay}

        elif cur_hp.type == "ode":
            # Find delay of ODE
            delay = self.get_ode_delay(cur_hp)
            assert delay >= 0, "exec_step: delay for ode less than zero"
            self.reason = {"delay": delay}

        elif cur_hp.type == "ode_comm":
            # Run ODE until one of the communication events (or the boundary)
            comms = []
            for io_comm, rest in cur_hp.io_comms:
                if io_comm.type == "input_channel":
                    comms.append((self.eval_channel(io_comm.ch_name), "?"))
                else:
                    comms.append((self.eval_channel(io_comm.ch_name), "!"))
            self.reason = {"comm": comms}
            if cur_hp.constraint != true_expr:
                delay = self.get_ode_delay(cur_hp)
                assert delay >= 0, "exec_step: delay for ode_comm less than zero"
                self.reason["delay"] = delay

        elif cur_hp.type == "select_comm":
            # Waiting for one of the input/outputs
            comms = []
            for comm_hp, out_hp in cur_hp.io_comms:
                if comm_hp.type == "input_channel":
                    comms.append((self.eval_channel(comm_hp.ch_name), "?"))
                elif comm_hp.type == "output_channel":
                    comms.append((self.eval_channel(comm_hp.ch_name), "!"))
                else:
                    raise NotImplementedError
            self.reason = {"comm": comms}

        elif cur_hp.type == 'ite':
            # Find the first condition that evaluates to true
            for i, (cond, sub_hp) in enumerate(cur_hp.if_hps):
                if self.eval_expr(cond):
                    pos = self.callstack.top_pos() + (i,) + start_pos(sub_hp)
                    self.callstack.renew(pos)
                    self.reason = None
                    return

            if cur_hp.else_hp is None:
                # If no else branch exists, skip the ITE block
                self.step_pos()
                self.reason = None
            else:
                # Otherwise, go to the else branch
                pos = self.callstack.top_pos() + (len(cur_hp.if_hps),) + start_pos(cur_hp.else_hp)
                self.callstack.renew(pos)
                self.reason = None

        else:
            raise NotImplementedError

    def exec_input_comm(self, ch_name, x, inst=None):
        """Perform an input communication on a given hybrid program.

        The input communication is specified by the channel name
        and input value.

        """
        cur_hp = get_pos(self.hp, self.callstack.top_pos(), self.procedures)

        if inst is not None:
            self.state.update(inst)

        if cur_hp.type == "input_channel":
            assert self.eval_channel(cur_hp.ch_name) == ch_name
            if cur_hp.var_name is None:
                assert x is None
            else:
                assert x is not None
                self.exec_assign(cur_hp.var_name, x, cur_hp)
            self.step_pos()

        elif cur_hp.type == "ode_comm":
            for i, (comm_hp, out_hp) in enumerate(cur_hp.io_comms):
                if comm_hp.type == "input_channel" and self.eval_channel(comm_hp.ch_name) == ch_name:
                    self.exec_assign(comm_hp.var_name, x, comm_hp)
                    pos=self.callstack.top_pos() + (i,) + start_pos(out_hp)
                    self.callstack.renew(pos)
                    return

            # Communication must be found among the interrupts
            assert False

        elif cur_hp.type == "select_comm":
            for i, (comm_hp, out_hp) in enumerate(cur_hp.io_comms):
                if comm_hp.type == "input_channel" and self.eval_channel(comm_hp.ch_name) == ch_name:
                    if comm_hp.var_name is None:
                        if x is not None:
                            raise SimulatorException(comm_hp, "input value is not None")
                    else:
                        if x is None:
                            raise SimulatorException(comm_hp, "input value is None")
                        self.exec_assign(comm_hp.var_name, x, comm_hp)
                    pos = self.callstack.top_pos() + (i,) + start_pos(out_hp)
                    self.callstack.renew(pos)
                    return

            # Communication must be found among the choices
            assert False

        else:
            assert False

    def exec_output_comm(self, ch_name, inst=None):
        """Perform an output communication on a given hybrid program.

        The output communication is specified by the channel name.

        Returns the output value.

        """
        cur_hp = get_pos(self.hp, self.callstack.top_pos(), self.procedures)

        if inst is not None:
            self.state.update(inst)

        if cur_hp.type == "output_channel":
            assert self.eval_channel(cur_hp.ch_name) == ch_name
            self.step_pos()
            return self.eval_expr(cur_hp.expr)

        elif cur_hp.type == "ode_comm":
            for i, (comm_hp, out_hp) in enumerate(cur_hp.io_comms):
                if comm_hp.type == "output_channel" and self.eval_channel(comm_hp.ch_name) == ch_name:
                    val = self.eval_expr(comm_hp.expr)
                    pos = self.callstack.top_pos() + (i,) + start_pos(out_hp)
                    self.callstack.renew(pos)
                    return val

            # Communication must be found among the interrupts
            assert False

        elif cur_hp.type == "select_comm":
            for i, (comm_hp, out_hp) in enumerate(cur_hp.io_comms):
                if comm_hp.type == "output_channel" and self.eval_channel(comm_hp.ch_name) == ch_name:
                    pos = self.callstack.top_pos() + (i,) + start_pos(out_hp)
                    self.callstack.renew(pos)
                    return self.eval_expr(comm_hp.expr)

            # Communication must be found among the choices
            assert False

        else:
            assert False

    def exec_delay(self, delay, *, time_series=None):
        """Perform delay on the hybrid program of the given length."""
        if self.callstack.top_pos() is None:
            return

        cur_hp = get_pos(self.hp, self.callstack.top_pos(), self.procedures)
        if cur_hp.type in ["input_channel", "output_channel", "select_comm"]:
            pass

        elif cur_hp.type == "wait":
            assert 'delay' in self.reason
            assert self.reason['delay'] >= delay
            if self.reason['delay'] == delay:
                self.step_pos()
            else:
                pos=self.callstack.top_pos()[:-1] + (self.callstack.top_pos()[-1] + delay,)
                self.callstack.renew(pos)

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
                    # Store previous state
                    ori_state = dict()
                    for (var_name, _), yval in zip(cur_hp.eqs, y):
                        ori_state[var_name] = self.state[var_name]
                        self.state[var_name] = yval
                    for var_name, expr in cur_hp.eqs:
                        res.append(self.eval_expr(expr))
                    # Restore previous state
                    for var_name, val in ori_state.items():
                        self.state[var_name] = val
                    return res
                
                y0 = []
                for var_name, _ in cur_hp.eqs:
                    if not isinstance(self.state[var_name], (int, float)):
                        raise SimulatorException('When executing %s, initial value is not a number' % cur_hp)
                    y0.append(self.state[var_name])

                t_eval = [x for x in get_range(0, delay)]
                sol = solve_ivp(ode_fun, [0, delay], y0, t_eval=t_eval, rtol=1e-5, atol=1e-7)

                # Store time series
                if time_series is not None:
                    for i in range(len(sol.t)):
                        for (var_name, _), yval in zip(cur_hp.eqs, sol.y):
                            self.state[var_name] = opt_round(yval[i])
                        time_series.append({'time': t_eval[i], 'state': copy.deepcopy(self.state)})

                # Update state with values at the end
                for i, (var_name, _) in enumerate(cur_hp.eqs):
                    self.state[var_name] = opt_round(sol.y[i][-1])

            if finish_ode:
                self.step_pos()
            else:
                if 'delay' in self.reason:
                    self.reason['delay'] -= delay

        else:
            assert False

def match_channel(out_ch: hcsp.Channel, in_ch: hcsp.Channel):
    """Matching between two channels.
    
    If there is no match, return None. Otherwise, return a pair of
    dictionaries out_arg, in_arg, containing the mapping from variables
    in the output and input channels to values, respectively.

    """
    if out_ch.name != in_ch.name or len(out_ch.args) != len(in_ch.args):
        return None
    inst_out, inst_in = dict(), dict()
    for out_arg, in_arg in zip(out_ch.args, in_ch.args):
        if isinstance(out_arg, AVar):
            if isinstance(in_arg, AConst):
                inst_out[out_arg.name] = in_arg.value
            elif isinstance(in_arg, AVar):
                return None  # both sides are variables
            else:
                raise TypeError
        elif isinstance(out_arg, AConst):
            if isinstance(in_arg, AConst):
                if out_arg != in_arg:
                    return None
            elif isinstance(in_arg, AVar):
                inst_in[in_arg.name] = out_arg.value
            else:
                raise TypeError
        else:
            raise TypeError
    return inst_out, inst_in

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
    for out_ch in out_ready:
        for in_ch in in_ready:
            match_res = match_channel(out_ch, in_ch)
            if match_res is not None:
                out_inst, in_inst = match_res
                assert in_ch.subst(in_inst) == out_ch.subst(out_inst)  # instantiated channel
                return ('comm', out_ready[out_ch], in_ready[in_ch], out_ch, in_ch, out_inst, in_inst)

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


def exec_parallel(infos: List[SimInfo], *, num_io_events=None, num_steps=3000, num_show=None,
                  show_interval=None, start_event=None, show_event_only=False, verbose=True):
    """Given a list of SimInfo objects, execute the hybrid programs
    in parallel on their respective states for the given number steps.

    The returned result is a dictionary containing the result of the
    run. The entries are:

    time - total time spent in the model.

    trace - list of events. Each event contains information about the
        event, as well as the current state after executing the event.

    time_series - records evolution of variables in each program by time.
        This is a dictionary indexed by names of programs.

    statemap - record of all state. 
    """
    # Overall returned result
    res = {
        'time': 0,    # Current time
        'trace': [],  # List of events
        'time_series': {},  # Evolution of variables, indexed by program
        'events': [],  # Concise list of event strings
        'statemap': dict()  # dict of all state
    }

    def log_event(ori_pos, **xargs):
        """Log the given event, starting with the given event info."""
        nonlocal num_event
        num_event += 1
        if verbose:
            if num_event % 10000 == 0:
                print('i:', num_event)

        new_event = xargs
        # Process log/warning/error string
        if 'str' in new_event:
            new_event['str'] = new_event['str'].encode('utf-8').decode('unicode_escape').strip()

        # Append the first 2000 events
        if num_event <= 2000:
            res['events'].append(new_event['str'])

        # Determine whether to append the current event
        if new_event['type'] != 'error':
            if num_show is not None and len(res['trace']) >= num_show + 1:
                return
            if show_interval is not None and (num_event - 1) % show_interval != 0:
                return

        # Fill in additional information about the event
        new_event['id'] = num_event - 1
        new_event['time'] = res['time']
        new_event['ori_pos'] = ori_pos

        # Fill in information about current position
        cur_info = dict()
        for info in infos:
            info_callstack = disp_of_callstack(info)
            fst_state = str(info.state)
            if fst_state in res['statemap']:
                state_num = res['statemap'].get(fst_state)
            else:
                state_num = len(res['statemap'])
                res['statemap'][fst_state] = state_num
            cur_info[info.name] = {'callstack': info_callstack, 'statenum': state_num}
        new_event['infos'] = cur_info
        # Finally add to trace
        if not show_event_only or new_event['type'] != 'step':
            res['trace'].append(new_event)

    def log_time_series(info: SimInfo, time, state):
        """Log the given time series for program with the given name."""
        if info.name not in res['time_series']:
            return
        new_entry = {
            "time": time,
            "event": len(res['trace']),
            "state": dict()
        }
        for output in info.outputs:
            if output.expr is None:
                if output.varname in state:
                    v = state[output.varname]
                    if isinstance(v, (int, float)):
                        new_entry['state'][output.varname] = v
                    elif isinstance(v, list):
                        for i, val in enumerate(v):
                            new_entry['state'][output.varname+'['+str(i)+']'] = val
            else:
                try:
                    v = eval_expr(output.expr, state)
                    if isinstance(v, (int, float)):
                        new_entry['state'][output.varname] = v
                    elif isinstance(v, list):
                        for i, val in enumerate(v):
                            new_entry['state'][output.varname+'['+str(i)+']'] = val
                except SimulatorException:
                    pass

        series = res['time_series'][info.name]
        if len(series) == 0 or new_entry != series[-1]:
            series.append(new_entry)

    if start_event:
        # If has a starting event, modify starting position accordingly
        num_event = start_event['id'] + 1
        res['time'] = start_event['time']
        for info in infos:
            pos = parse_pos(info.hp, start_event['infos'][info.name]['pos'])
            info.callstack.renew(pos)
            info.state = start_event['infos'][info.name]['state']

    else:
        # Otherwise use default starting position
        num_event = 0

        # List of processes that have been updated in the last round.
        start_pos = dict((info.name, disp_of_callstack(info)) for info in infos)

        # Record event and time series at the beginning.
        log_event(ori_pos=start_pos, type="start", str="start")
        for info in infos:
            log_time_series(info, 0, info.state)

        # Initialize time_series
        for info in infos:
            if info.outputs is None or len(info.outputs) > 0:
                # Has some variable to output
                res['time_series'][info.name] = []

    start_id = num_event
    if num_io_events is None:
        num_io_events = num_steps

    for _ in range(num_io_events):
        # Iterate over the processes, apply exec_step to each until
        # stuck, find the stopping reasons.
        for info in infos:
            while info.callstack.top_pos() is not None and not num_event >= start_id + num_steps:
                ori_pos = {info.name: disp_of_callstack(info)}
                try:
                    info.exec_step(infos)
                except SimulatorAssertionException as e:
                    if 'warning' not in res:
                        info.reason = {'warning': str(e)}
                        res['warning'] = (res['time'], str(e))
                except SimulatorException as e:
                    info.reason = {'error': str(e)}
                    res['warning'] = (res['time'], str(e))

                if info.reason is None:
                    log_event(ori_pos=ori_pos, type="step", str="step")
                    log_time_series(info, res['time'], info.state)
                elif 'log' in info.reason:
                    log_event(ori_pos=ori_pos, type="log", str='log ' + info.reason['log'])
                elif 'warning' in info.reason:
                    log_event(ori_pos=ori_pos, type="warning", str="warning: " + info.reason['warning'])
                elif 'error' in info.reason:
                    log_event(ori_pos=ori_pos, type="error", str="error: " + info.reason['error'])
                    break
                else:
                    break

            if info.callstack.top_pos() is None:
                info.reason = {'end': None}
        if num_event >= start_id + num_steps:
            break

        event = extract_event(infos)
        if event == "deadlock":
            log_event(ori_pos=dict(), type="deadlock", str="deadlock")
            break
        elif event[0] == "error":
            break
        elif event[0] == "delay":
            _, min_delay, delay_pos = event
            assert min_delay >= 0, "min_delay %s less than zero" % min_delay
            ori_pos = dict((infos[p].name, disp_of_callstack(infos[p])) for p in delay_pos)

            trace_str = "delay %s" % str(round(min_delay, 3))
            all_series = []
            for info in infos:
                series = []
                info.exec_delay(min_delay, time_series=series)
                for entry in series:
                    log_time_series(info, res['time'] + entry['time'], entry['state'])
                log_time_series(info, res['time'] + min_delay, info.state)

            log_event(ori_pos=ori_pos, type="delay", delay_time=min_delay, str=trace_str)
            res['time'] += min_delay
        else:  # event[0] == "comm"
            _, id_out, id_in, out_ch, in_ch, inst_out, inst_in = event
            ori_pos = {infos[id_out].name: disp_of_callstack(infos[id_out]),
                       infos[id_in].name: disp_of_callstack(infos[id_in])}
            try:
                val = infos[id_out].exec_output_comm(out_ch, inst=inst_out)
                infos[id_in].exec_input_comm(in_ch, val, inst=inst_in)
            except SimulatorException as e:
                log_event(ori_pos=ori_pos, type="error", str="error: " + str(e))
                res['warning'] = (res['time'], str(e))
                break

            val_str = str_of_val(val)
            if val_str != "":
                val_str = " " + val_str

            ch_name = out_ch.subst(inst_out)
            trace_str = "IO %s%s" % (ch_name, val_str)
            log_event(ori_pos=ori_pos, inproc=infos[id_in].name, outproc=infos[id_out].name,
                      type="comm", ch_name=str(ch_name), val=val, str=trace_str)
            log_time_series(infos[id_in], res['time'], infos[id_in].state)

        # Overflow detection
        has_overflow = False
        for info in infos:
            for k, v in info.state.items():
                if isinstance(v, (int, float)) and abs(v) > 1e10:
                    has_overflow = True

        if has_overflow:
            log_event(ori_pos=dict(), type="overflow", str="overflow")
            break

    # Finally, exchange key and value, and change state back into dict in res['statemap']
    statemap = dict()
    for key, value in res['statemap'].items():
        state = ast.literal_eval(key)
        statemap[value] = state
    res['statemap'] = statemap
    return res

def get_comm_maps(comm_in_map,comm_out_map,hp,name):
    for ch_name, direction in hcsp.get_comm_chs(hp):
        # do not check channels with vars and number in args
        hasvar = False
        for arg in ch_name.args:
            if(str(arg)[0] != '_' and str(arg) != 'run_now'):
                if isinstance(arg, AVar):
                    hasvar = True
        if hasvar:
            continue

        if direction == '?':
            if ch_name not in comm_in_map:
                comm_in_map[ch_name] = []
            comm_in_map[ch_name].append(name)
        else:
            if ch_name not in comm_out_map:
                comm_out_map[ch_name] = []
            comm_out_map[ch_name].append(name)
    return comm_in_map,comm_out_map

def instantation(comm_map_A, comm_map_B):
    # instanation of comm_map_A with comm_map_B
    new_map = {}
    deletechs = []
    for in_ch_name in comm_map_A.keys():
        hasunderline = False
        for i in range(len(in_ch_name.args)):
            if str(in_ch_name.args[i])[0] == '_'  or str(in_ch_name.args[i]) == 'run_now':
                hasunderline = True
                arg_rank = i
        if(hasunderline):
            for out_ch_name in comm_map_B.keys():
                samechannel = True
                if in_ch_name.name != out_ch_name.name:
                    continue
                if len(in_ch_name.args) != len(out_ch_name.args):
                    continue
                for i in range(len(out_ch_name.args)):
                    if i == arg_rank:
                        continue
                    if str(in_ch_name.args[i]) != str(out_ch_name.args[i]) \
                            and str(in_ch_name.args[i])[0] != '_'  \
                            and str(in_ch_name.args[i]) != 'run_now' \
                            and str(out_ch_name.args[i])[0] != '_'\
                            and str(out_ch_name.args[i]) != 'run_now':
                        samechannel = False
                if(samechannel):
                    new_map[out_ch_name] = comm_map_B[out_ch_name]
                    deletechs.append(in_ch_name)
    instantedchs =[]
    for k, v in new_map.items():
        comm_map_A[k] = v
        instantedchs.append(k)
    for ch in list(set(deletechs)):
        comm_map_A.pop(ch)
    return comm_map_A,comm_map_B,instantedchs

def check_comms(infos: List[hcsp.HCSPInfo]):
    """Given a list of HCSP infos, check for potential mismatch of
    communication channels.

    """
    # Map communication channels to processes containing them
    comm_in_map, comm_out_map = dict(), dict()
    warnings = []
    for info in infos:
        if info.hp.type == 'parallel':
            continue
        comm_in_map, comm_out_map = get_comm_maps(comm_in_map,comm_out_map,info.hp,info.name)
        if len(info.procedures) != 0:
            for key, procedure in info.procedures.items():
                comm_in_map, comm_out_map = get_comm_maps(comm_in_map,comm_out_map,procedure.hp,info.name)
    
    instantedchs=[]
    comm_in_map,comm_out_map,chs=instantation(comm_in_map,comm_out_map)
    instantedchs.extend(chs)
    comm_out_map,comm_in_map,chs=instantation(comm_out_map,comm_in_map)
    instantedchs.extend(chs)
    instantedchs = list(set(instantedchs))

    for ch_name, hp_names in comm_in_map.items():
        if len(hp_names) >= 2:
            warnings.append("Warning: input %s used in more than one process: %s" % (ch_name, ', '.join(hp_names)))
        if ch_name not in comm_out_map:
            warnings.append("Warning: input channel %s has no corresponding output" % ch_name)
        elif (hp_names[0] in comm_out_map[ch_name]) \
            and (ch_name not in instantedchs):
            warnings.append("Warning: input and output channel %s in the same process" % ch_name)

    for ch_name, hp_names in comm_out_map.items():
        if len(hp_names) >= 2:            
            warnings.append("Warning: output %s used in more than one process: %s" % (ch_name, ', '.join(hp_names)))
        if ch_name not in comm_in_map:
            warnings.append("Warning: output channel %s has no corresponding input" % ch_name)

    return warnings


# Some convenient functions from simulator
def eval_expr(e, state):
    return SimInfo("P1", hcsp.Skip(), state=state).eval_expr(e)
