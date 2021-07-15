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
    RelExpr, true_expr, false_expr, opt_round, get_range, split_disj, str_of_val
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import parser
from ss2hcsp.hcsp import pprint
from ss2hcsp.hcsp import graph_plot
import numpy as np


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
        if isinstance(eval_expr(expr.exprs[0], state), str):
            res = ""
            for s, e in zip(expr.signs, expr.exprs):
                if s == '+':
                    res += eval_expr(e, state)
                else:
                    raise SimulatorException("Type error when evaluating %s" % expr)
        else:
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
        elif expr.fun_name == "del_proc":
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
                raise SimulatorException('When evaluating %s: %s > %s' % (expr, args[0], args[1]))
            return random.randint(1, args[0])
        elif expr.fun_name == "zeros":
            if len(args) == 3:
                return np.zeros((args[0],args[1],args[2]),dtype=int).tolist()
        elif expr.fun_name == "protected_curve":
            # assert len(args) == 4
            # obs_pos, veh_pos, max_v, min_a = args
            a, = args
            assert len(a) == 4
            obs_pos, veh_pos, max_v, min_a = a
            if obs_pos <= 0:
                return max_v
            assert min_a < 0
            distance = obs_pos - veh_pos
            if distance > max_v * max_v / (-2 * min_a):
                return max_v
            elif distance >= 0:
                return math.sqrt(-2 * min_a * distance)
            else:
                return 0
        else:
            raise SimulatorException("When evaluating %s: unrecognized function" % expr)

    elif isinstance(expr, ModExpr):
        multiple = 1000
        return (round(eval_expr(expr.expr1, state) * multiple) %
                round(eval_expr(expr.expr2, state) * multiple)) / multiple

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
        if not isinstance(a, dict) or expr.field not in a:
            raise SimulatorException('When evaluating %s: field not found' % expr)
        return a[expr.field]

    elif isinstance(expr, BConst):
        return expr.value

    elif isinstance(expr, LogicExpr):
        # a = eval_expr(expr.expr1, state)
        # b = eval_expr(expr.expr2, state)
        if expr.op == "&&":
            return eval_expr(expr.expr1, state) and eval_expr(expr.expr2, state)
        elif expr.op == "||":
            return eval_expr(expr.expr1, state) or eval_expr(expr.expr2, state)
        elif expr.op == "-->":
            return (not eval_expr(expr.expr1, state)) or eval_expr(expr.expr2, state)
        elif expr.op == "<-->":
            return eval_expr(expr.expr1, state) == eval_expr(expr.expr2, state)
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
    """Evaluate channel ch_name at the given state.

    A special case is when one or more indices of the communication channel
    is a bound variable. In this case we do not modify the index.

    """
    args = []
    for arg in ch_name.args:
        if isinstance(arg, AVar) and arg.name.startswith("_"):
            args.append(arg)
        else:
            args.append(eval_expr(arg, state))
    return hcsp.Channel(ch_name.name, tuple(args))

def get_ode_delay(hp, state):
    """Obtain the delay needed for the given ODE, starting at the
    given state.
    
    """
    assert hp.type in ('ode', 'ode_comm')

    if hp.constraint == false_expr:
        return 0.0

    if not eval_expr(hp.constraint, state):
        return 0.0

    def get_deriv(name):
        """Returns the derivative of a variable."""
        for var_name, eq in hp.eqs:
            if var_name == name:
                return eq
        return AConst(0)
        
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
                print('get_ode_delay: cannot handle constraint %s' % c)
                raise NotImplementedError
        else:
            print('get_ode_delay: cannot handle constraint %s' % c)
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

    # List of variables that are guaranteed to stay zero.
    found = True
    while found:
        found = False
        for name in state:
            if name not in zero_vars and is_zero(get_deriv(name)) and state[name] == 0:
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

        # Condition comparing a variable to a constant, where the derivative
        # of the variable is also a constant.
        if (isinstance(e, RelExpr) and e.op in ('<', '<=', '>', '>=') and
            isinstance(e.expr1, AVar) and expr_unchanged(e.expr2) and
            expr_unchanged(get_deriv(e.expr1.name))):
            deriv = eval_expr(get_deriv(e.expr1.name), state)
            diff = eval_expr(e.expr2, state) - eval_expr(e.expr1, state)
            if e.op in ('<', '<='):
                if diff < 0:
                    return 0.0
                return min(diff / deriv, 100.0) if deriv > 0 else 100.0
            else:
                if diff > 0:
                    return 0.0
                return min(diff / deriv, 100.0) if deriv < 0 else 100.0        

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

class Frame:
    def __init__(self,pos=None,proc=None,curhp=None):
        self.pos=pos
        self.proc=proc #hcsp.Procedure
        self.curhp=curhp
        self.innerpos=[]
        self.renewinnerpos()
    
    def renewinnerpos(self):
        if self.pos is None:
            self.innerpos=None
        elif len(self.pos)==0:
            self.innerpos=None
        else:
            self.innerpos=self.pos[-1]
class Callstack:
    def __init__(self,pos,proc,curhp):
        self.callstack=[Frame(pos,proc,curhp)]    
        
    def push(self,pos,proc):
        # when percedure shift occur,push
        self.callstack.append(Frame(pos,proc))
        self.callstack[-1].renewinnerpos()
    
    def renew(self,pos,curhp):
        # renew pos in same percedure or main part
        self.callstack[-1].pos=pos
        self.callstack[-1].renewinnerpos()
        self.callstack[-1].curhp=curhp

    def pop(self):
        if self.callstack:
            self.callstack.pop()
        else:
            raise LookupError('callstack is empty!')

    def top_pos(self):
        return self.callstack[-1].pos

    def top_procedure(self):
        return self.callstack[-1].proc

    def top_hp(self):
        return self.callstack[-1].curhp

    def top_innerpos(self):
        return self.callstack[-1].innerpos    
    def getinfo(self):
        callstack_info={
            'procedure':[],
            'hp':[]
        }
        stack=copy.deepcopy(self.callstack)
        while len(stack.callstack)!=0:
            callstack_info['pos'].append(stack.top_pos())
            callstack_info['innerpos'].append(stack.top_innerpos())
            callstack_info['procedure'].append(stack.top_procedure())
            callstack_info['hp'].append(stack.top_hp())
            stack.pop()
        return callstack_info


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

def get_pos(hp, pos, rec_vars=None, procs=None):
    """Obtain the sub-program corresponding to the given position.
    
    rec_vars: mapping from recursion variables to HCSP processes.
    procs: mapping from procedure names to HCSP processes.

    """
    assert pos is not None, "get_pos: already reached the end."

    # rec_vars and procs default to empty dictionaries
    if rec_vars is None:
        rec_vars = dict()
    if procs is None:
        procs = dict()

    if hp.type == 'sequence':
        if len(pos) == 0:
            return hp
        return get_pos(hp.hps[pos[0]], pos[1:], rec_vars, procs)
    elif hp.type == 'loop':
        return get_pos(hp.hp, pos, rec_vars, procs)
    elif hp.type == 'wait':
        # assert len(pos) == 1
        return hp
    elif hp.type == 'ode_comm':
        if len(pos) == 0:
            return hp
        else:
            _, out_hp = hp.io_comms[pos[0]]
            return get_pos(out_hp, pos[1:], rec_vars, procs)
    elif hp.type == 'condition':
        if len(pos) == 0:
            return hp
        else:
            assert pos[0] == 0
            return get_pos(hp.hp, pos[1:], rec_vars, procs)
    elif hp.type == 'select_comm':
        if len(pos) == 0:
            return hp
        else:
            _, out_hp = hp.io_comms[pos[0]]
            return get_pos(out_hp, pos[1:], rec_vars, procs)
    elif hp.type == 'recursion':
        if len(pos) == 0:
            return hp
        else:
            rec_vars[hp.entry] = hp
            return get_pos(hp.hp, pos[1:], rec_vars, procs)
    elif hp.type == 'ite':
        if len(pos) == 0:
            return hp
        elif pos[0] < len(hp.if_hps):
            return get_pos(hp.if_hps[pos[0]][1], pos[1:], rec_vars, procs)
        else:
            assert pos[0] == len(hp.if_hps)
            return get_pos(hp.else_hp, pos[1:], rec_vars, procs)
    elif hp.type == 'var':
        if len(pos) == 0:
            return hp
        assert pos[0] == 0

        if hp.name in rec_vars:
            rec_hp = rec_vars[hp.name]
            return get_pos(rec_hp, pos[1:], rec_vars, procs)
        elif hp.name in procs:
            rec_hp = procs[hp.name].hp
            return get_pos(rec_hp, pos[1:], rec_vars, procs)
        else:
            raise SimulatorException("Unrecognized process variable: " + hp.name)
    else:
        assert len(pos) == 0
        return hp

def step_pos(hp, callstack, state, rec_vars=None, procs=None):
    """Execute a (non-communicating) step in the program. Returns the
    new position, or None if steping to the end.
    
    """
    # rec_vars and procs default to empty dictionaries
    
    if rec_vars is None:
        rec_vars = dict()
    if procs is None:
        procs = dict()

    def helper(hp, callstack):
        assert callstack.top_pos() is not None, "step_pos: already reached the end."
        if hp.type == 'sequence':
            assert len(callstack.top_pos()) > 0 and callstack.top_pos()[0] < len(hp.hps)
            callstack_temp=Callstack(callstack.top_pos()[1:],[],[])
            sub_step = helper(hp.hps[callstack.top_pos()[0]], callstack_temp)
            if sub_step.top_pos() is None:
                if callstack.top_pos()[0] == len(hp.hps) - 1:
                    callstack.renew(None,'end')
                    return callstack
                else:
                    if isinstance(callstack.top_procedure(),list):
                        pos=(callstack.top_pos()[0]+1,) + start_pos(hp.hps[callstack.top_pos()[0]+1])
                        curhp=get_pos(hp,pos,rec_vars,procs)
                        callstack.renew(pos,curhp)
                    else:
                        callstack.pop()
                        pos=(callstack.top_pos()[0]+1,) + start_pos(hp.hps[callstack.top_pos()[0]+1])                       
                        curhp=get_pos(hp,pos,rec_vars,procs)
                        callstack.renew(pos,curhp)
                    return callstack
            else:
                pos=(callstack.top_pos()[0],) + sub_step.top_pos()
                curhp=get_pos(hp,pos,rec_vars,procs)
                callstack.renew(pos,curhp)
                return callstack
        elif hp.type == 'select_comm':
            assert len(callstack.top_pos()) > 0
            _, out_hp = hp.io_comms[callstack.top_pos()[0]]
            callstack_temp=Callstack(callstack.top_pos()[1:],[],[])
            sub_step = helper(out_hp, callstack_temp)
            if sub_step.top_pos() is None:
                callstack.renew(None,'end')
                return callstack
            else:
                pos=(callstack.top_pos()[0],) + sub_step.top_pos()
                curhp=get_pos(hp,pos,rec_vars,procs)
                callstack.renew(pos,curhp)
                return callstack
        elif hp.type == 'loop':
            sub_step = helper(hp.hp, callstack)
            if sub_step.top_pos() is None:
                if hp.constraint != true_expr and not eval_expr(hp.constraint, state):
                    callstack.renew(None,'end')
                    return callstack
                else:
                    pos=start_pos(hp.hp)
                    curhp=get_pos(hp,pos,rec_vars,procs)
                    callstack.renew(pos,curhp)
                    return callstack
            else:
                pos=sub_step.top_pos()
                curhp=get_pos(hp,pos,rec_vars,procs)
                callstack.renew(pos,curhp)
                return callstack
        elif hp.type == 'condition':
            if len(callstack.top_pos()) == 0:
                callstack.renew(None,'end')
                return callstack
            callstack_temp=Callstack(callstack.top_pos()[1:],[],[])
            sub_step = helper(hp.hp, callstack_temp)
            if sub_step.top_pos() is None:
                callstack.renew(None,'end')
                return callstack
            else:
                pos=(0,) + sub_step.top_pos()
                curhp=get_pos(hp,pos,rec_vars,procs)
                callstack.renew(pos,curhp)
                return callstack
        elif hp.type == 'delay':
            assert len(callstack.top_pos()) == 1
            callstack.renew(None,'end')
            return callstack
        elif hp.type == 'recursion':
            rec_vars[hp.entry] = hp
            callstack_temp=Callstack(callstack.top_pos()[1:],[],[])
            sub_step = helper(hp.hp, callstack_temp)
            if sub_step.top_pos() is None:
                callstack.renew(None,'end')
                return callstack
            else:
                pos=(0,) + sub_step.top_pos()
                curhp=get_pos(hp,pos,rec_vars,procs)
                callstack.renew(pos,curhp)
                return callstack
        elif hp.type == 'var':
            if hp.name in rec_vars:
                rec_hp = rec_vars[hp.name]
            elif hp.name in procs:
                rec_hp = procs[hp.name].hp
            else:
                raise SimulatorException("Unrecognized process variable: " + hp.name)
            callstack_temp=Callstack(callstack.top_pos()[1:],[],[])
            sub_step = helper(rec_hp, callstack_temp)
            if sub_step.top_pos() is None:
                callstack.renew(None,'end')
                return callstack
            else:
                pos=(0,) + sub_step.top_pos()
                curhp=get_pos(hp,pos,rec_vars,procs)
                callstack.renew(pos,curhp)
                return callstack
        elif hp.type == 'ode_comm':
            if len(callstack.top_pos()) == 0:
                callstack.renew(None,'end')
                return callstack

            _, out_hp = hp.io_comms[callstack.top_pos()[0]]
            callstack_temp=Callstack(callstack.top_pos()[1:],[],[])
            sub_step = helper(out_hp, callstack_temp)
            if sub_step.top_pos() is None:
                callstack.renew(None,'end')
                return callstack
            else:
                pos=(callstack.top_pos()[0],) + sub_step.top_pos()
                curhp=get_pos(hp,pos,rec_vars,procs)
                callstack.renew(pos,curhp)
                return callstack    
        elif hp.type == 'ite':
            assert len(callstack.top_pos()) > 0
            if callstack.top_pos()[0] < len(hp.if_hps):
                _, sub_hp = hp.if_hps[callstack.top_pos()[0]]
                callstack_temp=Callstack(callstack.top_pos()[1:],[],[])
                sub_step = helper(sub_hp, callstack_temp)
            else:
                assert callstack.top_pos()[0] == len(hp.if_hps)
                callstack_temp=Callstack(callstack.top_pos()[1:],[],[])
                sub_step = helper(hp.else_hp, callstack_temp)
        
            if sub_step.top_pos() is None:
                callstack.renew(None,'end')
                return callstack
            else:
                pos=(callstack.top_pos()[0],) + sub_step.top_pos()
                curhp=get_pos(hp,pos,rec_vars,procs)
                callstack.renew(pos,curhp)
                return callstack
        else:
            callstack.renew(None,'end')
            return callstack

    return helper(hp, callstack)

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

def remove_rec(hp, pos, rec_vars=None, procs=None):
    """Given a position in a program possibly with recursion and
    procedure calls, return the simplest expression for the same position
    in the program (removing recursion). This simpler position is used
    for display in user interface.

    """
    if pos is None:
        return None

    rec_list = []
    for i in range(len(pos)+1):
        sub_hp = get_pos(hp, pos[:i], rec_vars, procs)
        if sub_hp.type == 'recursion':
            rec_list.append(i)

    if len(rec_list) >= 2:
        pos = pos[:rec_list[0]] + pos[rec_list[-1]:]
    return pos

def string_of_pos(hp, pos, rec_vars=None, procs=None):
    """Convert pos in internal representation to string form."""
    if pos is None:
        return 'end'
    elif get_pos(hp, pos, rec_vars, procs).type != 'wait':
        return 'p' + ','.join(str(p) for p in pos)
    else:
        return 'p' + ','.join(str(p) for p in pos[:-1]) + ',w' + str(pos[-1])

def disp_of_pos(hp, pos, rec_vars=None, procs=None):
    return string_of_pos(hp, remove_rec(hp, pos, rec_vars, procs), rec_vars, procs)


class SimInfo:
    """Represents a (non-parallel) HCSP program together with
    additional information on the current execution position and
    the current state.

    The current execution position is represented by a tuple of numbers,
    or None if execution has reached the end.

    """
    def __init__(self, name, hp, *, outputs=None, procedures=None, pos="start", state=None):
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

        # List of procedure declarations
        if procedures is None:
            procedures = []
        self.procedures = procedures

        # Current position of execution
        if isinstance(pos, str):
            pos = parse_pos(self.hp, pos)
        else:
            assert isinstance(pos, tuple)
        
        self.callstack = Callstack(pos,[],get_pos(self.hp,pos,None,self.procedures))

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

    def exec_assign(self, lname, val, hp):
        """Make the copy of val into lname. Note deep-copy need to be
        used to avoid aliasing.

        """
        if isinstance(lname, AVar):
            self.state[lname.name] = copy.deepcopy(val)
        elif isinstance(lname, ArrayIdxExpr):
            v = eval_expr(lname.expr1, self.state)
            idx = eval_expr(lname.expr2, self.state)
            if not isinstance(v, list):
                raise SimulatorException('%s is not a list, when executing %s' % (v, hp))
            if idx >= len(v):
                raise SimulatorException('Array index %s out of bounds, when executing %s' % (idx, hp))
            v[idx] = copy.deepcopy(val)
        elif isinstance(lname, FieldNameExpr):
            v = eval_expr(lname.expr, self.state)
            if lname.field not in v:
                raise SimulatorException('Field %s does not exist, when executing %s' % (lname.field, hp))
            v[lname.field] = copy.deepcopy(val)
        elif lname is None:
            pass
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
        cur_hp = get_pos(self.hp, self.callstack.top_pos(), rec_vars, self.procedures)
        if cur_hp.type == "skip":
            self.callstack=step_pos(self.hp, self.callstack, self.state, rec_vars, self.procedures)
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
            
            self.callstack=step_pos(self.hp, self.callstack, self.state, rec_vars, self.procedures)
            self.reason = None

        elif cur_hp.type == "assert":
            # Evaluate an assertion. If fails, immediate stop the execution
            # (like a runtime error).
            if not eval_expr(cur_hp.bexpr, self.state):
                error_msg = ''
                for msg in cur_hp.msgs:
                    val = eval_expr(msg, self.state)
                    error_msg += str(val)
                raise SimulatorException(error_msg)
            else:
                self.callstack=step_pos(self.hp, self.callstack, self.state, rec_vars, self.procedures)
                self.reason = None

        elif cur_hp.type == "test":
            # Evaluate a test. If fails, output a warning but do not stop
            # the execution.
            self.callstack=step_pos(self.hp, self.callstack, self.state, rec_vars, self.procedures)
            self.reason = None
            if not eval_expr(cur_hp.bexpr, self.state):
                warning_expr = ''
                for msg in cur_hp.msgs:
                    val = eval_expr(msg, self.state)
                    warning_expr += str(val)
                raise SimulatorAssertionException(cur_hp.bexpr, warning_expr)

        elif cur_hp.type == "log":
            # Output a log item to the simulator
            self.callstack=step_pos(self.hp, self.callstack, self.state, rec_vars, self.procedures)
            str_pat = eval_expr(cur_hp.pattern, self.state)
            if not isinstance(str_pat, str):
                str_pat = str(str_pat)
            vals = tuple(eval_expr(e, self.state) for e in cur_hp.exprs)
            try:
                log_expr = str_pat % vals
            except TypeError:
                raise SimulatorException("When evaluating %s %% %s, wrong number of arguments" \
                    % (str_pat, vals))
            self.reason = {"log": log_expr}

        elif cur_hp.type == "condition":
            # Evaluate the condition, either go inside or step to next
            if eval_expr(cur_hp.cond, self.state):
                pos=self.callstack.top_pos() + (0,) + start_pos(cur_hp.hp)
                thishp=get_pos(self.hp,pos,rec_vars,self.procedures)
                self.callstack.renew(pos,thishp)
            else:
                self.callstack=step_pos(self.hp, self.callstack, self.state, rec_vars, self.procedures)
            self.reason = None

        elif cur_hp.type == "recursion":
            # Enter into recursion
            pos=self.callstack.top_pos() + (0,) + start_pos(cur_hp.hp)
            thishp=get_pos(self.hp,pos,rec_vars,self.procedures)
            self.callstack.renew(pos,thishp)
            self.reason = None

        elif cur_hp.type == "var":
            # Return to body of recursion
            for i in range(len(self.callstack.top_pos())):
                hp = get_pos(self.hp, self.callstack.top_pos()[:i], rec_vars, self.procedures)
                if hp.type == 'recursion' and hp.entry == cur_hp.name:
                    pos=self.callstack.top_pos() + (0,) + start_pos(hp)
                    thishp=get_pos(self.hp,pos,rec_vars,self.procedures)
                    self.callstack.renew(pos,thishp)
                    self.reason = None
                    return

            # Otherwise, enter code of procedure
            if cur_hp.name in self.procedures:
                proc = self.procedures[cur_hp.name]
                self.callstack.push(self.callstack.top_pos() + (0,) + start_pos(proc.hp),proc)
                self.reason = None
                return

            # Otherwise, not a recursion or procedure call
            raise SimulatorException("Unrecognized process variable: " + cur_hp.name)

        elif cur_hp.type == "input_channel":
            # Waiting for input
            self.reason = {"comm": [(eval_channel(cur_hp.ch_name, self.state), "?")]}

        elif cur_hp.type == "output_channel":
            # Waiting for someone to receive output
            self.reason = {"comm": [(eval_channel(cur_hp.ch_name, self.state), "!")]}

        elif cur_hp.type == "wait":
            # Waiting for some number of seconds
            delay = eval_expr(cur_hp.delay, self.state) - self.callstack.top_pos()[-1]
            if delay < 0:
                raise SimulatorException("When executing %s: delay %s less than zero" % (cur_hp, delay))
            self.reason = {"delay": delay}

        elif cur_hp.type == "ode":
            # Find delay of ODE
            delay = get_ode_delay(cur_hp, self.state)
            assert delay >= 0, "exec_step: delay for ode less than zero"
            self.reason = {"delay": delay}

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
                delay = get_ode_delay(cur_hp, self.state)
                assert delay >= 0, "exec_step: delay for ode_comm less than zero"
                self.reason["delay"] = delay

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
                    pos=self.callstack.top_pos() + (i,) + start_pos(sub_hp)
                    thishp=get_pos(self.hp,pos,rec_vars,self.procedures)
                    self.callstack.renew(pos,thishp)
                    self.reason = None
                    return

            # Otherwise, go to the else branch
            pos=self.callstack.top_pos() + (len(cur_hp.if_hps),) + start_pos(cur_hp.else_hp)
            thishp=get_pos(self.hp,pos,rec_vars,self.procedures)
            self.callstack.renew(pos,thishp)
            self.reason = None

        else:
            raise NotImplementedError

    def exec_input_comm(self, ch_name, x, inst=None):
        """Perform an input communication on a given hybrid program.

        The input communication is specified by the channel name
        and input value.

        """
        rec_vars = dict()
        cur_hp = get_pos(self.hp, self.callstack.top_pos(), rec_vars, self.procedures)

        if inst is not None:
            self.state.update(inst)

        if cur_hp.type == "input_channel":
            assert eval_channel(cur_hp.ch_name, self.state) == ch_name
            if cur_hp.var_name is None:
                assert x is None
            else:
                assert x is not None
                self.exec_assign(cur_hp.var_name, x, cur_hp)
            self.callstack=step_pos(self.hp, self.callstack, self.state, rec_vars, self.procedures)

        elif cur_hp.type == "ode_comm":
            for i, (comm_hp, out_hp) in enumerate(cur_hp.io_comms):
                if comm_hp.type == "input_channel" and eval_channel(comm_hp.ch_name, self.state) == ch_name:
                    self.exec_assign(comm_hp.var_name, x, comm_hp)
                    pos=self.callstack.top_pos() + (i,) + start_pos(out_hp)
                    thishp=get_pos(self.hp,pos,rec_vars,self.procedures)
                    self.callstack.renew(pos,thishp)
                    return

            # Communication must be found among the interrupts
            assert False

        elif cur_hp.type == "select_comm":
            for i, (comm_hp, out_hp) in enumerate(cur_hp.io_comms):
                if comm_hp.type == "input_channel" and eval_channel(comm_hp.ch_name, self.state) == ch_name:
                    if comm_hp.var_name is None:
                        if x is not None:
                            raise SimulatorAssertionException(comm_hp, "input value is not None")
                    else:
                        if x is None:
                            raise SimulatorAssertionException(comm_hp, "input value is None")
                        self.exec_assign(comm_hp.var_name, x, comm_hp)
                    pos=self.callstack.top_pos() + (i,) + start_pos(out_hp)
                    thishp=get_pos(self.hp,pos,rec_vars,self.procedures)
                    self.callstack.renew(pos,thishp)
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
        rec_vars = dict()
        cur_hp = get_pos(self.hp, self.callstack.top_pos(), rec_vars, self.procedures)

        if inst is not None:
            self.state.update(inst)

        if cur_hp.type == "output_channel":
            assert eval_channel(cur_hp.ch_name, self.state) == ch_name
            self.callstack=step_pos(self.hp, self.callstack, self.state, rec_vars, self.procedures)
            return eval_expr(cur_hp.expr, self.state)

        elif cur_hp.type == "ode_comm":
            for i, (comm_hp, out_hp) in enumerate(cur_hp.io_comms):
                if comm_hp.type == "output_channel" and eval_channel(comm_hp.ch_name, self.state) == ch_name:
                    val = eval_expr(comm_hp.expr, self.state)
                    pos=self.callstack.top_pos() + (i,) + start_pos(out_hp)
                    thishp=get_pos(self.hp,pos,rec_vars,self.procedures)
                    self.callstack.renew(pos,thishp)
                    return val

            # Communication must be found among the interrupts
            assert False

        elif cur_hp.type == "select_comm":
            for i, (comm_hp, out_hp) in enumerate(cur_hp.io_comms):
                if comm_hp.type == "output_channel" and eval_channel(comm_hp.ch_name, self.state) == ch_name:
                    pos=self.callstack.top_pos() + (i,) + start_pos(out_hp)
                    thishp=get_pos(self.hp,pos,rec_vars,self.procedures)
                    self.callstack.renew(pos,thishp)
                    return eval_expr(comm_hp.expr, self.state)

            # Communication must be found among the choices
            assert False

        else:
            assert False

    def exec_delay(self, delay, *, time_series=None):
        """Perform delay on the hybrid program of the given length."""
        if self.callstack.top_pos() is None:
            return

        rec_vars = dict()
        cur_hp = get_pos(self.hp, self.callstack.top_pos(), rec_vars, self.procedures)
        if cur_hp.type in ["input_channel", "output_channel", "select_comm"]:
            pass

        elif cur_hp.type == "wait":
            assert 'delay' in self.reason
            assert self.reason['delay'] >= delay
            if self.reason['delay'] == delay:
                self.callstack = step_pos(self.hp, self.callstack, self.state, rec_vars, self.procedures)
            else:
                pos=self.callstack.top_pos()[:-1] + (self.callstack.top_pos()[-1] + delay,)
                thishp=get_pos(self.hp,pos,rec_vars,self.procedures)
                self.callstack.renew(pos,thishp)


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
                self.callstack = step_pos(self.hp, self.callstack, self.state, rec_vars, self.procedures)
            else:
                if 'delay' in self.reason:
                    self.reason['delay'] -= delay

        else:
            assert False

def match_channel(out_ch, in_ch):
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
            if isinstance(in_arg, (int, str)):
                inst_out[out_arg.name] = in_arg
            elif isinstance(in_arg, AVar):
                return None  # both sides are variables
            else:
                raise TypeError
        elif isinstance(out_arg, (int, str)):
            if isinstance(in_arg, (int, str)):
                if out_arg != in_arg:
                    return None
            elif isinstance(in_arg, AVar):
                inst_in[in_arg.name] = out_arg
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

def exec_parallel(infos, *, num_io_events=None, num_steps=400, num_show=None,
                  show_interval=None, start_event=None):
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

    def log_event(ori_pos, **xargs):
        """Log the given event, starting with the given event info."""
        nonlocal num_event
        num_event += 1
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
            info_pos = disp_of_pos(info.hp, info.callstack.top_pos(), None, info.procedures)
            cur_info[info.name] = {'pos': info_pos, 'state': copy.copy(info.state)}
        new_event['infos'] = cur_info

        # Finally add to trace
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

    if start_event:
        # If has a starting event, modify starting position accordingly
        num_event = start_event['id'] + 1
        res['time'] = start_event['time']
        for info in infos:
            pos=parse_pos(info.hp, start_event['infos'][info.name]['pos'])
            thishp=get_pos(info.hp,pos,None,None)
            info.callstack.renew(pos,thishp)
            info.state = start_event['infos'][info.name]['state']

    else:
        # Otherwise use default starting position
        num_event = 0

        # List of processes that have been updated in the last round.
        start_pos = dict((info.name, disp_of_pos(info.hp, info.callstack.top_pos())) for info in infos)

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

    for iteration in range(num_io_events):
        # Iterate over the processes, apply exec_step to each until
        # stuck, find the stopping reasons.
        for info in infos:
            while info.callstack.top_pos() is not None and not num_event >= start_id + num_steps:
                ori_pos = {info.name: disp_of_pos(info.hp, info.callstack.top_pos(), None, info.procedures)}
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
            ori_pos = dict((infos[p].name, disp_of_pos(infos[p].hp, infos[p].callstack.top_pos(), None, infos[p].procedures)) for p in delay_pos)

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
            ori_pos = {infos[id_out].name: disp_of_pos(infos[id_out].hp, infos[id_out].callstack.top_pos(), None, infos[id_out].procedures),
                       infos[id_in].name: disp_of_pos(infos[id_in].hp, infos[id_in].callstack.top_pos(), None, infos[id_in].procedures)}
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
