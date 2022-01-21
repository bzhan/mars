"""Wrapper for Wolfram Engine."""

from decimal import Decimal
from wolframclient.evaluation import WolframLanguageSession
from wolframclient.language import wl, wlexpr
from wolframclient.language.expression import WLFunction, WLSymbol
from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp.parser import aexpr_parser

# logging.basicConfig(level=logging.DEBUG)
path = "D:\Program Files\Wolfram Research\Wolfram Engine\\13.0\MathKernel.exe"
session = WolframLanguageSession(path)

def toWLexpr(e):
    """Convert a hcsp expression to WolframLanguage expression"""
    if isinstance(e, expr.AVar):
        return WLSymbol(e.name)
    elif isinstance(e, expr.AConst):
        if isinstance(e.value, int):
            return e.value
        elif isinstance(e.value, Decimal):
            return wl.Rationalize(e.value)
        else:
            print(e, type(e))
            raise NotImplementedError
    elif isinstance(e, expr.FunExpr):
        return WLFunction(WLSymbol(e.fun_name), *(toWLexpr(expr) for expr in e.exprs))
    elif isinstance(e, expr.BConst):
        return WLSymbol(str(e.value))

    elif isinstance(e, expr.OpExpr):
        if e.op == '+':
            return wl.Plus(toWLexpr(e.exprs[0]), toWLexpr(e.exprs[1]))
        elif e.op == '-':
            if len(e.exprs) == 1:
                return wl.Minus(toWLexpr(e.exprs[0]))
            else:
                return wl.Subtract(toWLexpr(e.exprs[0]), toWLexpr(e.exprs[1]))
        elif e.op == '*':
            return wl.Times(toWLexpr(e.exprs[0]), toWLexpr(e.exprs[1]))
        elif e.op == '/':
            return wl.Divide(toWLexpr(e.exprs[0]), toWLexpr(e.exprs[1]))
        elif e.op == '^':
            return wl.Power(toWLexpr(e.exprs[0]), toWLexpr(e.exprs[1]))
        else:
            raise NotImplementedError

    elif isinstance(e, expr.RelExpr):
        if e.op == '>':
            return wl.Greater(toWLexpr(e.expr1), toWLexpr(e.expr2))
        elif e.op == '>=':
            return wl.GreaterEqual(toWLexpr(e.expr1), toWLexpr(e.expr2))
        elif e.op == '<':
            return wl.Less(toWLexpr(e.expr1), toWLexpr(e.expr2))
        elif e.op == '<=':
            return wl.LessEqual(toWLexpr(e.expr1), toWLexpr(e.expr2))
        elif e.op == '==':
            return wl.Equal(toWLexpr(e.expr1), toWLexpr(e.expr2))
        elif e.op == '!=':
            return wl.Unequal(toWLexpr(e.expr1), toWLexpr(e.expr2))
        else:
            raise AssertionError

    elif isinstance(e, expr.LogicExpr):
        if e.op == '&&':
            return wl.And(toWLexpr(e.exprs[0]), toWLexpr(e.exprs[1]))
        elif e.op == '||':
            return wl.Or(toWLexpr(e.exprs[0]), toWLexpr(e.exprs[1]))
        elif e.op == '~':
            return wl.Not(toWLexpr(e.exprs[0]))
        elif e.op == '-->':
            return wl.Implies(toWLexpr(e.exprs[0]), toWLexpr(e.exprs[1]))
        elif e.op =='<-->':
            return wl.Equivalent(toWLexpr(e.exprs[0]), toWLexpr(e.exprs[1]))
        else:
            raise AssertionError
    elif isinstance(e, expr.ForAllExpr):
        if isinstance(e.vars, tuple):
            return wl.Forall(wl.List(toWLexpr(var) for var in e.vars), toWLexpr(e.expr))
        else:
            return wl.ForAll(toWLexpr(e.vars), toWLexpr(e.expr))
    elif isinstance(e, expr.ExistsExpr):
        if isinstance(e.vars, tuple):
            return wl.Exists(wl.List(toWLexpr(var) for var in e.vars), toWLexpr(e.expr))
        else:
            return wl.Exists(toWLexpr(e.vars), toWLexpr(e.expr))
    else:
        raise NotImplementedError


def toHcsp(e):
    """
    Translate a wlexpression to hcsp expression or program.
    Example1:
    wl: Rule[Global`y[Global`x], Plus[Times[Rational[1, 2], Power[Global`x, 2]], C[1]]]
    hcsp: y(x) := 1/2 * x^2 + C(1)

    Example2:
    wl: Rule[Global`x[Global`t], Times[Rational[1, 2], Plus[Times[Global`a, Power[Global`t, 2]], Times[2, Global`t, Global`v0], Times[2, Global`x0]]]])
    hcsp: x(t) := 1/2 * (a * t^2 + 2 * v0 * t + 2 * x0)
    
    """
    if isinstance(e, WLFunction):
        if e.head == WLSymbol("Rule"):
            assert len(e.args) == 2
            return hcsp.Assign(toHcsp(e.args[0]), toHcsp(e.args[1]))
        elif e.head == WLSymbol("Plus"):  # priority: 65
            if len(e.args) == 2:
                return expr.OpExpr('+', toHcsp(e.args[0]), toHcsp(e.args[1]))
            elif len(e.args) > 2:
                return expr.OpExpr('+', toHcsp(WLFunction(WLSymbol("Plus"), *e.args[:-1])),
                                        toHcsp(e.args[-1]))
            else:
                raise AssertionError
        elif e.head == WLSymbol("Times"):  # priority: 70
            if len(e.args) == 2:
                return expr.OpExpr('*', toHcsp(e.args[0]), toHcsp(e.args[1]))
            elif len(e.args) > 2:
                return expr.OpExpr('*', toHcsp(WLFunction(WLSymbol("Times"), *e.args[:-1])),
                                        toHcsp(e.args[-1]))
            else:
                raise AssertionError
        elif e.head == WLSymbol("Power"):  # priority: 85
            assert len(e.args) == 2
            return expr.OpExpr('^', toHcsp(e.args[0]), toHcsp(e.args[1]))
        elif e.head == WLSymbol("Rational"):  # priority: 85
            assert len(e.args) == 2
            return expr.OpExpr('/', toHcsp(e.args[0]), toHcsp(e.args[1]))
        else:
            return expr.FunExpr(toHcsp(e.head), [toHcsp(arg) for arg in e.args])
    elif isinstance(e, WLSymbol):
        str_e = str(e)
        if str_e.startswith("Global`"):
            str_e = str_e[7:]
        return expr.AVar(str_e)
    elif isinstance(e, int):
        return expr.AConst(e)
    else:
        assert False, "Unexpected expression: %s" % str(e)


def solveODE(hp, names, time_var):
    """ Return the solution dictionary. 

    Example: {'v': v + a * t}

    'v' : str, function name
     v + a * t : AExpr

    """
    assert isinstance(hp, hcsp.ODE)
    assert isinstance(names, set)
    for name in names:
        assert isinstance(name, str)

    if not isinstance(time_var, str):
        time_var = str(time_var)

    # with WolframLanguageSession(path) as session:
    # ODEs are tranlated from hcsp form to wolfram language 
    wlexpr_eqn, init2fun = Ode2Wlexpr(hp, names, time_var)

    # Solve the differential equations.
    # For example, sln is :
    # ((Rule[Global`y[Global`x], Plus[Times[Rational[1, 2], Power[Global`x, 2]], C[1]]]))
    slns = session.evaluate(wlexpr('DSolve' + wlexpr_eqn))

    # Solutions in WLlanguage are translated into a list of Assign programs in hcsp.
    # For example, [y(x) := 1/2 * x^2 + C(1)], or 
    # [v(t) := v0 + a * t, x(t) := x0 + v0 * t + a * t^2 / 2]
    solutions = []
    for sln in slns[0]:
        solutions.append(toHcsp(sln))

    # Tranlate solution into a dictionary form and 
    # change the inital value symbol to function name symbol, for the sake of ODE solution axiom.
    # e.g. from [v(t) := v0 + a * t] to {'v' : v + a * t}
    solution_dict = dict()
    for sol in solutions:

        fun_name = str(sol.var_name.fun_name)
        solution_dict[fun_name] = sol.expr.subst(init2fun)

    return solution_dict

def Ode2Wlexpr(hp, names, time_var):
    """
    Example: for ODE <x_dot = v, v_dot = a & v > 0>
    
    Return wlexpr_eqn: [{x'[t] == v[t], v'[t] == a, x[0] == x0, v[0] == v0}, {x[t], v[t]}, t] and
           init2var  : {'x0' : x, 'v0' : v}

    """

    eqs = hp.eqs # eqs: [('x', v), ('v', a)]

    # Map the function name variable to function expression.
    var2fun = dict() # {'x' : x[t], 'v' : v[t]}
    for eq in eqs:
        var2fun[eq[0]] = expr.AVar(eq[0] + '[' + time_var + ']')

    # Differential eqautions and their inital value are recorded in the dictionary.
    ode_wleqs = dict() # {"x'[t]" : 'v[t]', "v'[t]" : 'a', 'x[0]' : x0, 'v[0]' : v0}
    # Functions that will be solved.
    tosolve_funs = [] # ['x[t]', 'v[t]']
    # Map the initial value symbol to their function name variable.
    init2var = dict()  # {'x0' : 'x', 'v0' : 'v'}

    for eq in eqs:
        x_dot_t = eq[0] + "\'" + '[' + time_var +']'  # x'[t]
        deriv_expr = str(eq[1].subst(var2fun))  # 'v[t]'
        ode_wleqs[x_dot_t] = deriv_expr # {"x'[t]" : 'v[t]'}

        tosolve_funs.append(str(var2fun[eq[0]])) # ['x[t]', 'v[t]']

        # Create a new variable for initial value symbol of each functions.
        init_var = eq[0] + '0'
        while init_var in names:
            init_var = init_var + '0'
        # {'x0': x}
        init2var[init_var] = expr.AVar(eq[0])
        x_0 = eq[0] + '[0]'
        ode_wleqs[x_0] = init_var  # {"x'[t]" : 'v[t]', 'x[0]' : x0}
     
    ode_wleqs_list = []  # ["x'[t] == v[t], "x[0] == x0"]
    for left, right in ode_wleqs.items():
        ode_wleqs_list.append(left + '==' + right)

    # [{x'[t] == v[t], v'[t] == a, x[0] == x0, v[0] == v0}, {x[t], v[t]}, t]
    wlexpr_eqn = '['+ '{' + ','.join(ode_wleqs_list) + '}' + ',' + \
                      '{' + ','.join(tosolve_funs) + '}' + ',' + \
                      time_var + \
                 ']'

    return wlexpr_eqn, init2var


def wol_prove(e):
    """Attempt to prove the given condition."""
    if not isinstance(e, expr.BExpr):
        raise NotImplementedError

    wl_expr = toWLexpr(e)

    # with WolframLanguageSession(path) as session:
    result = session.evaluate(wl.Reduce(wl_expr, wl.Reals))
    if str(result) == 'True':
        return True
    else:
        return False
