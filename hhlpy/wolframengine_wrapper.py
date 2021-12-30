"""Wrapper for Wolfram Engine to solve ordinary differential equatiions."""

from wolframclient.evaluation import WolframLanguageSession
from wolframclient.language import wl, wlexpr
from wolframclient.language.expression import WLFunction, WLSymbol
from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp.parser import aexpr_parser

path = "D:\Program Files\WolframEngine_13.0\wolframengine\MathKernel.exe"

def solveODE(hp, names, time_var):
    """ Return the solution dictionary. 

    Example: {'v': v + a * t}

    'v' : str, function name
     v + a * t : AExpr

    """
    if not isinstance(hp, hcsp.ODE):
        raise AssertionError

    with WolframLanguageSession(path) as session:
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
           init2fun  : {'x0' : x, 'v0' : v}

    """

    eqs = hp.eqs # eqs: [('x', v), ('v', a)]

    # Collect the function names and their corresponding derivative expressions.
    fun_names = []
    deriv_exprs = []
    for eq in eqs:
        fun_names.append(eq[0]) # ['x', 'v']
        deriv_exprs.append(str(eq[1])) #['v', 'a']

    # If the derivative expression is a function names, add time variable for it.
    for i, deriv_expr in enumerate(deriv_exprs):
        if deriv_expr in fun_names:
            deriv_exprs[i] = deriv_expr + '[' + time_var + ']'  # ['v[t]', 'a']

    # Create the wlexpression for differential eqautions.

    # Map initial value symbol(str) to their function name symbol(AVar).
    init2fun = dict()
    # Functions to solve.
    tosolve_funs = []
    # Differential eqautions and their inital value.
    diff_eqs = []
    for i, fun_name in enumerate(fun_names):
        # Functions that will be solved.
        tosolve_funs.append(fun_name + '[' + time_var + ']') # {"x[t]", "v[t]"}

        # Create a new variable for initial value of each functions.
        init_var = fun_name + '0'
        while init_var in names:
            init_var = init_var + '0'
        # {'x0': x}
        init2fun[init_var] = expr.AVar(fun_name)

        diff_eq = fun_name + '\'' + '[' + time_var + ']' + '==' + deriv_exprs[i]
        diff_eqs.append(diff_eq) # ["x'[t] == v[t]", "v'[t] == a"]

        init_value_eq = fun_name + '[0]' + '==' + init_var
        diff_eqs.append(init_value_eq) # ["x'[t] == v[t]", "x[0] == x0", "v'[t] == a", "v[0] == v0"]

    # [{x'[t] == v[t], v'[t] == a, x[0] == x0, v[0] == v0}, {x[t], v[t]}, t]
    wlexpr_eqn = '['+ '{' + ','.join(diff_eqs) + '}' + ',' + \
                      '{' + ','.join(tosolve_funs) + '}' + ',' + \
                      time_var + \
                 ']'

    return wlexpr_eqn, init2fun

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
        


    



