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
        wlexpr_eqn, init2var = Ode2Wlexpr(hp, names, time_var)

        # Solve the differential equations.
        # For example, sol is :
        # ((Rule[Global`y[Global`x], Plus[Times[Rational[1, 2], Power[Global`x, 2]], C[1]]]))
        slns = session.evaluate(wlexpr('DSolve' + wlexpr_eqn))

        # Solution is tranlated into string, like 'y(x) = 1/2 * x^2 + C(1)', or 
        # ['v(t) = v0 + a * t', 'x(t) = x0 + v0 * t + a * t^2 / 2']
        solutions = []
        for sln in slns[0]:
            solutions.append(toString(sln))

        # Change the intial value symbol,  for the sake of ODE solution axiom
        # For example, from 'v(t) = v0 + a * t' to  'v(t) = v + a * t'
        for init_value, var in init2var.items():
            for i, sln in enumerate(solutions):
                sln = sln.replace(init_value, var)
                solutions[i] = sln

        print(solutions)
        # Tranlate solution into a dictionary form
        solution_dict = dict()
        for sol in solutions:
            sol_list = sol.split('=') # e.g. ['v(t)', 'v + a * t']

            assert len(sol_list) == 2
            idx = sol_list[0].index('(')
            fun_name = sol_list[0][:idx]
            sol_expr = aexpr_parser.parse(sol_list[1])

            solution_dict[fun_name] = sol_expr

    return solution_dict

def Ode2Wlexpr(hp, names, time_var):

    eqs = hp.eqs

    # <x_dot = v, v_dot = a & v > 0>

    # eqs: [('x', v), ('v', a)]
    # constraint: v > 0

    # wlexpr_eqn: [{x'[t] == v[t], v'[t] == a, x[0] == x0, v[0] == v0}, {x[t], v[t]}, t]

    # <x_dot = v, v_dot = a, c_dot = 1 & c < 1>

    # eqs: [('x', v), ('v', a), ('c', 1)]
    # constraint: v > 0

    # wlexpr_eqn: [{x'[t] == v[t], v'[t] == a, c'[t] == 1, x[0] == x0, v[0] == v0, c[0] = 0}, {x[t], v[t],c[t]}, t]
    fun_names = []
    deriv_exprs = []
    for eq in eqs:
        fun_names.append(eq[0]) # ['x', 'v']
        deriv_exprs.append(str(eq[1])) #['v', 'a']

    for i, deriv_expr in enumerate(deriv_exprs):
        if deriv_expr in fun_names:
            deriv_exprs[i] = deriv_expr + '[' + time_var + ']'  # ['v[t]', 'a']

    # Create the wlexpression for differential eqautions.

    # Map initial value to their function name.
    init2var = dict()
    # Functions that will be solved.
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
        # {'x0': 'x'}
        init2var[init_var] = fun_name

        diff_eq = fun_name + '\'' + '[' + time_var + ']' + '==' + deriv_exprs[i]
        diff_eqs.append(diff_eq) # ["x'[t] == v[t]", "v'[t] == a"]

        init_value_eq = fun_name + '[0]' + '==' + init_var
        diff_eqs.append(init_value_eq) # ["x'[t] == v[t]", "x[0] == x0", "v'[t] == a", "v[0] == v0"]

    # [{x'[t] == v[t], v'[t] == a, x[0] == x0, v[0] == v0}, {x[t], v[t]}, t]
    wlexpr_eqn = '['+ '{' + ','.join(diff_eqs) + '}' + ',' + \
                      '{' + ','.join(tosolve_funs) + '}' + ',' + \
                      time_var + \
                 ']'

    return wlexpr_eqn, init2var

def toString(e):
    if isinstance(e, WLFunction):
        if e.head == WLSymbol("Rule"):
            assert len(e.args) == 2
            return "%s = %s" % (toString(e.args[0]), toString(e.args[1]))
        elif e.head == WLSymbol("Plus"):
            print('args', e.args)
            assert len(e.args) == 2
            return "%s + %s" % (toString(e.args[0]), toString(e.args[1]))
        elif e.head == WLSymbol("Times"):
            assert len(e.args) == 2
            return "%s * %s" % (toString(e.args[0]), toString(e.args[1]))
        elif e.head == WLSymbol("Power"):
            assert len(e.args) == 2
            return "%s^%s" % (toString(e.args[0]), toString(e.args[1]))
        elif e.head == WLSymbol("Rational"):
            assert len(e.args) == 2
            return "%s/%s" % (toString(e.args[0]), toString(e.args[1]))            
        else:
            assert len(e.args) == 1, str(e)
            return "%s(%s)" % (toString(e.head), toString(e.args[0]))
    elif isinstance(e, WLSymbol):
        str_e = str(e)
        if str_e.startswith("Global`"):
            str_e = str_e[7:]
        return str_e
    elif isinstance(e, int):
        return str(e)
    else:
        assert False, "Unexpected expression: %s" % str(e)
        


    



