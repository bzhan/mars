"""Wrapper for Wolfram Engine."""

import os

from decimal import Decimal
from wolframclient.evaluation import WolframLanguageSession
from wolframclient.language import wl, wlexpr
from wolframclient.language.expression import WLFunction, WLSymbol
from wolframclient.exception import WolframKernelException
from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import hcsp
import platform

# logging.basicConfig(level=logging.DEBUG)
found_wolfram = False
path = None
session = None

default_locations = [
    "C:\\Program Files\\Wolfram Research\\Wolfram Engine\\13.1\\WolframKernel.exe",
    "/Applications/Wolfram Engine.app/Contents/MacOS/WolframKernel",
    "/usr/local/Wolfram/WolframEngine/13.1/Executables/WolframKernel"
]

for loc in default_locations:
    if os.path.exists(loc):
        path = loc
        break

if path is None:
    path = os.getenv("WolframKernel")

if path:
    try:
        session = WolframLanguageSession(path)
        found_wolfram = True
    except WolframKernelException:
        print("Failed to start Wolfram Kernel")
else:
    print("Please install Wolfram Kernel in a default location or specify its location in the environment variable \"WolframKernel\".")

def toWLexpr(e, functions=dict()):
    """Convert a hcsp expression to WolframLanguage expression"""
    def rec(e):
        if isinstance(e, expr.AVar):
            return WLSymbol("Global`" + e.name)
        elif isinstance(e, expr.AConst):
            if isinstance(e.value, int):
                return e.value
            elif isinstance(e.value, Decimal):
                return wl.Rationalize(e.value)
            else:
                print(e, type(e))
                raise NotImplementedError
        elif isinstance(e, expr.FunExpr):
            if e.fun_name in functions:
                return rec(expr.replace_function(e, functions))
            return WLFunction(WLSymbol("Global`" + e.fun_name), *(rec(expr) for expr in e.exprs))
        elif isinstance(e, expr.BConst):
            if e.value is True:
                return True
            else:
                return False
        elif isinstance(e, expr.OpExpr):
            if e.op == '+':
                return wl.Plus(rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == '-':
                if len(e.exprs) == 1:
                    return wl.Minus(rec(e.exprs[0]))
                else:
                    return wl.Subtract(rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == '*':
                return wl.Times(rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == '/':
                return wl.Divide(rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == '^':
                return wl.Power(rec(e.exprs[0]), rec(e.exprs[1]))
            else:
                raise NotImplementedError

        elif isinstance(e, expr.RelExpr):
            if e.op == '>':
                return wl.Greater(rec(e.expr1), rec(e.expr2))
            elif e.op == '>=':
                return wl.GreaterEqual(rec(e.expr1), rec(e.expr2))
            elif e.op == '<':
                return wl.Less(rec(e.expr1), rec(e.expr2))
            elif e.op == '<=':
                return wl.LessEqual(rec(e.expr1), rec(e.expr2))
            elif e.op == '==':
                return wl.Equal(rec(e.expr1), rec(e.expr2))
            elif e.op == '!=':
                return wl.Unequal(rec(e.expr1), rec(e.expr2))
            else:
                raise AssertionError

        elif isinstance(e, expr.LogicExpr):
            if e.op == '&&':
                return wl.And(rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == '||':
                return wl.Or(rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op == '!':
                return wl.Not(rec(e.exprs[0]))
            elif e.op == '->':
                return wl.Implies(rec(e.exprs[0]), rec(e.exprs[1]))
            elif e.op =='<->':
                return wl.Equivalent(rec(e.exprs[0]), rec(e.exprs[1]))
            else:
                raise AssertionError
        elif isinstance(e, expr.ForAllExpr):
            if isinstance(e.vars, tuple):
                return wl.ForAll({rec(var) for var in e.vars}, rec(e.expr))
            else:
                return wl.ForAll(rec(e.vars), rec(e.expr))
        elif isinstance(e, expr.ExistsExpr):
            if isinstance(e.vars, tuple):
                return wl.Exists({rec(var) for var in e.vars}, rec(e.expr))
            else:
                return wl.Exists(rec(e.vars), rec(e.expr))
        else:
            raise NotImplementedError

    return rec(e)

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
        
        # Translate to OpExpr in hcsp.
        elif e.head == WLSymbol("Plus"):  # priority: 65
            return expr.list_add(*(toHcsp(arg) for arg in e.args))
        elif e.head == WLSymbol("Times"):  # priority: 70
            return expr.list_mul(*(toHcsp(arg) for arg in e.args))
        elif e.head == WLSymbol("Power"):  # priority: 85
            assert len(e.args) == 2
            return expr.OpExpr('^', toHcsp(e.args[0]), toHcsp(e.args[1]))
        elif e.head == WLSymbol("Rational"):  # priority: 85
            assert len(e.args) == 2
            return expr.OpExpr('/', toHcsp(e.args[0]), toHcsp(e.args[1]))

        # Translate to RelExpr in hcsp.
        elif e.head == WLSymbol("Equal"):
            assert len(e.args) == 2
            return expr.RelExpr('==', toHcsp(e.args[0]), toHcsp(e.args[1]))
        elif e.head == WLSymbol("Greater"):
            assert len(e.args) == 2
            return expr.RelExpr('>', toHcsp(e.args[0]), toHcsp(e.args[1]))
        elif e.head == WLSymbol("GreaterEqual"):
            assert len(e.args) == 2
            return expr.RelExpr('>=', toHcsp(e.args[0]), toHcsp(e.args[1]))
        elif e.head == WLSymbol("Less"):
            assert len(e.args) == 2
            return expr.RelExpr('<', toHcsp(e.args[0]), toHcsp(e.args[1]))
        elif e.head == WLSymbol("LessEqual"):
            assert len(e.args) == 2
            return expr.RelExpr('<=', toHcsp(e.args[0]), toHcsp(e.args[1]))
        elif e.head == WLSymbol("UnEqual"):
            assert len(e.args) == 2
            return expr.RelExpr('!=', toHcsp(e.args[0]), toHcsp(e.args[1]))

        # Translate into LogicExpr in hcsp.
        elif e.head == WLSymbol("And"):
            if len(e.args) == 2:
                return expr.LogicExpr('&&', toHcsp(e.args[0]), toHcsp(e.args[1]))
            elif len(e.args) > 2:
                return expr.LogicExpr("&&", toHcsp(WLFunction(WLSymbol("And"), *e.args[:-1])),
                                            toHcsp(e.args[-1]))
            else:
                raise AssertionError
        elif e.head == WLSymbol("Or"):
            if len(e.args) == 2:
                return expr.LogicExpr('||', toHcsp(e.args[0]), toHcsp(e.args[1]))
            elif len(e.args) > 2:
                return expr.LogicExpr("||", toHcsp(WLFunction(WLSymbol("Or"), *e.args[:-1])),
                                            toHcsp(e.args[-1]))
            else:
                raise AssertionError
        elif e.head == WLSymbol("Not"):
            assert len(e.args) == 1
            return expr.LogicExpr('!', toHcsp(e.args[0]))
        elif e.head == WLSymbol("Implies"):
            assert len(e.args) == 2
            return expr.LogicExpr('->', toHcsp(e.args[0]), toHcsp(e.args[1]))
        elif e.head == WLSymbol("Equivalent"):
            assert len(e.args) == 2
            return expr.LogicExpr('<->', toHcsp(e.args[0]), toHcsp(e.args[1]))

        else:
            # Apply toHCSP to e.head because e.head may include "Global`"
            # For example, the solution is Global`x1[t] := t, 
            # then we need to delete "Global`" to match x1 with the variable in ODE.
            return expr.FunExpr(str(toHcsp(e.head)), [toHcsp(arg) for arg in e.args])

    elif isinstance(e, WLSymbol):
        str_e = str(e)
        if str_e.startswith("Global`"):
            str_e = str_e[7:]
        return expr.AVar(str_e)
    elif isinstance(e, int):
        if isinstance(e, bool):
            return expr.BConst(e)
        else:
            return expr.AConst(e)
    else:
        assert False, "Unexpected expression: %s" % str(e)


def solveODE(hp, names, time_var):
    """ Return the solution dictionary. 

    Example: {'v': v + a * t}

    'v' : str, function name
     v + a * t : Expr

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


def wl_prove(e, functions=dict()):
    """Attempt to prove the given condition."""
    if not isinstance(e, expr.Expr):
        raise NotImplementedError

    # If wolfram not found, just return failure
    if not found_wolfram:
        return False

    vars = e.get_vars()
    wl_expr = toWLexpr(e, functions)
    wl_vars = {toWLexpr(expr.AVar(var), functions) for var in vars}

    # wl_vars cannot be empty when using FindInstance function.
    if wl_vars:
        # We use FindInstance instead of Reduce here 
        # because that Reduce cannot reduce the VCs in basic 46, 47 into true，
        # even though the VCs should be valid.
        result = session.evaluate(wl.FindInstance(wl.Not(wl_expr), wl_vars, wl.Reals))
        # result is an empty tuple, i.e. no instance found for the not expression.
        if not result:
            return True
        else:
            return False
    # Cases when the wl_vars is empty. For example, when wl_expr is True.
    else:
        result = session.evaluate(wl.Reduce(wl_expr, wl.Reals))
        
        if str(result) == 'True':
            return True
        else:
            return False

def wl_simplify(e, functions=dict()):
    """Simplify the given hcsp expression"""
    wl_expr = toWLexpr(e, functions)
    # Use the Simplify function in wolfram.
    wl_expr = session.evaluate(wl.Simplify(wl_expr))
    hcsp_expr = toHcsp(wl_expr)

    return hcsp_expr

def wl_polynomial_div(p, q, constants, functions=dict()):
    """Compute the quotient and remainder of polynomial p and q"""
    vars = q.get_vars().difference(constants)
    # Sort the vars to get the same results everytime,
    # because result of PolynomialReduce depends on the sort of vars but set has no sort.
    vars_list = [var for var in vars]
    vars_list.sort()
    vars = wl.List(*[toWLexpr(expr.AVar(var), functions) for var in vars_list])
    
    p = toWLexpr(p, functions)
    q = toWLexpr(q, functions)

    # result is in the form, for example, (x, 1), 
    # in which x is the quotient, 1 is the remainder.
    quot_remains = dict()
    # Use PolynomialReduce instead of PolynomialQuotientRemainder,
    # because PolynomialQuotientRemainder only allows one var, 
    # which may lead to a fractional expression as quotient.
    # For example, quot is x/y, since x is the only var
    result = session.evaluate(wl.PolynomialReduce(p, q, vars))

    quot = toHcsp(result[0][0])
    remain = toHcsp(result[1])

    quot_remains[quot] = remain

    return quot_remains

def wl_is_polynomial(e, constants=set(), functions=dict()):
    """Verify whether the given expression is a polynomial"""
    vars = e.get_vars().difference(constants)
    vars = {toWLexpr(expr.AVar(var), functions) for var in vars}

    e = toWLexpr(e, functions)

    result = session.evaluate(wl.PolynomialQ(e, vars))

    if str(result) == 'True':
        return True
    else:
        return False


    
