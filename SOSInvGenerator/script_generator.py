# Program to generate matlab scripts.

import json

from script_common import *

def norm_to_ge_zero(cond):
    """Normalize the given condition to the form ... >= 0. Return
    the part that should be >= 0.
    
    """
    assert isinstance(cond, dict), "norm_to_ge_zero: invalid form of condition."
    if cond['ty'] == 'ge' or cond['ty'] == 'gt':
        return cond['lhs'] + '-' + cond['rhs']
    elif cond['ty'] == 'le' or cond['ty'] == 'lt':
        return cond['rhs'] + '-' + cond['lhs']
    else:
        raise NotImplementedError

def replace_subst(cond):
    if cond['ty'] == 'subst' and cond['base']=='Inv':
        return 'replace(inv,'+cond['var']+','+cond['expr']+')'
    elif cond['ty'] == 'subst' and cond['base']['ty'] == 'subst':
        return 'replace('+replace_subst(cond['base'])+','+cond['var']+','+cond['expr']+')'

def process_data(spdvars, constraints):
    num_constraints = len(constraints)

    myeps_list = ["myeps" + str(n) for n in range(num_constraints)]
    tol_list = ["tol" + str(n) for n in range(num_constraints)]

    str_spdvars = "sdpvar " + " ".join(spdvars) + ";"
    str_myeps = "sdpvar " + " ".join(myeps_list) + ";"
    str_lambdas = ["", "lambda1 = .5;", "lambda2 = 1;"]
    str_tols = [""] + [tol + " = 1e-6;" for tol in tol_list]

    str_list_vars = str_list(spdvars, ' ')
    str_poly_inv = "[inv, c0] = polynomial(%s, 6);" % str_list_vars

    num_flow = 0
    num_sos = 0

    def convert_precond(i, precond):
        """Convert constraint of the form precond --> Inv."""
        nonlocal num_sos
        
        exprs =[]
        Inv = "inv"
        for i in range(len(precond['from'])):
            if precond['from'][i]['ty'] == 'eq':
                Inv="replace("+Inv+","+precond['from'][i]['lhs']+","+precond['from'][i]['rhs']+")"
            else:
                exprs.append(norm_to_ge_zero(precond['from'][i]))
        num_from = len(exprs)
        cur_sos_list = ["s" + str(num_sos+1+i) for i in range(num_from)]
        num_sos += num_from
        def get_minus_term(cur_sos, exp):
            return "- %s * (%s)" % (cur_sos, exp)

        all_minus_term = "".join(get_minus_term(cur_sos, exp) for cur_sos, exp in zip(cur_sos_list, exprs))
        sos_eq = "f%d = sos(-%s%s - %s);" % (i, Inv, all_minus_term, myeps_list[i])
        return ["", sos_eq]

    def convert_postcond(i, postcond):
        """Convert constraint of the form Inv --> postcond."""
        nonlocal num_sos

        if len(postcond['to']) == 1 and len(postcond['from']) == 1:
            expr = norm_to_ge_zero(postcond['to'][0])
            expr = "-(%s)" % expr
            cur_sos = "s" + str(num_sos+1)
            num_sos += 1

            sos_eq = "f%d = sos(inv - %s * (%s) - %s);" % (i, cur_sos, expr, myeps_list[i])
            return ["", sos_eq]
        elif len(postcond['to']) > 1 and len(postcond['from']) > 1:
            exprs = [norm_to_ge_zero(postcond['to'][i]) for i in range(len(postcond['to']))]
            expr1 = ") * (".join(exprs)
            expr1 = "("+expr1+")"
            exprs = [norm_to_ge_zero(postcond['from'][i]) for i in range(1,len(postcond['from']))]
            expr2 = ") * (".join(exprs)
            expr2 = "("+expr2+")"
            cur_sos1 = "s" + str(num_sos+1)
            cur_sos2 = "s" + str(num_sos+2)
            num_sos += 2
            sos_eq = "f%d = sos(inv - %s * (%s) + %s * (%s)- %s);" % (i, cur_sos2, expr2, cur_sos1, expr1, myeps_list[i])
            return ["", sos_eq]



        
    
    
    def convert_sub(i, sub):
        if sub['from'][0] != 'Inv':
            raise NotImplementedError
        elif len(sub['from']) == 1:
            raise NotImplementedError
        strfrom = 'inv'
        for i in range(1,len(sub['from'])):
            if sub['from'][i]['ty'] =='eq':
                strfrom = "replace("+strfrom+","+sub['from'][i]['lhs'].strip()+","+sub['from'][i]['rhs'].strip()+")"

        if len(sub['to']) != 1: 
            raise NotImplementedError
        strto = replace_subst(sub['to'][0])
        sos_eq = "f%d = sos(lambda2*(%s)-(%s)- %s);" % (i, strfrom, strto, myeps_list[i])
        return ["", sos_eq]
        
    def convert_ode(i, ode):
        """Convert an ODE constraint."""
        nonlocal num_flow
        nonlocal num_sos
        assert constraint['from'][0]['base'] == 'Inv' and constraint['to'] == ['Inv'], \
            "convert_ode: invalid form of ode."

        vars = constraint['from'][0]['vars']
        diffs = constraint['from'][0]['diffs']
        domain = constraint['from'][0]['domain']
        
        # Only consider domain of size 1 so far.

        cur_flow_name = "flow" + str(num_flow)
        cur_dinv_name = "dinv" + str(num_flow)
        cur_lie_name = "lie" + str(num_flow)
        cur_flow = "%s = %s;" % (cur_flow_name, str_list(diffs, '; '))
        cur_dinv = "%s = %s;" % (cur_dinv_name, str_list(["jacobian(inv," + var + ")" for var in vars], ', '))
        cur_lie = "%s = %s * %s;" % (cur_lie_name, cur_dinv_name, cur_flow_name)
        num_flow += 1

        if domain == 'True':
            sos_eq = "f%d = sos(-%s - lambda1 * inv - %s);" % (i, cur_lie_name, myeps_list[i])
        elif len(domain) == 1:
            expdomain = norm_to_ge_zero(domain[0])
            cur_sos = "s" + str(num_sos+1)
            num_sos += 1
            sos_eq = "f%d = sos(-%s - lambda1 * inv - %s * (%s) - %s);" % (i, cur_lie_name, cur_sos, expdomain, myeps_list[i])
        elif len(domain) == 2:
            expdomain1 = norm_to_ge_zero(domain[0])
            expdomain2 = norm_to_ge_zero(domain[1])
            expdomain = "("+expdomain1+") * ("+expdomain2+")"
            cur_sos = "s" + str(num_sos+1)
            num_sos += 1
            sos_eq = "f%d = sos(-%s - lambda1 * inv - %s * (%s) - %s);" % (i, cur_lie_name, cur_sos, expdomain, myeps_list[i])

        return ["", cur_flow, cur_dinv, cur_lie, sos_eq]

    body = []
    for i, constraint in enumerate(constraints):
        if is_precond_constraint(constraint):
            body.extend(convert_precond(i, constraint))
        elif is_postcond_constraint(constraint):
            body.extend(convert_postcond(i, constraint))
        elif is_ode_constraint(constraint):
            body.extend(convert_ode(i, constraint))
        elif is_sub_constraint(constraint):
            body.extend(convert_sub(i, constraint))
        else:
            raise NotImplementedError

    header = []
    header.append(str_spdvars)
    header.append(str_myeps)
    header.extend(str_lambdas)
    header.extend(str_tols)
    header.extend(["", str_poly_inv])

    def str_poly(i):
        return "[s%d, c%d] = polynomial(%s, 4);" % (i, i, str_list_vars)
    header.extend([str_poly(i) for i in range(1,num_sos+1)])

    feasibility_constraints = \
        ["f" + str(i) for i in range(num_constraints)] + \
        ["sos(s" + str(i) + ")" for i in range(1,num_sos+1)] + \
        [myeps_list[i] + ">=" + tol_list[i] for i in range(num_constraints)]
    str_feasibility = "FeasibilityConstraints=[" + ",".join(feasibility_constraints) + "];"

    options = "options=sdpsettings('verbose', 1, 'solver', 'mosek');"

    solve_vars = ["c" + str(i) for i in range(num_sos+1)] + myeps_list
    str_solve = "sos_ans = solvesos(FeasibilityConstraints, [], options, [" + ";".join(solve_vars) + "]);"

    print_if = "if sos_ans.problem == 0"
    print1 = "  mono_inv=monolist(%s, 6);" % str_list_vars
    print2 = "  pinv=double(c0')*mono_inv;"
    print3 = "  sdisplay(clean(pinv,1e-6))"
    print4 = "else"
    print5 = "  fprintf(\"error\\n\")"
    print6 = "end"
    print7 = "quit"

    footer = ["", str_feasibility, "", options, "", str_solve, "", print_if, print1, print2, print3, print4, print5, print6, print7]

    return "\n".join(header + body + footer)


def process_file(file_name):
    with open(file_name + ".json", "r", encoding="utf-8") as f:
        f_data = json.load(f)

    return process_data(f_data['vars'], f_data['constraints'])


if __name__ == "__main__":
    print(process_file("input"))
