# Program to generate matlab scripts.

import json

def str_list(strs, sep):
    return "[" + sep.join(strs) + "]"

def norm_to_ge_zero(cond):
    """Normalize the given condition to the form ... >= 0. Return
    the part that should be >= 0.
    
    """
    assert isinstance(cond, dict), "norm_to_ge_zero: invalid form of condition."
    if cond['ty'] == 'ge':
        return cond['lhs'] + '-' + cond['rhs']
    else:
        raise NotImplementedError

def is_ode_constraint(constraint):
    return len(constraint['from']) == 1 and isinstance(constraint['from'][0], dict) and \
           constraint['from'][0]['ty'] == 'ode'
    
def is_precond_constraint(constraint):
    return not is_ode_constraint(constraint) and \
           len(constraint['to']) == 1 and constraint['to'][0] == 'Inv'

def is_postcond_constraint(constraint):
    return not is_ode_constraint(constraint) and \
           len(constraint['from']) == 1 and constraint['from'][0] == 'Inv'

def process_data(spdvars, constraints):
    num_constraints = len(constraints)

    myeps_list = ["myeps" + str(n) for n in range(num_constraints)]
    tol_list = ["tol" + str(n) for n in range(num_constraints)]

    str_spdvars = "sdpvar " + " ".join(spdvars) + ";"
    str_myeps = "sdpvar " + " ".join(myeps_list) + ";"
    str_lambdas = ["", "lambda1 = .5;", "lambda2 = 1;"]
    str_tols = [""] + [tol + " = 1e-4;" for tol in tol_list]

    str_list_vars = str_list(spdvars, ' ')
    str_poly_inv = "[inv, c0] = polynomial(%s, 6);" % str_list_vars

    num_flow = 0
    num_sos = 0

    def convert_precond(i, precond):
        """Convert constraint of the form precond --> Inv."""
        nonlocal num_sos

        if len(precond['from']) != 1:
            raise NotImplementedError

        expr = norm_to_ge_zero(precond['from'][0])
        cur_sos = "s" + str(num_sos+1)
        num_sos += 1

        sos_eq = "f%d = sos(-inv - %s * (%s) - %s);" % (i, cur_sos, expr, myeps_list[i])
        return ["", sos_eq]

    def convert_postcond(i, postcond):
        """Convert constraint of the form Inv --> postcond."""
        nonlocal num_sos

        if len(postcond['to']) != 1:
            raise NotImplementedError

        expr = norm_to_ge_zero(postcond['to'][0])
        expr = "-(%s)" % expr
        cur_sos = "s" + str(num_sos+1)
        num_sos += 1

        sos_eq = "f%d = sos(inv - %s * (%s) - %s);" % (i, cur_sos, expr, myeps_list[i])
        return ["", sos_eq]

    def convert_ode(i, ode):
        """Convert an ODE constraint."""
        nonlocal num_flow

        assert constraint['from'][0]['base'] == 'Inv' and constraint['to'] == ['Inv'], \
            "convert_ode: invalid form of ode."

        vars = constraint['from'][0]['vars']
        diffs = constraint['from'][0]['diffs']
        domain = constraint['from'][0]['domain'].strip()

        cur_flow_name = "flow" + str(num_flow)
        cur_dinv_name = "dinv" + str(num_flow)
        cur_lie_name = "lie" + str(num_flow)
        cur_flow = "%s = %s;" % (cur_flow_name, str_list(diffs, ';'))
        cur_dinv = "%s = %s;" % (cur_dinv_name, str_list(["jacobian(inv," + var + ")" for var in vars], ','))
        cur_lie = "%s = %s * %s;" % (cur_lie_name, cur_dinv_name, cur_flow_name)
        num_flow += 1

        if domain == 'True':
            sos_eq = "f%d = sos(-%s - lambda1 * inv - %s);" % (i, cur_lie_name, myeps_list[i])
        else:
            raise NotImplementedError

        return ["", cur_flow, cur_dinv, cur_lie, sos_eq]

    body = []
    for i, constraint in enumerate(constraints):
        if is_precond_constraint(constraint):
            body.extend(convert_precond(i, constraint))
        elif is_postcond_constraint(constraint):
            body.extend(convert_postcond(i, constraint))
        elif is_ode_constraint(constraint):
            body.extend(convert_ode(i, constraint))
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

    options = "options=sdpsettings('verbose', 1, 'solver', 'sdpt3');"

    solve_vars = ["c" + str(i) for i in range(num_sos+1)] + myeps_list
    str_solve = "solvesos(FeasibilityConstraints, [], options, [" + ";".join(solve_vars) + "])"

    footer = ["", str_feasibility, "", options, "", str_solve]

    return "\n".join(header + body + footer)


def process_file(file_name):
    with open("tests/" + file_name + ".json", "r", encoding="utf-8") as f:
        f_data = json.load(f)

    return process_data(f_data['vars'], f_data['constraints'])


if __name__ == "__main__":
    print(process_file("test1"))
