# Program to generate redlog scripts for checking an invariant.

import json

from script_common import *

def str_of_cond(cond):
    """Return the string form of a condition."""

    if isinstance(cond, dict):
        if cond['ty'] == 'ge':
            return "(%s >= %s)" % (cond['lhs'], cond['rhs'])
        elif cond['ty'] == 'gt':
            return "(%s > %s)" % (cond['lhs'], cond['rhs'])
        elif cond['ty'] == 'le':
            return "(%s <= %s)" % (cond['lhs'], cond['rhs'])
        elif cond['ty'] == 'lt':
            return "(%s < %s)" % (cond['lhs'], cond['rhs'])
        else:
            raise NotImplementedError
    elif cond == "Inv":
        return "(inv <= 0)"
    else:
        raise NotImplementedError

def str_of_conds(conds):
    return " and ".join([str_of_cond(cond) for cond in conds])

def process_data(spdvars, str_inv, constraints):
    num_constraints = len(constraints)

    num_ode = 0
    defs = []
    checks = []

    def forall_vars(str):
        for var in reversed(spdvars):
            str = "all(%s, %s)" % (var, str)
        return str

    def convert_precond(precond):
        """Convert constraint of the form precond --> Inv."""
        defs.append("pre := " + str_of_conds(precond['from']) + ";")
        checks.append("rlqe " + forall_vars("(not pre) or inv <= 0") + ";")

    def convert_postcond(postcond):
        """Convert constraint of the form Inv --> postcond."""
        defs.append("post := " + str_of_conds(postcond['to']) + ";")
        checks.append("rlqe " + forall_vars("(not (inv <= 0)) or post") + ";")

    def convert_ode(ode):
        """Convert an ODE constraint."""
        nonlocal num_ode

        assert constraint['from'][0]['base'] == 'Inv' and constraint['to'] == ['Inv'], \
            "convert_ode: invalid form of ode."

        vars = constraint['from'][0]['vars']
        diffs = constraint['from'][0]['diffs']
        domain = constraint['from'][0]['domain'].strip()

        str_ds = ["d%s%d := %s;" % (var, num_ode, diff) for var, diff in zip(vars, diffs)]
        str_lie_expr = " + ".join("df(inv,%s) * d%s%d" % (var, var, num_ode) for var in vars)
        str_lie = "lie%d := %s" % (num_ode, str_lie_expr) + ";"
        str_check_ode = "rlqe " + forall_vars("(not (inv = 0)) or lie%d < 0" % num_ode) + ";"
        num_ode += 1

        if domain == "True":
            defs.extend(str_ds + [str_lie])
            checks.append(str_check_ode)
        else:
            raise NotImplementedError

    for constraint in constraints:
        if is_precond_constraint(constraint):
            convert_precond(constraint)
        elif is_postcond_constraint(constraint):
            convert_postcond(constraint)
        elif is_ode_constraint(constraint):
            convert_ode(constraint)
        else:
            raise NotImplementedError


    str_load = "load_package \"qepcad\";"
    str_inv = "inv := " + str_inv + ";"
    str_open = "out output;"
    str_close = "shut output;"

    return "\n".join([str_load, str_inv] + defs + [str_open] + checks + [str_close])

def process_file(file_name):
    with open(file_name + ".json", "r", encoding="utf-8") as f:
        f_data = json.load(f)

    return process_data(f_data['vars'], f_data['inv'], f_data['constraints'])


if __name__ == "__main__":
    print(process_file("input"))
