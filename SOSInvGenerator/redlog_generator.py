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
        elif cond['ty'] == 'eq':
            return "(%s = %s)" % (cond['lhs'], cond['rhs'])
        else:
            raise NotImplementedError
    elif cond == "Inv":
        return "(inv)"
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
        checks.append("rlqe " + forall_vars("(not pre) or inv ") + ";")

    def convert_postcond(postcond):
        """Convert constraint of the form Inv --> postcond."""
        defs.append("post := " + str_of_conds(postcond['to']) + ";")
        checks.append("rlqe " + forall_vars("(not (inv)) or post") + ";")

    def convert_ode(ode):
        """Convert an ODE constraint."""
        nonlocal num_ode

        assert constraint['from'][0]['base'] == 'Inv' and constraint['to'] == ['Inv'], \
            "convert_ode: invalid form of ode."
      
        vars = constraint['from'][0]['vars']
        diffs = constraint['from'][0]['diffs']
        domain = constraint['from'][0]['domain']

        # Only consider domain of size 1 so far.
        if len(domain) > 1:
            raise NotImplementedError
        domain = domain[0].strip()

        str_ds = ["d%s%d := %s;" % (var, num_ode, diff) for var, diff in zip(vars, diffs)]
        defs.extend(str_ds)
        stepinv = " "
        for item in range(str_inv.count("&")+1):
            subinv = str_inv.split("&")[item]
            if subinv.find(">=") >= 0 :
                subinvp=subinv[0:subinv.find(">=")]
            elif subinv.find("<=") >= 0 :
                subinvp=subinv[0:subinv.find("<=")]
            elif subinv.find("=") >= 0 :
                subinvp=subinv[0:subinv.find("=")]
            elif subinv.find(">") >= 0 :
                subinvp=subinv[0:subinv.find(">")]
            elif subinv.find("<") >= 0 :
                subinvp=subinv[0:subinv.find("<")]
            str_subinv = "inv"+str(item) + " := " + subinv + ";" 
            str_subinvp = "invp"+str(item)+ " := " + subinvp + ";" 
            defs.extend([str_subinv])
            defs.extend([str_subinvp])
            str_lie_expr = " + ".join("df(invp%i,%s) * d%s%d" % (item, var, var, num_ode) for var in vars)
            str_lie = "lie%d%i := %s" % (num_ode, item, str_lie_expr) + ";"
            if subinv.find(">=") >= 0 :
                str_check_ode = "rlqe " + forall_vars("not ("+domain+stepinv+") or ((not (invp%i = 0)) or lie%d%i > 0) or lie%d%i >= 0" % (item, num_ode, item, num_ode, item)) + ";"
            elif subinv.find("<=") >= 0 :
                str_check_ode = "rlqe " + forall_vars("not ("+domain+stepinv+") or ((not (invp%i = 0)) or lie%d%i < 0) or lie%d%i <= 0" % (item, num_ode, item, num_ode, item)) + ";"
            elif subinv.find("=") >= 0 :
                str_check_ode = "rlqe " + forall_vars("not ("+domain+stepinv+") or (lie%d%i = 0)" % (num_ode, item)) + ";"
            elif subinv.find("<") >= 0 :
                str_check_ode = "rlqe " + forall_vars("not ("+domain+stepinv+") or ((not (invp%i = 0)) or lie%d%i < 0) or lie%d%i <= 0" % (item, num_ode, item, num_ode, item)) + ";"
            elif subinv.find(">") >= 0 :
                str_check_ode = "rlqe " + forall_vars("not ("+domain+stepinv+") or ((not (invp%i = 0)) or lie%d%i > 0) or lie%d%i >= 0" % (item, num_ode, item, num_ode, item)) + ";"
            stepinv = stepinv+"and  "+subinv 
            defs.extend([str_lie])
            checks.append(str_check_ode)
        
        num_ode += 1

        
        
        
        
        
        
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
