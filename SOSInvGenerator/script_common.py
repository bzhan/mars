# Common procedures for script generation.

def str_list(strs, sep):
    return "[" + sep.join(strs) + "]"

def is_ode_constraint(constraint):
    return len(constraint['from']) == 1 and isinstance(constraint['from'][0], dict) and \
           constraint['from'][0]['ty'] == 'ode'
    
def is_precond_constraint(constraint):
    return not is_ode_constraint(constraint) and \
           len(constraint['to']) == 1 and constraint['to'][0] == 'Inv'

def is_postcond_constraint(constraint):
    return not is_ode_constraint(constraint) and \
            constraint['from'][0] == 'Inv'
