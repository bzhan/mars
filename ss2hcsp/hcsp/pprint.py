"""Pretty-printing for HCSP commands."""

from ss2hcsp.hcsp.expr import true_expr
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import expr


def pprint_lines(hp, *, max_line=None, record_pos=False):
    """Pretty-printing for a HCSP command.
    
    If max_line=None, always change line on sequence, select_comm,
    and parallel.

    Otherwise, change line only if not changing line would result in
    exceeding the width (note indentation is not counted in the width,
    so the actual printed line may exceed the width by a little).

    If record_pos is True, return an additional dictionary mapping
    program positions to where the corresponding position in the
    program is printed.

    """
    lines = []

    if record_pos:
        mapping = dict()

    def new_line(indent):
        lines.append(" " * indent)

    def add_str(s):
        lines[-1] += s

    def start_pos(pos):
        if record_pos:
            pos = 'p' + ','.join(str(p) for p in pos)
            mapping[pos] = {'start_x': len(lines)-1, 'start_y': len(lines[-1])}

    def end_pos(pos):
        if record_pos:
            pos = 'p' + ','.join(str(p) for p in pos)
            mapping[pos].update({'end_x': len(lines)-1, 'end_y': len(lines[-1])})

    def rec(hp, indent, pos):
        if max_line and len(str(hp)) <= max_line:
            new_line(indent)
            add_str(str(hp))

        elif hp.type == 'sequence':
            for i, sub_hp in enumerate(hp.hps):
                if sub_hp.type == 'select_comm':
                    new_line(indent)
                    add_str("{")
                    rec(sub_hp, indent+2, pos+(i,))
                    new_line(indent)
                    add_str("}")
                else:
                    rec(sub_hp, indent, pos+(i,))

        elif hp.type == 'select_comm':
            new_line(indent)
            start_pos(pos)
            for i, (comm_hp, out_hp) in enumerate(hp.io_comms):
                comm_hp_no_semicolon = str(comm_hp)[:-1]
                if out_hp.type == 'select_comm':
                    add_str("%s --> {" % comm_hp_no_semicolon)
                    rec(out_hp, indent+2, pos+(i,))
                    if i != len(hp.io_comms) - 1:
                        new_line(indent)
                        add_str("} $")
                        new_line(indent)
                    else:
                        new_line(indent)
                        add_str("}")
                else:
                    add_str("%s -->" % comm_hp_no_semicolon)
                    rec(out_hp, indent+2, pos+(i,))
                    if i != len(hp.io_comms) - 1:
                        add_str(" $")
                        new_line(indent)
            end_pos(pos)

        elif hp.type == 'loop':
            new_line(indent),
            add_str("{")
            rec(hp.hp, indent+2, pos+(0,))
            new_line(indent)
            if hp.constraint == true_expr:
                add_str("}*")
            else:
                add_str("}*(%s)" % hp.constraint)

        elif hp.type == 'ode':
            new_line(indent)
            start_pos(pos)
            str_eqs = ", ".join(var_name + "_dot = " + str(expr) for var_name, expr in hp.eqs)
            conjs = expr.split_conj(hp.constraint)
            if len(conjs) == 1:
                add_str("{%s & %s}" % (str_eqs, hp.constraint))
            else:
                add_str("{%s &" % str_eqs)
                for i, constraint in enumerate(conjs):
                    new_line(indent+2)
                    if i != len(conjs)-1:
                        add_str("%s &&" % constraint)
                    else:
                        add_str("%s" % constraint)
                new_line(indent)
                add_str("}")
            end_pos(pos)

        elif hp.type == 'ode_comm':
            new_line(indent)
            start_pos(pos)
            str_eqs = ", ".join(var_name + "_dot = " + str(expr) for var_name, expr in hp.eqs)
            add_str("{%s & %s} |> [] (" % (str_eqs, hp.constraint))
            for i, (comm_hp, out_hp) in enumerate(hp.io_comms):
                new_line(indent+2)
                add_str("%s -->" % str(comm_hp)[:-1])
                rec(out_hp, indent+4, pos+(i,))
                if i != len(hp.io_comms) - 1:
                    add_str(",")
            new_line(indent)
            add_str(")")
            end_pos(pos)
        
        elif hp.type == 'recursion':
            new_line(indent)
            start_pos(pos)
            add_str("rec %s {" % hp.entry)
            rec(hp.hp, indent+2, pos+(0,))
            new_line(indent)
            add_str("}")
            end_pos(pos)

        elif hp.type == 'ite':
            new_line(indent)
            start_pos(pos)
            add_str("if (%s) {" % hp.if_hps[0][0])
            rec(hp.if_hps[0][1], indent+2, pos+(0,))
            new_line(indent)
            for i, (cond, sub_hp) in enumerate(hp.if_hps[1:], 1):
                add_str("} else if (%s) {" % cond)
                rec(sub_hp, indent+2, pos+(i,))
                new_line(indent)
            if hp.else_hp is not None:
                add_str("} else {")
                rec(hp.else_hp, indent+2, pos+(len(hp.if_hps),))
                new_line(indent)
            add_str("}")
            end_pos(pos)
            
        else:
            new_line(indent)
            start_pos(pos)
            add_str(str(hp))
            end_pos(pos)

    rec(hp, 0, ())
    if record_pos:
        return lines, mapping
    else:
        return lines


def pprint(hp):
    return '\n'.join(pprint_lines(hp))
