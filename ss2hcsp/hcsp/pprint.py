"""Pretty-printing for HCSP commands."""

from ss2hcsp.hcsp import hcsp

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
            pos = 'p' + '.'.join(str(p) for p in pos)
            mapping[pos] = {'start_x': len(lines)-1, 'start_y': len(lines[-1])}

    def end_pos(pos):
        if record_pos:
            pos = 'p' + '.'.join(str(p) for p in pos)
            mapping[pos].update({'end_x': len(lines)-1, 'end_y': len(lines[-1])})

    def rec(hp, indent, pos):
        if max_line and len(str(hp)) <= max_line:
            new_line(indent)
            add_str(str(hp))

        elif hp.type == 'sequence':
            for i, sub_hp in enumerate(hp.hps):
                rec(sub_hp, indent, pos+(i,))
                if i != len(hp.hps) - 1:
                    add_str(';')

        elif hp.type == 'condition':
            new_line(indent)
            start_pos(pos)
            if hp.hp.type == 'sequence' or hp.hp.type == 'select_comm':
                add_str(str(hp.cond) + " -> (")
                start_pos(pos+(0,))
                rec(hp.hp, indent+2, pos+(0,))
                end_pos(pos+(0,))
                new_line(indent)
                add_str(")")
            else:
                add_str(str(hp.cond) + " -> ")
                start_pos(pos+(0,))
                add_str(str(hp.hp))
                end_pos(pos+(0,))
            end_pos(pos)

        elif hp.type == 'select_comm':
            new_line(indent)
            start_pos(pos)
            for i, (comm_hp, out_hp) in enumerate(hp.io_comms):
                add_str("%s -->" % comm_hp)
                rec(out_hp, indent+2, pos+(i,))
                if i != len(hp.io_comms) - 1:
                    add_str(" $")
                    new_line(indent)
            end_pos(pos)

        elif hp.type == 'loop':
            new_line(indent),
            add_str("(")
            rec(hp.hp, indent+2, pos)
            new_line(indent)
            add_str(")**")

        elif hp.type == 'ode_comm':
            new_line(indent)
            start_pos(pos)
            str_eqs = ", ".join(var_name + "_dot = " + str(expr) for var_name, expr in hp.eqs)
            add_str("<%s & %s> |> [] (" % (str_eqs, hp.constraint))
            for i, (comm_hp, out_hp) in enumerate(hp.io_comms):
                new_line(indent+2)
                add_str("%s -->" % comm_hp)
                rec(out_hp, indent+4, pos+(i,))
            new_line(indent)
            add_str(")")
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
