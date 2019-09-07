"""Pretty-printing for HCSP commands."""

from ss2hcsp.hcsp import hcsp

def pprint_lines(hp, max_line=None):
    """Pretty-printing for a HCSP command.
    
    If max_line=None, always change line on sequence, select_comm,
    and parallel.

    Otherwise, change line only if not changing line would result in
    exceeding the width (note indentation is not counted in the width,
    so the actual printed line may exceed the width by a little).

    """
    def rec(hp):
        if max_line and len(str(hp)) <= max_line:
            return [str(hp)]
        if hp.type == 'sequence':
            args_lines = [rec(hp) for hp in hp.hps]
            res = []
            for i, arg_lines in enumerate(args_lines):
                res.extend(arg_lines)
                if i != len(args_lines) - 1:
                    res[-1] = res[-1] + ";"
            return res
        elif hp.type == 'condition':
            if hp.hp.type == 'sequence' or hp.hp.type == 'select_comm':
                lines = rec(hp.hp)
                return [str(hp.cond) + " -> ("] + ["  " + line for line in lines] + [")"]
            else:
                return [str(hp)]
        elif hp.type == 'select_comm':
            args_lines = [rec(hp) for hp in hp.hps]
            res = []
            for i, arg_lines in enumerate(args_lines):
                if hp.hps[i].type == 'sequence':
                    arg_lines = [arg_lines[0]] + ["  " + line for line in arg_lines[1:]]
                res.extend(arg_lines)
                if i != len(args_lines) - 1:
                    res[-1] = res[-1] + " $"
            return res
        elif hp.type == 'parallel':
            args_lines = [rec(hp) for hp in hp.hps]
            res = []
            for i, arg_lines in enumerate(args_lines):
                res.extend(arg_lines)
                if i != len(args_lines) - 1:
                    res[-1] = res[-1] + " ||"
            return res
        else:
            return [str(hp)]

    return rec(hp)


def pprint(hp):
    return '\n'.join(pprint_lines(hp))
