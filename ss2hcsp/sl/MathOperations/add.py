from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, OpExpr, true_expr, RelExpr, AConst
from ss2hcsp.hcsp import hcsp as hp


def convert_add(spec, in_vars):
    if spec[0] == '+':
        expr = in_vars[0]
    else:
        expr = OpExpr("-", in_vars[0])
    for op, in_var in zip(spec[1:], in_vars[1:]):
        if op == '+':
            expr = OpExpr("+", expr, in_var)
        else:
            expr = OpExpr("-", expr, in_var)
    return expr

class Add(SL_Block):
    """Add (or subtract) a list of dest lines."""
    def __init__(self, name, dest_spec, st=-1):
        super(Add, self).__init__()
        """dest_spec is a list of either '+' or '-'."""
        self.name = name
        self.type = "add"
        self.is_continuous = (st == 0)
        self.num_src = 1
        self.num_dest = len(dest_spec)
        self.src_lines = [[]]
        self.dest_lines = [None] * self.num_dest

        assert all(s == '+' or s == '-' for s in dest_spec)
        self.dest_spec = dest_spec  # string

        assert isinstance(st, (int, float))
        self.st = st

    def __str__(self):
        return "%s: Add[in = %s, out = %s, st = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), str(self.st))

    def __repr__(self):
        return str(self)

    def get_output_hp(self):
        in_vars = [AVar(line.name) for line in self.dest_lines]
        expr = convert_add(self.dest_spec, in_vars)
        out_var = self.src_lines[0][0].name
        time_cond = RelExpr("==", OpExpr("%", AVar("t"), AConst(self.st)), AConst(0))
        return hp.Condition(cond=time_cond, hp=hp.Assign(var_name=out_var, expr=expr))

    def get_var_map(self):
        in_vars = [AVar(line.name) for line in self.dest_lines]
        expr = convert_add(self.dest_spec, in_vars)
        out_var = self.src_lines[0][0].name
        return {out_var: [(true_expr, expr)]}
