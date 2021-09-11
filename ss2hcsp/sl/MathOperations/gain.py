from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, AConst, true_expr, RelExpr, OpExpr
import ss2hcsp.hcsp.hcsp as hp


def convert_gain(factor, in_var):
    """Compute the assignment corresponding to gain block."""
    return OpExpr("*", AVar(in_var), AConst(factor))


class Gain(SL_Block):
    """Multiply dest line by a factor."""
    def __init__(self, name, factor=1, st=-1):
        super(Gain, self).__init__()
        self.name = name
        self.type = "gain"
        self.is_continuous = (st == 0)
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]

        assert isinstance(factor, (int, float))
        self.factor = factor

        assert isinstance(st, (int, float))
        self.st = st

    def __str__(self):
        in_vars = self.dest_lines[0].name
        expr = convert_gain(self.factor, in_vars)
        out_var = self.src_lines[0][0].name
        return "%s: %s = %s  (st = %s)" % (self.name, out_var, str(expr), str(self.st))

    def __repr__(self):
        return "Gain(%s, %s, %s, in = %s, out = %s)" % \
            (self.name, self.factor, self.st, str(self.dest_lines), str(self.src_lines))

    def get_output_hp(self):
        in_var = self.dest_lines[0].name
        expr = convert_gain(self.factor, in_var)
        out_var = self.src_lines[0][0].name
        cond = RelExpr("==", OpExpr("%", AVar("t"), AConst(self.st)), AConst(0))
        return hp.Condition(cond=cond, hp=hp.Assign(var_name=out_var, expr=expr))

    def get_var_subst(self):
        in_var = self.dest_lines[0].name
        expr = convert_gain(self.factor, in_var)
        out_var = self.src_lines[0][0].name
        return {out_var: expr}

    def get_var_map(self):
        in_var = self.dest_lines[0].name
        expr = convert_gain(self.factor, in_var)
        out_var = self.src_lines[0][0].name
        return {out_var: [(true_expr, expr)]}
