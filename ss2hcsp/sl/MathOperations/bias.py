from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, AConst, true_expr, OpExpr, RelExpr
import ss2hcsp.hcsp.hcsp as hp


def convert_bias(bias, in_var):
    """Compute the assignment corresponding to bias block."""
    if bias >= 0:
        return OpExpr("+", AVar(in_var), AConst(bias))
    else:
        return OpExpr("-", AVar(in_var), AConst(-bias))


class Bias(SL_Block):
    def __init__(self, name, bias=0, st=-1):
        super(Bias, self).__init__("bias", name, 1, 1, st)

        assert isinstance(bias, (int, float))
        self.bias = bias

    def __str__(self):
        in_var = self.dest_lines[0].name
        expr = convert_bias(self.bias, in_var)
        out_var = self.src_lines[0][0].name
        return "%s: %s = %s  (st = %s)" % (self.name, out_var, expr, self.st)

    def __repr__(self):
        return "Bias(%s, %s, %s, in = %s, out = %s)" % \
            (self.name, self.bias, self.st, str(self.dest_lines), str(self.src_lines))

    def get_output_hp(self):
        in_var = self.dest_lines[0].name
        expr = convert_bias(self.bias, in_var)
        out_var = self.src_lines[0][0].name
        cond = RelExpr("==", OpExpr("%", AVar("t"), AConst(self.st)), AConst(0))
        return hp.Condition(cond=cond, hp=hp.Assign(var_name=out_var, expr=expr))

    def get_var_subst(self):
        in_var = self.dest_lines[0].name
        expr = convert_bias(self.bias, in_var)
        out_var = self.src_lines[0][0].name
        return {out_var: expr}

    def get_var_map(self):
        in_var = self.dest_lines[0].name
        expr = convert_bias(self.bias, in_var)
        out_var = self.src_lines[0][0].name
        return {out_var: [(true_expr, expr)]}
