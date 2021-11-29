from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, AConst, true_expr, OpExpr, RelExpr
import ss2hcsp.hcsp.hcsp as hp


class Bias(SL_Block):
    def __init__(self, name, bias=0, st=-1):
        super(Bias, self).__init__("bias", name, 1, 1, st)

        assert isinstance(bias, (int, float))
        self.bias = bias

    def get_expr(self):
        """Compute the assignment corresponding to bias block."""
        in_var = AVar(self.dest_lines[0].name)
        if self.bias >= 0:
            return OpExpr("+", in_var, AConst(self.bias))
        else:
            return OpExpr("-", in_var, AConst(-self.bias))

    def __str__(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return "%s: %s = %s  (st = %s)" % (self.name, out_var, expr, self.st)

    def __repr__(self):
        return "Bias(%s, %s, %s, in = %s, out = %s)" % \
            (self.name, self.bias, self.st, str(self.dest_lines), str(self.src_lines))

    def get_output_hp(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return hp.Assign(out_var, expr)

    def get_var_subst(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return {out_var: expr}

    def get_var_map(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return {out_var: [(true_expr, expr)]}
