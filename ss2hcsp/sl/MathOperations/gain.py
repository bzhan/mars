
from typing import Dict
from ss2hcsp.matlab import function
from ss2hcsp.matlab import convert
from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp import expr
import ss2hcsp.hcsp.hcsp as hp


class Gain(SL_Block):
    """Multiply dest line by a factor."""
    def __init__(self, name: str, factor: function.Expr, st=-1):
        super(Gain, self).__init__("gain", name, 1, 1, st)

        assert isinstance(factor, function.Expr)
        self.factor = factor

    def get_expr(self) -> expr.Expr:
        """Compute the assignment corresponding to gain block."""
        in_var = expr.AVar(self.dest_lines[0].name)
        return expr.OpExpr("*", in_var, convert.convert_expr(self.factor)[1])

    def __str__(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return "%s: %s = %s  (st = %s)" % (self.name, out_var, str(expr), str(self.st))

    def __repr__(self):
        return "Gain(%s, %s, %s, in = %s, out = %s)" % \
            (self.name, self.factor, self.st, str(self.dest_lines), str(self.src_lines))

    def get_output_hp(self) -> hp.HCSP:
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return hp.Assign(out_var, expr)

    def get_var_subst(self) -> Dict[str, expr.Expr]:
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return {out_var: expr}
