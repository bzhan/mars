"""Transfer function"""

from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp import expr
from ss2hcsp.matlab import function

class TransferFcn(SL_Block):
    def __init__(self, name, denom: function.Expr):
        super(TransferFcn, self).__init__("transfer_fcn", name, 1, 1, st=0)
        self.denom = denom

    def __str__(self):
        in_var = expr.AVar(self.dest_lines[0].name)
        out_var = expr.AVar(self.src_lines[0][0].name)
        coeff = self.get_coeff()
        return "%s: %s_dot = -%s * %s + %s * %s" % (self.name, out_var, coeff, out_var, coeff, in_var)

    def get_coeff(self) -> float:
        assert isinstance(self.denom, function.ListExpr)
        assert len(self.denom.args) == 2
        assert self.denom.args[1] == function.AConst(1)
        assert isinstance(self.denom.args[0], function.AConst)
        return 1.0 / self.denom.args[0].value

    def __repr__(self):
        return "TransferFcn(%s, %s)" % (self.name, self.denom)
