from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, RelExpr, AConst, FunExpr, OpExpr, IfExpr
from ss2hcsp.hcsp import hcsp as hp


class Sqrt(SL_Block):
    """Compute the square root"""
    def __init__(self, name, operator, st=-1):
        super(Sqrt, self).__init__("sqrt", name, 1, 1, st)

        assert operator == 'signedSqrt'
        self.operator = operator

    def get_expr(self):
        in_var = AVar(self.dest_lines[0].name)
        return IfExpr(
            RelExpr(">=", in_var, AConst(0)),
            FunExpr("sqrt", [in_var]),
            OpExpr("-", FunExpr("sqrt", [OpExpr("-", in_var)])))

    def __str__(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return "%s: %s = %s  (st = %s)" % (self.name, out_var, expr, str(self.st))

    def __repr__(self):
        return "Sqrt(%s, %s, %s, in = %s, out = %s)" % \
            (self.name, self.operator, self.st, str(self.dest_lines), str(self.src_lines))

    def get_output_hp(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return hp.Assign(out_var, expr)

    def get_var_subst(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return {out_var: expr}
