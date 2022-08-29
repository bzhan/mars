from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, AConst, LogicExpr, RelExpr, IfExpr, OpExpr
from ss2hcsp.hcsp import hcsp as hp


class Saturation(SL_Block):
    """Compute the saturation value of the dest_line wrt. the upper and lower limits."""
    def __init__(self, name, up_lim, low_lim, st=-1):
        super(Saturation, self).__init__("saturation", name, 1, 1, st)

        assert isinstance(up_lim, (int, float)) and isinstance(low_lim, (int, float))
        self.up_lim = up_lim
        self.low_lim = low_lim

    def get_expr(self):
        in_var = AVar(self.dest_lines[0].name)
        return IfExpr(RelExpr("<=", in_var, AConst(self.low_lim)), AConst(self.low_lim),
                      IfExpr(RelExpr(">=", in_var, AConst(self.up_lim)), AConst(self.up_lim), in_var))

    def __str__(self):
        out_var = self.src_lines[0][0].name
        expr = self.get_expr()
        return "%s: %s = %s  (st = %s)" % (self.name, out_var, expr, self.st)

    def __repr__(self):
        return "Saturation(%s, %s, %s, %s, in = %s, out = %s)" % \
            (self.name, self.up_lim, self.low_lim, self.st, str(self.dest_lines), str(self.src_lines))

    def get_output_hp(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return hp.Assign(out_var, expr)

    def get_var_subst(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return {out_var: expr}

    def get_var_map(self):
        in_var = AVar(self.dest_lines[0].name)
        cond0 = RelExpr("<", in_var, AConst(self.low_lim))
        expr0 = AConst(self.low_lim)
        cond1 = RelExpr(">", in_var, AConst(self.up_lim))
        expr1 = AConst(self.up_lim)
        cond2 = LogicExpr("&&", cond0.neg(), cond1.neg())
        expr2 = in_var
        out_var = self.src_lines[0][0].name
        return {out_var: [(cond0, expr0), (cond1, expr1), (cond2, expr2)]}
