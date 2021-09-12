from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, true_expr, RelExpr, AConst, OpExpr
from ss2hcsp.hcsp import hcsp as hp


class Square(SL_Block):
    """Compute the square"""
    def __init__(self, name, operator, st=-1):
        super(Square, self).__init__("square", name, 1, 1, st)

        assert operator == 'square'
        self.operator = operator

    def get_expr(self):
        """Compute the assignment corresponding to a square block."""
        in_var = AVar(self.dest_lines[0].name)
        return OpExpr("*", in_var, in_var)

    def __str__(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return "%s: %s = %s  (st = %s)" % (self.name, out_var, expr, self.st)

    def __repr__(self):
        return "Square(%s, %s, %s, in = %s, out = %s)" % \
            (self.name, self.operator, self.st, str(self.dest_lines), str(self.src_lines))

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
        if self.operator == "square":
            expr = OpExpr("*", in_var, in_var)
            out_var = self.src_lines[0][0].name
            return {out_var: [(true_expr, expr)]}
