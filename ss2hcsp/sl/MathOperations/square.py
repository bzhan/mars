from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, true_expr, RelExpr, AConst, OpExpr
from ss2hcsp.hcsp import hcsp as hp


def convert_square(in_var):
    """Compute the assignment corresponding to a square block."""
    return OpExpr("*", AVar(in_var), AVar(in_var))


class Square(SL_Block):
    """Compute the square"""
    def __init__(self, name, operator, st=-1):
        super(Square, self).__init__("square", name, 1, 1, st)

        assert operator == 'square'
        self.operator = operator

    def __str__(self):
        in_var = self.dest_lines[0].name
        expr = convert_square(in_var)
        out_var = self.src_lines[0][0].name
        return "%s: %s = %s  (st = %s)" % (self.name, out_var, expr, self.st)

    def __repr__(self):
        return "Square(%s, %s, %s, in = %s, out = %s)" % \
            (self.name, self.operator, self.st, str(self.dest_lines), str(self.src_lines))

    def get_output_hp(self):
        in_var = self.dest_lines[0].name
        expr = convert_square(in_var)
        out_var = self.src_lines[0][0].name
        cond = RelExpr("==", OpExpr("%", AVar("t"), AConst(self.st)), AConst(0))
        return hp.Condition(cond=cond, hp=hp.Assign(var_name=out_var, expr=expr))

    def get_var_subst(self):
        in_var = self.dest_lines[0].name
        expr = convert_square(in_var)
        out_var = self.src_lines[0][0].name
        return {out_var: expr}

    def get_var_map(self):
        in_var = AVar(self.dest_lines[0].name)
        if self.operator == "square":
            expr = OpExpr("*", in_var, in_var)
            out_var = self.src_lines[0][0].name
            return {out_var: [(true_expr, expr)]}
