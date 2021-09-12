from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, FunExpr, true_expr, RelExpr, AConst
from ss2hcsp.hcsp import hcsp as hp


class Abs(SL_Block):
    """Compute the absolute value of the dest line."""
    def __init__(self, name, st=-1):
        super(Abs, self).__init__("abs", name, 1, 1, st)

    def get_expr(self):
        in_var = AVar(self.dest_lines[0].name)
        return FunExpr("abs", [in_var])
        
    def __str__(self):
        out_var = self.src_lines[0][0].name
        expr = self.get_expr()
        return "%s: %s = %s  (st = %s)" % (self.name, out_var, expr, self.st)

    def __repr__(self):
        return "Abs(%s, %s, in = %s, out = %s)" % \
            (self.name, self.st, self.dest_lines, self.src_lines)

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
        expr = FunExpr("abs", [in_var])
        out_var = self.src_lines[0][0].name
        return {out_var: [(true_expr, expr)]}
