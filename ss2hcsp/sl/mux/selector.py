"""Selector block"""

from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp import expr
from ss2hcsp.matlab import function

class Selector(SL_Block):
    def __init__(self, name: str, width: int, indices: function.Expr):
        super(Selector, self).__init__("selector", name, 1, 1, st=0)
        self.width = width
        self.indices = indices

    def get_expr(self):
        in_var = expr.AVar(self.dest_lines[0].name)
        assert isinstance(self.indices, function.ListExpr)
        hp_args = []
        for arg in self.indices.args:
            assert isinstance(arg, function.AConst)
            hp_args.append(expr.ArrayIdxExpr(in_var, expr.AConst(arg.value - 1)))
        return expr.ListExpr(*hp_args)

    def __str__(self):
        out_var = self.src_lines[0][0].name
        return "%s: %s = %s" % (self.name, out_var, self.get_expr())

    def __repr__(self):
        return "Selector(%s, %s, %s)" % (self.name, self.width, self.indices)

    def get_var_subst(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return {out_var: expr}
