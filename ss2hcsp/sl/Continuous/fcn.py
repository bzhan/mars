"""Simulink function block"""

from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.matlab import function
from ss2hcsp.matlab import convert
from ss2hcsp.hcsp import expr

class Fcn(SL_Block):
    def __init__(self, name, expr: function.Expr):
        super(Fcn, self).__init__("fcn", name, 1, 1, st=0)
        self.expr = expr

    def get_expr(self):
        """Compute the assignment corresponding to the function block"""
        in_vars = [expr.AVar(line.name) for line in self.dest_lines]
        assert len(in_vars) == 1
        in_var = in_vars[0]

        # Replace function application u by array access
        _, hp_expr = convert.convert_expr(self.expr, arrays={'u'})
        hp_expr = hp_expr.subst({'u': in_var})
        return hp_expr

    def __str__(self):
        out_var = self.src_lines[0][0].name
        hp_expr = self.get_expr()
        return "%s: %s = %s" % (self.name, out_var, hp_expr)

    def __repr__(self):
        return "Fcn(%s, %s)" % (self.name, self.expr)

    def get_var_subst(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return {out_var: expr}
