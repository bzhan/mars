from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import true_expr, AConst


class Constant(SL_Block):
    """Block for constant."""
    def __init__(self, name, value):
        super(Constant, self).__init__("constant", name, 1, 0, st=0)

        assert isinstance(value, (int, float))
        self.value = value

    def __str__(self):
        out_var = self.src_lines[0][0].name
        return "%s: %s = %s" % (self.name, out_var, self.value)

    def __repr__(self):
        return "Constant(%s, %s, out = %s)" % (self.name, self.value, str(self.src_lines))

    def get_var_subst(self):
        out_var = self.src_lines[0][0].name
        return {out_var: AConst(self.value)}

    def get_var_map(self):
        out_var = self.src_lines[0][0].name
        expr = AConst(self.value)
        return {out_var: [(true_expr, expr)]}
