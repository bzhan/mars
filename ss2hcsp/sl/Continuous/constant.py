from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import true_expr, AConst


class Constant(SL_Block):
    """Block for constant."""
    def __init__(self, name, value):
        super(Constant, self).__init__()
        self.name = name
        self.type = "constant"
        self.is_continuous = True
        self.num_src = 1
        self.num_dest = 0
        self.src_lines = [[]]
        self.dest_lines = []

        assert isinstance(value, (int, float))
        self.value = value

        self.st = 0

    def __str__(self):
        return "%s: Constant[value = %s, out = %s]" % (self.name, str(self.value), str(self.src_lines))

    def __repr__(self):
        return str(self)

    def get_var_map(self):
        out_var = self.src_lines[0][0].name
        expr = AConst(self.value)
        return {out_var: [(true_expr, expr)]}
