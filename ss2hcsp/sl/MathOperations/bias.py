from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, AConst, PlusExpr, true_expr


class Bias(SL_Block):
    def __init__(self, name, bias=0, st=-1):
        super(Bias, self).__init__()
        self.name = name
        self.type = "bias"
        self.is_continuous = (st == 0)
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]

        assert isinstance(bias, (int, float))
        self.bias = bias

        assert isinstance(st, (int, float))
        self.st = st

    def __str__(self):
        return "%s: Bias[in = %s, out = %s, st = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), str(self.st))

    def __repr__(self):
        return str(self)

    def get_var_map(self):
        in_var = AVar(self.dest_lines[0].name)
        expr = PlusExpr("++", [in_var, AConst(self.bias)])
        out_var = self.src_lines[0][0].name
        return {out_var: [(true_expr, expr)]}
