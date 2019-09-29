from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, AConst, TimesExpr, true_expr


class Gain(SL_Block):
    """Multiply dest line by a factor."""
    def __init__(self, name, factor=1, st=-1):
        super(Gain, self).__init__()
        self.name = name
        self.type = "gain"
        self.is_continuous = (st == 0)
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]

        assert isinstance(factor, (int, float))
        self.factor = factor

        assert isinstance(st, (int, float))
        self.st = st

    def __str__(self):
        return "%s: Gain[in = %s, out = %s, st = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), str(self.st))

    def get_var_map(self):
        in_var = AVar(self.dest_lines[0].name)
        expr = TimesExpr("**", [in_var, AConst(self.factor)])
        out_var = self.src_lines[0][0].name
        return {out_var: [(true_expr, expr)]}
