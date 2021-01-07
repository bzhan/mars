from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, AConst, LogicExpr, RelExpr


class Saturation(SL_Block):
    """Compute the saturation value of the dest_line wrt. the upper and lower limits."""
    def __init__(self, name, up_lim, low_lim, st=-1):
        super(Saturation, self).__init__()
        self.name = name
        self.type = "saturation"
        self.is_continuous = (st == 0)
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]

        assert isinstance(st, (int, float))
        self.st = st

        assert isinstance(up_lim, (int, float)) and isinstance(low_lim, (int, float))
        self.up_lim = up_lim
        self.low_lim = low_lim

    def __str__(self):
        return "%s: Saturation[in = %s, out = %s, up_lim = %s, low_lim = %s, st = %s]" % \
               (self.name, self.dest_lines, self.src_lines, self.up_lim, self.low_lim, self.st)

    def __repr__(self):
        return str(self)

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
