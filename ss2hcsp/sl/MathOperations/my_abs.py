from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, FunExpr, true_expr


class Abs(SL_Block):
    """Compute the absolute value of the dest line."""
    def __init__(self, name, st=-1):
        super(Abs, self).__init__()
        self.name = name
        self.type = "abs"
        self.is_continuous = (st == 0)
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]

        assert isinstance(st, (int, float))
        self.st = st

    def __str__(self):
        return "%s: Abs[in = %s, out = %s, st = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), str(self.st))

    def get_var_map(self):
        in_var = AVar(self.dest_lines[0].name)
        expr = FunExpr("abs", [in_var])
        out_var = self.src_lines[0][0].name
        return {out_var: [(true_expr, expr)]}
