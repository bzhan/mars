from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, AConst, RelExpr


class Switch(SL_Block):
    """Switch of two dest lines."""
    def __init__(self, name, relation, threshold, st=-1):
        super(Switch, self).__init__()
        self.name = name
        self.type = "switch"
        self.is_continuous = (st == 0)
        self.num_src = 1
        self.num_dest = 3
        self.src_lines = [[]]
        self.dest_lines = [None] * self.num_dest
        self.relation = relation

        assert isinstance(threshold, (int, float))
        self.threshold = threshold

        assert isinstance(st, (int, float))
        self.st = st

    def __str__(self):
        return "%s: Switch[in = %s, out = %s, st = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), str(self.st))

    def get_var_map(self):
        in_vars = [AVar(line.name) for line in self.dest_lines]
        cond0 = RelExpr(self.relation, in_vars[1], AConst(self.threshold))
        expr0 = in_vars[0]
        cond2 = cond0.neg()
        expr2 = in_vars[2]
        out_var = self.src_lines[0][0].name
        return {out_var: [(cond0, expr0), (cond2, expr2)]}
