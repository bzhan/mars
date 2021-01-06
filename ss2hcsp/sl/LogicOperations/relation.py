from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, AConst, RelExpr


class Relation(SL_Block):
    """Relation of two dest lines."""
    def __init__(self, name, relation, *, st=-1):
        super(Relation, self).__init__()
        self.name = name
        self.type = "relation"
        self.is_continuous = (st == 0)
        self.num_src = 1
        self.num_dest = 2
        self.src_lines = [[]]
        self.dest_lines = [None] * self.num_dest

        assert relation in ["<", ">", "==", "!=", ">=", "<="]
        self.relation = relation

        assert isinstance(st, (int, float))
        self.st = st

    def __str__(self):
        return "%s: Relation[in = %s, out = %s, st = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), str(self.st))

    def __repr__(self):
        return str(self)

    def get_var_map(self):
        in_vars = [AVar(line.name) for line in self.dest_lines]
        cond0 = RelExpr(self.relation, in_vars[0], in_vars[1])
        expr0 = AConst(1)
        cond1 = cond0.neg()
        expr1 = AConst(0)
        out_var = self.src_lines[0][0].name
        return {out_var: [(cond0, expr0), (cond1, expr1)]}
