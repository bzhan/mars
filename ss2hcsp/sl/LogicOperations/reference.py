from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, AConst, RelExpr


class Reference(SL_Block):
    def __init__(self, name, relop, st=-1):
        super(Reference, self).__init__()
        self.name = name
        self.type = "reference"
        self.is_continuous = (st == 0)
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]

        assert relop in ["<=", "<", ">", ">=", "==", "~="]
        self.relop = relop

        assert isinstance(st, (float, int))
        self.st = st

    def __str__(self):
        return "%s: Reference[in = %s, out = %s, st = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), str(self.st))

    def __repr__(self):
        return str(self)

    def get_var_map(self):
        in_var = AVar(self.dest_lines[0].name)
        cond0 = RelExpr(self.relop, in_var, AConst(0))
        expr0 = AConst(1)
        cond1 = cond0.neg()
        expr1 = AConst(0)
        out_var = self.src_lines[0][0].name
        return {out_var: [(cond0, expr0), (cond1, expr1)]}
