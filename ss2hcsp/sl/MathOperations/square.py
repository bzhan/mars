from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, true_expr, RelExpr, AConst
from ss2hcsp.hcsp import hcsp as hp


class Square(SL_Block):
    """Compute the square"""
    def __init__(self, name, operator, st=-1):
        super(Square, self).__init__()
        self.name = name
        self.operator = operator
        assert isinstance(st, (int, float))
        self.st = st
        self.type = "square"
        self.is_continuous = (st == 0)
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]

    def __str__(self):
        return "%s: %s[in=%s, out=%s, st=%s]" % \
               (self.name, self.operator, str(self.dest_lines), str(self.src_lines), str(self.st))

    def __repr__(self):
        return str(self)

    def get_output_hp(self):
        in_var = AVar(self.dest_lines[0].name)
        assert self.operator == "square"
        expr = OpExpr("*", in_var, in_var)
        out_var = self.src_lines[0][0].name
        time_cond = RelExpr("==", OpExpr("%", AVar("t"), AConst(self.st)), AConst(0))
        return hp.Condition(cond=time_cond, hp=hp.Assign(var_name=out_var, expr=expr))

    def get_var_map(self):
        in_var = AVar(self.dest_lines[0].name)
        if self.operator == "square":
            expr = OpExpr("*", in_var, in_var)
            out_var = self.src_lines[0][0].name
            return {out_var: [(true_expr, expr)]}
