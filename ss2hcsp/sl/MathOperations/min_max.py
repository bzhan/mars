from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, FunExpr, true_expr, RelExpr, OpExpr, AConst
from ss2hcsp.hcsp import hcsp as hp


class MinMax(SL_Block):
    """Min or max of dest lines."""
    def __init__(self, name, num_dest, fun_name="min", st=-1):
        super(MinMax, self).__init__()
        self.name = name
        self.type = "min_max"
        self.is_continuous = (st == 0)
        self.num_src = 1
        self.num_dest = num_dest
        self.src_lines = [[]]
        self.dest_lines = [None] * self.num_dest

        assert fun_name in ["min", "max"]
        self.fun_name = fun_name
        assert isinstance(st, (int, float))
        self.st = st

    def __str__(self):
        return "%s: %s[in = %s, out = %s, st = %s]" % \
               (self.name, self.fun_name, str(self.dest_lines), str(self.src_lines), str(self.st))

    def __repr__(self):
        return str(self)

    def get_output_hp(self):
        in_vars = [AVar(line.name) for line in self.dest_lines]
        expr = FunExpr(self.fun_name, in_vars)
        out_var = self.src_lines[0][0].name
        time_cond = RelExpr("==", OpExpr("%", AVar("t"), AConst(self.st)), AConst(0))
        return hp.Condition(cond=time_cond, hp=hp.Assign(var_name=out_var, expr=expr))

    def get_var_map(self):
        in_vars = [AVar(line.name) for line in self.dest_lines]
        expr = FunExpr(self.fun_name, in_vars)
        out_var = self.src_lines[0][0].name
        return {out_var: [(true_expr, expr)]}
