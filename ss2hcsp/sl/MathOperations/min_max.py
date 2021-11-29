from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, FunExpr, true_expr, RelExpr, OpExpr, AConst
from ss2hcsp.hcsp import hcsp as hp


class MinMax(SL_Block):
    """Min or max of dest lines."""
    def __init__(self, name, num_dest, fun_name="min", st=-1):
        super(MinMax, self).__init__("min_max", name, 1, num_dest, st)

        assert fun_name in ["min", "max"]
        self.fun_name = fun_name

    def get_expr(self):
        in_vars = [AVar(line.name) for line in self.dest_lines]
        return FunExpr(self.fun_name, in_vars)

    def __str__(self):
        out_var = self.src_lines[0][0].name
        expr = self.get_expr()
        return "%s: %s = %s  (st = %s)" % (self.name, out_var, expr, self.st)

    def __repr__(self):
        return "MinMax(%s, %s, %s, %s, in = %s, out = %s)" % \
            (self.name, self.num_dest, self.fun_name, self.st, str(self.dest_lines), str(self.src_lines))

    def get_output_hp(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return hp.Assign(out_var, expr)

    def get_var_subst(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return {out_var: expr}

    def get_var_map(self):
        in_vars = [AVar(line.name) for line in self.dest_lines]
        expr = FunExpr(self.fun_name, in_vars)
        out_var = self.src_lines[0][0].name
        return {out_var: [(true_expr, expr)]}
