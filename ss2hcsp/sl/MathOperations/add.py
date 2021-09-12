"""Addition block"""

from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, OpExpr, true_expr, RelExpr, AConst
from ss2hcsp.hcsp import hcsp as hp


class Add(SL_Block):
    """Add (or subtract) a list of dest lines."""
    def __init__(self, name, dest_spec, st=-1):
        super(Add, self).__init__("add", name, 1, len(dest_spec), st)

        # dest_spec is a list of either '+' or '-'
        assert all(s == '+' or s == '-' for s in dest_spec)
        self.dest_spec = dest_spec  # string

    def get_expr(self):
        """Compute the assignment corresponding to an add block."""
        in_vars = [AVar(line.name) for line in self.dest_lines]
        if self.dest_spec[0] == '+':
            expr = in_vars[0]
        else:
            expr = OpExpr("-", in_vars[0])
        for op, in_var in zip(self.dest_spec[1:], in_vars[1:]):
            if op == '+':
                expr = OpExpr("+", expr, in_var)
            else:
                expr = OpExpr("-", expr, in_var)
        return expr

    def __str__(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return "%s: %s = %s  (st = %s)" % (self.name, out_var, expr, self.st)

    def __repr__(self):
        return "Add(%s, %s, %s, in = %s, out = %s)" % \
            (self.name, self.dest_spec, self.st, self.dest_lines, self.src_lines)

    def get_output_hp(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return hp.Assign(out_var, expr)

    def get_var_subst(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return {out_var: expr}

    def get_var_map(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return {out_var: [(true_expr, expr)]}
