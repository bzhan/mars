from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, true_expr, OpExpr, RelExpr, AConst
from ss2hcsp.hcsp import hcsp as hp


class Product(SL_Block):
    """Multiply (or divide) a list of dest lines."""
    def __init__(self, name, dest_spec, st=-1):
        """dest_spec is a list of either '*' or '/'."""
        super(Product, self).__init__("product", name, 1, len(dest_spec), st)

        # dest_spec is a list of either '*' or '/'
        assert all(s == '*' or s == '/' for s in dest_spec)
        assert len(dest_spec) >= 2
        self.dest_spec = dest_spec  # string

    def get_expr(self):
        """Compute the assignment corresponding to a product block."""
        in_vars = [AVar(line.name) for line in self.dest_lines]
        if self.dest_spec[0] == '*':
            expr = in_vars[0]
        else:
            expr = OpExpr("/", AConst(1), in_vars[0])
        for op, in_var in zip(self.dest_spec[1:], in_vars[1:]):
            if op == '*':
                expr = OpExpr("*", expr, in_var)
            else:
                expr = OpExpr("/", expr, in_var)
        return expr

    def __str__(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return "%s: %s = %s  (st = %s)" % (self.name, out_var, str(expr), str(self.st))

    def __repr__(self):
        return "Product(%s, %s, %s, in = %s, out = %s)" % \
            (self.name, self.dest_spec, self.st, self.dest_lines, self.src_lines)

    def get_output_hp(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return hp.Assign(out_var, expr)

    def get_var_subst(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return {out_var: expr}
