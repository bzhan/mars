from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, TimesExpr, true_expr


class Product(SL_Block):
    """Multiply (or divide) a list of dest lines."""
    def __init__(self, name, dest_spec, st=-1):
        super(Product, self).__init__()
        """dest_spec is a list of either '*' or '/'."""
        self.name = name
        self.type = "product"
        self.is_continuous = (st == 0)
        self.num_src = 1
        self.num_dest = len(dest_spec)
        self.src_lines = [[]]
        self.dest_lines = [None] * self.num_dest

        assert all(s == '*' or s == '/' for s in dest_spec)
        assert len(dest_spec) >= 2
        self.dest_spec = dest_spec  # string

        assert isinstance(st, (int, float))
        self.st = st

    def __str__(self):
        return "%s: Product[in = %s, out = %s, st = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), str(self.st))

    def __repr__(self):
        return str(self)

    def get_var_map(self):
        in_vars = [AVar(line.name) for line in self.dest_lines]
        expr = TimesExpr(self.dest_spec, in_vars)
        out_var = self.src_lines[0][0].name
        return {out_var: [(true_expr, expr)]}
