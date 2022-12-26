from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, AConst, RelExpr, OpExpr, IfExpr
from ss2hcsp.hcsp import hcsp as hp


class Switch(SL_Block):
    """Switch of two dest lines."""
    def __init__(self, name, relation, threshold, st=-1):
        super(Switch, self).__init__("switch", name, 1, 3, st)

        assert relation in ('>=', '>', '<=', '<')
        self.relation = relation

        assert isinstance(threshold, (int, float))
        self.threshold = threshold

    def get_expr(self):
        in_vars = [AVar(line.name) for line in self.dest_lines]
        return IfExpr(RelExpr(self.relation, in_vars[1], AConst(self.threshold)),
                      in_vars[0], in_vars[2])

    def __str__(self):
        out_var = self.src_lines[0][0].name
        expr = self.get_expr()
        return "%s: %s = %s  (st = %s)" % (self.name, out_var, expr, self.st)

    def __repr__(self):
        return "Switch(%s, %s, %s, %s, in = %s, out = %s)" % \
            (self.name, self.relation, self.threshold, self.st, str(self.dest_lines), str(self.src_lines))

    def get_output_hp(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return hp.Assign(out_var, expr)

    def get_var_subst(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return {out_var: expr}
