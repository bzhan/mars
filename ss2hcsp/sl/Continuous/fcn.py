from ss2hcsp.sl.sl_block import SL_Block

class Fcn(SL_Block):
    def __init__(self, name, expr):
        super(Fcn, self).__init__("fcn", name, 1, 1, st=0)
        self.expr = expr

    def __str__(self):
        in_var = self.dest_lines[0].name
        out_var = self.src_lines[0][0].name
        return "%s: %s = %s(%s)" % (self.name, out_var, self.expr, in_var)

    def __repr__(self):
        return "Fcn(%s, %s)" % (self.name, self.expr)
