from ss2hcsp.sl.sl_block import SL_Block

class Fcn(SL_Block):
    def __init__(self, name, expr):
        super(Fcn, self).__init__("fcn", name, 1, 1, st=0)
        self.expr = expr

    def __str__(self):
        return "fcn: %s" % self.expr

    def __repr__(self):
        return "Fcn(%s, %s)" % (self.name, self.expr)
