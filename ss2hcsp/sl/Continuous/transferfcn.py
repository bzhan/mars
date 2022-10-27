from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, OpExpr

class TransferFcn(SL_Block):
    def __init__(self, name, denom):
        super(TransferFcn, self).__init__("transferfcn", name, 1, 1, st=0)

        self.denom = denom

    def __str__(self):
        in_var = AVar(self.dest_lines[0].name)
        out_var = AVar(self.src_lines[0][0].name)
        return "%s: %s = [transfer 1/%s] %s" % (self.name, out_var, self.denom, in_var)

    def __repr__(self):
        return "TransferFcn(%s, %s)" % (self.name, self.denom)
