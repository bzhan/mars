from ss2hcsp.sl.sl_block import SL_Block

class TransferFcn(SL_Block):
    def __init__(self, name, denom):
        super(TransferFcn, self).__init__("transferfcn", name, 1, 1, st=0)

        self.denom = denom

    def __str__(self):
        return "%s: transfer 1/%s" % (self.name, self.denom)

    def __repr__(self):
        return "TransferFcn(%s, %s)" % (self.name, self.denom)
