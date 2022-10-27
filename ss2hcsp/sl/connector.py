"""Connectors"""

from ss2hcsp.sl.sl_block import SL_Block

class From(SL_Block):
    """From block"""
    def __init__(self, name, tag):
        super(From, self).__init__("from", name, 1, 0, st=-1)
        self.tag = tag

    def __str__(self):
        return "From: %s" % self.tag

    def __repr__(self):
        return "From(%s, %s)" % (self.name, self.tag)


class Goto(SL_Block):
    """Goto block"""
    def __init__(self, name, tag):
        super(Goto, self).__init__("goto", name, 0, 1, st=-1)
        self.tag = tag

    def __str__(self):
        return "Goto: %s" % self.tag

    def __repr__(self):
        return "Goto(%s, %s)" % (self.name, self.tag)
