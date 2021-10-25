"""Scope block"""

from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp import hcsp as hp


class Scope(SL_Block):
    """Represents an output signal"""
    def __init__(self, name, num_dest, st=-1):
        super(Scope, self).__init__("scope", name, 0, num_dest, st)

    def __str__(self):
        in_vars = [line.name for line in self.dest_lines]
        return "%s: output %s" % (self.name, ', '.join(in_vars))

    def __repr__(self):
        return "Scope(%s, %s, %s, in = %s)" % \
            (self.name, self.num_dest, self.st, str(self.dest_lines))

    def get_output_hp(self):
        return hp.Skip()
