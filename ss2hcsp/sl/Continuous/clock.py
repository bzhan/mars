from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp import hcsp 
from ss2hcsp.hcsp.expr import AConst

class Clock(SL_Block):
    def __init__(self, name, period):
        # Clock has one output line and no input lines.
        super(Clock, self).__init__("clock", name, 1, 0, 0)
        self.period = period

    def __str__(self):
        return "%s: Clock(period = %s)" % (self.name,self.max_step)

    def __repr__(self):
        return str(self)

    def get_hcsp(self):
        return hcsp.Sequence(hcsp.Loop(hcsp.Sequence(
            hcsp.OutputChannel('ch_clock', AConst(1)),
            hcsp.OutputChannel('ch_clock', AConst(0)))))
