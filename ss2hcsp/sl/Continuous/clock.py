from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp import hcsp 
from ss2hcsp.hcsp.expr import AVar, AConst,BExpr, conj,disj

class Clock(SL_Block):
        def __init__(self,name, period):
                super (Clock, self).__init__()
                self.name = name
                self.type = "clock"
                self.period = period
        def __str__(self):
                return "%s: Clock(period = %s)" % (self.name,self.max_step)

        def __repr__(self):
                return str(self)
        def get_hcsp(self):
                out_var = self.src_lines[0][0].name
                out_branch = str(self.src_lines[0][0].branch)
                return hcsp.Sequence(
                            hcsp.Loop(
                            hcsp.Sequence(
                            # hcsp.OutputChannel('ch_' + out_var + '_' + out_branch, AConst(1)),
                            hcsp.OutputChannel('ch_clock', AConst(1)),
                            hcsp.OutputChannel('ch_clock', AConst(0)),
                            # hcsp.Wait(AConst(float(self.period)/2)),
                            # # hcsp.OutputChannel('ch_' + out_var + '_' + out_branch, AConst(0)),
                            # hcsp.OutputChannel('ch_clock', AConst(0)),
                            # hcsp.Wait(AConst(float(self.period)/2))
                            )))