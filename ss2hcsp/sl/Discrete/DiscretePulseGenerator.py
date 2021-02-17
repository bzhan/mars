from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp import hcsp 
from ss2hcsp.hcsp.expr import AVar, AConst,BExpr, conj,disj
from ss2hcsp.hcsp.parser import bexpr_parser, hp_parser
class DiscretePulseGenerator(SL_Block):
    """Block for unit delay."""
    def __init__(self,name="", amplitude=1,period=2,pluseType="",pluseWidth=1,phaseDelay=1,timeSource="",sampleTime=1,is_continuous=False):
        super(DiscretePulseGenerator, self).__init__()
        self.name = name
        self.type = "DiscretePulseGenerator"
        self.amplitude=amplitude
        self.period=period
        self.pluseType=pluseType
        self.pluseWidth=pluseWidth
        self.phaseDelay=phaseDelay
        self.timeSource=timeSource
        self.st=sampleTime
        self.is_continuous = is_continuous
        self.num_src = 1
        self.src_lines = [[]]


    def __str__(self):
        return "%s: DiscretePulseGenerator[amplitude = %s, period = %s, pluseType = %s, pluseWidth = %s,phaseDelay= %s,timeSource = %s,sampleTime= %s]" % \
               (self.name,str(self.amplitude), str(self.period), str(self.pluseType), str(self.pluseWidth), str(self.phaseDelay),str(self.timeSource),str(self.st))

    def __repr__(self):
        return str(self)
    def get_hcsp(self):
        assert len(self.src_lines) == 1 and len(self.src_lines[0]) == 1
        out_var = self.src_lines[0][0].name
        out_branch = str(self.src_lines[0][0].branch)
        if self.pluseType == "Time based":
            if self.timeSource == "Use simulation time":
                final_cond=None
                tri_event=False
                for lines in self.src_lines:
                        for line in lines:
                            if line.dest_block.type == "triggered_subsystem" or line.dest_block.is_triggered_chart:
                        #Pcomp ← osig := outtri; Pcomp; Btri(osig, outtri) → tri!
                                # if line.dest_block.trigger_type == "rising":
                                    if  self.phaseDelay == 0:
                                        return hcsp.Sequence(
                                            # hcsp.Assign("osig", AConst(self.amplitude)),
                                            hcsp.OutputChannel('ch_' + 'trig', AConst(self.amplitude)),
                                            hcsp.Loop(
                                            hcsp.Sequence(
                                            hcsp.Assign("out_tri", AConst(self.amplitude)),
                                            #hcsp.Condition(cond=final_cond, hp=hp_parser.parse("tri"+'! "'+tri_event+'"'+"")), 
                                            hcsp.Wait(AConst((self.pluseWidth*(self.period/100)))),
                                            hcsp.OutputChannel('ch_' + 'trig', AVar("out_tri")),
                                            hcsp.Assign("out_tri", AConst(0)),
                                            # hcsp.Assign("osig",  AVar("out_tri")),
                                            hcsp.Wait(AConst(self.period-(self.pluseWidth*(self.period/100)))),
                                            hcsp.OutputChannel('ch_' +'trig' , AVar("out_tri"))
                                            )))
                                    else:
                                        return hcsp.Sequence(
                                            hcsp.OutputChannel('ch_' + 'trig', AConst(0)),
                                            hcsp.Loop(
                                            hcsp.Sequence(
                                            hcsp.Assign("out_tri", AConst(0)),
                                            hcsp.Wait(AConst((self.phaseDelay))),
                                            hcsp.OutputChannel('ch_' + 'trig', AVar("out_tri")),
                                            hcsp.Assign("out_tri", AConst(self.amplitude)),
                                            #hcsp.Condition(cond=final_cond, hp=hp_parser.parse("tri"+'! "'+tri_event+'"'+"")),
                                            hcsp.Wait(AConst((self.pluseWidth*(self.period/100)))),
                                            hcsp.OutputChannel('ch_' + 'trig', AVar("out_tri")),
                                            hcsp.Assign("out_tri", AConst(0)),
                                            # hcsp.Assign("osig", AConst(0)),
                                            hcsp.Wait(AConst(self.period-(self.pluseWidth*(self.period/100))-self.phaseDelay)),
                                            hcsp.OutputChannel('ch_' + 'trig', AVar("out_tri"))
                                            )))
        else:                   
            assert self.pluseWidth <= self.period
            if self.timeSource == "Use simulation time":
                final_cond=None
                tri_event=""
                for lines in self.src_lines:
                        for line in lines:
                            if line.dest_block.type == "triggered_subsystem" or  line.dest_block.is_triggered_chart:
                                    if  self.phaseDelay == 0:
                                        return hcsp.Sequence(
                                                # hcsp.Assign("osig", AConst(self.amplitude)),
                                                hcsp.OutputChannel('ch_' + 'trig',AConst(self.amplitude)),
                                                hcsp.Loop(
                                                hcsp.Sequence(
                                                hcsp.Assign("out_tri", AConst(self.amplitude)),
                                                hcsp.Wait(AConst(self.pluseWidth*self.st)),
                                                hcsp.OutputChannel('ch_' + 'trig', AVar("out_tri")),
                                                hcsp.Assign("out_tri", AConst(0)),
                                                hcsp.Wait(AConst(self.period*self.st-(self.pluseWidth*self.st))),
                                                hcsp.OutputChannel('ch_' + 'trig', AVar("out_tri"))
                                                )))
                                    else:
                                        return hcsp.Sequence(
                                            # hcsp.Assign("osig", AConst(0)),
                                            hcsp.OutputChannel('ch_' + 'trig',AConst(0)),
                                            hcsp.Loop(
                                            hcsp.Sequence(
                                            hcsp.Assign("out_tri", AConst(0)), 
                                            
                                            hcsp.Wait(AConst((self.phaseDelay))),
                                            hcsp.OutputChannel('ch_' + 'trig', AVar("out_tri")),
                                            hcsp.Assign("out_tri", AConst(self.amplitude)),
                                            # hcsp.Condition(cond=final_cond, hp=hp_parser.parse("tri"+'! "'+tri_event+'"'+"")),
                                           
                                            hcsp.Wait(AConst(self.pluseWidth*self.st)),
                                            hcsp.OutputChannel('ch_' + 'trig', AVar("out_tri")),
                                            hcsp.Assign("out_tri", AConst(0)),
                                            # hcsp.Assign("osig",  AVar("out_tri")),
                                           
                                            hcsp.Wait(AConst(self.period*self.st-(self.pluseWidth*self.st)-self.phaseDelay*self.st)),
                                            hcsp.OutputChannel('ch_' + 'trig', AVar("out_tri"))
                                            )))
