from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp import hcsp 
from ss2hcsp.hcsp.expr import AVar, AConst, OpExpr, BExpr, conj,disj, RelExpr
from ss2hcsp.hcsp.parser import bexpr_parser, hp_parser
class DiscretePulseGenerator(SL_Block):
    """Block for unit delay."""
    def __init__(self,name="", amplitude=1,period=2,pluseType="",pluseWidth=1,phaseDelay=1,timeSource="",sampleTime=1,is_continuous=False):
        super(DiscretePulseGenerator, self).__init__(name="", num_dest=0, num_src=1, st=1, type="DiscretePulseGenerator")
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

    def get_output_hp(self):
        out_var = self.src_lines[0][0].name
        assert isinstance(self.phaseDelay, int) and self.phaseDelay >= 0
        assert isinstance(self.period, (int,float)) and self.period > 0
        # t_delay := (t - phaseDelay) % period
        t_delay = hcsp.Assign(var_name="t_delay", expr=OpExpr("%", OpExpr("-", AVar("t"), AConst(self.phaseDelay*10)),
                                                              AConst(self.period*10)))
        # if 0 <= t_delay <= period * pluseWidth % then out_var := amplitude
        # else out_var := 0
        assert isinstance(self.pluseWidth, int) and 0 < self.pluseWidth < 100
        # assert (self.period * self.pluseWidth) % 100 == 0
        if_then_else = hcsp.ITE(if_hps=[(conj(RelExpr(">=", AVar("t_delay"), AConst(0*10)),
                                              RelExpr("<", AVar("t_delay"), AConst(self.period * self.pluseWidth / 100*10))),
                                         hcsp.Assign(var_name=out_var, expr=AConst(self.amplitude)))],
                                else_hp=hcsp.Assign(var_name=out_var, expr=AConst(0)))
        return hcsp.Sequence(t_delay, if_then_else,hcsp.Condition(RelExpr("==",AVar("pre_"+out_var),AConst("")),hcsp.Assign(AVar("pre_"+out_var),AVar(out_var))))

    
    def get_hcsp(self):
        if self.pluseType == "Time based":
            if self.timeSource == "Use simulation time":
                final_cond=None
                tri_event=False
                for lines in self.src_lines:
                        for line in lines:
                           
                        #Pcomp ← osig := outtri; Pcomp; Btri(osig, outtri) → tri!
                                # if line.dest_block.trigger_type == "rising":
                                    if  self.phaseDelay == 0:
                                        return hcsp.Sequence(
                                            # hcsp.Assign("osig", AConst(self.amplitude)),
                                            hcsp.OutputChannel(line.ch_name, AConst(self.amplitude)),
                               
                                            hcsp.Loop(
                                            hcsp.Sequence(
                                            hcsp.Assign("out_tri", AConst(self.amplitude)),
                                            #hcsp.Condition(cond=final_cond, hp=hp_parser.parse("tri"+'! "'+tri_event+'"'+"")), 
                                            hcsp.Wait(AConst((self.pluseWidth*(self.period/100)))),
                                            hcsp.OutputChannel(line.ch_name, AVar("out_tri")),
                                     
                                            hcsp.Assign("out_tri", AConst(0)),
                                            # hcsp.Assign("osig",  AVar("out_tri")),
                                            hcsp.Wait(AConst(self.period-(self.pluseWidth*(self.period/100)))),
                                            hcsp.OutputChannel(line.ch_name , AVar("out_tri"))
                                        
                                            )))
                                    else:
                                        return hcsp.Sequence(
                                            hcsp.OutputChannel(line.ch_name, AConst(0)),
                                           
                                            hcsp.Loop(
                                            hcsp.Sequence(
                                            hcsp.Assign("out_tri", AConst(0)),
                                            hcsp.Wait(AConst((self.phaseDelay))),
                                            hcsp.OutputChannel(line.ch_name, AVar("out_tri")),
                                            
                                            hcsp.Assign("out_tri", AConst(self.amplitude)),
                                            #hcsp.Condition(cond=final_cond, hp=hp_parser.parse("tri"+'! "'+tri_event+'"'+"")),
                                            hcsp.Wait(AConst((self.pluseWidth*(self.period/100)))),
                                            hcsp.OutputChannel(line.ch_name, AVar("out_tri")),
                                         
                                            hcsp.Assign("out_tri", AConst(0)),
                                            # hcsp.Assign("osig", AConst(0)),
                                            hcsp.Wait(AConst(self.period-(self.pluseWidth*(self.period/100))-self.phaseDelay)),
                                            hcsp.OutputChannel(line.ch_name, AVar("out_tri"))
                                            
                                            )))
        else:                   
            assert self.pluseWidth <= self.period
            if self.timeSource == "Use simulation time":
                final_cond=None
                tri_event=""
                for lines in self.src_lines:
                        for line in lines:
                           
                                    if  self.phaseDelay == 0:
                                        return hcsp.Sequence(
                                                # hcsp.Assign("osig", AConst(self.amplitude)),
                                                hcsp.OutputChannel(line.ch_name,AConst(self.amplitude)),
                                                
                                                hcsp.Loop(
                                                hcsp.Sequence(
                                                hcsp.Assign("out_tri", AConst(self.amplitude)),
                                                hcsp.Wait(AConst(self.pluseWidth*self.st)),
                                                hcsp.OutputChannel(line.ch_name, AVar("out_tri")),
                                                
                                                hcsp.Assign("out_tri", AConst(0)),
                                                hcsp.Wait(AConst(self.period*self.st-(self.pluseWidth*self.st))),
                                                hcsp.OutputChannel(line.ch_name, AVar("out_tri"))
                                                
                                                )))
                                    else:
                                        return hcsp.Sequence(
                                            # hcsp.Assign("osig", AConst(0)),
                                            hcsp.OutputChannel(line.ch_name,AConst(0)),
                                            
                                            hcsp.Loop(
                                            hcsp.Sequence(
                                            hcsp.Assign("out_tri", AConst(0)), 
                                            
                                            hcsp.Wait(AConst((self.phaseDelay))),
                                            hcsp.OutputChannel(line.ch_name, AVar("out_tri")),
                                            
                                            hcsp.Assign("out_tri", AConst(self.amplitude)),
                                            # hcsp.Condition(cond=final_cond, hp=hp_parser.parse("tri"+'! "'+tri_event+'"'+"")),
                                           
                                            hcsp.Wait(AConst(self.pluseWidth*self.st)),
                                            hcsp.OutputChannel(line.ch_name, AVar("out_tri")),
                                            
                                            hcsp.Assign("out_tri", AConst(0)),
                                            # hcsp.Assign("osig",  AVar("out_tri")),
                                           
                                            hcsp.Wait(AConst(self.period*self.st-(self.pluseWidth*self.st)-self.phaseDelay*self.st)),
                                            hcsp.OutputChannel(line.ch_name, AVar("out_tri"))
                                            
                                            )))
    def get_hcsp1(self):
        if self.pluseType == "Time based":
            if self.timeSource == "Use simulation time":
                final_cond=None
                tri_event=False
                for lines in self.src_lines:
                        for line in lines:
                           
                        #Pcomp ← osig := outtri; Pcomp; Btri(osig, outtri) → tri!
                                # if line.dest_block.trigger_type == "rising":
                                    if  self.phaseDelay == 0:
                                        return hcsp.Sequence(
                                            # hcsp.Assign("osig", AConst(self.amplitude)),
                                            
                                            hcsp.OutputChannel("ch_trig", AConst(self.amplitude)),
                                            hcsp.Loop(
                                            hcsp.Sequence(
                                            hcsp.Assign("out_tri", AConst(self.amplitude)),
                                            #hcsp.Condition(cond=final_cond, hp=hp_parser.parse("tri"+'! "'+tri_event+'"'+"")), 
                                            hcsp.Wait(AConst((self.pluseWidth*(self.period/100)))),
                                           
                                            hcsp.OutputChannel("ch_trig", AVar("out_tri")),
                                            hcsp.Assign("out_tri", AConst(0)),
                                            # hcsp.Assign("osig",  AVar("out_tri")),
                                            hcsp.Wait(AConst(self.period-(self.pluseWidth*(self.period/100)))),
                                            
                                            hcsp.OutputChannel("ch_trig", AVar("out_tri"))
                                            )))
                                    else:
                                        return hcsp.Sequence(
                                            
                                            hcsp.OutputChannel("ch_trig", AConst(0)),
                                            hcsp.Loop(
                                            hcsp.Sequence(
                                            hcsp.Assign("out_tri", AConst(0)),
                                            hcsp.Wait(AConst((self.phaseDelay))),
                                           
                                            hcsp.OutputChannel("ch_trig", AVar("out_tri")),
                                            hcsp.Assign("out_tri", AConst(self.amplitude)),
                                            #hcsp.Condition(cond=final_cond, hp=hp_parser.parse("tri"+'! "'+tri_event+'"'+"")),
                                            hcsp.Wait(AConst((self.pluseWidth*(self.period/100)))),
                                            
                                            hcsp.OutputChannel("ch_trig", AVar("out_tri")),
                                            hcsp.Assign("out_tri", AConst(0)),
                                            # hcsp.Assign("osig", AConst(0)),
                                            hcsp.Wait(AConst(self.period-(self.pluseWidth*(self.period/100))-self.phaseDelay)),
                                            
                                            hcsp.OutputChannel("ch_trig", AVar("out_tri"))
                                            )))
        else:                   
            assert self.pluseWidth <= self.period
            if self.timeSource == "Use simulation time":
                final_cond=None
                tri_event=""
                for lines in self.src_lines:
                        for line in lines:
                           
                                    if  self.phaseDelay == 0:
                                        return hcsp.Sequence(
                                                # hcsp.Assign("osig", AConst(self.amplitude)),
                                                
                                                hcsp.OutputChannel("ch_trig",AConst(self.amplitude)),
                                                hcsp.Loop(
                                                hcsp.Sequence(
                                                hcsp.Assign("out_tri", AConst(self.amplitude)),
                                                hcsp.Wait(AConst(self.pluseWidth*self.st)),
                                                
                                                hcsp.OutputChannel("ch_trig", AVar("out_tri")),
                                                hcsp.Assign("out_tri", AConst(0)),
                                                hcsp.Wait(AConst(self.period*self.st-(self.pluseWidth*self.st))),
                                                
                                                hcsp.OutputChannel("ch_trig", AVar("out_tri"))
                                                )))
                                    else:
                                        return hcsp.Sequence(
                                            # hcsp.Assign("osig", AConst(0)),
                                            
                                            hcsp.OutputChannel("ch_trig",AConst(0)),
                                            hcsp.Loop(
                                            hcsp.Sequence(
                                            hcsp.Assign("out_tri", AConst(0)), 
                                            
                                            hcsp.Wait(AConst((self.phaseDelay))),
                                            
                                            hcsp.OutputChannel("ch_trig", AVar("out_tri")),
                                            hcsp.Assign("out_tri", AConst(self.amplitude)),
                                            # hcsp.Condition(cond=final_cond, hp=hp_parser.parse("tri"+'! "'+tri_event+'"'+"")),
                                           
                                            hcsp.Wait(AConst(self.pluseWidth*self.st)),
                                            
                                            hcsp.OutputChannel("ch_trig", AVar("out_tri")),
                                            hcsp.Assign("out_tri", AConst(0)),
                                            # hcsp.Assign("osig",  AVar("out_tri")),
                                           
                                            hcsp.Wait(AConst(self.period*self.st-(self.pluseWidth*self.st)-self.phaseDelay*self.st)),
                                            
                                            hcsp.OutputChannel("ch_trig", AVar("out_tri"))
                                            )))
                           
                           

