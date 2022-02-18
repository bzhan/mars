from decimal import Decimal
import math

from ss2hcsp.sl.sl_block import SL_Block, get_gcd
from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.expr import AVar, AConst, OpExpr, conj


class DiscretePulseGenerator(SL_Block):
    """Block for unit delay."""
    def __init__(self, name, pulseType, amplitude, period, pulseWidth, phaseDelay):
        assert isinstance(period, Decimal)
        assert isinstance(pulseWidth, Decimal)
        assert isinstance(phaseDelay, Decimal)

        self.pulseType = pulseType
        self.amplitude = amplitude
        self.period = period
        self.pulseWidth = pulseWidth
        self.phaseDelay = phaseDelay

        # Compute sample time from period, pulseWidth and phaseDelay
        self.on_width = self.pulseWidth / 100 * self.period
        self.off_width = (1 - self.pulseWidth / 100) * self.period
        st = get_gcd([self.phaseDelay + self.on_width, self.period, self.off_width])

        # Convert start, end, and period to number of sample times
        self.start_st = int(self.phaseDelay / st)
        self.end_st = int((self.phaseDelay + self.on_width) / st)
        self.period_st = int(self.period / st)

        # Now call parent class's constructor
        super(DiscretePulseGenerator, self).__init__("DiscretePulseGenerator", name, 1, 0, st)

        # Tick variable
        self.tick_var = self.name + "_tick"

    def __str__(self):
        return "%s: DiscretePulseGenerator[amplitude = %s, period = %s, pulseWidth = %s, phaseDelay = %s]" % \
            (self.name, str(self.amplitude), str(self.period), str(self.pulseWidth), str(self.phaseDelay))

    def __repr__(self):
        return str(self)

    def get_init_hp(self):
        return hp.Assign(self.tick_var, AConst(0))

    def get_output_hp(self):
        # Output variable
        out_var = self.src_lines[0][0].name

        procs = []
        cycle_st = OpExpr("%", AVar(self.tick_var), AConst(self.period_st))
        cond = conj(hp.RelExpr(">=", cycle_st, AConst(self.start_st)),
                    hp.RelExpr("<", cycle_st, AConst(self.end_st)))
        act1 = hp.Assign(out_var, AConst(self.amplitude))
        act2 = hp.Assign(out_var, AConst(0.0))
        procs.append(hp.ITE([(cond, act1)], act2))
        procs.append(hp.Assign(self.tick_var, OpExpr("+", AVar(self.tick_var), AConst(1))))
        return hp.seq(procs)
    
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
                           
                           

