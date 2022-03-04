from decimal import Decimal

from ss2hcsp.sl.sl_block import SL_Block, get_gcd
from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.expr import AVar, AConst, OpExpr, conj


class DiscretePulseGenerator(SL_Block):
    """Block for pulse generator."""
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
