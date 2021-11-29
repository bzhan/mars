"""Continuous sources"""

from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, AConst, FunExpr


class Sine(SL_Block):
    """Sine wave"""
    def __init__(self, name, amplitude, bias, frequency, phase, st):
        super(Sine, self).__init__("sine", name, 1, 0, st)

        self.amplitude = amplitude
        self.bias = bias
        self.frequency = frequency
        self.phase = phase

    def get_expr(self):
        """Obtain the expression corresponding to the block."""
        e = AVar("t")
        if self.frequency != 1:
            e = AConst(self.frequency) * e
        if self.phase != 0:
            e = e + AConst(self.phase)
        e = FunExpr("sin", [e])
        if self.amplitude != 1:
            e = AConst(self.amplitude) * e
        if self.bias != 0:
            e = e + AConst(self.bias)
        return e

    def __str__(self):
        out_var = self.src_lines[0][0].name
        expr = self.get_expr()
        return "%s: %s = %s  (st = %s)" % (self.name, out_var, expr, self.st)

    def __repr__(self):
        return "Sine(%s, %s, %s, %s, %s, %s, out = %s)" % \
            (self.name, self.amplitude, self.bias, self.frequency, self.phase, self.st,
             str(self.src_lines))

    def get_var_subst(self):
        out_var = self.src_lines[0][0].name
        expr = self.get_expr()
        return {out_var: expr}
