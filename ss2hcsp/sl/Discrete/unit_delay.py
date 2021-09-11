"""Unit delay block"""

from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, AConst, RelExpr, OpExpr
from ss2hcsp.hcsp.parser import hp_parser
from ss2hcsp.hcsp import hcsp as hp


class UnitDelay(SL_Block):
    """Block for unit delay."""
    def __init__(self, name, init_value=0, st=-1):
        super(UnitDelay, self).__init__()
        self.name = name
        self.type = "unit_delay"
        self.is_continuous = False
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]

        assert isinstance(init_value, (int, float))
        self.init_value = init_value
        assert st > 0
        self.st = st

    def __str__(self):
        out_var = self.src_lines[0][0].name
        in_var = self.dest_lines[0].name
        return "%s: %s = %s -> pre(%s)  (st = %s)" % (self.name, out_var, self.init_value, in_var, self.st)

    def __repr__(self):
        return "UnitDelay(%s, %s, %s, in = %s, out = %s)" % \
            (self.name, self.init_value, self.st, str(self.dest_lines), str(self.src_lines))

    def get_output_hp(self):
        out_var = self.src_lines[0][0].name
        cond = RelExpr("==", OpExpr("%", AVar("t"), AConst(self.st)), AConst(0))
        return hp.Condition(cond=cond, hp=hp.Assign(var_name=out_var, expr=AVar(self.name+"_state")))

    def get_update_hp(self):
        in_var = self.dest_lines[0].name
        cond = RelExpr("==", OpExpr("%", AVar("t"), AConst(self.st)), AConst(0))
        return hp.Condition(cond=cond, hp=hp.Assign(var_name=self.name+"_state", expr=AVar(in_var)))
