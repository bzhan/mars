"""Discrete PID Controller"""

from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, AConst, RelExpr, OpExpr
from ss2hcsp.hcsp import hcsp as hp


class DiscretePID(SL_Block):
    """Block for unit delay."""
    def __init__(self, name, controller="PI", st=-1, pid=(), init_value=0, saturation=(), kb=0):
        super(DiscretePID, self).__init__()
        self.name = name
        self.type = "discrete_PID_controller"
        self.is_continuous = False
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]

        self.controller = controller
        assert st > 0
        self.st = st
        assert len(pid) == 3
        self.pid = pid
        self.init_value = init_value
        assert len(saturation) == 2 and saturation[0] < saturation[1]
        self.saturation = saturation
        self.kb = kb

    def __str__(self):
        return "%s: DiscretePID[controller = %s, in = %s, out = %s, st = %s]" % \
               (self.name, str(self.controller), str(self.dest_lines), str(self.src_lines), str(self.st))

    def __repr__(self):
        return str(self)

    def get_init_hps(self):
        return [hp.Assign(var_name="Integrator_DSTATE", expr=AConst(self.init_value))]

    def get_output_hp(self):
        in_var = self.dest_lines[0].name
        out_var = self.src_lines[0][0].name

        step0 = hp.Assign(var_name="rtb_Sum", expr=AVar(in_var))
        step1 = hp.Assign(var_name="rtb_IntegralGain", expr=OpExpr("*", AVar("rtb_Sum"), AConst(self.pid[1])))
        step2 = hp.Assign(var_name="rtb_Sum", expr=OpExpr("*", AVar("rtb_Sum"), AConst(self.pid[0])))
        step3 = hp.Assign(var_name="rtb_SumFdbk", expr=OpExpr("+", AVar("rtb_Sum"), AVar("Integrator_DSTATE")))
        step4 = hp.ITE(if_hps=[(RelExpr(">", AVar("rtb_SumFdbk"), AConst(self.saturation[1])),
                                hp.Assign(var_name="rtb_SumFdbk_0", expr=AConst(self.saturation[1]))),
                               (RelExpr("<", AVar("rtb_SumFdbk"), AConst(self.saturation[0])),
                                hp.Assign(var_name="rtb_SumFdbk_0", expr=AConst(self.saturation[0])))],
                       else_hp=hp.Assign(var_name="rtb_SumFdbk_0", expr=AVar("rtb_SumFdbk"))
                       )
        expr0 = OpExpr("*", OpExpr("-", AVar("rtb_SumFdbk_0"), AVar("rtb_SumFdbk")), AConst(self.kb))
        expr1 = OpExpr("*", OpExpr("+", expr0, AVar("rtb_IntegralGain")), AConst(self.st))
        step5 = hp.Assign(var_name="rtb_IntegralGain", expr=OpExpr("+", expr1, AVar("Integrator_DSTATE")))
        step6 = hp.Assign(var_name="rtb_Sum", expr=OpExpr("+", AVar("rtb_Sum"), AVar("rtb_IntegralGain")))
        step7 = hp.ITE(if_hps=[(RelExpr(">", AVar("rtb_Sum"), AConst(self.saturation[1])),
                                hp.Assign(var_name=out_var, expr=AConst(self.saturation[1]))),
                               (RelExpr("<", AVar("rtb_Sum"), AConst(self.saturation[0])),
                                hp.Assign(var_name=out_var, expr=AConst(self.saturation[0])))],
                       else_hp=hp.Assign(var_name=out_var, expr=AVar("rtb_Sum")))
        step8 = hp.Assign(var_name="Integrator_DSTATE", expr=AVar("rtb_IntegralGain"))

        time_cond = RelExpr("==", OpExpr("%", AVar("t"), AConst(self.st)), AConst(0))

        return hp.Condition(cond=time_cond,
                            hp=hp.Sequence(step0, step1, step2, step3, step4, step5, step6, step7, step8))
