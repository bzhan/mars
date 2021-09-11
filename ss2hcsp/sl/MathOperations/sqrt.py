from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, RelExpr, AConst, FunExpr, OpExpr
from ss2hcsp.hcsp import hcsp as hp

class Sqrt(SL_Block):
    """Compute the square root"""
    def __init__(self, name, operator="signedSqrt", st=-1):
        super(Sqrt, self).__init__()
        self.name = name
        self.operator = operator
        assert isinstance(st, (int, float))
        self.st = st
        self.type = "sqrt"
        self.is_continuous = (st == 0)
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]

    def __str__(self):
        return "%s: %s[in=%s, out=%s, st=%s]" % \
               (self.name, self.operator, str(self.dest_lines), str(self.src_lines), str(self.st))

    def __repr__(self):
        return str(self)

    def get_output_hp(self):
        in_var = AVar(self.dest_lines[0].name)
        assert self.operator == "signedSqrt"
        cond = RelExpr("<", in_var, AConst(0))
        expr0 = OpExpr("-", FunExpr("sqrt", [FunExpr("abs", [in_var])]))
        expr1 = FunExpr("sqrt", [in_var])
        out_var = self.src_lines[0][0].name
        time_cond = RelExpr("==", OpExpr("%", AVar("t"), AConst(self.st)), AConst(0))
        return hp.Condition(cond=time_cond,
                            hp=hp.ITE(if_hps=[(cond, hp.Assign(var_name=out_var, expr=expr0))],
                                      else_hp=hp.Assign(var_name=out_var, expr=expr1)
                                      )
                            )

    def get_var_map(self):
        in_var = AVar(self.dest_lines[0].name)
        if self.operator == "signedSqrt":
            cond0 = RelExpr("<", in_var, AConst(0))
            expr0 = OpExpr("-", FunExpr("sqrt", [FunExpr("abs", [in_var])]))
            cond1 = cond0.neg()
            expr1 = FunExpr("sqrt", [in_var])
            out_var = self.src_lines[0][0].name
            return {out_var: [(cond0, expr0), (cond1, expr1)]}
