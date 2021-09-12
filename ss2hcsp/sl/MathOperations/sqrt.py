from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, RelExpr, AConst, FunExpr, OpExpr, IfExpr
from ss2hcsp.hcsp import hcsp as hp


def convert_sqrt(in_var):
    in_var = AVar(in_var)
    return IfExpr(
        RelExpr(">=", in_var, AConst(0)),
        FunExpr("sqrt", [in_var]),
        OpExpr("-", FunExpr("sqrt", [OpExpr("-", in_var)])))


class Sqrt(SL_Block):
    """Compute the square root"""
    def __init__(self, name, operator, st=-1):
        super(Sqrt, self).__init__("sqrt", name, 1, 1, st)

        assert operator == 'signedSqrt'
        self.operator = operator

    def __str__(self):
        in_var = self.dest_lines[0].name
        expr = convert_sqrt(in_var)
        out_var = self.src_lines[0][0].name
        return "%s: %s = %s  (st = %s)" % (self.name, out_var, expr, str(self.st))

    def __repr__(self):
        return "Sqrt(%s, %s, %s, in = %s, out = %s)" % \
            (self.name, self.operator, self.st, str(self.dest_lines), str(self.src_lines))

    def get_output_hp(self):
        in_var = self.dest_lines[0].name
        expr = convert_sqrt(in_var)
        out_var = self.src_lines[0][0].name
        cond = RelExpr("==", OpExpr("%", AVar("t"), AConst(self.st)), AConst(0))
        return hp.Condition(cond=cond, hp=hp.Assign(var_name=out_var, expr=expr))

    def get_var_subst(self):
        in_var = self.dest_lines[0].name
        expr = convert_sqrt(in_var)
        out_var = self.src_lines[0][0].name
        return {out_var: expr}

    def get_var_map(self):
        in_var = AVar(self.dest_lines[0].name)
        if self.operator == "signedSqrt":
            cond0 = RelExpr("<", in_var, AConst(0))
            expr0 = OpExpr("-", FunExpr("sqrt", [FunExpr("abs", [in_var])]))
            cond1 = cond0.neg()
            expr1 = FunExpr("sqrt", [in_var])
            out_var = self.src_lines[0][0].name
            return {out_var: [(cond0, expr0), (cond1, expr1)]}
