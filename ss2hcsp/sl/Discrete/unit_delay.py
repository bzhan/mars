from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, AConst, RelExpr, FunExpr
from ss2hcsp.hcsp.parser import hp_parser


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
        # assert isinstance(delay, (int, float))
        # self.delay = delay
        # self.st = delay
        assert st > 0
        self.st = st

    def __str__(self):
        return "%s: UnitDelay[init = %s, in = %s, out = %s, delay = %s]" % \
               (self.name, str(self.init_value), str(self.dest_lines), str(self.src_lines), str(self.st))

    def __repr__(self):
        return str(self)

    # def get_var_map(self):
    #     in_var = AVar(self.dest_lines[0].name)
    #     cond0 = RelExpr("<", AVar("t"), AConst(self.st))
    #     expr0 = AConst(self.init_value)
    #     cond1 = cond0.neg()
    #     expr1 = FunExpr("delay", [in_var, AConst(self.st)])
    #     out_var = self.src_lines[0][0].name
    #     return {out_var: [(cond0, expr0), (cond1, expr1)]}

    def get_hcsp(self):
        assert len(self.dest_lines) == 1
        in_var = self.dest_lines[0].name
        in_branch = str(self.dest_lines[0].branch)
        assert len(self.src_lines) == 1 and len(self.src_lines[0]) == 1
        out_var = self.src_lines[0][0].name
        out_branch = str(self.src_lines[0][0].branch)
        return hp_parser.parse(in_var + " := " + str(self.init_value) + "; "
                               + "ch_" + out_var + "_" + out_branch + "!" + in_var + "; "
                               + "(ch_" + in_var + "_" + in_branch + "?" + in_var + "; t := 0; "
                               + "<t_dot = 1, " + in_var + "_dot = 0 & t < " + str(self.st) + ">; "
                               + "ch_" + out_var + "_" + out_branch + "!" + in_var + ")**")
