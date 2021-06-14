from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import RelExpr, AVar, AConst, true_expr, false_expr, LogicExpr, ModExpr
import ss2hcsp.hcsp.hcsp as hp


class Subsystem(SL_Block):
    """Subsystem is block in which there is a diagram"""
    def __init__(self, name, num_src, num_dest):
        super(Subsystem, self).__init__()
        self.name = name
        self.type = "subsystem"
        self.is_continuous = False
        self.num_src = num_src
        self.num_dest = num_dest
        self.src_lines = [[] for _ in range(self.num_src)]
        self.dest_lines = [None] * self.num_dest
        self.diagram = None

    def __str__(self):
        str_diagram = str(self.diagram)
        res = "%s: Subsystem[in = %s, out = %s, diagram =\n" % (self.name, self.dest_lines, self.src_lines)
        for line in str_diagram.split('\n'):
            res += "  " + line + "\n"
        res += "]"
        return res

    def __repr__(self):
        return str(self)

    def add_enabled_condition_to_innerBlocks(self, init_en_cond=true_expr):
        en_line = self.dest_lines[-1]
        en_cond = RelExpr(">", AVar(en_line.name), AConst(0))
        if init_en_cond != true_expr:
            en_cond = LogicExpr("&&", init_en_cond, en_cond)
        for block in self.diagram.blocks:
            if hasattr(block, "enable"):
                block.enable = en_cond
            elif block.type in ["enabled_subsystem", "triggered_subsystem"]:
                block.add_enabled_condition_to_innerBlocks(init_en_cond=en_cond)


class Triggered_Subsystem(Subsystem):
    def __init__(self, name, num_src, num_dest, trigger_type):
        super(Triggered_Subsystem, self).__init__(name, num_src, num_dest)
        self.type = "triggered_subsystem"
        self.trigger_type = trigger_type
        self.st = -1

    def __str__(self):
        return "%s: Triggered_Subsystem[in = %s, out = %s, tri = %s, diagram = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), self.trigger_type, str(self.diagram))

    def __repr__(self):
        return str(self)

    def get_output_hp(self):
        cond = RelExpr("==", ModExpr(AVar("t"), AConst(self.st)), AConst(0))
        return hp.Condition(cond=cond, hp=hp.Var(self.name))

    def get_init_hps(self):
        init_hps = []
        for block in self.diagram.blocks:
            if block.type == "constant":
                out_var = block.src_lines[0][0].name
                init_hps.append(hp.Assign(var_name=out_var, expr=AConst(block.value)))
            elif block.type == "unit_delay":
                init_hps.append(hp.Assign(var_name=block.name+"_state", expr=AConst(block.init_value)))
            elif block.type == "triggered_subsystem":
                init_hps.extend(block.get_init_hps)
        return init_hps

    def get_discrete_triggered_condition(self):
        trig_var = self.dest_lines[-1].name
        trig_sig = AVar(trig_var)
        pre_sig = AVar("pre_" + trig_var)
        # rising: (pre_sig < 0 && trig_sig >= 0) || (pre_sig == 0 && trig_x > 0)
        op0, op1, op2, op3 = "<", ">=", "==", ">"
        if self.trigger_type == "falling":  # (pre_sig > 0 && trig_sig <= 0) || (pre_sig == 0 && trig_x < 0)
            op0, op1, op2, op3 = ">", "<=", "==", "<"
        elif self.trigger_type == "either":  # (pre_sig < 0 && trig_sig >= 0) || (pre_sig >= 0 && trig_x < 0)
            op0, op1, op2, op3 = "<", ">=", ">=", "<"
        elif self.trigger_type == "function-call":
            raise RuntimeError("Not implemented yet")
        trig_cond = LogicExpr("||",
                              LogicExpr("&&",
                                        RelExpr(op0, pre_sig, AConst(0)),
                                        RelExpr(op1, trig_sig, AConst(0))),
                              LogicExpr("&&",
                                        RelExpr(op2, pre_sig, AConst(0)),
                                        RelExpr(op3, trig_sig, AConst(0))))
        return trig_cond

    def get_continuous_triggered_condition(self):
        trig_sig = AVar(self.dest_lines[-1].name)
        if self.trigger_type == "rising":
            return RelExpr(">=", trig_sig, AConst(0))
        elif self.trigger_type == "falling":
            return RelExpr("<=", trig_sig, AConst(0))
        elif self.trigger_type == "either":
            return RelExpr("==", trig_sig, AConst(0))
        else:
            raise RuntimeError("Not implemented yet")

    def get_procedure(self):
        """ Get the procedure body by topological sort. """
        # Get a list of sorted blocks
        block_dict = {name: block for name, block in self.diagram.block_dict
                      if block.type not in ["in_port", "out_port", "constant"]}
        sorted_blocks = []
        while block_dict:
            head_block_names = []
            for name, block in block_dict.items():
                src_blocks = block.get_src_blocks()
                if src_blocks.isdisjoint(set(block_dict.keys())):
                    sorted_blocks.append(block)
                    head_block_names.append(name)
            assert head_block_names
            for name in head_block_names:
                del block_dict[name]

        # Get the main body of the procedure
        sorted_procedures = [hp.Var(block.name) for block in sorted_blocks]
        main_body = hp.Sequence(*sorted_procedures)

        # Get the triggered condition
        trig_var = self.dest_lines[-1].name
        trig_sig = AVar(trig_var)
        pre_sig = AVar("pre_"+trig_var)
        trig_cond = self.get_discrete_triggered_condition()

        # Initializations
        triggered = self.name + "_triggered"
        init_hps = [hp.Assign(var_name=triggered, expr=true_expr),  # name_triggered := true
                    hp.Assign(var_name=pre_sig.name, expr=AConst(0)),  # pre_sig := 0
                    hp.Assign(var_name=trig_sig.name, expr=AConst(0))]  # trig_sig := 0
        for block in self.diagram.blocks:
            if block.type == "constant":
                line_name = block.src_lines[0][0].name
                init_hps.append(hp.Assign(var_name=line_name, expr=AConst(block.value)))
        init_hp = hp.Sequence(*init_hps)

        # Complete the main body and then return
        if_triggered = RelExpr("==", AVar(triggered), true_expr)  # Triggered at the last step
        procedure = hp.Sequence(init_hp,
                                hp.Loop(
                                    hp.Sequence(
                                        hp.ITE(if_hps=[(if_triggered, hp.Assign(var_name=triggered, expr=false_expr))],
                                               else_hp=hp.Condition(cond=trig_cond,
                                                                    hp=hp.Sequence(hp.Assign(var_name=triggered,
                                                                                             expr=true_expr),
                                                                                   main_body))),
                                        hp.Assign(var_name=pre_sig.name, expr=trig_sig))
                                ))
        return procedure


class Enabled_Subsystem(Subsystem):
    def __init__(self, name, num_src, num_dest):
        super(Enabled_Subsystem, self).__init__(name, num_src, num_dest)
        self.type = "enabled_subsystem"
        self.st = -1

    def __str__(self):
        return "%s: Enabled_Subsystem[in = %s, out = %s, diagram = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), str(self.diagram))

    def __repr__(self):
        return str(self)
