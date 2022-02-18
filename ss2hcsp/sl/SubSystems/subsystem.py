from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import RelExpr, AVar, AConst, true_expr, LogicExpr, conj, OpExpr, FunExpr
import ss2hcsp.hcsp.hcsp as hp


class Subsystem(SL_Block):
    """Subsystem is block in which there is a diagram"""
    def __init__(self, type, name, num_src, num_dest, st):
        super(Subsystem, self).__init__(type, name, num_src, num_dest, st)
        self.diagram = None

    def __str__(self):
        res = "%s: subsystem\n" % (self.name)
        res += "\n".join("  " + line for line in str(self.diagram).split('\n'))
        return res

    def __repr__(self):
        return "Subsystem(%s, %s, %s, %s, in = %s, out = %s)" % \
            (self.name, self.num_src, self.num_dest, self.st, str(self.dest_lines), str(self.src_lines))

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
        super(Triggered_Subsystem, self).__init__("triggered_subsystem", name, num_src, num_dest, st=-1)

        # Trigger type
        assert trigger_type in ("rising", "falling", "either", None), \
            "Unknown trigger type: %s" % trigger_type
        self.trigger_type = trigger_type

        # A flag variable denoting if the subsystem was triggered at the last step
        self.triggered = self.name + "_triggered"

        # Trigger lines: [(line_name, trigger_type, event), ...]
        self.trigger_lines = list()

    def __str__(self):
        trig_var = self.dest_lines[-1].name
        res = "%s: on_%s(%s):\n" % (self.name, self.trigger_type, trig_var)
        res += "\n".join("  " + line for line in str(self.diagram).split('\n'))
        return res

    def __repr__(self):
        return "Triggered_Subsystem(%s, %s, %s, %s, in = %s, out = %s)" % \
            (self.name, self.num_src, self.num_dest, self.trigger_type,
             str(self.dest_lines), str(self.src_lines))

    def get_pre_cur_trig_signals(self, line):
        """Obtain variables for current and previous trigger value."""
        # trig_var = self.dest_lines[-1].name
        cur_sig = AVar(line)
        pre_sig = AVar("pre_" + line)
        return pre_sig, cur_sig

    def get_output_hp(self):
        output_hps = list()
        for line, trigger_type, event in self.trigger_lines:
            name_line_triggered = self.name+"_"+line+"_triggered"
            if_triggered = RelExpr("==", AVar(name_line_triggered), AConst(1))
            time_cond = RelExpr("==", OpExpr("%", AVar("t"), AConst(self.st)), AConst(0))
            trig_cond = self.get_discrete_triggered_condition(line, trigger_type)
            pre_sig, cur_sig = self.get_pre_cur_trig_signals(line)
            if event:
                assert self.type == "stateflow"
                push_event = hp.Assign(var_name=self.name+"EL",
                                       expr=FunExpr(fun_name="push", exprs=[AVar(self.name+"EL"), AConst(event)]))
                execute_chart = hp.Var(self.exec_name)
                pop_event = hp.Assign(var_name=self.name+"EL",
                                      expr=FunExpr(fun_name="pop", exprs=[AVar(self.name+"EL")]))
                main_execute = hp.Sequence(push_event, execute_chart, pop_event)
            else:
                assert self.type == "triggered_subsystem"
                main_execute = hp.Var(self.name)
            # output_hp = hp.Sequence(
            #     hp.ITE(if_hps=[(if_triggered, hp.Assign(var_name=name_line_triggered, expr=AConst(0)))],
            #            else_hp=hp.Condition(cond=conj(time_cond,trig_cond),
            #                                 hp=hp.Sequence(
            #                                     hp.Assign(var_name=name_line_triggered, expr=AConst(1)),
            #                                     main_execute))),
            #     hp.Assign(var_name=pre_sig.name, expr=cur_sig)
            # )
            output_hp = hp.Sequence(
            hp.ITE(if_hps=[(if_triggered, hp.Assign(var_name=name_line_triggered, expr=AConst(0)))],
                   else_hp=hp.Condition(cond=trig_cond,
                                        hp=hp.Sequence(
                                            hp.Assign(var_name=name_line_triggered, expr=AConst(1)),
                                            main_execute))),
            hp.Assign(var_name=pre_sig.name, expr=cur_sig)
        )
            output_hps.append(output_hp)

        return hp.seq(output_hps)

    def get_init_hps(self):
        # Initialize the triggered signals
        init_hps = list()
        for line, _, _ in self.trigger_lines:
            pre_sig, cur_sig = self.get_pre_cur_trig_signals(line)
            init_hps.append(hp.Assign(var_name=self.name+"_"+line+"_triggered", expr=AConst(1)))
            if not self.is_continuous:
                init_hps.append(hp.Assign(var_name=pre_sig.name, expr=AConst(0)))  # pre_sig := 0
                init_hps.append(hp.Assign(var_name=cur_sig.name, expr=AConst(0)))  # cur_sig := 0

        # Initialize the output variables
        for lines in self.src_lines:
            out_var = lines[0].name
            init_hps.append(hp.Assign(var_name=out_var, expr=AConst(0)))

        # Initialize the variables of the inner blocks
        if self.type == "triggered_subsystem":
            for block in self.diagram.blocks_dict.values():
                if block.type == "constant":
                    out_var = block.src_lines[0][0].name
                    init_hps.append(hp.Assign(var_name=out_var, expr=AConst(block.value)))
                elif block.type == "unit_delay":
                    init_hps.append(hp.Assign(var_name=block.name+"_state", expr=AConst(block.init_value)))
                elif block.type == "triggered_subsystem":
                    init_hps.extend(block.get_init_hps())
        return init_hps

    def get_discrete_triggered_condition(self, line, trigger_type):
        """Obtain the discrete trigger condition."""
        pre_sig, cur_sig = self.get_pre_cur_trig_signals(line)

        # Compare pre_sig and cur_sig with zero. Different comparisons for
        # different trigger conditions.
        if trigger_type == "rising":
            # (pre_sig < 0 && cur_sig >= 0) || (pre_sig == 0 && cur_sig > 0)
            op0, op1, op2, op3 = "<", ">=", "==", ">"
        elif trigger_type == "falling":
            # (pre_sig > 0 && cur_sig <= 0) || (pre_sig == 0 && cur_sig < 0)
            op0, op1, op2, op3 = ">", "<=", "==", "<"
        elif trigger_type == "either":
            # (pre_sig < 0 && cur_sig >= 0) || (pre_sig >= 0 && cur_sig < 0)
            op0, op1, op2, op3 = "<=", ">", ">", "<="
            
        else:
            raise NotImplementedError("Unknown trigger type: %s" % trigger_type)

        return LogicExpr(
            "||", LogicExpr("&&", RelExpr(op0, pre_sig, AConst(0)), RelExpr(op1, cur_sig, AConst(0))),
                  LogicExpr("&&", RelExpr(op2, pre_sig, AConst(0)), RelExpr(op3, cur_sig, AConst(0))))

    def get_continuous_triggered_condition(self):
        """Obtain the continuous trigger condition.
        
        Currently, we assume that the trigger line is the output of an
        integrator.

        """
        trig_line = self.dest_lines[-1]
        trig_sig = AVar(trig_line.name)
        assert trig_line.src_block.type == "integrator"
        trig_sig_dot = AVar(trig_line.src_block.dest_lines[0].name)

        if self.trigger_type == "rising":
            return conj(RelExpr("!=", AVar(self.triggered), AConst(1)),
                        RelExpr(">", trig_sig_dot, AConst(0)), RelExpr("==", trig_sig, AConst(0)))
        elif self.trigger_type == "falling":
            return conj(RelExpr("!=", AVar(self.triggered), AConst(1)),
                        RelExpr("<", trig_sig_dot, AConst(0)), RelExpr("==", trig_sig, AConst(0)))
        elif self.trigger_type == "either":
            return conj(RelExpr("!=", AVar(self.triggered), AConst(1)),
                        RelExpr("!=", trig_sig_dot, AConst(0)), RelExpr("==", trig_sig, AConst(0)))
        else:
            raise RuntimeError("Not implemented yet")

    def delete_subsystems(self):
        self.diagram.delete_subsystems()
        for block in self.diagram.block_dict.values():
            assert block.type not in ["subsystem", "enabled_subsystem"]
            if block.type == "triggered_subsystem":
                block.delete_subsystems()

    def get_procedures(self):
        """ Get the procedure body by topological sort. """
        # Get a list of sorted blocks
        block_dict = {name: block for name, block in self.diagram.blocks_dict.items()
                      if block.type not in ["in_port", "out_port", "constant"]}

        # Get a topological sort of the blocks
        # First, move all the Unit_Delay blocks from block_dict to sorted_blocks
        sorted_blocks = [block for block in block_dict.values() if block.type == "unit_delay"]
        for block in sorted_blocks:
            del block_dict[block.name]
        # Get a topological sort of the remaining blocks
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

        # Get the OUTPUT of each block in sorted_blocks
        output_hps = [block.get_output_hp() for block in sorted_blocks]
        # Get the UPDATE of Unit_Delay blocks
        update_hps = [block.get_update_hp() for block in sorted_blocks if block.type == "unit_delay"]

        result_hps = output_hps + update_hps
        result_hp = hp.Sequence(*result_hps) if len(result_hps) > 1 else result_hps[0]
        procedures = [hp.Procedure(name=self.name, hp=result_hp)]

        # Get the var-procedure mappings of the inner triggered subsystems
        for block in sorted_blocks:
            if block.type == "triggered_subsystem":
                inner_procedures = block.get_procedures()
                assert set(proc.name for proc in procedures).isdisjoint(
                    set(proc.name for proc in inner_procedures))
                procedures.extend(inner_procedures)

        return procedures


class Enabled_Subsystem(Subsystem):
    def __init__(self, name, num_src, num_dest):
        super(Enabled_Subsystem, self).__init__("enabled_subsystem", name, num_src, num_dest, st=-1)

    def __str__(self):
        en_line = self.dest_lines[-1]
        en_cond = RelExpr(">", AVar(en_line.name), AConst(0))
        res = "%s: on %s:\n" % (self.name, en_cond)
        res += "\n".join("  " + line for line in str(self.diagram).split('\n'))
        return res

    def __repr__(self):
        return "Enabled_Subsystem(%s, %s, %s, in = %s, out = %s)" % \
            (self.name, self.num_src, self.num_dest, str(self.dest_lines), str(self.src_lines))
