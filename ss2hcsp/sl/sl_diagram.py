from ss2hcsp.sl.sl_line import SL_Line
from ss2hcsp.hcsp import hcsp as hp

from functools import reduce
from math import gcd


class SL_Diagram:
    """Represents a Simulink diagram."""
    def __init__(self):
        # List of blocks, in order of insertion.
        self.blocks = list()

        # Dictionary of blocks indexed by name
        self.blocks_dict = dict()

    def add_block(self, block):
        """Add given block to the diagram."""
        self.blocks.append(block)
        self.blocks_dict[block.name] = block

    def add_line(self, src, dest, src_port, dest_port, *, name="?"):
        """Add given line to the diagram."""
        line = SL_Line(src, dest, src_port, dest_port, name=name)
        src_block = self.blocks_dict[line.src]
        dest_block = self.blocks_dict[line.dest]
        
        src_block.add_src(line.src_port, line)
        dest_block.add_dest(line.dest_port, line)

    def __str__(self):
        return "\n".join(str(block) for block in self.blocks)

    def check(self):
        """Checks the diagram is valid. Among the checks are:

        For each block, each dest port is filled, each src port has
        at least one outgoing line.

        """
        pass

    def add_line_name(self):
        # Give each group of lines a name
        num_lines = 0
        for block in self.blocks:
            # Give name to the group of lines containing each
            # incoming line (if no name is given already).
            for i, line in enumerate(block.dest_lines):
                src, src_port = line.src, line.src_port
                line_group = self.blocks_dict[src].src_lines[src_port]
                if line_group[0].name == "?":
                    for line2 in line_group:
                        line2.name = "x" + str(num_lines)
                    num_lines += 1
            # Give name to each group of outgoing lines (if no
            # name is given already).
            for i, lines in enumerate(block.src_lines):
                if lines[0].name == "?":
                    for line in lines:
                        line.name = "x" + str(num_lines)
                    num_lines += 1

    def translate_continuous(self):
        """Translate the given diagram to an HCSP program."""
        self.add_line_name()
        
        # Initial values for variables
        init_hps = []

        # Differential equation
        ode_eqs = []

        for block in self.blocks:
            if block.type == "integrator":
                src_name = block.src_lines[0][0].name
                init_hps.append(hp.Assign(var_name=src_name, expr=block.init_value))
                dest_name = block.dest_lines[0].name
                ode_eqs.append((src_name, dest_name))
            elif block.type == "constant":
                src_name = block.src_lines[0][0].name
                init_hps.append(hp.Assign(var_name=src_name, expr=block.value))
                ode_eqs.append((src_name, "0"))

        init_hps.append(hp.Assign(var_name="t", expr="0"))
        ode_eqs.append(("t", "1"))

        # Add communication for each port
        comm_hps = []
        for block in self.blocks:
            if block.type == 'in_port':
                src_name = block.src_lines[0][0].name
                comm_hps.append((hp.InputChannel(var_name=src_name), hp.Skip()))
            elif block.type == 'out_port':
                dest_name = block.dest_lines[0].name
                comm_hps.append((hp.OutputChannel(expr=dest_name), hp.Skip()))

        ode_hp = hp.ODE_Comm(eqs=ode_eqs, constraint="True", io_comms=comm_hps)
        return hp.Sequence(hp.Sequence(*init_hps), hp.Loop(ode_hp))

    def translate_discrete(self):
        """Translate the given diagram to an HCSP program."""
        self.add_line_name()

        # Initialization
        init_hp = hp.Assign(var_name="t", expr="0")

        # Get input and output channels
        in_channels = []
        out_channels = []
        for block in self.blocks:
            if block.type == "in_port":  # get input channels
                in_channels.append(hp.InputChannel(var_name=block.src_lines[0][0].name))
            elif block.type == "out_port":  # get output channels
                out_channels.append(hp.OutputChannel(expr=block.dest_lines[0].name))

        # Get discrete processes
        discrete_hps = []
        for block in self.blocks:
            if not hasattr(block, "st"):
                continue
            cond = "t%" + block.st + "==0"
            block_hp = None
            in_vars = [line.name for line in block.dest_lines]  # keep the order?
            out_var = block.src_lines[0][0].name
            if block.type in ["gain", "bias", "abs", "not"]:
                in_var = in_vars[0]
                block_hp = None
                if block.type == "gain":
                    if block.factor.startswith("-"):
                        expr = in_var + "*(" + block.factor + ")"
                    else:
                        expr = in_var + "*" + block.factor
                    block_hp = hp.Assign(var_name=out_var, expr=expr)
                elif block.type == "bias":
                    if block.bias.startswith("-"):
                        expr = in_var + block.bias
                    else:
                        expr = in_var + "+" + block.bias
                    block_hp = hp.Assign(var_name=out_var, expr=expr)
                elif block.type == "abs":
                    # cond_hp1 = hp.Condition(cond=in_var + ">=0", hp=hp.Assign(var_name=out_var, expr=in_var))
                    # cond_hp2 = hp.Condition(cond=in_var + "<0", hp=hp.Assign(var_name=out_var, expr="-" + in_var))
                    # block_hp = hp.Sequence(cond_hp1, cond_hp2)
                    block_hp = hp.Assign(var_name=out_var, expr="abs(" + in_var + ")")
                elif block.type == "not":
                    block_hp = hp.Assign(var_name=out_var, expr="1-" + in_var)
            elif block.type in ["add", "divide"]:
                assert len(in_vars) == len(block.dest_spec)
                # Get the head of the expression
                expr = in_vars[0]
                if block.dest_spec[0] == "-":
                    expr = "-" + expr
                elif block.dest_spec[0] == "/":
                    expr = "1/" + expr
                for i in range(1, len(block.dest_spec)):
                    expr = expr + block.dest_spec[i] + in_vars[i]
                block_hp = hp.Assign(var_name=out_var, expr=expr)
            elif block.type in ["or", "and"]:
                if block.type == "or":
                    block_hp = hp.Assign(var_name=out_var, expr="max(" + ", ".join(in_vars) + ")")
                elif block.type == "and":
                    block_hp = hp.Assign(var_name=out_var, expr="min(" + ", ".join(in_vars) + ")")
            elif block.type == "relation":
                block_hp = hp.Assign(var_name=out_var, expr=block.relation.join(in_vars))
            elif block.type == "switch":
                cond0 = in_vars[1] + block.relation + block.threshold
                cond_hp0 = hp.Condition(cond=cond0, hp=hp.Assign(var_name=out_var, expr=in_vars[0]))
                cond2 = in_vars[1] + block.neg_relation + block.threshold
                cond_hp2 = hp.Condition(cond=cond2, hp=hp.Assign(var_name=out_var, expr=in_vars[2]))
                block_hp = hp.Sequence(cond_hp0, cond_hp2)
            discrete_hps.append(hp.Condition(cond=cond, hp=block_hp))

        # Get the time process
        # Compute the GCD of sample times of all the discrete blocks
        st_gcd = reduce(gcd, [int(block.st) for block in self.blocks if hasattr(block, "st")])
        temp = hp.Assign(var_name="temp", expr="t")
        time_ode = hp.ODE(eqs=[("t", "1")], constraint="t<temp+" + str(st_gcd))
        time_process = hp.Sequence(temp, time_ode)

        # Get loop body
        loop_hps = in_channels + discrete_hps + out_channels
        loop_hps.append(time_process)
        loop_hps = hp.Sequence(*loop_hps)

        return hp.Sequence(init_hp, hp.Loop(loop_hps))
