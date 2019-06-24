from ss2hcsp.sl.sl_line import SL_Line
from ss2hcsp.hcsp import hcsp as hp

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

    def add_line(self, src, dest, src_port, dest_port):
        """Add given line to the diagram."""
        line = SL_Line(src, dest, src_port, dest_port)
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

    def translate(self):
        """Translate the given diagram to an HCSP program."""
        # Give each group of lines a name
        num_lines = 0
        for block in self.blocks:
            # Give name to the group of lines containing each
            # incoming line (if no name is given already).
            for i, line in enumerate(block.dest_lines):
                src, src_port = line.src, line.src_port
                line_group = self.blocks_dict[src].src_lines[src_port]
                if line_group[0].name == "":
                    for line2 in line_group:
                        line2.name = "x" + str(num_lines)
                    num_lines += 1
            # Give name to each group of outgoing lines (if no
            # name is given already).
            for i, lines in enumerate(block.src_lines):
                if lines[0].name == "":
                    for line in lines:
                        line.name = "x" + str(num_lines)
                    num_lines += 1
        
        # Initial values for variables
        init_hps = []

        # Differential equation
        ode_eqs = []

        for block in self.blocks:
            if block.type == 'integrator':
                src_name = block.src_lines[0][0].name
                dest_name = block.dest_lines[0].name
                init_hps.append(hp.Assign(dest_name, block.init_value))
                ode_eqs.append((src_name, dest_name))

        init_hps.append(hp.Assign("t", "0"))
        ode_eqs.append(("t", "1"))

        # Add communication for each port
        comm_hps = []
        for block in self.blocks:
            if block.type == 'in_port':
                src_name = block.src_lines[0][0].name
                comm_hps.append((hp.InputChannel("ch" + src_name, src_name), hp.Skip()))
            elif block.type == 'out_port':
                dest_name = block.dest_lines[0].name
                comm_hps.append((hp.OutputChannel("ch" + dest_name, dest_name), hp.Skip()))

        ode_hp = hp.ODE_Comm(ode_eqs, "True", comm_hps)
        return hp.Sequence(hp.Sequence(*init_hps), hp.Loop(ode_hp))
