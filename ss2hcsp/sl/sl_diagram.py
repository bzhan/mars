from ss2hcsp.sl.sl_line import SL_Line
# from ss2hcsp.hcsp import hcsp as hp

from functools import reduce
from math import gcd
import re


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
        return "\n".join(str(block) for block in self.blocks_dict.values())

    def check(self):
        """Checks the diagram is valid. Among the checks are:

        For each block, each dest port is filled, each src port has
        at least one outgoing line.

        """
        pass

    def add_line_name(self):
        # Give each group of lines a name
        num_lines = 0
        for block in self.blocks_dict.values():
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

    def comp_inher_st(self):
        """Compute the sample time for each block with inherent sample time.
        This function cannot be executed correctly until all the ports are deleted, i.e.,
        delete_ports() should precede comp_inher_st(), or let delete_port() be
        at the begining of comp_inher_st()."""
        # self.delete_ports()
        terminate = False
        while not terminate:
            terminate = True
            for block in self.blocks_dict.values():
                if block.st == "-1":
                    in_st = []  # list of sample times of inputs of the block
                    for line in block.dest_lines:
                        if line.src in self.blocks_dict and self.blocks_dict[line.src].st != "-1":
                            in_block = self.blocks_dict[line.src]
                            in_st.append(int(in_block.st))
                        else:
                            in_st = None
                            break
                    if in_st:
                        st_gcd = reduce(gcd, in_st)
                        if st_gcd == 0:
                            block.is_continuous = True
                        block.st = str(st_gcd)
                        terminate = False

        # Define the sample time for each block whose sample time is still unknown
        for block in self.blocks_dict.values():
            if block.st == "-1":
                known_in_st = []  # list of known sample times of inputs of the block
                unknown_in_st = []  # list of unknown sample times of inputs of the block
                for line in block.dest_lines:
                    if line.src in self.blocks_dict:
                        in_block = self.blocks_dict[line.src]
                        if re.match("\\d+", self.blocks_dict[line.src]):
                            known_in_st.append(int(in_block.st))
                        else:
                            unknown_in_st.append(in_block.name)
                    else:  # in_block is a port, which is deleted at the begining
                        unknown_in_st.append(line.name)
                if known_in_st:
                    st_gcd = reduce(gcd, known_in_st) if len(known_in_st) >= 2 else known_in_st[0]
                    unknown_in_st.append(str(st_gcd))
                if len(unknown_in_st) == 1:
                    block.st = unknown_in_st[0]
                else:  # len(unknown_in_st) >= 2
                    block.st = "gcd(" + ", ".join(unknown_in_st) + ")"

    def delete_ports(self):
        for block in self.blocks:
            if block.type == "in_port" or block.type == "out_port":
                del self.blocks_dict[block.name]
        self.blocks = self.blocks_dict.values()
