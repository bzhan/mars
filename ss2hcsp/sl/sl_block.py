"""Simulink blocks."""

from decimal import Decimal
from functools import reduce
from math import gcd, pow

from ss2hcsp.sl.sl_line import SL_Line
from ss2hcsp.hcsp.expr import true_expr


def get_gcd(sample_times):
    """Return the gcd of a list of sample times.

    If some of the sample times are not integers, first multiply by an
    appropriate power of 10 before taking gcd.

    """
    if len(sample_times) == 0:
        return 0  # continuous

    assert isinstance(sample_times, (list, tuple)) and len(sample_times) >= 1
    assert all(isinstance(st, (int, Decimal)) for st in sample_times)

    if len(sample_times) == 1:
        return sample_times[0]

    if 0 in sample_times:
        return 0
    elif -2 in sample_times:
        return -2
    elif -1 in sample_times:
        return -1

    scaling_positions = []
    for st in sample_times:
        if isinstance(st, int) or int(st) == st:
            scaling_positions.append(0)
        else:  # isinstance(st, Decimal)
            scaling_positions.append(len(str(st)) - str(st).index(".") - 1)
    scale = 10 ** max(scaling_positions)
    scaling_sample_times = [int(st * scale) for st in sample_times]
    result_gcd = reduce(gcd, scaling_sample_times)
    if result_gcd % scale == 0:
        return result_gcd // int(scale)
    else:
        return Decimal(result_gcd) / scale

class SL_Block:
    """Represents a block in a Simulink diagram."""
    def __init__(self, type, name, num_src, num_dest, st):
        # Name of the block
        self.name = name

        # Type of the block, corresponds to class name
        self.type = type

        # Whether a block is continuous or discrete
        self.is_continuous = (st == 0)

        # Number of ports for lines originating from the block
        self.num_src = num_src

        # Number of ports for lines ending at the block
        self.num_dest = num_dest

        # Lines originating from the block, maintained as a list
        # of lists of SL_Line objects.
        self.src_lines = [[] for _ in range(num_src)]

        # Lines ending at the block, maintained as a list of
        # SL_Line objects
        self.dest_lines = [None] * num_dest

        # Sample time
        assert isinstance(st, (int, Decimal))
        self.st = st

        # Enabled condition
        self.enable = true_expr

    def add_src(self, port_id, sl_line):
        """Add a source line."""
        # assert port_id < self.num_src
        assert isinstance(sl_line, SL_Line)
        # First check if there is a branch that is currently None
        for branch in range(len(self.src_lines[port_id])):
            if self.src_lines[port_id][branch] is None:
                sl_line.branch = branch
                self.src_lines[port_id][branch] = sl_line
                return
        # If all filled, append at the end.
        sl_line.branch = len(self.src_lines[port_id])
        self.src_lines[port_id].append(sl_line)

    def add_dest(self, port_id, sl_line):
        """Add a destination line."""
        assert port_id < self.num_dest
        if len(self.dest_lines):
            self.dest_lines[port_id] = sl_line

    def get_src_blocks(self):
        return set(line.src for line in self.dest_lines)

    def get_input_vars(self):
        return set(line.name for line in self.dest_lines)

    def get_output_vars(self):
        assert all(len(set(line.name for line in line_list)) == 1 for line_list in self.src_lines)
        return set(line_list[0].name for line_list in self.src_lines)

    def get_init_hp(self):
        return None

    def get_output_hp(self):
        return None
