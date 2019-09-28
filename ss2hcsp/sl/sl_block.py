class SL_Block:
    """Represents a block in a Simulink diagram."""
    def __init__(self):
        # Name of the block
        self.name = ""

        # Type of the block, corresponds to class name
        self.type = ""

        # Whether a block is continuous or discrete
        self.is_continuous = False

        # Number of ports for lines originating from the block
        self.num_src = 0

        # Number of ports for lines ending at the block
        self.num_dest = 0

        # Lines originating from the block, maintained as a list
        # of lists of SL_Line objects.
        self.src_lines = [[]]

        # Lines ending at the block, maintained as a list of
        # SL_Line objects
        self.dest_lines = []

        # Sample time
        self.st = "-1"

    def __str__(self):
        return self.name

    # Add a source line
    def add_src(self, port_id, sl_line):
        assert port_id < self.num_src
        # sl_line is an object of class SL_Line
        for branch in range(len(self.src_lines[port_id])):
            if self.src_lines[port_id][branch] is None:
                sl_line.branch = branch
                self.src_lines[port_id][branch] = sl_line
                return
        sl_line.branch = len(self.src_lines[port_id])
        self.src_lines[port_id].append(sl_line)

    # Add a destination line
    def add_dest(self, port_id, sl_line):
        assert port_id < self.num_dest
        self.dest_lines[port_id] = sl_line

    def get_src_blocks(self):
        return set(line.src for line in self.dest_lines)

    def get_input_vars(self):
        return set(line.name for line in self.dest_lines)

    def get_output_vars(self):
        assert all(len(set(line.name for line in line_list)) == 1 for line_list in self.src_lines)
        return set(line_list[0].name for line_list in self.src_lines)
