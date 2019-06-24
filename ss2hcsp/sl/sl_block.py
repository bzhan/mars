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
        self.src_lines = []

        # Lines ending at the block, maintained as a list of
        # SL_Line objects
        self.dest_lines = []

    def add_src(self, port_id, sl_line):
        assert port_id < self.num_src
        self.src_lines[port_id].append(sl_line)

    def add_dest(self, port_id, sl_line):
        assert port_id < self.num_dest
        self.dest_lines[port_id] = sl_line
