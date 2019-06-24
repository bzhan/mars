from ss2hcsp.sl.sl_block import SL_Block

class Port(SL_Block):
    """Represents an input/output channel for the overall diagram."""
    def __init__(self, name, port_type):
        """port_type specifies whether it is an input or output channel.
        'in_port' means the block has a src line entering the diagram.
        'out_port' means the block has a dest line leaving the diagram.

        """
        self.name = name
        assert port_type == 'in_port' or port_type == 'out_port'
        self.type = port_type

        if self.type == 'in_port':
            self.num_src = 1
            self.src_lines = [[]]
            self.num_dest = 0
            self.dest_lines = []
        else:
            self.num_src = 0
            self.src_lines = []
            self.num_dest = 1
            self.dest_lines = [None]
