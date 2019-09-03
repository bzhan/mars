from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar


class Port(SL_Block):
    """Represents an input/output channel for the overall diagram."""
    def __init__(self, name, port_type):
        super(Port, self).__init__()
        """port_type specifies whether it is an input or output channel.
        'in_port' means the block has a src line entering the diagram.
        'out_port' means the block has a dest line leaving the diagram.

        """
        self.name = name
        assert port_type in ['in_port', 'out_port']
        self.type = port_type

        if self.type == 'in_port':
            self.num_src = 1
            self.src_lines = [[]]
            self.num_dest = 0
            self.dest_lines = []
            self.st = AVar(name=self.name)
        else:
            self.num_src = 0
            self.src_lines = []
            self.num_dest = 1
            self.dest_lines = [None]
            self.st = -1

    def __str__(self):
        if self.type == 'in_port':
            return "%s: InPort[out = %s]" % (self.name, str(self.src_lines))
        else:
            return "%s: OutPort[in = %s]" % (self.name, str(self.dest_lines))
