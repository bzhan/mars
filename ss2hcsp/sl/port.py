from ss2hcsp.sl.sl_block import SL_Block


class Port(SL_Block):
    """Represents an input/output channel for the overall diagram."""
    def __init__(self, name, port_name="", port_type="in_port"):
        """port_type specifies whether it is an input or output channel.
        'in_port' means the block has a src line entering the diagram.
        'out_port' means the block has a dest line leaving the diagram.

        """
        super(Port, self).__init__()
        self.name = name  # of the form in_0 or out_1
        if port_name:  # the real name
            self.port_name = port_name
        else:
            self.port_name = self.name
        assert port_type in ['in_port', 'out_port']
        self.type = port_type
        self.st = -1

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

    def __str__(self):
        if self.type == 'in_port':
            input = self.src_lines[0][0].name
            return "%s: input %s" % (self.name, input)
        else:
            output = self.dest_lines[0].name
            return "%s: output %s" % (self.name, output)

    def __repr__(self):
        return "Port(%s, %s, %s, in = %s, out = %s)" % \
            (self.name, self.port_name, self.type, str(self.dest_lines), str(self.src_lines))
