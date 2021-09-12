from ss2hcsp.sl.sl_block import SL_Block


class Port(SL_Block):
    """Represents an input/output channel for the overall diagram."""
    def __init__(self, name, port_name="", port_type="in_port"):
        """port_type specifies whether it is an input or output channel.
        'in_port' means the block has a src line entering the diagram.
        'out_port' means the block has a dest line leaving the diagram.

        """
        assert port_type in ['in_port', 'out_port']
        if port_type == 'in_port':
            num_src, num_dest = 1, 0
        else:
            num_src, num_dest = 0, 1
        super(Port, self).__init__(port_type, name, num_src, num_dest, st=-1)

        # The real name
        if port_name:
            self.port_name = port_name
        else:
            self.port_name = self.name

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
