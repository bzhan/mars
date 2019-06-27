from ss2hcsp.sl.sl_block import SL_Block


class Divide(SL_Block):
    """Multiply (or divide) a list of dest lines."""
    def __init__(self, name, dest_spec, *, st=-1):
        """dest_spec is a list of either '*' or '/'."""
        self.name = name
        self.type = "divide"
        self.is_continuous = False
        self.num_src = 1
        self.num_dest = len(dest_spec)
        self.src_lines = [[]]
        self.dest_lines = [None] * self.num_dest

        assert all(s == '*' or s == '/' for s in dest_spec)
        assert len(dest_spec) >= 2
        self.dest_spec = dest_spec  # string
        self.st = str(st)

    def __str__(self):
        return "%s: Divide[in = %s, out = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines))
