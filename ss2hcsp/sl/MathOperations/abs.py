from ss2hcsp.sl.sl_block import SL_Block


class Abs(SL_Block):
    """Compute the absolute value of the dest line."""
    def __init__(self, name, *, st=-1):
        self.name = name
        self.type = "abs"
        self.is_continuous = False
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]
        self.st = str(st)

    def __str__(self):
        return "%s: Abs[in = %s, out = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines))
