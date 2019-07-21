from ss2hcsp.sl.sl_block import SL_Block


class And(SL_Block):
    """Conjunction of dest lines."""
    def __init__(self, name, num_dest, *, st=-1):
        self.name = name
        self.type = "and"
        self.is_continuous = (st == 0)
        self.num_src = 1
        self.num_dest = num_dest
        self.src_lines = [[]]
        self.dest_lines = [None] * self.num_dest

        assert isinstance(st, (int, float))
        self.st = st

    def __str__(self):
        return "%s: And[in = %s, out = %s, st = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), str(self.st))
