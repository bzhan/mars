from ss2hcsp.sl.sl_block import SL_Block


class Gain(SL_Block):
    """Multiply dest line by a factor."""
    def __init__(self, name, factor=1, *, st=-1):
        self.name = name
        self.type = "gain"
        self.is_continuous = (st == 0)
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]

        assert isinstance(factor, (int, float))
        self.factor = factor

        assert isinstance(st, (int, float))
        self.st = st

    def __str__(self):
        return "%s: Gain[in = %s, out = %s, st = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), int(self.st))
