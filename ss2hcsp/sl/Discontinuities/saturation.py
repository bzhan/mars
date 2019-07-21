from ss2hcsp.sl.sl_block import SL_Block


class Saturation(SL_Block):
    """Compute the saturation value of the dest line wrt. the upper and lower limits."""
    def __init__(self, name, up_lim, low_lim, *, st=-1):
        self.name = name
        self.type = "saturation"
        self.is_continuous = (st == 0)
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]

        assert isinstance(st, (int, float))
        self.st = st

        assert isinstance(up_lim, (int, float)) and isinstance(low_lim, (int, float))
        self.up_lim = up_lim
        self.low_lim = low_lim

    def __str__(self):
        return "%s: Saturation[in = %s, out = %s, st = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), str(self.st))
