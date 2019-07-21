from ss2hcsp.sl.sl_block import SL_Block


class MinMax(SL_Block):
    """Min or max of dest lines."""
    def __init__(self, name, num_dest, *, fun_name="min", st=-1):
        self.name = name
        self.type = "min_max"
        self.is_continuous = (st == 0)
        self.num_src = 1
        self.num_dest = num_dest
        self.src_lines = [[]]
        self.dest_lines = [None] * self.num_dest

        assert fun_name in ["min", "max"]
        self.fun_name = fun_name
        assert isinstance(st, (int, float))
        self.st = st

    def __str__(self):
        return "%s: %s[in = %s, out = %s, st = %s]" % \
               (self.name, self.fun_name, str(self.dest_lines), str(self.src_lines), str(self.st))
