from ss2hcsp.sl.sl_block import SL_Block


class UnitDelay(SL_Block):
    """Block for unit delay."""
    def __init__(self, name, init_value, st=-1):
        self.name = name
        self.type = "unit_delay"
        self.is_continuous = True
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]

        assert isinstance(init_value, (int, float))
        self.init_value = init_value
        assert isinstance(st, (int, float))
        self.st = 0.2 if st == -1 else st  # in conformity with MATLAB_R2018a

    def __str__(self):
        return "%s: UnitDelay[init = %s, in = %s, out = %s]" % \
               (self.name, str(self.init_value), str(self.dest_lines), str(self.src_lines))
