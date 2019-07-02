from ss2hcsp.sl.sl_block import SL_Block


class Bias(SL_Block):
    def __init__(self, name, bias=0, *, st=-1):
        self.name = name
        self.type = "bias"
        self.is_continuous = False
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]

        self.bias = str(bias)  # string of a number
        self.st = str(st)

    def __str__(self):
        return "%s: Bias[in = %s, out = %s, st = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), self.st)
