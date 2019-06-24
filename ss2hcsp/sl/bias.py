from ss2hcsp.sl.sl_block import SL_Block

class Bias(SL_Block):
    def __init__(self, name, bias):
        self.name = name
        self.type = "bias"
        self.is_continuous = False
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]

        self.bias = bias
