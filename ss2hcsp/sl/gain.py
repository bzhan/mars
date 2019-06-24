from ss2hcsp.sl.sl_block import SL_Block

class Gain(SL_Block):
    """Multiply dest line by a factor."""
    def __init__(self, name, factor):
        self.name = name
        self.type = "gain"
        self.is_continuous = False
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]

        self.factor = factor
