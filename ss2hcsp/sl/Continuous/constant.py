from ss2hcsp.sl.sl_block import SL_Block


class Constant(SL_Block):
    """Block for constant."""
    def __init__(self, name, value):
        self.name = name
        self.type = "constant"
        self.is_continuous = True
        self.num_src = 1
        self.num_dest = 0
        self.src_lines = [[]]
        self.dest_lines = []

        self.value = str(value)  # string

        self.st = "0"

    def __str__(self):
        return "%s: Constant[value = %s, out = %s]" % (self.name, self.value, str(self.src_lines))
