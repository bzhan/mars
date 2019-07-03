from ss2hcsp.sl.sl_block import SL_Block


class Integrator(SL_Block):
    """Block for integration."""
    def __init__(self, name, init_value):
        self.name = name
        self.type = "integrator"
        self.is_continuous = True
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]
        self.init_value = str(init_value)

        self.st = "0"

    def __str__(self):
        return "%s: Integrator[init = %s, in = %s, out = %s]" % \
               (self.name, self.init_value, str(self.dest_lines), str(self.src_lines))
