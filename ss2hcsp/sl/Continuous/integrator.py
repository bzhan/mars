from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.parser import hp_parser


class Integrator(SL_Block):
    """Block for integration."""
    def __init__(self, name, init_value=0):
        super(Integrator, self).__init__("integrator", name, 1, 1, st=0)

        assert isinstance(init_value, (int, float))
        self.init_value = init_value

    def __str__(self):
        in_var = self.dest_lines[0].name
        out_var = self.src_lines[0][0].name
        return "%s: %s_dot = %s  (init = %s)" % (self.name, out_var, in_var, self.init_value)

    def __repr__(self):
        return "Integrator(%s, %s, in = %s, out = %s)" % \
            (self.name, self.init_value, str(self.dest_lines),  str(self.src_lines))
