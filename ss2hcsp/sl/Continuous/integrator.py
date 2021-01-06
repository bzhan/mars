from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.parser import hp_parser


class Integrator(SL_Block):
    """Block for integration."""
    def __init__(self, name, init_value=0):
        super(Integrator, self).__init__()
        self.name = name
        self.type = "integrator"
        self.is_continuous = True
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]

        assert isinstance(init_value, (int, float))
        self.init_value = init_value
        self.st = 0

    def __str__(self):
        return "%s: Integrator[init = %s, in = %s, out = %s]" % \
               (self.name, str(self.init_value), str(self.dest_lines), str(self.src_lines))

    def __repr__(self):
        return str(self)


class Buffer(Integrator):
    num = 0

    def __init__(self, name=None, init_value=0):
        super(Buffer, self).__init__(name, init_value)
        self.type = "buffer"
        if not name:
            self.name = "buffer" + str(Buffer.num)
            Buffer.num += 1

    def __str__(self):
        return "%s: Buffer[init = %s, in = %s, out = %s]" % \
               (self.name, str(self.init_value), str(self.dest_lines), str(self.src_lines))

    def get_hp(self):
        in_name = self.dest_lines[0]
        out_name = self.src_lines[0][0]
        init_value = str(self.init_value)
        return hp_parser.parse(in_name + " := " + init_value + "; <" + in_name + "_dot = 0 & true> |> [] (ch_"
                               + in_name + "?" + in_name + " --> skip, ch_" + out_name + "!" + in_name + " --> skip)")
