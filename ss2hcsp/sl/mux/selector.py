from ss2hcsp.sl.sl_block import SL_Block

class Selector(SL_Block):
    def __init__(self, name, width, indices):
        super(Selector, self).__init__("selector", name, 1, 1, st=0)
        self.width = width
        self.indices = indices

    def __str__(self):
        in_var = self.dest_lines[0].name
        out_var = self.src_lines[0][0].name
        return "%s: %s = %s%s" % (self.name, out_var, in_var, self.indices)

    def __repr__(self):
        return "Selector(%s, %s, %s)" % (self.name, self.width, self.indices)
