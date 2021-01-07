from ss2hcsp.sl.sl_block import SL_Block


class Subsystem(SL_Block):
    """Subsystem is block in which there is a diagram"""
    def __init__(self, name, num_src, num_dest):
        super(Subsystem, self).__init__()
        self.name = name
        self.type = "subsystem"
        self.is_continuous = False
        self.num_src = num_src
        self.num_dest = num_dest
        self.src_lines = [[] for _ in range(self.num_src)]  # [[]] * self.num_src
        self.dest_lines = [None] * self.num_dest
        self.diagram = None

    def __str__(self):
        str_diagram = str(self.diagram)
        res = "%s: Subsystem[in = %s, out = %s, diagram =\n" % (self.name, self.dest_lines, self.src_lines)
        for line in str_diagram.split('\n'):
            res += "  " + line + "\n"
        res += "]"
        return res

    def __repr__(self):
        return str(self)


class Triggered_Subsystem(Subsystem):
    def __init__(self, name, num_src, num_dest, trigger_type):
        super(Triggered_Subsystem, self).__init__(name, num_src, num_dest)
        self.type = "triggered_subsystem"
        self.trigger_type = trigger_type
        self.st = -2  # non-periodic

    def __str__(self):
        return "%s: Triggered_Subsystem[in = %s, out = %s, tri = %s, diagram = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), self.trigger_type, str(self.diagram))

    def __repr__(self):
        return str(self)
