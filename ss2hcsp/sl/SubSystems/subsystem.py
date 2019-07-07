from ss2hcsp.sl.sl_block import SL_Block
# from ss2hcsp.sl.sl_diagram import SL_Diagram


class Subsystem(SL_Block):
    """Subsystem is block in which there is a diagram"""
    def __init__(self, name, num_src, num_dest):
        self.name = name
        self.type = "subsystem"
        self.is_continuous = False
        self.num_src = num_src
        self.num_dest = num_dest
        self.src_lines = [[] for _ in range(self.num_src)]  # [[]] * self.num_src
        self.dest_lines = [None] * self.num_dest
        self.diagram = None

    def __str__(self):
        return "%s: Subsystem[in = %s, out = %s, diagram = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), str(self.diagram))
