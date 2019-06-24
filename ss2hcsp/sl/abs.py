class Abs(SL_Block):
    """Compute the absolute value of the dest line."""
    def __init__(self, name):
        self.name = name
        self.type = "abs"
        self.is_continuous = False
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]
