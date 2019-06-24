class Divide:
    """Multiply (or divide) a list of dest lines."""
    def __init__(self, name, dest_spec):
        """dest_spec is a list of either '*' or '/'."""
        self.name = name
        self.type = "divide"
        self.is_continuous = False
        self.num_src = len(dest_spec)
        self.num_dest = 1
        self.src_lines = [[]] * self.num_src
        self.dest_lines = [None] * self.num_src

        assert all(s == '*' or s == '/' for s in dest_spec)
        self.dest_spec = dest_spec
