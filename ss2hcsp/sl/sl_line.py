class SL_Line:
    """Represents a single line in a Simulink diagram."""
    def __init__(self, src, dest, src_port, dest_port, *, name="?", ch_name="?"):
        # Source and target block
        assert isinstance(src, str) and isinstance(dest, str)
        self.src = src  # string
        self.dest = dest  # string

        # Port number within source and target block
        self.src_port = src_port  # nat
        self.dest_port = dest_port  # nat

        self.name = name
        self.ch_name = ch_name

        self.branch = None

        self.src_block = None
        self.dest_block = None

    def __str__(self):
        return self.name

    def __repr__(self):
        return "SL_Line(%s, %s, %s, %s, %s, %s)" % \
            (self.src, self.dest, self.src_port, self.dest_port, self.name, self.ch_name)
