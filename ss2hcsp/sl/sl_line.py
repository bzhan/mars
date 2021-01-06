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

    def __str__(self):
        return self.name
        # return "{" + self.src + "->" + self.dest + "}"

    def __repr__(self):
        return str(self)
