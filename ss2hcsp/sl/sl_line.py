"""Represents a single line in a Simulink diagram."""

class SL_Line:
    def __init__(self, src: str, dest: str, src_port: int, dest_port: int, *, name="?", ch_name="?"):
        # Source and target block
        assert isinstance(src, str) and isinstance(dest, str)
        self.src = src
        self.dest = dest

        # Port number within source and target block
        self.src_port = src_port
        self.dest_port = dest_port

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

class UnknownLine(SL_Line):
    def __init__(self):
        super(UnknownLine, self).__init__("?", "?", 0, 0, name="??", ch_name="??")

unknownLine = UnknownLine()
