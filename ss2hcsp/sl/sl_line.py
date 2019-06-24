class SL_Line:
    """Represents a single line in a Simulink diagram."""
    def __init__(self, src, dest, src_port, dest_port):
        # Source and target block
        assert isinstance(src, str) and isinstance(dest, str)
        self.src = src
        self.dest = dest

        # Port number within source and target block
        self.src_port = src_port
        self.dest_port = dest_port
