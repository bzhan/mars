class SL_Diagram:
    """Represents a Simulink diagram."""
    def __init__(self):
        # Dictionary of blocks indexed by name
        self.blocks = dict()

    def add_block(self, block):
        """Add given block to the diagram."""
        self.blocks[block.name] = block

    def add_line(self, src, dest, src_port, dest_port):
        """Add given line to the diagram."""
        line = SL_Line(src, dest, src_port, dest_port)
        src_block = self.blocks[line.src]
        dest_block = self.blocks[line.dest]
        
        src_block.add_src(line.src_port, line)
        dest_block.add_dest(line.dest_port, line)
