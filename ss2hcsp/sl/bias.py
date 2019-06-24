class Bias:
    def __init__(self, name, bias):
        self.name = name
        self.type = "bias"
        self.is_continuous = False
        self.num_src = 1
        self.num_dest = 1
        self.src_lines = [[]]
        self.dest_lines = [None]

        self.bias = bias
