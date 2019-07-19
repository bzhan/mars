from ss2hcsp.sl.sl_block import SL_Block


class Relation(SL_Block):
    """Relation of two dest lines."""
    def __init__(self, name, relation, *, st=-1):
        self.name = name
        self.type = "relation"
        self.is_continuous = False
        self.num_src = 1
        self.num_dest = 2
        self.src_lines = [[]]
        self.dest_lines = [None] * self.num_dest

        assert relation in ["<", ">", "==", "!=", ">=", "<="]
        self.relation = relation

        assert isinstance(st, (int, float))
        self.st = st

    def __str__(self):
        return "%s: Relation[in = %s, out = %s, st = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), str(self.st))
