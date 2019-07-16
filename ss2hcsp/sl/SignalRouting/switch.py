from ss2hcsp.sl.sl_block import SL_Block


class Switch(SL_Block):
    """Switch of two dest lines."""
    def __init__(self, name, relation, threshold, *, st=-1):
        self.name = name
        self.type = "switch"
        self.is_continuous = False
        self.num_src = 1
        self.num_dest = 3
        self.src_lines = [[]]
        self.dest_lines = [None] * self.num_dest

        # Pairs of inverse relations
        relation_pair = {"<": ">=", ">": "<=", "==": "!=", "!=": "==", ">=": "<", "<=": ">"}
        assert relation in relation_pair
        self.relation = relation
        self.neg_relation = relation_pair[relation]

        assert isinstance(threshold, (int, float))
        self.threshold = threshold

        assert isinstance(st, int)
        self.st = st

    def __str__(self):
        return "%s: Switch[in = %s, out = %s, st = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), str(self.st))
