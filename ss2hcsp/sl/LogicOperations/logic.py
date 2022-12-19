from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp.expr import AVar, AConst, OpExpr, FunExpr, true_expr


class Logic(SL_Block):
    def __init__(self, name, num_dest, st=-1):
        super(Logic, self).__init__()
        self.name = name
        self.type = "logic"
        self.is_continuous = (st == 0)
        self.num_src = 1
        self.num_dest = num_dest
        self.src_lines = [[]]
        self.dest_lines = [None] * self.num_dest

        assert isinstance(st, (int, float))
        self.st = st


class And(Logic):
    def __init__(self, name, num_dest, st=-1):
        super(And, self).__init__(name, num_dest, st)
        self.type = "and"

    def __str__(self):
        return "%s: And[in = %s, out = %s, st = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), str(self.st))

    def __repr__(self):
        return str(self)


class Or(Logic):
    def __init__(self, name, num_dest, st=-1):
        super(Or, self).__init__(name, num_dest, st)
        self.type = "or"

    def __str__(self):
        return "%s: Or[in = %s, out = %s, st = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), str(self.st))

    def __repr__(self):
        return str(self)


class Not(Logic):
    def __init__(self, name, num_dest=1, st=-1):
        assert num_dest == 1
        super(Not, self).__init__(name, num_dest, st)
        self.type = "not"

    def __str__(self):
        return "%s: Not[in = %s, out = %s, st = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), str(self.st))

    def __repr__(self):
        return str(self)
