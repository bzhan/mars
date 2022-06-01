from ss2hcsp.hcsp import expr

class Invariant:
    """Arithmetic expression."""
    def __init__(self):
        pass

class LoopInvariant(Invariant):
    """Represents an invariant of a loop program.
    inv : BExpr - invariant
    proof_methods: tuple - methods used for proof. 
                           For example, ('z3', (1.1, 'wolfram_engine'))

    """
    def __init__(self, inv, proof_methods = tuple(), meta=None):
        super(Invariant, self).__init__()
        assert isinstance(inv, expr.BExpr)
        assert isinstance(proof_methods, tuple)
        for proof_method in proof_methods:
            assert isinstance(proof_method, (str, tuple))
        self.meta = meta
        self.inv = inv
        self.proof_methods = proof_methods

class CutInvariant(Invariant):
    def __init__(self, inv, rule = None, rule_arg=None, meta=None):
        super(Invariant, self).__init__()
        self.meta = meta
        self.inv = inv
        self.rule = rule
        self.rule_arg = rule_arg

class GhostIntro(Invariant):
    def __init__(self, var, diff, meta=None):
        super(Invariant, self).__init__()
        self.meta = meta
        self.var = var
        self.diff = diff
        