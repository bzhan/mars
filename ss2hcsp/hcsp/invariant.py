from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.label import Label

class Invariant:
    """Arithmetic expression."""
    def __init__(self):
        pass

class LoopInvariant(Invariant):
    """Represents an invariant of a loop program.
    inv : Expr - invariant
    proof_methods: tuple - methods used for proof. 
    """
    def __init__(self, inv, proof_methods = tuple(), meta=None):
        super(Invariant, self).__init__()
        assert isinstance(inv, expr.Expr)
        assert isinstance(proof_methods, tuple)
        for proof_method in proof_methods:
            assert isinstance(proof_method, ProofMethod)
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

class ProofMethod:
    """Represents the label and corresponding proof method.
    For example, label: 1.1
                 method: z3            
    """
    def __init__(self, method, label=None, meta=None):
        self.meta = meta
        # label can be None
        if label:
            assert isinstance(label, Label)
            self.label = label
        assert isinstance(method, str)
        self.method = method
        