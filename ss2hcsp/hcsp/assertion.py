from ss2hcsp.hcsp.expr import Expr
from ss2hcsp.hcsp.label import Label

class Assertion:
    """Arithmetic expression."""
    def __init__(self):
        pass

class OrdinaryAssertion(Assertion):
    """Represents an assertion with its expression and proof methods.
    expr : Expr - assertion expression
    proof_methods: tuple - methods used for proof. 

    Both loop invariant with proof methods and post condition with proof methods are
    instances of OrdinaryAssertion.
    """
    def __init__(self, expr, proof_methods, meta=None):
        super(OrdinaryAssertion, self).__init__()
        assert isinstance(expr, Expr)
        assert isinstance(proof_methods, ProofMethods)
        self.meta = meta
        self.expr = expr
        self.proof_methods = proof_methods


class CutInvariant(Assertion):
    def __init__(self, expr, proof_methods, rule = None, rule_arg=None, meta=None):
        super(CutInvariant, self).__init__()
        assert isinstance(expr, Expr)
        assert isinstance(proof_methods, ProofMethods)
        if rule:
            assert isinstance(rule, str)
        if rule_arg:
            assert isinstance(rule_arg, Expr)
        self.meta = meta
        self.expr = expr
        self.proof_methods = proof_methods
        self.rule = rule
        self.rule_arg = rule_arg

class GhostIntro(Assertion):
    def __init__(self, var, diff, meta=None):
        super(GhostIntro, self).__init__()
        assert isinstance(diff, Expr)
        self.meta = meta
        self.var = str(var)
        self.diff = diff


class ProofMethod():
    """Represents the label and corresponding proof method.
    For example, label: 1.1
                 method: z3            
    """
    def __init__(self, method, label=None, meta=None):
        self.meta = meta
        # label can be None
        if label:
            assert isinstance(label, Label)
        assert isinstance(method, str)
        self.label = label
        self.method = method

    def __str__(self):
        if self.label:
            return str(self.label) + ': ' + self.method
        else:
            return self.method

class ProofMethods():

    def __init__(self, *pms, meta=None):
       
        assert all(isinstance(pm, ProofMethod) for pm in pms)

        self.pms = tuple(pms)
        self.meta = meta