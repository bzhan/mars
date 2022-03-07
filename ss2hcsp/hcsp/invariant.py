
class Invariant:
    """Arithmetic expression."""
    def __init__(self):
        pass

class CutInvariant(Invariant):
    def __init__(self, inv, method, meta=None):
        super(Invariant, self).__init__()
        self.meta = meta
        self.inv = inv
        self.method = method

class GhostIntro(Invariant):
    def __init__(self, var, diff, meta=None):
        super(Invariant, self).__init__()
        self.meta = meta
        self.var = var
        self.diff = diff