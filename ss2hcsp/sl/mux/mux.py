from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.expr import AVar, FunExpr, ListExpr

class Mux(SL_Block):
    """docstring for Mux"""
    def __init__(self, name, inputs, ports):
        super(Mux, self).__init__(name=name, num_dest=int(inputs), num_src=1, st=-1, type="mux")
        self.inputs = inputs
        self.signal_names = list()
        self.ports = ports

    def __str__(self):
        in_vars = [line.name for line in self.dest_lines]
        out_var = self.src_lines[0][0].name
        return "%s: %s = %s" % (self.name, out_var, '[' + ', '.join(in_vars) + ']')

    def __repr__(self):
        return str(self)

    def get_expr(self):
        """Compute the assignment corresponding to a mux block."""
        in_vars = [line.name for line in self.dest_lines]
        e = ListExpr(*(AVar(var) for var in in_vars))
        return e

    def get_output_hp(self):
        out_var = self.src_lines[0][0].name
        # Use a different way for discrete assignments
        in_vars = [line.name for line in self.dest_lines]
        e = AVar(in_vars[0])
        for i in range(1, len(in_vars)):
            e = FunExpr("push", [e, AVar(in_vars[i])])
        return hp.Assign(out_var, e)

    def get_var_subst(self):
        expr = self.get_expr()
        out_var = self.src_lines[0][0].name
        return {out_var: expr}
