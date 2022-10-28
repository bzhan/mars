from decimal import Decimal

from ss2hcsp.sl.sl_block import SL_Block, get_gcd
from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.expr import conj, AVar, AConst, OpExpr, RelExpr


class SignalBuilder(SL_Block):
    """Block for Signal Builder."""
    def __init__(self, name, signal_names=(), time_axises=(), data_axises=(), out_index=()):
        # Both time_axises and data_axises are lists of tuples of values, where
        # each tuple represents one series.
        assert len(time_axises) == len(data_axises) == len(signal_names)
        self.num_series = len(signal_names)
        for i in range(self.num_series):
            assert len(time_axises[i]) == len(data_axises[i])
            assert all(isinstance(v, Decimal) for v in time_axises[i])

        self.signal_names = [name.replace(' ', '_') for name in signal_names]
        self.time_axises = time_axises
        self.data_axises = data_axises
        self.out_indexs = out_index

        # Now compute the sample time
        st = get_gcd([t for t in self.time_axises[0] if t > 0])
        for axes in self.time_axises[1:]:
            st = get_gcd([st, *(t for t in axes if t > 0)])
        super(SignalBuilder, self).__init__("signalBuilder", name, len(signal_names), 0, st)

        # Variable representing tick within the signal builder
        self.tick_var = self.name + "_tick"

    def __str__(self):
        return "%s: SignalBuilder[signals = %s, out = %s]" % (self.name, str(self.signal_names), str(self.src_lines))

    def __repr__(self):
        return str(self)

    def get_init_hp(self):
        return hp.Assign(self.tick_var, AConst(0))

    def get_output_hp(self):
        procs = []
        for s_id in range(self.num_series):
            branches = []
            time_axis = self.time_axises[s_id]
            data_axis = self.data_axises[s_id]
            signal_name = self.src_lines[s_id][0].name
            for i in range(len(time_axis)-1):
                left = int(time_axis[i] / self.st)
                right = int(time_axis[i+1] / self.st)
                if left == right:
                    continue
                cond = conj(RelExpr(">=", AVar(self.tick_var), AConst(left)),
                            RelExpr("<", AVar(self.tick_var), AConst(right)))
                slope = (data_axis[i+1] - data_axis[i]) / (right - left)
                act = hp.Assign(AVar(signal_name),
                    OpExpr("+", OpExpr("*", AConst(slope), OpExpr("-", AVar(self.tick_var), AConst(left))),
                                AConst(data_axis[i])))
                branches.append((cond, act))

            else_act = hp.Assign(AVar(signal_name), AConst(data_axis[-1]))
            procs.append(hp.ITE(branches, else_act))
        procs.append(hp.Assign(self.tick_var, OpExpr("+", AVar(self.tick_var), AConst(1))))
        return hp.seq(procs)
