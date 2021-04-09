from ss2hcsp.sl.sl_block import SL_Block
from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.expr import AVar, AConst
from math import gcd


def lcm(x, y):
    assert isinstance(x, int) and x > 0 and isinstance(y, int) and y > 0
    return x * y // gcd(x, y)


class Discrete_Buffer(SL_Block):
    num = 0

    def __init__(self, in_st, out_st, name=None):
        super(Discrete_Buffer, self).__init__()
        self.type = "discrete_buffer"
        if not name:
            self.name = "buffer" + str(Discrete_Buffer.num)
            Discrete_Buffer.num += 1
        assert isinstance(in_st, int) and in_st > 0
        self.in_st = in_st
        assert isinstance(out_st, int) and out_st > 0
        self.out_st = out_st

        self.num_src = 1
        self.num_dest = 1

        self.src_lines = [[]]
        self.dest_lines = [None]

    def __str__(self):
        return "%s: Discrete_Buffer[in = %s, out = %s, in_st = %s, out_st = %s]" % \
               (self.name, str(self.dest_lines), str(self.src_lines), str(self.in_st), str(self.out_st))

    def get_hcsp(self):
        assert len(self.dest_lines) == 1
        in_var = self.dest_lines[0].name
        branch = self.dest_lines[0].branch
        in_channel = hp.InputChannel(ch_name="ch_" + in_var + "_" + str(branch), var_name=in_var)

        assert len(self.src_lines) == 1 and len(self.src_lines[0]) == 1
        out_var = self.src_lines[0][0].name
        branch = self.src_lines[0][0].branch
        out_channel = hp.OutputChannel(ch_name="ch_" + out_var + "_" + str(branch), expr=AVar(in_var))

        channel_seq = []
        for i in range(lcm(self.in_st, self.out_st)):
            if i % self.in_st == 0 and i % self.out_st == 0:
                channel_seq.append(hp.Sequence(in_channel, out_channel))
            elif i % self.in_st == 0:
                channel_seq.append(in_channel)
            elif i % self.out_st == 0:
                channel_seq.append(out_channel)
            else:
                channel_seq.append(None)

        # Add delays into channel_seq
        channel_delay_seq = []
        for e in channel_seq:
            if isinstance(e, hp.HCSP):
                channel_delay_seq.append(e)
            channel_delay_seq.append("delay")

        hcsp_queue = []
        i = 0
        while i < len(channel_delay_seq):
            if isinstance(channel_delay_seq[i], hp.HCSP):
                hcsp_queue.append(channel_delay_seq[i])
                i += 1
            else:  # channel_delay_seq[i] == "delay"
                delay = 0
                while i < len(channel_delay_seq) and not isinstance(channel_delay_seq[i], hp.HCSP):
                    assert channel_delay_seq[i] == "delay"
                    delay += 1
                    i += 1
                hcsp_queue.append(hp.Wait(AConst(delay)))

        return hp.Loop(hp.Sequence(*hcsp_queue))
