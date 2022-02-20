from decimal import Decimal

from ss2hcsp.sl.sl_block import SL_Block, get_gcd
from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.parser import hp_parser, bexpr_parser
from ss2hcsp.hcsp.expr import conj, true_expr, AVar, AConst, OpExpr, RelExpr


class SignalBuilder(SL_Block):
    """Block for Signal Builder."""
    def __init__(self, name, signal_names=(), time_axises=(), data_axises=(), out_index=()):
        # Both time_axises and data_axises are lists of tuples of values, where
        # each tuple represents one series.
        assert len(time_axises) == len(data_axises) == len(signal_names)
        self.num_series = len(signal_names)
        for i in range(self.num_series):
            assert len(time_axises[i]) == len(data_axises[i])

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
            signal_name = self.signal_names[s_id]
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

    def rename_src_lines(self):
        assert len(self.signal_names) == len(self.src_lines)
        for i in range(len(self.signal_names)):
            for line in self.src_lines[i]:
                line.name = self.signal_names[i]

    def get_hp(self, init_ode=hp.Skip(), ode_hps=()):
        assert isinstance(init_ode, hp.HCSP)
        assert all(isinstance(ode_hp, (hp.ODE, hp.ODE_Comm)) for ode_hp in ode_hps)

        # Merge all time axises into one uniformed time axis
        uniformed_time_axis = []
        for time_axis in self.time_axises:
            for i in range(len(time_axis)-1):
                if time_axis[i] == time_axis[i+1] and time_axis[i] not in uniformed_time_axis:
                    uniformed_time_axis.extend(time_axis[i:i+2])  # Add the times at which values jump
        for time_axis in self.time_axises:
            for time in time_axis:
                if time not in uniformed_time_axis:
                    uniformed_time_axis.append(time)
        uniformed_time_axis.sort()

        # Get the matrix of signals based on the uniformed time axis
        signal_matrix = []
        for i in range(len(self.time_axises)):
            time_axis = self.time_axises[i]
            data_axis = self.data_axises[i]

            signal = []
            local_cursor = 0  # local cursor on time_axis of i-th signal
            cursor = 0  # cursor on uniformed_time_axis
            while cursor < len(uniformed_time_axis):
                assert uniformed_time_axis[cursor] <= time_axis[local_cursor]
                if uniformed_time_axis[cursor] == time_axis[local_cursor]:
                    signal.append(data_axis[local_cursor])
                    local_cursor += 1
                    cursor += 1
                elif uniformed_time_axis[cursor] < time_axis[local_cursor]:
                    assert time_axis[local_cursor-1] <= uniformed_time_axis[cursor]
                    signal.append(
                        (data_axis[local_cursor] - data_axis[local_cursor-1]) /
                        (time_axis[local_cursor] - time_axis[local_cursor-1]) *
                        (uniformed_time_axis[cursor] - time_axis[local_cursor-1])
                        + data_axis[local_cursor - 1]
                    )
                    cursor += 1
            assert local_cursor == len(time_axis)
            signal_matrix.append(signal)

        # Merge uniformed_time_axis and signal_matrix to get a new matrix in the form of
        # [[time, data0, data1, ...], [...], ...]
        signals = [[uniformed_time_axis[i]]+[row[i] for row in signal_matrix] for i in range(len(signal_matrix[0]))]
        # if all(e == 0 for e in signals[0]):
        #     signals = signals[1:]

        # Generate the HCSP process
        assert len(self.signal_names) + 1 == len(signals[0])
        init = "t := " + str(signals[0][0]) + "; " +\
               "".join(signal_name + " := " + str(value) + "; "
                       for signal_name, value in zip(self.signal_names, signals[0][1:]))\
               + "signals := " + str(signals[1:])
        init_hp = hp_parser.parse(init)

        pop_t = "next_t_datas := bottom(signals); signals := get(signals); next_t := bottom(next_t_datas); "
        pop_datas = "next_datas := get(next_t_datas); " + "".join("next_" + signal_name +
                                                                  " := bottom(next_datas); "
                                                                  "next_datas := get(next_datas); "
                                                                  for signal_name in self.signal_names)
        if_time_jump = "t == next_t -> (" +\
                       "".join(signal_name + " := next_" + signal_name + "; " for signal_name in self.signal_names) +\
                       pop_t + pop_datas[:-2] + ");"
        slopes = "".join("slope_" + signal_name + " := (next_" + signal_name + " - " + signal_name +
                         ") / (next_t - t); " for signal_name in self.signal_names)
        body_hp = hp_parser.parse(pop_t + pop_datas + if_time_jump + slopes[:-2])

        # Insert the ode of the Signal Builder into the odes of integrators
        ode = hp_parser.parse("<" + "".join(signal_name + "_dot = slope_" + signal_name + ", "
                                            for signal_name in self.signal_names) + "t_dot = 1 & t < next_t>")

        cond_ode_hps = []
        for ode_hp in ode_hps:
            assert isinstance(ode_hp, (hp.ODE, hp.ODE_Comm))
            if ode_hp.constraint == true_expr:
                cond_ode_hps.append(ode_hp)
            else:
                cond_ode_hps.append(hp.Condition(cond=ode_hp.constraint, hp=ode_hp))
            ode_hp.eqs.extend(ode.eqs)
            ode_hp.constraint = conj(ode_hp.constraint, ode.constraint)
        if not cond_ode_hps:  # ode_hps is empty
            cond_ode_hps = [ode]
        final_ode_hp = cond_ode_hps[0] if len(cond_ode_hps) == 1 else hp.Sequence(*cond_ode_hps)
        if isinstance(final_ode_hp, hp.ODE_Comm):
            final_ode_hp = hp.Loop(hp=final_ode_hp, constraint=final_ode_hp.constraint)

        # The while-loop is the main body of the generated HCSP process
        while_loop = hp.Loop(hp=hp.Sequence(body_hp, final_ode_hp), constraint=bexpr_parser.parse("len(signals) > 0"))
        result_hp = hp.Sequence(init_hp, init_ode, while_loop)

        return result_hp

    '''
    def get_hp_sample(self, st=1, exe_low=0, exe_up=0):
        """
        :param st: it sends signal values periodically (s)
        :param exe_low: the lower bound of execution time (s)
        :param exe_up:  the upper bound of execution time (s)
        :return: an interleaving of channel operations and wait statements
        """

        assert exe_low <= exe_up <= st

        # For precision requirement, amplifying the times
        precision = 1000
        st = round(st * precision)
        exe_low = round(exe_low * precision)
        exe_up = round(exe_up * precision)

        time_commSeq = dict()  # {0: "ch_x!; ch_y!; ...", st: ..., 2st: ..., }
        for i in range(len(self.signal_names)):
            var_name = self.signal_names[i]
            time_axis = [round(time * precision) for time in self.time_axises[i]]  # ms -> s if precision == 1000
            data_axis = self.data_axises[i]
            assert len(time_axis) == len(data_axis)

            j = 0
            while j + 1 < len(time_axis):
                if time_axis[j] == time_axis[j+1]:
                    j += 1
                    continue
                start_t = time_axis[j] if time_axis[j] % st == 0 else time_axis[j] + st - (time_axis[j] % st)
                end_t = time_axis[j+1] - (time_axis[j+1] % st)
                if end_t == time_axis[j+1] and j + 2 < len(time_axis):
                    end_t -= st  # right continuous
                slope = (data_axis[j+1] - data_axis[j]) / (time_axis[j+1] - time_axis[j])
                while start_t <= end_t:
                    data = data_axis[j] + slope * (start_t - time_axis[j])
                    if start_t not in time_commSeq:
                        time_commSeq[start_t] = ""
                    ######
                    if var_name == "laser_error_error":
                        time_commSeq[start_t] += "laser_v_tran!(" + str(data) + " + v); "
                    elif var_name == "laser_error_valid":
                        time_commSeq[start_t] += "laser_valid_tran!" + str(data) + "; "
                    elif var_name == "wheel_error_error":
                        time_commSeq[start_t] += "wheel_v_tran!(" + str(data) + " + v); "
                    elif var_name == "wheel_error_valid":
                        time_commSeq[start_t] += "wheel_valid_tran!" + str(data) + "; "
                    elif var_name == "obstacle_radar_position":
                        time_commSeq[start_t] += "radar_tran!" + str(data) + "; "
                    else:
                        time_commSeq[start_t] += "ch_" + var_name + "!" + str(data) + "; "
                    ######
                    start_t += st
                j += 1
            i += 1

        list_time_hp = sorted((time, commSeq) for time, commSeq in time_commSeq.items())
        # print(list_time_hp)
        assert list_time_hp[0][0] == 0
        result_hp = ""
        for _, commSeq in list_time_hp:
            ######
            result_hp += "ch_veh_v?v; "
            ######
            exe_time = round(random.uniform(exe_low, exe_up), 4)
            if exe_time > 0:
                result_hp += "wait(" + str(exe_time / precision) + "); "
            result_hp += commSeq + "wait(" + str((st-exe_time) / precision) + "); "

        return hp_parser.parse(result_hp[:-2])
    '''
