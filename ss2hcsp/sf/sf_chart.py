from ss2hcsp.sf.sf_state import AND_State, OR_State, Junction
from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.expr import AConst, AVar, RelExpr, FunExpr, PlusExpr, BExpr, conj
from ss2hcsp.hcsp.parser import bexpr_parser, hp_parser


def get_common_ancestor(state0, state1):
    if state0 == state1:
        return state0.father

    state_to_root = []
    cursor = state0
    while cursor:
        state_to_root.append(cursor)
        cursor = cursor.father

    cursor = state1
    while cursor not in state_to_root:
        cursor = cursor.father
    return cursor


def get_hps(hps):  # get the process from a list of hps
    assert isinstance(hps, list)
    if not hps:
        return hp.Skip()

    _hps = []
    for _hp in hps:
        assert _hp
        if isinstance(_hp, hp.HCSP):
            _hps.append(_hp)
        elif isinstance(_hp, tuple):
            assert len(_hp) == 2
            cond = _hp[0]
            assert isinstance(cond, BExpr)
            _hps.append(hp.Condition(cond=cond, hp=get_hps(_hp[1])))

    if len(_hps) == 1:
        return _hps[0]
    else:
        return hp.Sequence(*_hps)


class SF_Chart:
    def __init__(self, name, state):
        self.name = name
        assert isinstance(state, AND_State)
        self.state = state
        self.all_states = state.get_all_descendants()  # dict
        assert self.state.ssid not in self.all_states
        self.all_states[self.state.ssid] = self.state
        self.add_names()

    def __str__(self):
        return "Chart(%s):\n%s" % (self.name, str(self.state))

    def add_names(self):  # add names to states and junctions
        self.state.name = "S1"
        if self.state.children:
            if isinstance(self.state.children[0], AND_State):
                self.state.name = "S0"
                num = 1
                for child in self.state.children:
                    child.name = "S" + str(num)
                    num += 1

        and_num = or_num = jun_num = 0
        for state in self.all_states.values():
            if not state.name:
                if isinstance(state, AND_State):
                    state.name = "AND" + str(and_num)
                    and_num += 1
                elif isinstance(state, OR_State):
                    state.name = "OR" + str(or_num)
                    or_num += 1
                elif isinstance(state, Junction):
                    state.name = "Jun" + str(jun_num)
                    jun_num += 1
                else:
                    raise RuntimeError("Error State!")

    def get_state_by_name(self, name):
        for state in self.all_states.values():
            if state.name == name:
                return state

    def execute_event(self, state, event_var="E"):
        hps = list()
        if isinstance(state, (OR_State, Junction)):
            for out_tran in state.out_trans:
                event, condition, cond_act, tran_act = out_tran.parse()
                conds = []
                if event:
                    conds.append(bexpr_parser.parse(event_var + " == " + event))
                if condition:
                    conds.append(condition)
                conds.append(bexpr_parser.parse("done == 0"))
                cond = conj(*conds) if len(conds) >= 2 else conds[0]
                cond_act = [cond_act] if cond_act else []  # delete None
                tran_act = [tran_act] if tran_act else []  # delete None

                dst_state = self.all_states[out_tran.dst]
                assert not isinstance(dst_state, AND_State)
                dst_state.tran_acts = state.tran_acts + tran_act
                common_ancestor = get_common_ancestor(state, dst_state)
                assert common_ancestor == get_common_ancestor(dst_state, state)
                descendant_exit = state.all_descendant_exit() if isinstance(state, OR_State) else []
                exit_to_ancestor = state.exit_to(ancestor=common_ancestor)
                enter_into_dst = common_ancestor.enter_into(descendant=dst_state)

                processes = list()
                if isinstance(dst_state, OR_State):
                    processes = cond_act + descendant_exit + exit_to_ancestor + dst_state.tran_acts + enter_into_dst \
                                + [hp_parser.parse("done := 1")]
                elif isinstance(dst_state, Junction):
                    if not dst_state.visited:  # hasn't been visited before
                        dst_state.visited = True
                        assert dst_state.process is None
                        dst_state.process = descendant_exit + exit_to_ancestor + enter_into_dst \
                                            + self.execute_event(state=dst_state, event_var=event_var)
                        processes = cond_act + dst_state.process
                        dst_state.process = get_hps(dst_state.process)
                    else:  # visited before
                        processes = cond_act + descendant_exit + exit_to_ancestor + dst_state.tran_acts \
                                    + enter_into_dst + [hp.HCSP(name=dst_state.name)]
                if cond:
                    hps.append((cond, processes))
                else:
                    hps.extend(processes)
        # else:  # isinstance(state, AND_State)
        #     if state.du:
        #         hps.append(state.du)
        #     for child in state.children:
        #         if isinstance(child, AND_State):
        #             hps.extend(self.execute_event(state=child, event_var=event_var))
        #         elif isinstance(child, OR_State):
        #             # activated = "a_" + child.ssid + "==1"
        #             activated = child.activated()
        #             hps.append((activated, self.execute_event(state=child, event_var=event_var)))
        return hps

    def get_monitor_process(self):
        # Get the number of AND_states
        assert len(self.state.children) >= 1
        state_num = len(self.state.children) if isinstance(self.state.children[0], AND_State) else 1

        # Get M process
        hp_M = hp.Sequence(hp.Assign(var_name="num", expr=AConst(0)), hp.Loop(hp.HCSP(name="M_main")))
        hp_M.name = "M"

        # Get M_main process
        hp_M_main = hp.Condition(cond=RelExpr(op="==", expr1=AVar("num"), expr2=AConst(0)),
                                 hp=hp.Sequence(hp.InputChannel(ch_name="tri", var_name=AVar("E")),
                                                hp.Assign(var_name="EL", expr=AVar("[]")),
                                                hp.Assign(var_name="NL", expr=AVar("[]")),
                                                hp.Assign(var_name="EL", expr=FunExpr(fun_name="push",
                                                                                      exprs=[AVar("EL"), AVar("E")])),
                                                hp.Assign(var_name="NL", expr=FunExpr(fun_name="push",
                                                                                      exprs=[AVar("NL"), AConst(1)])),
                                                hp.Assign(var_name="num", expr=AConst(1))))
        for num in range(1, state_num + 1):
            hp_M_main = hp.Sequence(hp_M_main,
                                    hp.Condition(cond=RelExpr(op="==", expr1=AVar("num"), expr2=AConst(num)),
                                                 hp=hp.SelectComm(hp.OutputChannel(ch_name="BC" + str(num),
                                                                                   expr=AVar("E")),
                                                                  hp.Sequence(hp.InputChannel(ch_name="BR" + str(num),
                                                                                              var_name=AVar("E")),
                                                                              hp.Assign(var_name="EL",
                                                                                        expr=FunExpr(fun_name="push",
                                                                                                     exprs=[AVar("EL"), AVar("E")])),
                                                                              hp.Assign(var_name="NL",
                                                                                        expr=FunExpr(fun_name="push",
                                                                                                     exprs=[AVar("NL"), AConst(1)])),
                                                                              hp.Assign(var_name="num", expr=AConst(1))),
                                                                  hp.Sequence(hp.InputChannel(ch_name="BO" + str(num)),
                                                                              hp.Assign(var_name="num",
                                                                                        expr=PlusExpr(signs="++",
                                                                                                      exprs=[AVar("num"), AConst(1)])),
                                                                              hp.Assign(var_name="NL",
                                                                                        expr=FunExpr(fun_name="pop",
                                                                                                     exprs=[AVar("NL")])),
                                                                              hp.Assign(var_name="NL",
                                                                                        expr=FunExpr(fun_name="push",
                                                                                                     exprs=[AVar("NL"), AConst(num)])))
                                                                  )))
        hp_M_main = hp.Sequence(hp_M_main,
                                hp.Condition(cond=RelExpr(op="==", expr1=AVar("num"), expr2=AConst(state_num + 1)),
                                             hp=hp.Sequence(hp.Assign(var_name="EL", expr=FunExpr(fun_name="pop",
                                                                                                  exprs=[AVar("EL")])),
                                                            hp.Assign(var_name="NL", expr=FunExpr(fun_name="pop",
                                                                                                  exprs=[AVar("NL")])),
                                                            hp.Condition(cond=RelExpr(op="==", expr1=AVar("EL"), expr2=AVar("[]")),
                                                                         hp=hp.Assign(var_name="num", expr=AConst(0))),
                                                            hp.Condition(cond=RelExpr(op="!=", expr1=AVar("EL"), expr2=AVar("[]")),
                                                                         hp=hp.Sequence(hp.Assign(var_name="E",
                                                                                                  expr=FunExpr(fun_name="top",
                                                                                                               exprs=[AVar("EL")])),
                                                                                        hp.Assign(var_name="num",
                                                                                                  expr=FunExpr(fun_name="top",
                                                                                                               exprs=[AVar("NL")])))))))
        hp_M_main.name = "M_main"
        return hp_M, hp_M_main, state_num
        # print("M_main = ", hp_M_main)

    def get_process(self, event_var="E"):
        def get_S_du_and_P_diag(_state, _hps):
            _s_du = list()
            _p_diag = list()
            _p_diag_name = "Diag_" + _state.name

            if _state.du:  # add dur
                _s_du.append(_state.du)
            if _state.children:
                _s_du.append(hp.HCSP(name=_p_diag_name))  # P_diag

                if isinstance(_state.children[0], AND_State):
                    _p_diag = [hp.HCSP(name=_child.name) for _child in _state.children]
                else:
                    _p_diag = [hp.Condition(cond=_child.activated(), hp=hp.HCSP(name=_child.name))
                               for _child in _state.children if isinstance(_child, OR_State)]

            if len(_s_du) == 0:
                _s_du = hp.Skip()
            elif len(_s_du) == 1:
                _s_du = _s_du[0]
            else:
                _s_du = hp.Sequence(*_s_du)
            # _s_du = dur; P_diag

            if _hps:  # generated from an OR-state
                init = hp_parser.parse("done := 0")
                _s_du = hp.Condition(cond=bexpr_parser.parse("done == 0"), hp=_s_du)
                # _s_du = \neg done -> (dur; P_diag)

                _s_du = hp.Sequence(init, get_hps(_hps), _s_du)
                # _s_du = done := False; TTN(...); \neg done -> (dur; P_diag)
            return _s_du, _p_diag, _p_diag_name

        # Analyse P_diag recursively
        def analyse_P_diag(_p_diag):
            for proc in _p_diag:
                _state_name = proc.hp.name if isinstance(proc, hp.Condition) else proc.name
                assert _state_name
                _state = self.get_state_by_name(name=_state_name)
                _s_du, new_p_diag, new_p_diag_name = get_S_du_and_P_diag(_state=_state,
                                                                         _hps=self.execute_event(_state))
                _s_du.name = _state_name
                processes.append(_s_du)
                if new_p_diag:
                    new_p_diag_proc = hp.Sequence(*new_p_diag) if len(new_p_diag) >= 2 else new_p_diag[0]
                    assert new_p_diag_name
                    new_p_diag_proc.name = new_p_diag_name
                    processes.append(new_p_diag_proc)
                    analyse_P_diag(new_p_diag)

        hp_M, hp_M_main, state_num = self.get_monitor_process()
        processes = [hp_M, hp_M_main]
        # Get D process (system process)
        process = hp.HCSP(name="M")
        for num in range(state_num):
            process = hp.Parallel(process, hp.HCSP(name="S" + str(num + 1)))
        process.name = "D"
        processes.append(process)

        # Get each S_i process
        parallel_states = self.state.children if self.state.name == "S0" else [self.state]
        assert len(parallel_states) == state_num
        i = 1
        for s_i in parallel_states:  # for each S_i state
            assert s_i.name == "S" + str(i)
            s_du, p_diag, p_diag_name = get_S_du_and_P_diag(_state=s_i, _hps=self.execute_event(state=s_i))
            assert isinstance(s_du, hp.HCSP) and isinstance(p_diag, list)
            assert p_diag == [] or all(isinstance(s, hp.HCSP) for s in p_diag)

            # S_i = s_i_proc
            s_i_proc = hp.Sequence(get_hps(s_i.activate()),
                                   hp.Loop(hp.Sequence(hp_parser.parse("BC" + str(i) + "?" + event_var),
                                                       s_du,  # S_du
                                                       hp.OutputChannel(ch_name="BO" + str(i)))))
            s_i_proc.name = s_i.name
            processes.append(s_i_proc)

            # P_diag = p_diag_proc
            if p_diag:
                p_diag_proc = hp.Sequence(*p_diag) if len(p_diag) >= 2 else p_diag[0]
                assert p_diag_name
                p_diag_proc.name = p_diag_name
                processes.append(p_diag_proc)
                analyse_P_diag(p_diag)  # analyse P_diag recursively

            i += 1

        assert all((hasattr(process, "name")) for process in processes)
        return processes
