from ss2hcsp.sf.sf_state import AND_State, OR_State, Junction
from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.expr import AConst, BExpr, conj
from ss2hcsp.hcsp.parser import bexpr_parser, hp_parser
import re


def get_common_ancestor(state0, state1):
    if state0 == state1:
        assert state0.father == state1.father
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
    for i in range(len(hps)):
        assert hps[i]
        if isinstance(hps[i], hp.HCSP):
            if isinstance(hps[i], hp.OutputChannel) and hps[i].ch_name.startswith("BR"):
                # For example, hps[i].expr.name = E_S1
                state_name = (lambda x: x[x.index("_") + 1:])(hps[i].expr.name)  # S1
                hps[i].expr = (lambda x: AConst('"' + x[:x.index("_")] + '"'))(hps[i].expr.name)  # "e"
                assert hps[i + 1] == hp.Var("X")
                _hps.extend(hps[i:i + 2])
                if len(hps) - 1 >= i + 2:
                    _hps.append(hp.Condition(cond=bexpr_parser.parse("a_" + state_name + " == 1"),
                                             hp=get_hps(hps[i + 2:])))
                break
            else:
                _hps.append(hps[i])
        elif isinstance(hps[i], tuple):
            assert len(hps[i]) == 2
            cond = hps[i][0]
            assert isinstance(cond, BExpr)
            _hps.append(hp.Condition(cond=cond, hp=get_hps(hps[i][1])))

    if len(_hps) == 1:
        return _hps[0]
    else:
        return hp.Sequence(*_hps)


def parse_act_into_hp(acts, root, location):  # parse a list of actions of Simulink into a hcsp list
    assert isinstance(acts, list)
    assert all(isinstance(act, str) for act in acts)
    assert isinstance(root, AND_State) and isinstance(location, (AND_State, OR_State))
    hps = list()
    # acts = action.split(";")
    for act in acts:
        if re.match(pattern="\\w+ *:=.+", string=act):  # an assigment
            hps.append(hp_parser.parse(act))
        elif re.match(pattern="\\w+", string=act):  # an event
            event = act + "_" + location.name
            root_num = re.findall(pattern="\\d+", string=root.name)
            assert len(root_num) == 1
            root_num = root_num[0]
            hps.append(hp_parser.parse("BR" + root_num + "!" + event))
            hps.append(hp.Var("X"))
    return hps


class SF_Chart:
    def __init__(self, name, state):
        self.name = name
        assert isinstance(state, AND_State)
        self.state = state
        self.all_states = state.get_all_descendants()  # dict
        assert self.state.ssid not in self.all_states
        self.all_states[self.state.ssid] = self.state
        self.add_names()
        self.find_root_for_states()
        self.find_root_and_loc_for_trans()
        self.parse_acts_on_states_and_trans()

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

    def find_root_for_states(self):  # get the root of each state in chart
        def find_root_recursively(_state):
            if isinstance(_state, (AND_State, OR_State)) and _state.father:
                _state.root = _state.father.root
                for _child in _state.children:
                    find_root_recursively(_child)

        if self.state.name == "S0":
            for child in self.state.children:
                assert isinstance(child, AND_State)
                child.root = child
                for grandchild in child.children:
                    find_root_recursively(grandchild)
        elif self.state.name == "S1":
            for state in self.all_states.values():
                state.root = self.state
        else:
            raise RuntimeError("add_names() should be executed in advance!")

    def find_root_and_loc_for_trans(self):  # get root and location for each transition in chart
        for state in self.all_states.values():
            if hasattr(state, "default_tran") and state.default_tran:
                state.default_tran.root = state.root
                state.default_tran.location = state.father
            if hasattr(state, "out_trans") and state.out_trans:
                for tran in state.out_trans:
                    tran.root = state.root
                    src_state = self.all_states[tran.src]
                    dst_state = self.all_states[tran.dst]
                    tran.location = get_common_ancestor(src_state, dst_state)

    def parse_acts_on_states_and_trans(self):
        for state in self.all_states.values():
            if isinstance(state, (AND_State, OR_State)):
                if state.en:
                    state.en = parse_act_into_hp(acts=state.en, root=state.root, location=state)
                if state.du:
                    state.du = parse_act_into_hp(acts=state.du, root=state.root, location=state)
                if state.ex:
                    state.ex = parse_act_into_hp(acts=state.ex, root=state.root, location=state)
                if hasattr(state, "default_tran") and state.default_tran:
                    assert not state.default_tran.tran_acts
                    acts = state.default_tran.cond_acts
                    root = state.default_tran.root
                    location = state.default_tran.location
                    state.default_tran.cond_acts = parse_act_into_hp(acts, root, location)
                if hasattr(state, "out_trans") and state.out_trans:
                    for tran in state.out_trans:
                        tran.cond_acts = parse_act_into_hp(tran.cond_acts, tran.root, tran.location)
                        tran.tran_acts = parse_act_into_hp(tran.tran_acts, tran.root, tran.location)

    def get_state_by_name(self, name):
        for state in self.all_states.values():
            if state.name == name:
                return state

    # State transition
    def execute_event(self, state, event_var="E"):
        hps = list()
        if isinstance(state, (OR_State, Junction)):
            for out_tran in state.out_trans:
                # event, condition, cond_act, tran_act = out_tran.parse()
                conds = list()
                if out_tran.event:
                    conds.append(bexpr_parser.parse(event_var + ' == "' + out_tran.event + '"'))
                if out_tran.condition:
                    conds.append(out_tran.condition)
                conds.append(bexpr_parser.parse("done == 0"))
                cond = conj(*conds) if len(conds) >= 2 else conds[0]
                # cond_act = [cond_act] if cond_act else []  # delete None
                # tran_act = [tran_act] if tran_act else []  # delete None

                dst_state = self.all_states[out_tran.dst]
                assert not isinstance(dst_state, AND_State)
                dst_state.tran_acts = state.tran_acts + out_tran.tran_acts
                common_ancestor = get_common_ancestor(state, dst_state)
                assert common_ancestor == get_common_ancestor(dst_state, state)
                descendant_exit = state.all_descendant_exit() if isinstance(state, OR_State) else []
                exit_to_ancestor = state.exit_to(ancestor=common_ancestor)
                enter_into_dst = common_ancestor.enter_into(descendant=dst_state)

                processes = list()
                if isinstance(dst_state, OR_State):
                    processes = out_tran.cond_acts + descendant_exit + exit_to_ancestor + dst_state.tran_acts \
                                + enter_into_dst + [hp_parser.parse("done := 1")]
                elif isinstance(dst_state, Junction):
                    if not dst_state.visited:  # hasn't been visited before
                        dst_state.visited = True
                        assert dst_state.process is None
                        dst_state.process = descendant_exit + exit_to_ancestor + enter_into_dst \
                                            + self.execute_event(state=dst_state, event_var=event_var)
                        processes = out_tran.cond_acts + dst_state.process
                        dst_state.process = get_hps(dst_state.process)
                    else:  # visited before
                        processes = out_tran.cond_acts + descendant_exit + exit_to_ancestor + dst_state.tran_acts \
                                    + enter_into_dst + [hp.Var(dst_state.name)]
                if cond:
                    hps.append((cond, processes))
                else:
                    hps.extend(processes)
        return hps

    def get_monitor_process(self):
        # Get the number of AND_states
        assert len(self.state.children) >= 1
        state_num = len(self.state.children) if isinstance(self.state.children[0], AND_State) else 1

        # Get M process
        hp_M = hp.Sequence(hp.Assign(var_name="num", expr=AConst(0)), hp.Loop(hp.Var("M_main")))

        # Get M_main process
        hp_M_main = hp_parser.parse('num == 0 -> (E := "e"; EL := []; EL := push(EL, E); '
                                    'NL := []; NL := push(NL, 1); num := 1)')
        for i in range(1, state_num + 1):
            i = str(i)
            hp_M_main = hp.Sequence(hp_M_main,
                                    hp_parser.parse("num == " + i + " -> (BC" + i + "!E --> skip $ BR" + i
                                                    + "?E --> EL := push(EL, E); NL := push(NL, 1); num := 1 $ BO" + i
                                                    + "? --> num := num+1; NL := pop(NL); NL := push(NL, 1))"))
        hp_M_main = hp.Sequence(hp_M_main,
                                hp_parser.parse("num == " + str(state_num + 1) +
                                                " -> (EL := pop(EL); NL := pop(NL); EL == [] -> (num := 0);"
                                                " EL != [] -> (E := top(EL); num := top(NL)))"))
        return hp_M, hp_M_main, state_num

    def get_process(self, event_var="E"):
        # List of HCSP processes
        processes = hp.HCSPProcess()

        def get_S_du_and_P_diag(_state, _hps):
            _s_du = list()
            _p_diag = list()
            _p_diag_name = "Diag_" + _state.name

            if _state.du:  # add dur
                _s_du.extend(_state.du)
            if _state.children:
                _s_du.append(hp.Var(_p_diag_name))  # P_diag

                if isinstance(_state.children[0], AND_State):
                    _p_diag = [hp.Var(_child.name) for _child in _state.children]
                else:
                    _p_diag = [hp.Condition(cond=_child.activated(), hp=hp.Var(_child.name))
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
                processes.add(_state_name, _s_du)
                if new_p_diag:
                    new_p_diag_proc = hp.Sequence(*new_p_diag) if len(new_p_diag) >= 2 else new_p_diag[0]
                    assert new_p_diag_name
                    processes.add(new_p_diag_name, new_p_diag_proc)
                    analyse_P_diag(new_p_diag)

        # M and M_main
        hp_M, hp_M_main, state_num = self.get_monitor_process()
        processes.add("M", hp_M)
        processes.add("M_main", hp_M_main)

        # Get D process (system process)
        process = hp.Var("M")
        for num in range(state_num):
            process = hp.Parallel(process, hp.Var("S" + str(num + 1)))
        processes.insert(0, "D", process)

        # Get each S_i process
        parallel_states = self.state.children if self.state.name == "S0" else [self.state]
        assert len(parallel_states) == state_num
        i = 1
        for s_i in parallel_states:  # for each S_i state
            assert s_i.name == "S" + str(i)
            s_du, p_diag, p_diag_name = get_S_du_and_P_diag(_state=s_i, _hps=self.execute_event(state=s_i))
            assert isinstance(s_du, hp.HCSP) and isinstance(p_diag, list)
            assert all(isinstance(s, hp.HCSP) for s in p_diag)

            # Body of process S_i
            s_i_proc = hp.Sequence(hp_parser.parse("BC" + str(i) + "?" + event_var),
                                   s_du,  # S_du
                                   hp.OutputChannel(ch_name="BO" + str(i)))

            # P_diag = p_diag_proc
            if p_diag:
                p_diag_proc = hp.Sequence(*p_diag) if len(p_diag) >= 2 else p_diag[0]
                assert p_diag_name
                processes.add(p_diag_name, p_diag_proc)
                analyse_P_diag(p_diag)  # analyse P_diag recursively

            # Check if there is an X in the processes
            # If so, then there is an event triggered inner the states,
            # which means process S_i is recursive.
            contain_X = False
            for _, process in processes.hps:
                # if hp.Var("X") in hp.decompose(process):
                if process.contain_hp(name="X"):
                    contain_X = True
                    s_i_proc = hp.Sequence(get_hps(s_i.init()), get_hps(s_i.activate()), hp.Recursion(s_i_proc))
                    break
            if not contain_X:
                s_i_proc = hp.Sequence(get_hps(s_i.init()), get_hps(s_i.activate()), hp.Loop(s_i_proc))

            # The output order is after D, M and M_main
            processes.insert(3, s_i.name, s_i_proc)

            i += 1

        return processes
