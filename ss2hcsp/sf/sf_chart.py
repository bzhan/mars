from ss2hcsp.sl.SubSystems.subsystem import Subsystem
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

    # Get VIn
    def vin(_i, _vars): return "; ".join("VIn" + str(_i) + "_" + _var + "!" + _var for _var in _vars)

    hps = list()
    # acts = action.split(";")
    for act in acts:
        # print(re.match(pattern="\\w+", string=act), act)
        if re.match(pattern="^\\w+ *:=.+$", string=act):  # an assigment
            hps.append(hp_parser.parse(act))
        elif re.match(pattern="^\\w+\\(\\w*\\)$", string=act):  # a function
            assert isinstance(root.chart, SF_Chart)
            fun_path = tuple(act[:act.index("(")].split("."))
            for path, fun in root.chart.fun_dict.items():
                assert len(fun_path) <= len(path) and isinstance(fun, hp.HCSP)
                if path[-len(fun_path):] == fun_path:
                    hps.append(fun)
                    break
        elif re.match(pattern="^\\w+$", string=act):  # an event
            assert isinstance(root.chart, SF_Chart)
            root.chart.has_event = True
            event = act + "_" + location.name
            root_num = re.findall(pattern="\\d+", string=root.name)
            assert len(root_num) == 1
            root_num = root_num[0]
            hps.append(hp_parser.parse("BR" + root_num + "!" + event))
            if location.root.chart.all_vars:
                hps.append(hp_parser.parse(vin(root_num, location.root.chart.all_vars)))
            hps.append(hp.Var("X"))
    return hps


class SF_Chart(Subsystem):
    def __init__(self, name, state, all_vars, num_src, num_dest, st=-1):
        super(SF_Chart, self).__init__(name, num_src, num_dest)

        self.type = "stateflow"

        assert isinstance(state, AND_State)
        self.diagram = state
        self.diagram.chart = self

        self.all_states = state.get_all_descendants()  # dict
        assert self.diagram.ssid not in self.all_states
        self.all_states[self.diagram.ssid] = self.diagram

        # The dictionary of functions in stateflow,
        # in form of {path (tuple): function (hcsp)}
        self.fun_dict = state.get_fun_dict()

        self.has_event = False  # if the acts in the sf_chart have any broadcast event

        self.all_vars = all_vars

        self.st = st

        self.port_to_in_var = dict()
        self.port_to_out_var = dict()

        self.add_names()
        self.find_root_for_states()
        self.find_root_and_loc_for_trans()

        self.parse_acts_on_states_and_trans()

    def __str__(self):
        return "Chart(%s):\n%s" % (self.name, str(self.diagram))

    def add_names(self):  # add names to states and junctions
        self.diagram.name = "S1"
        if self.diagram.children:
            if isinstance(self.diagram.children[0], AND_State):
                self.diagram.name = "S0"
                num = 1
                for child in self.diagram.children:
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

        if self.diagram.name == "S0":
            for child in self.diagram.children:
                assert isinstance(child, AND_State)
                child.root = child
                for grandchild in child.children:
                    find_root_recursively(grandchild)
        elif self.diagram.name == "S1":
            for state in self.all_states.values():
                state.root = self.diagram
        else:
            raise RuntimeError("add_names() should be executed in advance!")

    def find_root_and_loc_for_trans(self):  # get root and location for each transition in chart
        for state in self.all_states.values():
            if hasattr(state, "default_tran") and state.default_tran:
                state.default_tran.root = state.root
                state.default_tran.location = state.father
            out_trans = list(state.out_trans) if hasattr(state, "out_trans") else list()
            inner_trans = list(state.inner_trans) if hasattr(state, "inner_trans") else list()
            for tran in out_trans + inner_trans:
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
                    cond_acts = state.default_tran.cond_acts
                    tran_acts = state.default_tran.tran_acts
                    root = state.default_tran.root
                    location = state.default_tran.location
                    state.default_tran.cond_acts = parse_act_into_hp(cond_acts, root, location)
                    state.default_tran.tran_acts = parse_act_into_hp(tran_acts, root, location)
                out_trans = list(state.out_trans) if hasattr(state, "out_trans") else list()
                inner_trans = list(state.inner_trans) if hasattr(state, "inner_trans") else list()
                for tran in out_trans + inner_trans:
                    tran.cond_acts = parse_act_into_hp(tran.cond_acts, tran.root, tran.location)
                    tran.tran_acts = parse_act_into_hp(tran.tran_acts, tran.root, tran.location)

    def get_state_by_name(self, name):
        for state in self.all_states.values():
            if state.name == name:
                return state

    # Execute one step from a state
    def execute_one_step_from_state(self, state):
        def are_instances(objects, classes):
            assert len(objects) == len(classes)
            return all(isinstance(_obj, _class) for _obj, _class in zip(objects, classes))

        # Transfer an object into a Condition one if it is of ITE with len(if_hps) == 1 and else_hp == hp.Skip()
        def to_Condition(obj):
            if isinstance(obj, hp.ITE) and len(obj.if_hps) == 1 and obj.else_hp == hp.Skip():
                return hp.Condition(cond=obj.if_hps[0][0], hp=obj.if_hps[0][1])
            return obj

        # Get the result hcsp of executing outgoing and inner transitions from state
        out_tran_hp = self.execute_trans_from_state(state, tran_type="out_trans")
        assert isinstance(out_tran_hp, (hp.Skip, hp.ITE))
        in_tran_hp = self.execute_trans_from_state(state, tran_type="inner_trans")
        assert isinstance(in_tran_hp, (hp.Skip, hp.ITE))

        # Get during action
        during_hp = get_hps(state.du) if state.du else hp.Skip()

        # Composite out_tran_hp, during_hp and in_tran_hp
        comp = [out_tran_hp, during_hp, in_tran_hp]
        if are_instances(comp, [hp.Skip, hp.Skip, hp.Skip]):
            return hp.Skip()
        if are_instances(comp, [hp.Skip, hp.Skip, hp.ITE]):
            return to_Condition(in_tran_hp)
        if are_instances(comp, [hp.Skip, hp.HCSP, hp.Skip]):
            assert not isinstance(during_hp, hp.Skip)
            return during_hp
        if are_instances(comp, [hp.Skip, hp.HCSP, hp.ITE]):
            assert not isinstance(during_hp, hp.Skip)
            return hp.Sequence(during_hp, to_Condition(in_tran_hp))
        if are_instances(comp, [hp.ITE, hp.Skip, hp.Skip]):
            return to_Condition(out_tran_hp)
        if are_instances(comp, [hp.ITE, hp.Skip, hp.ITE]):
            assert out_tran_hp.else_hp == hp.Skip()
            out_tran_hp.else_hp = to_Condition(in_tran_hp)
            return out_tran_hp
        if are_instances(comp, [hp.ITE, hp.HCSP, hp.Skip]):
            assert not isinstance(during_hp, hp.Skip)
            assert out_tran_hp.else_hp == hp.Skip()
            out_tran_hp.else_hp = during_hp
            return out_tran_hp
        if are_instances(comp, [hp.ITE, hp.HCSP, hp.ITE]):
            assert not isinstance(during_hp, hp.Skip)
            assert out_tran_hp.else_hp == hp.Skip()
            out_tran_hp.else_hp = hp.Sequence(during_hp, to_Condition(in_tran_hp))
            return out_tran_hp

    # Execute transitions from a state
    def execute_trans_from_state(self, state, tran_type="out_trans", event_var="E"):
        assert tran_type in ["out_trans", "inner_trans"]

        # An AND-state has no outgoing transitions
        # A Junction has no inner transitions
        if isinstance(state, AND_State) and tran_type == "out_trans" \
                or isinstance(state, Junction) and tran_type == "inner_trans":
            return hp.Skip()

        if tran_type == "out_trans":
            assert isinstance(state, (OR_State, Junction))
            trans = state.out_trans
        else:  # tran_type == "inner_trans"
            assert isinstance(state, (OR_State, AND_State))
            trans = state.inner_trans
        # state must be the source of each transition in trans
        assert all(state.ssid == tran.src for tran in trans)

        if_hps, else_hp = list(), hp.Skip()
        # if isinstance(state, (OR_State, Junction)):
        for tran in trans:
            conds = list()
            if tran.event:
                conds.append(bexpr_parser.parse(event_var + ' == "' + tran.event + '"'))
            if tran.condition:
                conds.append(tran.condition)
            conds.append(bexpr_parser.parse("done == 0"))
            cond = conj(*conds) if len(conds) >= 2 else conds[0]

            dst_state = self.all_states[tran.dst]
            assert not isinstance(dst_state, AND_State)

            dst_state.tran_acts = state.tran_acts + tran.tran_acts
            common_ancestor = get_common_ancestor(state, dst_state)
            assert common_ancestor == get_common_ancestor(dst_state, state)
            descendant_exit = list() if isinstance(state, Junction) else state.all_descendant_exit()
            exit_to_ancestor = state.exit_to(common_ancestor)
            enter_into_dst = common_ancestor.enter_into(dst_state)

            hps = list()
            if isinstance(dst_state, OR_State):
                hps = tran.cond_acts + descendant_exit + exit_to_ancestor + dst_state.tran_acts + enter_into_dst \
                      + [hp_parser.parse("done := 1")]
            elif isinstance(dst_state, Junction):
                if not dst_state.visited:  # has not been visited before
                    dst_state.visited = True
                    assert dst_state.process is None
                    dst_state.process = self.execute_trans_from_state(dst_state, dst_state.out_trans)
                    assert isinstance(dst_state.process, (hp.Skip, hp.Condition, hp.ITE))
                    hps = tran.cond_acts + descendant_exit + exit_to_ancestor + dst_state.tran_acts \
                          + enter_into_dst + ([] if dst_state.process == hp.Skip() else [dst_state.process])
                else:  # visited before
                    hps = tran.cond_acts + descendant_exit + exit_to_ancestor + dst_state.tran_acts \
                          + enter_into_dst + [hp.Var(dst_state.name)]
            if_hps.append((cond, get_hps(hps)))

        if len(if_hps) >= 1:
            return hp.ITE(if_hps, else_hp)

        assert if_hps == list()
        return hp.Skip()

    def get_monitor_process(self):
        # Get the number of AND_states
        assert len(self.diagram.children) >= 1
        state_num = len(self.diagram.children) if isinstance(self.diagram.children[0], AND_State) else 1

        # Get input channels
        in_channels = []
        # print(self.subsystem)
        for port_id, in_var in self.port_to_in_var.items():
            line = self.dest_lines[port_id]
            ch_name = "ch_" + line.name + "_" + str(line.branch)
            in_channels.append(ch_name + "?" + in_var)

        # Get output channels
        out_channels = []
        for port_id, out_var in self.port_to_out_var.items():
            lines = self.src_lines[port_id]
            for line in lines:
                ch_name = "ch_" + line.name + "_" + str(line.branch)
                out_channels.append(ch_name + "!" + out_var)

        # Variable Initialisation
        init_var = hp_parser.parse("; ".join(var + " := 0" for var in self.all_vars + ["num"]))
        # Initial input and output channels, and delay
        init_ch = hp_parser.parse("; ".join(in_channels + out_channels + ["wait(" + str(self.st) + ")"]))
        # Get M process
        hp_M = hp.Sequence(init_var, init_ch, hp.Loop(hp.Var("M_main")))

        # Get VOut
        def vout(_i, _vars):
            if not _vars:
                return "skip"
            return "; ".join("VOut" + str(_i) + "_" + _var + "!" + _var for _var in _vars)

        # Get VIn
        def vin(_i, _vars):
            if not _vars:
                return "skip"
            return "; ".join("VIn" + str(_i) + "_" + _var + "?" + _var for _var in _vars)

        in_channels = "; ".join(in_channels) + "; " if in_channels else ""
        out_channels = "; ".join(out_channels) + "; " if out_channels else ""

        # Get M_main process
        hp_M_main = hp_parser.parse("num == 0 -> (" + in_channels + 'E := ""; EL := [""]; NL := [1]; num := 1)')
        for i in range(1, state_num + 1):
            i = str(i)
            hp_M_main = hp.Sequence(hp_M_main,
                                    hp_parser.parse("num == " + i + " -> (BC" + i + "!E --> " + vout(i, self.all_vars)
                                                    + " $ BR" + i + "?E -->" + vin(i, self.all_vars) +
                                                    "; EL := push(EL, E); NL := push(NL, 1); num := 1 $ BO" + i
                                                    + "? -->" + vin(i, self.all_vars)
                                                    + "; num := num+1; NL := pop(NL); NL := push(NL, 1))"))
        hp_M_main = hp.Sequence(hp_M_main,
                                hp_parser.parse("num == " + str(state_num + 1) +
                                                " -> (EL := pop(EL); NL := pop(NL); EL == [] -> (num := 0; "
                                                + out_channels + "wait(" + str(self.st)
                                                + ")); EL != [] -> (E := top(EL); num := top(NL)))"))
        return hp_M, hp_M_main, state_num

    def get_process(self, event_var="E"):
        def get_S_du_and_P_diag(_state, _hps):
            _s_du = list()
            _p_diag = list()
            _p_diag_name = "Diag_" + _state.name

            # if _state.du:  # add during action
            #     _s_du.extend(_state.du)
            if isinstance(_state, OR_State) and _state.has_aux_var("state_time"):
                _s_du.append(hp_parser.parse("state_time := state_time+" + str(self.st)))
            if _state.children:
                _s_du.append(hp.Var(_p_diag_name))  # P_diag

                if isinstance(_state.children[0], AND_State):
                    _p_diag = [hp.Var(_child.name) for _child in _state.children]
                else:  # OR_State
                    _p_diag = [(_child.activated(), hp.Var(_child.name))
                               for _child in _state.children if isinstance(_child, OR_State)]

            if len(_s_du) == 0:
                _s_du = hp.Skip()
            elif len(_s_du) == 1:
                _s_du = _s_du[0]
            else:
                _s_du = hp.Sequence(*_s_du)
            # _s_du = dur; P_diag

            # _hps is TTN(...)
            if _hps != hp.Skip():  # generated from an OR-state
                init = hp_parser.parse("done := 0")
                _s_du = hp.Sequence(init, _hps) if _s_du == hp.Skip() \
                    else hp.Sequence(init, _hps, hp.Condition(cond=bexpr_parser.parse("done == 0"), hp=_s_du))
                # _s_du = done := False; TTN(...); \neg done -> (P_diag)
            return _s_du, _p_diag, _p_diag_name

        # Analyse P_diag recursively
        def analyse_P_diag(_p_diag, _processes):
            for proc in _p_diag:
                # _state_name = proc.hp.name if isinstance(proc, hp.Condition) else proc.name
                _state_name = proc.name if isinstance(proc, hp.Var) else proc[1].name
                assert _state_name
                _state = self.get_state_by_name(name=_state_name)
                _s_du, new_p_diag, new_p_diag_name = get_S_du_and_P_diag(_state=_state,
                                                                         _hps=self.execute_one_step_from_state(_state))
                _processes.add(_state_name, _s_du)
                if new_p_diag:
                    if isinstance(new_p_diag[0], hp.Var):
                        assert all(isinstance(e, hp.Var) for e in new_p_diag)
                        new_p_diag_proc = hp.Sequence(*new_p_diag) if len(new_p_diag) >= 2 else new_p_diag[0]
                    else:
                        assert all(isinstance(e, tuple) and len(e) == 2 for e in new_p_diag)
                        new_p_diag_proc = hp.ITE(if_hps=new_p_diag, else_hp=hp.Skip()) if len(new_p_diag) >= 2 \
                            else hp.Condition(cond=new_p_diag[0][0], hp=new_p_diag[0][1])
                    assert new_p_diag_name
                    _processes.add(new_p_diag_name, new_p_diag_proc)
                    analyse_P_diag(new_p_diag, _processes)

        # Get VOut
        def vout(_i, _vars):
            if not _vars:
                return "skip"
            return "; ".join("VOut" + str(_i) + "_" + _var + "?" + _var for _var in _vars)

        # Get VIn
        def vin(_i, _vars):
            if not _vars:
                return "skip"
            return "; ".join("VIn" + str(_i) + "_" + _var + "!" + _var for _var in _vars)

        # If there is no event, return two functions and move to get_pure_process
        if not self.has_event:
            return get_S_du_and_P_diag, analyse_P_diag

        # List of HCSP processes
        processes = hp.HCSPProcess()
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
        parallel_states = self.diagram.children if self.diagram.name == "S0" else [self.diagram]
        assert len(parallel_states) == state_num
        i = 1
        for s_i in parallel_states:  # for each S_i state
            assert s_i.name == "S" + str(i)
            s_du, p_diag, p_diag_name = get_S_du_and_P_diag(_state=s_i,
                                                            _hps=self.execute_one_step_from_state(s_i))
            assert isinstance(s_du, hp.HCSP) and isinstance(p_diag, list)
            assert all(isinstance(s, (hp.Var, tuple)) for s in p_diag)

            # Body of process S_i
            s_i_proc = hp.Sequence(hp_parser.parse("BC" + str(i) + "?" + event_var + "; " + vout(i, self.all_vars)),
                                   s_du,  # S_du
                                   hp_parser.parse("BO" + str(i) + "!; " + vin(i, self.all_vars)))

            # P_diag = p_diag_proc
            if p_diag:
                if isinstance(p_diag[0], hp.Var):
                    assert all(isinstance(e, hp.Var) for e in p_diag)
                    p_diag_proc = hp.Sequence(*p_diag) if len(p_diag) >= 2 else p_diag[0]
                else:
                    assert all(isinstance(e, tuple) and len(e) == 2 for e in p_diag)
                    p_diag_proc = hp.ITE(if_hps=p_diag, else_hp=hp.Skip()) if len(p_diag) >= 2 \
                        else hp.Condition(cond=p_diag[0][0], hp=p_diag[0][1])
                assert p_diag_name
                processes.add(p_diag_name, p_diag_proc)
                analyse_P_diag(p_diag, processes)  # analyse P_diag recursively

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

        new_processes = hp.HCSPProcess()
        substituted = processes.substitute()
        # Only one parallel process
        assert len([process for process in substituted.values() if isinstance(process, hp.Parallel)]) == 1
        for name, process in substituted.items():
            if isinstance(process, hp.Parallel):
                for _hp in process.hps:
                    assert isinstance(_hp, hp.Var)
                    new_processes.add(_hp.name, substituted[_hp.name])
                break

        return new_processes

    def get_pure_process(self):
        assert not self.has_event
        get_S_du_and_P_diag, analyse_P_diag = self.get_process()

        # Initialise variables
        init_vars = [hp_parser.parse(var + " := 0") for var in self.all_vars]
        # Initialise and Activate states
        init_states = []
        activate_states = []
        parallel_states = self.diagram.children if self.diagram.name == "S0" else [self.diagram]
        for s_i in parallel_states:
            init_states.extend(s_i.init())
            activate_states.extend(s_i.activate())
        for sub_hp in init_states + activate_states:
            assert isinstance(sub_hp, (hp.Assign, hp.Sequence))
            if isinstance(sub_hp, hp.Sequence):
                assert all(isinstance(_hp, hp.Assign) for _hp in sub_hp.hps)
        # Null channel operations at the first round
        in_chs = []
        for port_id, in_var in self.port_to_in_var.items():
            line = self.dest_lines[port_id]
            ch_name = "ch_" + line.name + "_" + str(line.branch)
            in_chs.append(hp_parser.parse(ch_name + "?" + in_var))
        out_chs = []
        for port_id, out_var in self.port_to_out_var.items():
            lines = self.src_lines[port_id]
            for line in lines:
                ch_name = "ch_" + line.name + "_" + str(line.branch)
                out_chs.append(hp_parser.parse(ch_name + "!" + out_var))

        # Initialzation of the process
        init_hps = init_vars + init_states + activate_states + in_chs + out_chs
        # Delay one period at the first round
        init_hp = hp.Sequence(*init_hps, hp.Wait(AConst(self.st)))

        processes = hp.HCSPProcess()
        # Get main process
        main_body = [hp.Var(state.name) for state in parallel_states]
        main_processes = in_chs + main_body + out_chs
        main_process = hp.Sequence(init_hp, hp.Loop(hp.Sequence(*main_processes, hp.Wait(AConst(self.st)))))
        processes.add(self.name, main_process)

        # Get each S_i process
        i = 0
        for s_i in parallel_states:  # for each S_i state
            i += 1
            assert s_i.name == "S" + str(i)

            s_du, p_diag, p_diag_name = get_S_du_and_P_diag(_state=s_i,
                                                            _hps=self.execute_one_step_from_state(s_i))
            assert isinstance(s_du, hp.HCSP) and isinstance(p_diag, list)
            assert all(isinstance(s, (hp.Var, tuple)) for s in p_diag)
            processes.add(s_i.name, s_du)

            # P_diag = p_diag_proc
            if p_diag:
                if isinstance(p_diag[0], hp.Var):
                    assert all(isinstance(e, hp.Var) for e in p_diag)
                    p_diag_proc = hp.Sequence(*p_diag) if len(p_diag) >= 2 else p_diag[0]
                else:
                    assert all(isinstance(e, tuple) and len(e) == 2 for e in p_diag)
                    p_diag_proc = hp.ITE(if_hps=p_diag, else_hp=hp.Skip()) if len(p_diag) >= 2 \
                        else hp.Condition(cond=p_diag[0][0], hp=p_diag[0][1])
                assert p_diag_name
                processes.add(p_diag_name, p_diag_proc)
                analyse_P_diag(p_diag, processes)  # analyse P_diag recursively

        substituted = processes.substitute()
        processes.hps = [(self.name, substituted[self.name])]

        return processes
