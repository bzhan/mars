from ss2hcsp.sf.sf_state import AND_State, OR_State, Junction
from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.expr import AConst, AVar, RelExpr, FunExpr, PlusExpr


def get_common_ancestor(state0, state1):
    state_to_root = []
    cursor = state0
    while cursor:
        state_to_root.append(cursor)
        cursor = cursor.father

    cursor = state1
    while cursor not in state_to_root:
        cursor = cursor.father
    return cursor


class SF_Chart:
    def __init__(self, name, state):
        self.name = name
        assert isinstance(state, AND_State)
        self.state = state
        self.all_states = state.get_all_descendants()
        assert self.state.ssid not in self.all_states
        self.all_states[self.state.ssid] = self.state
        # print(len(self.all_states))

    def __str__(self):
        return "Chart(%s):\n%s" % (self.name, str(self.state))

    def execute_event(self, state, event_var="E"):
        acts = []
        if isinstance(state, (OR_State, Junction)):
            for out_tran in state.out_trans:
                event, condition, cond_act, tran_act = out_tran.parse()
                cond_hp = event_var + "==" + event + "&&" + condition + "&&done==0"
                dst_state = self.all_states[out_tran.dst]
                dst_state.tran_acts = state.tran_acts + [tran_act]
                assert not isinstance(dst_state, AND_State)
                common_ancestor = get_common_ancestor(state, dst_state)
                assert common_ancestor == get_common_ancestor(dst_state, state)
                descendant_exit = state.all_descendant_exit() if isinstance(state, OR_State) else []
                exit_to_ancestor = state.exit_to(ancestor=common_ancestor)
                enter_into_dst = common_ancestor.enter_into(descendant=dst_state)

                if isinstance(dst_state, OR_State):
                    acts.append((cond_hp, [cond_act] + descendant_exit + exit_to_ancestor + dst_state.tran_acts
                                 + enter_into_dst + ["done := 1"]))
                elif isinstance(dst_state, Junction):
                    if not dst_state.visited:  # hasn't been visited before
                        dst_state.visited = True
                        acts.append((cond_hp, [cond_act] + descendant_exit + exit_to_ancestor + enter_into_dst
                                     + self.execute_event(state=dst_state, event_var=event_var)))
                    else:  # visited before
                        acts.append((cond_hp, [cond_act] + descendant_exit + exit_to_ancestor + dst_state.tran_acts
                                     + enter_into_dst + [dst_state.name]))
                    # acts.append((cond_hp, [cond_act] + descendant_exit + exit_to_ancestor
                    #              + enter_into_dst + dst_state.process))
        else:  # isinstance(state, AND_State)
            acts.append(state.du)
            for child in state.children:
                if isinstance(child, AND_State):
                    acts.extend(self.execute_event(state=child, event_var=event_var))
                elif isinstance(child, OR_State):
                    # activated = "a_" + child.ssid + "==1"
                    activated = child.name
                    acts.append((activated, self.execute_event(state=child, event_var=event_var)))
        return acts

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

    def get_process(self):
        hp_M, hp_M_main, state_num = self.get_monitor_process()

        # Get D process (system process)
        process = hp.HCSP(name="M")
        for num in range(state_num):
            process = hp.Parallel(process, hp.HCSP(name="S" + str(num + 1)))
        process.name = "D"

        return process
