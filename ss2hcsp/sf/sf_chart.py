from ss2hcsp.sl.SubSystems.subsystem import Subsystem,Triggered_Subsystem
from ss2hcsp.sf.sf_state import AND_State, OR_State, Junction,GraphicalFunction
from ss2hcsp.sf.sf_message import SF_Message
from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.expr import AVar,AConst, BExpr, conj,disj,LogicExpr,RelExpr,FunExpr
from ss2hcsp.hcsp.parser import bexpr_parser, hp_parser
from ss2hcsp.hcsp.hcsp import Condition , Assign
from ss2hcsp.matlab import function
from ss2hcsp.hcsp.parser import aexpr_parser
import re


def get_common_ancestor(state0, state1, tran_type="out_trans"):
    assert tran_type in ["out_trans", "inner_trans"]
    if state0 == state1:
        assert state0.father == state1.father
        if tran_type == "out_trans":
            return state0.father
        else:  # inner_trans
            return state0

    state_to_root = []
    cursor = state0
    while cursor:
        state_to_root.append(cursor)
        cursor = cursor.father

    cursor = state1
    while cursor not in state_to_root:
        cursor = cursor.father
    return cursor


class SF_Chart(Subsystem):
    def __init__(self, name, state, data, num_src, num_dest, st=0.1,input_message_queue=None,local_message_queue=None,event_list=None, is_triggered_chart=False,trigger_dest=None,trigger_type="",sf_charts=None,max_step=0.2):
        super(SF_Chart, self).__init__(name, num_src, num_dest)

        self.type = "stateflow"
        self.num_src = 10
        self.num_dest = num_dest
        self.src_lines = [[] for _ in range(self.num_src)]  # [[]] * self.num_src
        self.dest_lines = [None] * self.num_dest

        assert isinstance(state, (AND_State,OR_State))
        self.diagram = state
        self.diagram.chart = self

        self.all_states = state.get_all_descendants() # dict
        assert self.diagram.ssid not in self.all_states
        self.all_states[self.diagram.ssid] = self.diagram

        # The dictionary of functions in stateflow,
        # in form of {path (tuple): function (hcsp)}
        self.fun_dict = dict()
        self.mesg_hp = list()
        self.has_event = False  # if the acts in the sf_chart have any broadcast event

        self.data = data
        self.all_vars = sorted(data.keys())

        self.st = 2

        self.port_to_in_var = dict()
        self.port_to_out_var = dict()
        self.triggerport_to_in_var=dict()
        self.triggerport_to_out_var=dict()

        self.dest_state_root_num=-1
        self.dest_state_name=""
        if input_message_queue is None:
            input_message_queue = []
        self.input_message_queue=input_message_queue
        if local_message_queue is None:
            local_message_queue = []
        self.local_message_queue=local_message_queue
        if  event_list is None:
            event_list = []
        self.event_list=event_list
        self.is_triggered_chart=is_triggered_chart
        if  trigger_dest is None:
            trigger_dest = []
        self.trigger_dest=trigger_dest
        self.trigger_type=trigger_type
        if sf_charts is None:
            sf_charts = {}
        self.sf_charts=sf_charts
        self.max_step=max_step
        self.after_funcs_dicts=dict()#{state.ssid:A list of sequential logic contained in the output transition of the state}
        funs_state_name=list()
        children_list=list()
       
        # Gets the full name of the state  
        for state in self.all_states.values():
            if isinstance(state,(AND_State,OR_State)):
                state.whole_name=state.get_state_whole_name()
        self.add_state_fun_after()    

    def add_state_fun_after(self):
        #Parses the first parameter of the timing logic
        for state in self.all_states.values():
            if isinstance(state,(OR_State)):
                if hasattr(state,"func_after") and state.has_aux_var("state_time"+str(state.ssid)) and len(state.func_after)>0:                          
                            for fun in state.func_after:
                                self.after_funcs_dicts[state.ssid]=fun
                            state.func_after=self.parse_after_func(state.func_after,state.ssid)
    def add_state_time(self):
        #Initializes state_time for the state containing sequential logic in the output transition
        add_state_time=list()
        for s in self.all_states.values():
                if isinstance(s,OR_State) and s.has_aux_var("state_time"+str(s.ssid)):
                    add_state_time.append(hp_parser.parse("state_time"+str(s.ssid)+" := "+"state_time"+str(s.ssid)+"+"+str(self.st)))
        return add_state_time

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
                child.chart = self
                for grandchild in child.children:
                    find_root_recursively(grandchild)
        elif self.diagram.name == "S1":
            assert self.diagram.chart == self
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
            for tran in out_trans:
                tran.root = state.father.root if isinstance(state, Junction) else state.root
                src_state = self.all_states[tran.src]
                dst_state = self.all_states[tran.dst]
                tran.location = get_common_ancestor(src_state, dst_state, "out_trans")
            inner_trans = list(state.inner_trans) if hasattr(state, "inner_trans") else list()
            for tran in out_trans + inner_trans:
                tran.root = state.father.root if isinstance(state, Junction) else state.root
                src_state = self.all_states[tran.src]
                dst_state = self.all_states[tran.dst]
                tran.location = get_common_ancestor(src_state, dst_state, "inner_trans")

    def singal_state_parse_acts_on_states_and_trans(self,state):
        if state.is_parse_act == False:
               
                state.is_parse_act=True
                if isinstance( state, (AND_State, OR_State)):
                    if state.en:
                         state.en = parse_act_into_hp(acts= state.en, root= state.root, location= state)
                    if  state.du:
                        state.du = parse_act_into_hp(acts= state.du, root= state.root, location=state)
                    if  state.ex:
                         state.ex = parse_act_into_hp(acts= state.ex, root= state.root, location= state)
                    if hasattr( state, "default_tran") and  state.default_tran:
                        cond_acts =  state.default_tran.cond_acts
                        tran_acts =  state.default_tran.tran_acts
                        root =  state.default_tran.root
                        location =  state.default_tran.location
                        state.default_tran.cond_acts = parse_act_into_hp(cond_acts, root, location)
                        state.default_tran.tran_acts = parse_act_into_hp(tran_acts, root, location)
                    out_trans = list(state.out_trans) if hasattr(state, "out_trans") else list()
                    inner_trans = list(state.inner_trans) if hasattr( state, "inner_trans") else list()
                    for tran in out_trans + inner_trans:
                        tran.cond_acts = parse_act_into_hp(tran.cond_acts, tran.root, self.get_state_by_ssid(tran.src))                  
                        tran.tran_acts = parse_act_into_hp(tran.tran_acts, tran.root, self.get_state_by_ssid(tran.src))
                elif isinstance( state, Junction):
                    if hasattr( state, "default_tran") and  self.all_states[state.ssid].default_tran:
                        cond_acts =  state.default_tran.cond_acts
                        tran_acts =  state.default_tran.tran_acts
                        root =  state.default_tran.root
                        location =  state.default_tran.location
                        state.default_tran.cond_acts = parse_act_into_hp(cond_acts, root, location)
                        state.default_tran.tran_acts = parse_act_into_hp(tran_acts, root, location)
                    for tran in  state.out_trans:
                        tran.cond_acts = parse_act_into_hp(tran.cond_acts, tran.root, tran.location)
                        tran.tran_acts = parse_act_into_hp(tran.tran_acts, tran.root, tran.location)
                else:
                    print( state, type( state))
                    raise RuntimeError("Error State!")
    def parse_after_func(self,lists,ssid):
        #Parse whether the first parameter in sequential logic is a function. 
        #If it is a function, parse it. If it is not a function, do not parse it
        hp_fun_onCon=list()
        for right in lists:
            if isinstance(right,(function.FunctionCall,function.Var,FunExpr,AVar)): 
                longest_path=self.get_fun_by_path(str(right))
                if isinstance(right,(function.FunctionCall)):
                    right_name=str(right.func_name)
                elif isinstance(right,FunExpr):
                    right_name=str(right.fun_name)
                else:
                    right_name=str(right)
                
                if longest_path is None:
                    
                    if isinstance(right,(function.FunctionCall,FunExpr)):
                        if isinstance(right,function.FunctionCall):
                            exprs=right.args
                        else:
                            exprs=right.exprs
                        right_exprs=[str(expr) for expr in exprs]
                    else:
                        right_exprs=list()
                    if len(right_exprs) == 1:
                        if right_exprs[0].isdigit():
                                right_exprs[0]=int(right_exprs[0])-1
                        else:
                                right_exprs[0]=right_exprs[0]+"-1"
                        right=right_name+"["+str(right_exprs[0])+"]"+str(right)[str(right).index(")")+1:]
                    elif len(right_exprs) > 1:
                        right_temp = right_name
                        for expr in right_exprs:
                            if expr.isdigit():
                                expr=int(expr)-1
                            else:
                                expr=expr+"-1"                                  
                            right_temp = right_temp + "["+str(expr)+"]"
                        right=right_temp+str(right)[str(right).index(")")+1:]
                    else:
                        right=right_name
                else:
                    if isinstance(right,(function.FunctionCall,FunExpr)):
                        if isinstance(right,function.FunctionCall):
                            exprs=right.args
                        else:
                            exprs=right.exprs
                        right_exprs=[str(expr) for expr in exprs]
                    else:
                        right_exprs=list()
                    exprs=longest_path[1]
                    if exprs is not None and len(right_exprs) > 0:
                        for  var in range(0,len(exprs)):
                            hp_fun_onCon.append(hp_parser.parse(str(exprs[var])+":="+str(right_exprs[var])))
                    return_var=longest_path[0]
                    if return_var is not None:
                        if isinstance(return_var,function.ListExpr):
                            hp_fun_onCon.append(hp_parser.parse(str(return_var[0])+":= 0"))

                            
                        else:
                            hp_fun_onCon.append(hp_parser.parse(str(return_var)+":= 0"))
                           
                    hp_fun_onCon.append(self.fun_dict[longest_path])   

                    if return_var is not None:
                        if isinstance(return_var,function.ListExpr):
                            hp_fun_onCon.append(hp_parser.parse(str(right_name+"_"+str(return_var[0])+str(ssid)+":="+str(return_var[0]))))
                            right=str(right_name+"_"+str(return_var[0]))
                            
                        else:
                            hp_fun_onCon.append(hp_parser.parse(str(right_name+"_"+str(return_var)+str(ssid)+":="+str(return_var))))
                            right=str(right_name+"_"+str(return_var))
        return hp_fun_onCon
    def parse_acts_on_states_and_trans(self):
        for state in self.all_states.values():
            if state.is_parse_act == False:
                state.is_parse_act=True
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
                        tran.cond_acts = parse_act_into_hp(tran.cond_acts, tran.root, self.get_state_by_ssid(tran.src))                  
                        tran.tran_acts = parse_act_into_hp(tran.tran_acts, tran.root, self.get_state_by_ssid(tran.src))
                elif isinstance(state, Junction):
                    if hasattr(state, "default_tran") and state.default_tran:
                        cond_acts = state.default_tran.cond_acts
                        tran_acts = state.default_tran.tran_acts
                        root = state.default_tran.root
                        location = state.default_tran.location
                        state.default_tran.cond_acts = parse_act_into_hp(cond_acts, root, location)
                        state.default_tran.tran_acts = parse_act_into_hp(tran_acts, root, location)
                    for tran in state.out_trans:
                        tran.cond_acts = parse_act_into_hp(tran.cond_acts, tran.root, tran.location)
                        tran.tran_acts = parse_act_into_hp(tran.tran_acts, tran.root, tran.location)
                else:
                    print(state, type(state))
                    raise RuntimeError("Error State!")

    def get_state_by_whole_name(self, name):
        for state in self.all_states.values():
            if state.whole_name == name:
                return state
    def get_state_by_name(self, name):
        for state in self.all_states.values():
            if state.name == name:
                return state
    def get_state_by_ssid(self, ssid):
        for state in self.all_states.values():
            if state.ssid == ssid:
                return state
    def get_fun_by_path(self, fun_path):       
        assert isinstance(fun_path, str)
        if "(" in fun_path:
            fun_path1=fun_path
            fun_path = tuple(fun_path[:fun_path.index("(")].split("."))
        else:
            fun_path = tuple(fun_path[:].split("."))
        matched_paths = []
        for path, fun in self.fun_dict.items():
            return_var=path[0]
            path1=path[2:]
            assert len(fun_path) <= len(path1)
            # assert len(fun_path) <= len(path1) and isinstance(fun, hp.HCSP)
            if path1[-len(fun_path):] == fun_path :
                matched_paths.append(path)
        if matched_paths:
            assert matched_paths
            path_lengths = [len(path) for path in matched_paths]
            assert len(path_lengths) == len(set(path_lengths))
            longest_path = matched_paths[path_lengths.index(max(path_lengths))]
        else:
            longest_path = None
        if longest_path is not None:
            fun_hp=self.fun_dict[longest_path]
            if isinstance(fun_hp,OR_State):
                if not fun_hp.is_parse_act:
                    for f in fun_hp.children:
                        self.singal_state_parse_acts_on_states_and_trans(fun_hp)

                hps=hp.Sequence(hp_parser.parse("done := 0"),get_hcsp(fun_hp.activate(),self),self.execute_one_step_from_state(fun_hp))
                self.fun_dict[longest_path]=hps
        return longest_path     
