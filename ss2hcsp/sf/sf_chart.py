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
    def __init__(self, name, state, data, num_src, num_dest, st=0.1,message_list=None,event_list=None, is_triggered_chart=False,trigger_dest=None,trigger_type="",sf_charts=None,max_step=0.2):
        super(SF_Chart, self).__init__(name, num_src, num_dest)

        self.type = "stateflow"
        self.num_src = 10
        self.num_dest = num_dest
        self.src_lines = [[] for _ in range(self.num_src)]  # [[]] * self.num_src
        self.dest_lines = [None] * self.num_dest

        assert isinstance(state, (AND_State, OR_State))
        self.diagram = state
        self.diagram.chart = self

        self.all_states = state.get_all_descendants() # dict
        assert self.diagram.ssid not in self.all_states
        self.all_states[self.diagram.ssid] = self.diagram

        self.data = data
        self.all_vars = sorted(data.keys())

        self.st = 2

        self.port_to_in_var = dict()
        self.port_to_out_var = dict()
        self.triggerport_to_in_var=dict()
        self.triggerport_to_out_var=dict()

        self.dest_state_root_num=-1
        self.dest_state_name=""
        if message_list is None:
            message_list = []
        self.input_message_queue=message_list
        if message_list is None:
            message_list = []
        self.local_message_queue=message_list
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
       
        # Gets the full name of the state  
        for state in self.all_states.values():
            if isinstance(state, (AND_State, OR_State)):
                state.whole_name = state.get_state_whole_name()

    def __str__(self):
        return "Chart(%s):\n%s" % (self.name, str(self.diagram))

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
