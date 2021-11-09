from ss2hcsp.sl.SubSystems.subsystem import Subsystem,Triggered_Subsystem
from ss2hcsp.sf.sf_state import AND_State, OR_State, Junction,GraphicalFunction
from ss2hcsp.sf.sf_message import SF_Message
from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.expr import AVar,AConst, BExpr, conj,disj,LogicExpr,RelExpr,FunExpr
from ss2hcsp.hcsp.parser import bexpr_parser, hp_parser
from ss2hcsp.hcsp.hcsp import Condition , Assign
from ss2hcsp.matlab import function


class SF_Chart(Subsystem):
    def __init__(self, name, state, data, num_src, num_dest):
        super(SF_Chart, self).__init__("stateflow", name, num_src, num_dest, 1)

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

        self.port_to_in_var = dict()
        self.port_to_out_var = dict()

    def __str__(self):
        return "Chart(%s):\n%s" % (self.name, str(self.diagram))
