from ss2hcsp.sl.SubSystems.subsystem import Triggered_Subsystem
from ss2hcsp.sf.sf_state import AND_State, OR_State


class SF_Chart(Triggered_Subsystem):
    def __init__(self, name, state, data, num_src, num_dest, st):
        super(SF_Chart, self).__init__(name, num_src, num_dest, None)

        self.type = "stateflow"
        self.st = st

        self.input_events = list()  # [(trigger_type, event)]
        self.exec_name = ""

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
        input_events_str = ""
        if self.input_events:
            for trigger_type, event in self.input_events:
                input_events_str += "Input event %s, %s\n" % (trigger_type, event)
        return "Chart(%s):\n%s%s" % (self.name, input_events_str, str(self.diagram))
