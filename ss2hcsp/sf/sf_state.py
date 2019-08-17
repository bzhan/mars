from ss2hcsp.hcsp.hcsp import HCSP
from xml.dom.minidom import Element
from ss2hcsp.sl.parse_xml import get_attribute_value, get_children_info
import re
from ss2hcsp.hcsp.parser import hp_parser
from ss2hcsp.sf.sf_transition import Transition
from ss2hcsp.sf.sf_junction import Junction


class SF_State:
    def __init__(self, name="", en=None, du=None, ex=None, activated=False):
        self.name = name
        self.en = en  # entry
        self.du = du  # during
        self.ex = ex  # exit
        self.activated = activated
        self.father = None
        self.children = []

    def __str__(self):
        result = ""
        if hasattr(self, "default_tran") and self.default_tran:
            assert isinstance(self, OR_State)
            # Display the default transition
            result += str(self.default_tran)
        if isinstance(self, OR_State):
            result += "OR"
        elif isinstance(self, AND_State):
            result += "AND"
        result += "(" + self.ssid + ") activated=" + str(self.activated) + "\n"
        if self.en:
            result += "en: [" + self.en + "]\n"
        if self.du:
            result += "du: [" + self.du + "]\n"
        if self.ex:
            result += "ex: [" + self.ex + "]\n"
        # Display output transitions
        if isinstance(self, OR_State):
            for tran in self.out_trans:
                result += str(tran) + "State or Junction(" + tran.dst + ")\n"
        # Display children
        for child in self.children:
            result += "{" + str(child) + "}\n"
        result = "Contains states:" + result + "\n"
        return result

    def add_children(self, states, transitions, junctions):
        for element in states + transitions + junctions:
            assert isinstance(element, Element)

        # Get the list of transition objects
        trans_list = []
        for transition in transitions:
            tran_ssid = transition.getAttribute("SSID")
            tran_label = get_attribute_value(block=transition, attribute="labelString")
            if tran_label is None:
                tran_label = ""
            assert len([child for child in transition.childNodes if child.nodeName == "src"]) == 1
            assert len([child for child in transition.childNodes if child.nodeName == "dst"]) == 1
            src_ssid, dst_ssid = None, None
            for child in transition.childNodes:
                if child.nodeName == "src":
                    src_ssid = get_attribute_value(block=child, attribute="SSID")
                elif child.nodeName == "dst":
                    dst_ssid = get_attribute_value(block=child, attribute="SSID")
            assert dst_ssid
            for tran in trans_list:  # the uniqueness of transitions
                assert not(tran.src == src_ssid and tran.dst == dst_ssid)
            trans_list.append(Transition(ssid=tran_ssid, label=tran_label, src=src_ssid, dst=dst_ssid))
        # The number of default transitions is less than 1
        assert len([tran for tran in trans_list if tran.src is None]) <= 1

        # Get states
        for state in states:
            state_ssid = state.getAttribute("SSID")
            labels = get_attribute_value(block=state, attribute="labelString").split("\n")
            state_name = labels[0]  # the name of the state

            acts = []  # contrains en, du and ex
            act = ""
            for label in labels[:0:-1]:
                act = label + act
                if re.match(pattern="(en)|(du)|(ex)", string=act):
                    acts.append(act)
                    act = ""
            en, du, ex = None, None, None
            for act in acts:
                # hcsp = (lambda x: hp_parser.parse(x[x.index(":") + 1:].strip()))(act)
                state_act = (lambda x: x[x.index(":") + 1:].strip())(act)
                if act.startswith("en"):
                    en = state_act
                elif act.startswith("du"):
                    du = state_act
                elif act.startswith("ex"):
                    ex = state_act
                else:
                    raise RuntimeError("Error in state actions!")

            # Add default transition and output-transitions to the state
            default_tran = None
            out_trans = []
            for tran in trans_list:
                if tran.src is None and tran.dst == state_ssid:
                    default_tran = tran
                elif tran.src == state_ssid:
                    out_trans.append(tran)

            # Create a state object
            state_type = get_attribute_value(block=state, attribute="type")
            if state_type == "AND_STATE":
                assert default_tran is None and out_trans == []
                order = int(get_attribute_value(block=state, attribute="executionOrder"))
                child_state = AND_State(ssid=state_ssid, name=state_name, en=en, du=du, ex=ex, order=order)
            elif state_type == "OR_STATE":
                child_state = OR_State(ssid=state_ssid, out_trans=out_trans, name=state_name, en=en, du=du, ex=ex,
                                       default_tran=default_tran)
            else:
                raise RuntimeError("ErrorStates")

            # Add grandchildren to the current child state
            sub_states, sub_transitions, sub_junctions = get_children_info(block=state)
            child_state.add_children(states=sub_states, transitions=sub_transitions, junctions=sub_junctions)
            child_state.father = self
            self.children.append(child_state)

        # Get junctions
        for junction in junctions:
            junc_ssid = junction.getAttribute("SSID")
            out_trans = []
            for tran in trans_list:
                if tran.src == junc_ssid:
                    out_trans.append(tran)
            self.children.append(Junction(ssid=junc_ssid, out_trans=out_trans))

        # Check
        has_AND_state = has_OR_state = has_JUN = False
        for child in self.children:
            if isinstance(child, AND_State):
                has_AND_state = True
            elif isinstance(child, OR_State):
                has_OR_state = True
            elif isinstance(child, Junction):
                has_JUN = True
            else:
                raise RuntimeError("ErrorState")
            # AND-states cannot be in the same father state with OR-states or Junctions
            assert not(has_AND_state and (has_OR_state or has_JUN))

    def activate(self):
        acts = []  # acts generated by activation
        assert not self.activated
        self.activated = True
        if self.en:  # entry action
            acts.append(self.en)
        # Activate children
        for child in self.children:
            if isinstance(child, (AND_State, Junction)):
                acts.extend(child.activate())
            elif isinstance(child, OR_State) and child.default_tran:
                # Activate the state with default transition
                acts.append(child.default_tran.label)  # execute the default transition
                acts.extend(child.activate())
                break
        return acts

    def exit(self):
        assert self.activated
        self.activated = False
        return self.ex


class OR_State(SF_State):
    def __init__(self, ssid, out_trans, name="", en=None, du=None, ex=None, default_tran=None, activated=False):
        super(OR_State, self).__init__(name, en, du, ex, activated)
        self.ssid = ssid
        self.out_trans = out_trans
        self.default_tran = default_tran  # The default transition to this state

    def execute(self, event):
        pass


class AND_State(SF_State):
    def __init__(self, ssid, name="", en=None, du=None, ex=None, order=0, activated=False):
        super(AND_State, self).__init__(name, en, du, ex, activated)
        self.ssid = ssid
        self.order = order

    def execute(self, event):
        pass
