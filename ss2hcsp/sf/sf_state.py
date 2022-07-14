from ss2hcsp.hcsp.parser import expr_parser, hp_parser
from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.expr import RelExpr,LogicExpr,FunExpr
import re


class SF_State:
    """Represents a state in a Stateflow diagram.

    Each state has an ID and a name.

    Each state records events (represented by its name) that
    happens when:

    - entry: when first entering the state.
    - during: when none of the outgoing edges can be executed.
    - exit: when exiting the state.

    """
    def __init__(self, ssid, inner_trans=(), name="", en=None, du=None, ex=None):
        self.ssid = ssid  # ID of the state
        self.name = name  # Name of the state
        self.en = en  # entry event
        self.du = du  # during event
        self.ex = ex  # exit event
        self.father = None  # parent state
        self.children = list()  # list of children states
        self.chart = None  # The chart containing this state
        self.whole_name=""

        # Inner transitions of this state
        assert isinstance(inner_trans, (list, tuple))
        self.inner_trans = inner_trans

    def get_state_whole_name(self):
        if isinstance(self, (OR_State, AND_State)):
            s = self.name
            if self.father is None:
                return self.name
            else:
                child_s = self.father.get_state_whole_name()
                s = child_s + "_" + s
            return s

    def __eq__(self, other):
        return self.ssid == other.ssid

    def __str__(self):
        # Header: ID and name
        if isinstance(self, OR_State):
            result = "OR"
        elif isinstance(self, AND_State):
            result = "AND"
        result += "{id=" + self.ssid + ", name=" + self.name + "}\n"

        # Display the default transition
        if isinstance(self, OR_State) and self.default_tran:
            result += "  Default: " + str(self.default_tran) + "\n"

        # Display the history junction
        if isinstance(self, OR_State) and self.has_history_junc:
            result += "  History: " + str(self.has_history_junc) + "\n"

        # Events
        if self.en:
            result += "  en: " + str(self.en) + "\n"
        if self.du:
            result += "  du: " + str(self.du) + "\n"
        if self.ex:
            result += "  ex: " + str(self.ex) + "\n"

        # Display output transitions
        if isinstance(self, OR_State) and self.out_trans:
            result += "  Out-Transitions:\n"
            for tran in self.out_trans:
                result += "    " + str(tran) + "\n"

        # Display inner transitions
        if self.inner_trans:
            result += "  IN-transitions:\n"
            for tran in self.inner_trans:
                result += "    " + str(tran) + "\n"

        # Display children
        if self.children:
            result += "  Children:\n"
            for child in self.children:
                child_lines = str(child).splitlines()
                result += "\n".join("    " + line for line in child_lines) + "\n"

        return result

    def get_all_descendants(self):
        """Returns a dictionary containing all descendents of self.
        
        Returns - dict(str, SF_State): mapping from ID to nodes.

        """
        assert isinstance(self, (AND_State, OR_State))
        descendants = dict()
        for child in self.children:
            assert child.ssid not in descendants
            descendants[child.ssid] = child
            if isinstance(child, (AND_State, OR_State)):
                child_descendants = child.get_all_descendants()
                #assert all(ssid not in descendants for ssid in child_descendants.keys())
                descendants.update(child_descendants)
        return descendants

    def get_vars(self):
        """Returns set of variables in the actions of the current state.
        
        This function enters recursively into child states.

        """
        var_set = set()

        # Collect variables in entry, during and exit actions
        en_du_ex_acts = (self.en if self.en else list()) \
                        + (self.du if self.du else list()) \
                        + (self.ex if self.ex else list())
        for act in en_du_ex_acts:
            #assert isinstance(act, hp.HCSP)
            if isinstance(act, (hp.Assign, hp.Sequence)):
                var_set = var_set.union(act.get_vars())

        # All states have inner transitions.
        for tran in self.inner_trans:
            var_set = var_set.union(tran.get_vars())

        # Only OR states have outgoing and default transitions.
        if isinstance(self, OR_State):                           
            for tran in self.out_trans:
                var_set = var_set.union(tran.get_vars())
            if self.default_tran:
                var_set = var_set.union(self.default_tran.get_vars())
        
        # Variables in child states.
        for child in self.children:
            var_set = var_set.union(child.get_vars())

        return var_set

    def check_children(self):
        """Check validity of state.

        Checks:
        - if a state contains AND states, then it should not contain OR states
          or junctions.

        """
        has_AND_state = has_OR_state = has_Junction = False
        for child in self.children:
            if isinstance(child, AND_State):
                has_AND_state = True
            elif isinstance(child, OR_State):
                has_OR_state = True
            elif isinstance(child, Junction):
                has_Junction = True
            else:  # Error State
                return False

        # AND_state cannot be in the same father state with OR_state or Junction
        if has_AND_state and (has_OR_state or has_Junction):
            return False

        # Check child states.
        for child in self.children:
            if isinstance(child, (AND_State, OR_State)) and not child.check_children():
                return False

        return True


class OR_State(SF_State):
    """Represents an OR state."""
    def __init__(self, ssid, out_trans=(), inner_trans=(), name="",
                 en=None, du=None, ex=None, default_tran=None):
        super(OR_State, self).__init__(ssid, inner_trans, name, en, du, ex)
        self.out_trans = out_trans        # outgoing transitions
        self.default_tran = default_tran  # default transition to this state
        self.has_history_junc = False     # history junction to this state


class AND_State(SF_State):
    """Represents an AND state."""
    def __init__(self, ssid, inner_trans=(), name="", en=None, du=None, ex=None, order=0):
        super(AND_State, self).__init__(ssid, inner_trans, name, en, du, ex)
        self.order = order                # order within the parent state 


class Junction:
    """Represents a junction."""
    def __init__(self, ssid, out_trans, name="", junc_type="", default_tran=None):
        self.ssid = ssid
        self.out_trans = out_trans
        self.name = name
        self.whole_name = ""
        self.father = None
        self.visited = False
        self.type = junc_type
        self.processes = list()
        self.tran_acts = list()  # the queue to store transition actions
        self.default_tran = default_tran
        self.is_parse_act = False

    def __str__(self):
        result = "JUN(" + self.ssid + ") " + self.name + "\n"
        for tran in self.out_trans:
            result += "  " + str(tran) + "\n"
        return result

    def get_vars(self):
        var_set = set()
        for tran in self.out_trans:
            var_set = var_set.union(tran.get_vars())
        return var_set


class GraphicalFunction:
    def __init__(self, name, params, return_var, transitions, junctions):
        self.name = name
        self.params = params
        self.return_var = return_var
        self.transitions = transitions
        self.junctions = junctions

        # Obtain default transition
        self.default_tran = None
        for ssid, tran in self.transitions.items():
            if tran.src is None:
                self.default_tran = tran
                break
        assert self.default_tran, "GraphicalFunction: no default transition found"

    def __str__(self):
        res = "GraphicalFunction(%s,%s,%s\n" % (self.name, self.params, self.return_var)
        res += "  Junctions:\n"
        for junc in self.junctions:
            for line in str(junc).split('\n'):
                res += "  " + line + "\n"
        res += "  Default transition:\n"
        res += "    " + str(self.default_tran) + "\n"
        res += ")"
        return res
