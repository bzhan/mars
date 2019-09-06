from ss2hcsp.hcsp.parser import bexpr_parser, hp_parser


class SF_State:
    """Represents a state in a Stateflow diagram.

    Each state has an ID and a name.

    Each state records events (represented by its name) that
    happens when:

    - entry: when first entering the state.
    - during: when none of the outgoing edges can be executed.
    - exit: when exiting the state.

    """
    def __init__(self, ssid, name="", en=None, du=None, ex=None):
        self.ssid = ssid  # ID of the state
        self.name = name  # Name of the state
        self.en = en  # entry event
        self.du = du  # during event
        self.ex = ex  # exit event
        self.father = None  # parent state
        self.children = list()  # list of children states
        self.root = None  # root of the tree of containment relation

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

        # Events
        if self.en:
            result += "  en: [" + str(self.en) + "]\n"
        if self.du:
            result += "  du: [" + str(self.du) + "]\n"
        if self.ex:
            result += "  ex: [" + str(self.ex) + "]\n"

        # Display output transitions
        if isinstance(self, OR_State) and self.out_trans:
            result += "  Transitions:\n"
            for tran in self.out_trans:
                result += "    " + str(tran) + "\n"

        # Display children
        if self.children:
            result += "  Children:\n"
            for child in self.children:
                child_lines = str(child).splitlines()
                result += "\n".join("    " + line for line in child_lines) + "\n"

        return result

    def _activate(self):  # turn on
        return hp_parser.parse("a_" + self.name + " := 1")

    def _exit(self):
        return hp_parser.parse("a_" + self.name + " := 0")

    def activated(self):
        return bexpr_parser.parse("a_" + self.name + " == 1")

    def activate(self):  # return a list of hps
        hps = list()
        # if isinstance(self, OR_State):
        hps.append(self._activate())  # turn on
        if self.en:
            hps.extend(self.en)
        # Activate children
        for child in self.children:
            if isinstance(child, (AND_State, Junction)):
                # hps.append(child._activate())
                hps.extend(child.activate())
            elif isinstance(child, OR_State) and child.default_tran:
                # Activate the state with default transition
                # _, _, cond_act, _ = child.default_tran.parse()
                if child.default_tran.cond_acts:
                    hps.extend(child.default_tran.cond_acts)
                hps.extend(child.activate())
                break
        hps = [_hp for _hp in hps if _hp]  # delete Nones
        return hps

    def all_descendant_exit(self):  # return a list hps
        hps = list()
        for child in self.children[::-1]:  # the AND_state with the lowest priority exits first
            if isinstance(child, AND_State):
                hps.extend(child.all_descendant_exit())
                if child.ex:
                    hps.extend(child.ex)
                hps.append(child._exit())
            elif isinstance(child, OR_State):
                child_exit_hps = child.all_descendant_exit()
                if child.ex:
                    child_exit_hps.extend(child.ex)
                child_exit_hps.append(child._exit())  # turn off
                hps.append((child.activated(), child_exit_hps))
        return hps

    def exit_to(self, ancestor):  # return a list of hps
        assert isinstance(self, OR_State)
        assert isinstance(ancestor, (AND_State, OR_State))
        hps = list()
        if self.ex:
            hps.extend(self.ex)
        hps.append(self._exit())  # turn off
        if self.father != ancestor:
            hps.extend(self.father.exit_to(ancestor))
        return hps

    def enter_into(self, descendant):  # return a list of hps
        assert isinstance(self, (AND_State, OR_State))
        assert isinstance(descendant, (OR_State, Junction))
        # assert self.is_ancestor_of(descendant)
        ancestor_chain = []  # from descendant to self
        cursor = descendant
        while cursor != self:
            ancestor_chain.append(cursor)
            cursor = cursor.father
        ancestor_chain.reverse()  # from self to descendant
        assert ancestor_chain == [] or ancestor_chain[0].father == self and ancestor_chain[-1] == descendant

        hps = []
        for state in ancestor_chain[:-1]:
            assert isinstance(state, OR_State)
            hps.append(self._activate())  # turn on
            if state.en:
                hps.extend(state.en)
        if isinstance(descendant, OR_State):
            hps.extend(descendant.activate())
        return hps

    def get_all_descendants(self):
        assert isinstance(self, (AND_State, OR_State))
        descendants = dict()
        for child in self.children:
            assert child.ssid not in descendants
            descendants[child.ssid] = child
            if isinstance(child, (AND_State, OR_State)):
                child_descendants = child.get_all_descendants()
                assert all(ssid not in descendants for ssid in child_descendants.keys())
                descendants.update(child_descendants)
        return descendants

    def check_children(self):
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

        for child in self.children:
            if isinstance(child, (AND_State, OR_State)) and not child.check_children():
                return False
        return True

    # def is_ancestor_of(self, state):  # return if self is an ancestor of the state
    #     if state.father == self:
    #         return True
    #     if state.father is None:
    #         return False
    #     return self.is_ancestor_of(state.father)


class OR_State(SF_State):
    def __init__(self, ssid, out_trans, name="", en=None, du=None, ex=None, default_tran=None):
        super(OR_State, self).__init__(ssid, name, en, du, ex)
        self.out_trans = out_trans
        self.default_tran = default_tran  # The default transition to this state
        self.tran_acts = []  # the queue to store transition actions


class AND_State(SF_State):
    def __init__(self, ssid, name="", en=None, du=None, ex=None, order=0):
        super(AND_State, self).__init__(ssid, name, en, du, ex)
        self.order = order


class Junction:
    def __init__(self, ssid, out_trans, name=""):
        self.ssid = ssid
        self.out_trans = out_trans
        self.name = name
        self.father = None
        self.visited = False
        self.process = None
        self.tran_acts = []  # the queue to store transition actions

    def __str__(self):
        result = "JUN(" + self.ssid + ") " + self.name + "\n"
        for tran in self.out_trans:
            result += str(tran) + "(" + tran.dst + ")\n"
        return result

    def exit_to(self, ancestor):  # return a list of hps
        assert isinstance(ancestor, (AND_State, OR_State))
        if self.father != ancestor:
            return self.father.exit_to(ancestor)
        return list()
