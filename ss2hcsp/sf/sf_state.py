from ss2hcsp.hcsp import hcsp as hp
from ss2hcsp.hcsp.parser import bexpr_parser, hp_parser


class SF_State:
    def __init__(self, ssid, name="", en=None, du=None, ex=None):
        self.ssid = ssid
        self.name = name
        self.en = en  # entry
        self.du = du  # during
        self.ex = ex  # exit
        self.father = None
        self.children = []

    def __eq__(self, other):
        return self.ssid == other.ssid

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
        result += "(" + self.ssid + ") " + self.name + "\n"
        if self.en:
            result += "en: [" + str(self.en) + "]\n"
        if self.du:
            result += "du: [" + str(self.du) + "]\n"
        if self.ex:
            result += "ex: [" + str(self.ex) + "]\n"
        # Display output transitions
        if isinstance(self, OR_State):
            for tran in self.out_trans:
                result += str(tran) + "(" + tran.dst + ")\n"
        # Display children
        result += "contains states:\n"
        for child in self.children:
            result += "{" + str(child) + "}\n"
        return result

    def _activate(self):  # turn on
        return hp_parser.parse("a_" + self.name + " := 1")

    def _exit(self):
        return hp_parser.parse("a_" + self.name + " := 0")

    def activated(self):
        return bexpr_parser.parse("a_" + self.name + " == 1")

    def activate(self):  # return a list of hps
        hps = list()
        if isinstance(self, OR_State):
            hps.append(self._activate())  # turn on
        if self.en:
            hps.append(self.en)
        # Activate children
        for child in self.children:
            if isinstance(child, (AND_State, Junction)):
                hps.extend(child.activate())
            elif isinstance(child, OR_State) and child.default_tran:
                # Activate the state with default transition
                _, _, cond_act, _ = child.default_tran.parse()
                if cond_act:
                    hps.append(cond_act)
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
                    hps.append(child.ex)
            elif isinstance(child, OR_State):
                child_exit_hps = child.all_descendant_exit()
                if child.ex:
                    child_exit_hps.append(child.ex)
                child_exit_hps.append(child._exit())  # turn off
                hps.append((child.activated(), child_exit_hps))
        return hps

    def exit_to(self, ancestor):  # return a list of hps
        assert isinstance(self, OR_State)
        assert isinstance(ancestor, (AND_State, OR_State))
        hps = list()
        if self.ex:
            hps.append(self.ex)
        hps.append(self._exit())  # turn off
        if self.father != ancestor:
            hps.extend(self.father.exit_to(ancestor))
        return hps

    def enter_into(self, descendant):  # return a list of hps
        assert isinstance(self, (AND_State, OR_State))
        assert isinstance(descendant, (OR_State, Junction))
        # assert self.is_ancestor_of(descendant)
        # assert self.activated
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
                hps.append(state.en)
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
                for ssid in child_descendants.keys():
                    assert ssid not in descendants
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

    # def activate(self):
    #     # assert not self.actatived
    #     self.actatived = True
    #
    # def exit(self):
    #     # assert self.actatived
    #     self.actatived = False

    def exit_to(self, ancestor):  # return a list of hps
        assert isinstance(ancestor, (AND_State, OR_State))
        if self.father != ancestor:
            return self.father.exit_to(ancestor)
        return list()
