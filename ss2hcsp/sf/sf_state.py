from ss2hcsp.hcsp.parser import bexpr_parser, hp_parser
from ss2hcsp.hcsp import hcsp as hp
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
    def __init__(self, ssid, inner_trans=(), name="",original_name="", en=None, du=None, ex=None):
        self.ssid = ssid  # ID of the state
        self.name = name  # Name of the state
        self.original_name=original_name
        self.en = en  # entry event
        self.du = du  # during event
        self.ex = ex  # exit event
        self.father = None  # parent state
        self.children = list()  # list of children states
        self.root = None  # root of the tree of containment relation
        self.chart = None  # The chart containing this state

        # self.tran_acts = []  # the queue to store transition actions

        # Inner transitions of this state
        assert isinstance(inner_trans, (list, tuple))
        self.inner_trans = inner_trans
        self.funs = None  # functions in this state

        # Variables modified in this state
        # self.modified_vars = sorted(list(self.get_modified_vars()))

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

    def init(self):               #初始化时所有的状态都为退出状态
        hps = list()
        hps.append(self._exit())  # turn off
        for child in self.children:
            if isinstance(child, (AND_State, OR_State)):
                hps.extend(child.init())
        return hps


#_activate和activated的区别



    def _activate(self):  # turn on
        time_process = "state_time := 0; " if isinstance(self, OR_State) and self.has_aux_var("state_time") else ""
        activate_process = "a_" + self.name + " := 1" #等于1表示该状态处于活动状态
        return hp_parser.parse(time_process + activate_process)    #？？？？？
        # return hp_parser.parse("a_" + self.name + " := 1")

    def _exit(self):
        return hp_parser.parse("a_" + self.name + " := 0")#等于0表示该状态退出，不在处于活动状态

    def activated(self):
        return bexpr_parser.parse("a_" + self.name + " == 1")
#历史节点需修改
    def activate(self):  # return a list of hps
        hps = list()
        hps.append(self._activate())
        if self.en:
            hps.extend(self.en)
        if isinstance(self, OR_State) and self.has_history_junc == True and self.acth != None:   
                    
                for child in self.children:
                    if isinstance(child,(AND_State,OR_State)):
                        child_hps=list()
                        if isinstance(child, AND_State):
                                # hps.append(child._activate())
                            child_hps.extend(child.activate())
                        elif isinstance(child, OR_State):
                                # Activate the state with default transition
                                
                            if child.default_tran:
                                if child.default_tran.cond_acts:
                                    child_hps.extend(child.default_tran.cond_acts)
                                if child.default_tran.tran_acts:
                                    child_hps.extend(child.default_tran.tran_acts)
                                child_hps.extend(child.activate())
                            else:
                                child_hps.extend(child.activate())
                                
                        elif isinstance(child, Junction):
                            pass
                        hps.append((bexpr_parser.parse(self.name+"_"+"acth" +' == "' +"a_"+ child.name + '"'), child_hps))
                    
        else:
                # Activate children
                for child in self.children:
                    if isinstance(child, AND_State):
                        # hps.append(child._activate())
                        hps.extend(child.activate())
                    elif isinstance(child, OR_State) and child.default_tran:
                        # Activate the state with default transition
                        
                        if child.default_tran.cond_acts:
                            hps.extend(child.default_tran.cond_acts)
                        if child.default_tran.tran_acts:
                            hps.extend(child.default_tran.tran_acts)
                        hps.extend(child.activate())
                        break
                    elif isinstance(child, Junction):
                        pass
        hps = [_hp for _hp in hps if _hp]  # delete Nones
        return hps
#历史节点修改
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
                if child.father.has_history_junc == True:
                    child.father.acth =child.name
                    child_exit_hps.append(hp_parser.parse(child.fathe.name+"_"+"acth" +' := "' +"a_"+ child.name + '"'))   
                hps.append((child.activated(), child_exit_hps))

        return hps
#历史节点修改
    def exit_to(self, ancestor):  # return a list of hps
        assert isinstance(self, (OR_State, AND_State))
        assert isinstance(ancestor, (AND_State, OR_State))
        hps = list()
        if self == ancestor:
            return hps
        if self.ex:
            hps.extend(self.ex)
        
        hps.append(self._exit())  # turn off
        if self.father ==ancestor and isinstance(self, OR_State) and isinstance(ancestor, OR_State) and ancestor.has_history_junc == True :
                self.father.acth = self.name
                hps.append(hp_parser.parse(self.father.name+"_"+"acth" +' := "' +"a_"+ self.name + '"'))
        if self.father != ancestor:
            
            if self.father.has_history_junc == True :
                self.father.acth = self.name
                hps.append(hp_parser.parse(self.father.name+"_"+"acth" +' := "' +"a_"+ self.name + '"'))
            hps.extend(self.father.exit_to(ancestor))
        return hps
#历史节点修改
    def enter_into(self, descendant):  # return a list of hps
        assert isinstance(self, (AND_State, OR_State))
        # assert isinstance(descendant, (AND_State, OR_State))
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
            # if state.father.has_history_junc == True and state.father.acth != None:
            #     hps.append(bexpr_parser.parse(state.father.name+"_"+"acth" +' == "' +"a_"+ state.name + '"'))
            #     state=state.father.acth
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

    def get_fun_dict(self):                         
        fun_dict = dict()
        if self.funs:
            for fun in self.funs:
                assert (self.name, fun.name) not in fun_dict
                fun_dict[(self.name, fun.name)] = fun.parse()
        for child in self.children:
            if isinstance(child, (AND_State, OR_State)):
                child_fun_dict = child.get_fun_dict()
                for path, hcsp in child_fun_dict.items():
                    new_path = (self.name,) + path
                    assert new_path not in fun_dict
                    fun_dict[new_path] = hcsp
        return fun_dict

    def get_vars(self):
        var_set = set()
        en_du_ex_acts = (self.en if self.en else list()) \
                        + (self.du if self.du else list()) \
                        + (self.ex if self.ex else list())
        for act in en_du_ex_acts:
            assert isinstance(act, hp.HCSP)
            if isinstance(act, (hp.Assign, hp.Sequence)):
                var_set = var_set.union(act.get_vars())
        for tran in self.inner_trans:                         #并行状态中只能有内部转换，or状态中3种转换都可以有  
            var_set = var_set.union(tran.get_vars())
        if isinstance(self, OR_State):                           
            for tran in self.out_trans:
                var_set = var_set.union(tran.get_vars())
            if self.default_tran:
                var_set = var_set.union(self.default_tran.get_vars())
        for child in self.children:
            var_set = var_set.union(child.get_vars())

        return var_set

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


class OR_State(SF_State):
    def __init__(self, ssid, out_trans, inner_trans=(), name="",original_name="", en=None, du=None, ex=None, default_tran=None):
        super(OR_State, self).__init__(ssid, inner_trans, name,original_name, en, du, ex)
        self.out_trans = out_trans
        self.default_tran = default_tran  # The default transition to this state
       #个人新添加的历史节点内容
        self.has_history_junc=False  #The history junction to this state
        self.acth=None              # the latest state

    def has_aux_var(self, var_name):
        # return if the state has the auxiliary variable var_name
        # The auxiliary variables are all in the conditions of outgoing transitions
        for tran in self.out_trans:
            if var_name in tran.cond_vars:
                return True
        return False


class AND_State(SF_State):
    def __init__(self, ssid, inner_trans=(), name="",original_name="", en=None, du=None, ex=None, order=0):
        super(AND_State, self).__init__(ssid, inner_trans, name,original_name, en, du, ex)
        self.order = order


class Junction:
    def __init__(self, ssid, out_trans, name="",junc_type=""):
        self.ssid = ssid
        self.out_trans = out_trans
        self.name = name
        self.father = None
        self.visited = False
        self.type=junc_type
        self.processes = list()
        self.tran_acts = list()  # the queue to store transition actions

        # Variables modified in this junction
        # self.modified_vars = sorted(list(self.get_modified_vars()))

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

    def get_vars(self):
        var_set = set()
        for tran in self.out_trans:
            var_set = var_set.union(tran.get_vars())
        return var_set


class Function:
    def __init__(self, ssid, name, script):
        self.ssid = ssid
        self.name = name
        self.script = script

    def parse(self):
        assert "==" not in self.script
        script = re.sub(pattern="=", repl=":=", string=self.script)
        acts = [act.strip("; ") for act in script.split("\n") if act.strip("; ")]
        assert re.match(pattern="function \\w+", string=acts[0])
        hps = [hp_parser.parse(act) for act in acts[1:]]
        assert all(isinstance(_hp, hp.Assign) for _hp in hps) and len(hps) >= 1
        result_hp = hp.Sequence(*hps) if len(hps) >= 2 else hps[0]  
        return result_hp
