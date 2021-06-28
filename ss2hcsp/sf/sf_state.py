from ss2hcsp.hcsp.parser import bexpr_parser, hp_parser
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
    def __init__(self, ssid, inner_trans=(), name="",original_name="", en=None, du=None, ex=None):
        self.ssid = ssid  # ID of the state
        self.name = name  # Name of the state
        self.original_name = original_name
        self.en = en  # entry event
        self.du = du  # during event
        self.ex = ex  # exit event
        self.father = None  # parent state
        self.children = list()  # list of children states
        self.root = None  # root of the tree of containment relation
        self.chart = None  # The chart containing this state
        self.is_parse_act=False
        # self.tran_acts = []  # the queue to store transition actions
        self.whole_name=""
        # Inner transitions of this state
        assert isinstance(inner_trans, (list, tuple))
        self.inner_trans = inner_trans
        self.funs = None  # functions in this state
        # Variables modified in this state
        # self.modified_vars = sorted(list(self.get_modified_vars()))

    def get_state_whole_name(self):
        if "(" in self.name:
            self.name=str(self.name)[:str(self.name).index("(")]
        s=self.name
        if self.father is None:
            return self.name
        else:
            child_s=self.father.get_state_whole_name()
            s=child_s+"_"+s
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


    def init(self):
        """Initialize the state."""
        # First exit the current state
        hps = list()
        hps.append(self._exit())

        # Next, call init function for all child states
        for child in self.children:
            if isinstance(child, (AND_State, OR_State)):
                hps.extend(child.init())
        return hps

    def _activate(self):
        """Activation function for the state."""
        # If state_time variable exists, set it to zero
        if isinstance(self, OR_State) and self.has_aux_var("state_time" + str(self.ssid)):
            time_process = "state_time" + str(self.ssid) + " := 0; "
        else:
            time_process = ""

        # Set the activation variable to 1
        activate_process = "a_" + self.whole_name + " := 1"
        return hp_parser.parse(time_process + activate_process)

    def _exit(self):
        """Exit function for the state."""
        # Set the activation variable to 0
        return hp_parser.parse("a_" + self.whole_name + " := 0")

    def activated(self):
        """Return whether the current state is active."""
        return bexpr_parser.parse("a_" + self.whole_name + " == 1")

    def exited(self):
        """Return whether the current state is non-active."""
        if "(" in self.name:
            self.name=str(self.name)[:str(self.name).index("(")]
        return bexpr_parser.parse("a_" + self.whole_name + " == 0")

    def activate(self):
        """Return procedure for activating a node."""
        # Set basic variables
        hps = list()
        hps.append(self._activate())
        
        # Execute entry action
        if self.en:
            hps.extend(self.en)

        # Handle the case with history junction
        if isinstance(self, OR_State) and self.has_history_junc and self.acth != None:   
            for child in self.children:
                if isinstance(child, (AND_State, OR_State)):
                    child_hps = list()
                    if isinstance(child, AND_State):
                        child_hps.extend(child.activate())
                    elif isinstance(child, OR_State):
                        # Activate the state with default transition                            
                        if child.default_tran:
                            if child.default_tran.cond_acts:
                                if child.default_tran.condition:
                                    child_hps.append(hp.Condition(child.default_tran.condition,hp.Sequence(*child.default_tran.cond_acts)))
                                else:
                                    child_hps.extend(child.default_tran.cond_acts)

                            if child.default_tran.tran_acts:
                                child_hps.extend(child.default_tran.tran_acts)
                            child_hps.extend(child.activate())
                            # child_hps.extend(hp_parser.parse("done := 1"))
                        else:
                            child_hps.extend(child.activate())
                            
                    elif isinstance(child, Junction):
                        if child.default_tran:  
                            if child.default_tran.cond_acts:
                                if child.default_tran.condition:
                                    child_hps.append(hp.Condition(child.default_tran.condition,hp.Sequence(*child.default_tran.cond_acts)))
                                else:
                                    child_hps.extend(child.default_tran.cond_acts)

                            if child.default_tran.tran_acts:
                                child_hps.extend(child.default_tran.tran_acts)
                        else:
                            pass
                    hps.append((bexpr_parser.parse(self.name+"_"+"acth" +' == "' +"a_"+ child.name + '"'), child_hps))

        # Now consider case without history junction
        else:
            # Activate children
            for child in self.children:
                if isinstance(child, AND_State):
                    hps.extend(child.activate())
                elif isinstance(child, OR_State):
                    # Activate the state with default transition
                    # print(child.name)
                    # if child.has_aux_var("state_time"):
                    #     hps.append(hp_parser.parse("state_time := 0"))
                    if child.default_tran: 
                        if child.default_tran.cond_acts:
                            if child.default_tran.condition:
                                hps.append(hp.Condition(child.default_tran.condition,hp.Sequence(*child.default_tran.cond_acts) ))          
                            else:
                                hps.extend(child.default_tran.cond_acts)
                        if child.default_tran.tran_acts:
                            hps.extend(child.default_tran.tran_acts)
                        hps.extend(child.activate())
                        break
                        # hps.extend(hp_parser.parse("done := 1"))
                elif isinstance(child, Junction):
                    if child.default_tran:
                        if child.default_tran.cond_acts:
                            if child.default_tran.condition:
                                hps.append(hp.Condition(child.default_tran.condition,hp.Sequence(*child.default_tran.cond_acts)))         
                            else:
                                hps.extend(child.default_tran.cond_acts)
                        if child.default_tran.tran_acts:
                            hps.extend(child.default_tran.tran_acts)
                    else:
                        pass
                        #hps.extend(hp_parser.parse("done := 1"))
                     
        hps = [_hp for _hp in hps if _hp]  # delete Nones
        return hps

    def all_descendant_exit(self):
        """Return procedure for exiting a node."""
        hps = list()

        # the AND_state with the lowest priority exits first
        for child in self.children[::-1]:
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
                if child.father.has_history_junc:
                    child.father.acth = child.name
                    child_exit_hps.append(hp_parser.parse(child.fathe.name+"_"+"acth" +' := "' +"a_"+ child.name + '"'))   
                hps.append((child.activated(), child_exit_hps))

        return hps

    def exit_to(self, ancestor):
        """Return procedure for exiting self, and returning to ancestor.
        
        Mainly for updating history junction.

        """
        assert isinstance(self, (OR_State, AND_State))
        assert isinstance(ancestor, (AND_State, OR_State))
        hps = list()

        # Case when self is already the top-level node
        if self == ancestor:
            return hps

        # Run the ex function, and set variables
        if self.ex:
            hps.extend(self.ex)
        hps.append(self._exit())

        # If ancestor is immediate father
        if self.father == ancestor and isinstance(self, OR_State) and \
            isinstance(ancestor, OR_State) and ancestor.has_history_junc:
            self.father.acth = self.name
            hps.append(hp_parser.parse(self.father.name+"_"+"acth" +' := "' +"a_"+ self.name + '"'))

        # If ancestor is not immediate father
        if self.father != ancestor:
            if self.father.has_history_junc:
                self.father.acth = self.name
                hps.append(hp_parser.parse(self.father.name+"_"+"acth" +' := "' +"a_"+ self.name + '"'))
            hps.extend(self.father.exit_to(ancestor))
        return hps

    def enter_into(self, descendant):
        """Return procedure for entering self, eventually into descendent."""
        assert isinstance(self, (AND_State, OR_State))

        # Obtain the chain of nodes from immediate child to descendent
        ancestor_chain = []
        cursor = descendant
        while cursor != self:
            ancestor_chain.append(cursor)
            cursor = cursor.father
        ancestor_chain.reverse()

        # First element is immediate child, last element is descendent
        assert ancestor_chain == [] or ancestor_chain[0].father == self and \
            ancestor_chain[-1] == descendant

        # Activate each element in the chain
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

    def get_fun_dict(self):
        """Returns a dictionary of functions."""
        fun_dict = dict()
        if self.funs:
            for fun in self.funs:
                if isinstance(fun,Function):
                    assert (self.name, fun.name) not in fun_dict
                    name = str(fun.name)
                    if "(" in name:
                        name = name[:name.index("(")]
                    fun_dict[(fun.return_var,fun.exprs,self.name, name)] = fun.parse()

        for child in self.children:
            if isinstance(child, (AND_State, OR_State)):
                child_fun_dict = child.get_fun_dict()
                for path, hcsp in child_fun_dict.items():
                    path1 = path[2:]
                    new_path = (path[0],path[1],self.name,) + path1
                    assert new_path not in fun_dict
                    fun_dict[new_path] = hcsp
        return fun_dict

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
    def __init__(self, ssid, out_trans=(), inner_trans=(), name="", original_name="",
                 en=None, du=None, ex=None, default_tran=None):
        super(OR_State, self).__init__(ssid, inner_trans, name, original_name, en, du, ex)
        self.out_trans = out_trans        # outgoing transitions
        self.default_tran = default_tran  # default transition to this state
        self.has_history_junc = False     # history junction to this state
        self.acth = None                  # (when there is history junction) the latest state
        self.func_after=list()               
        self.get_after_func()
    def has_aux_var(self, var_name):
        """Return if the state has the auxiliary variable var_name
        
        The auxiliary variables are all in the conditions of outgoing transitions.

        """
        for tran in self.out_trans:
            if var_name in tran.cond_vars:
                return True
        return False

    def get_tran_after_cond(self,condition):
        aexpr1=condition.expr1
        aexpr2=condition.expr2
        if isinstance(aexpr1,RelExpr) and ("state_time"+self.ssid) in str(aexpr1):
            self.func_after.append(aexpr1.expr2)
        elif isinstance(aexpr1,LogicExpr):
            self.get_tran_after_cond(aexpr1)
        elif isinstance(aexpr2,RelExpr) and ("state_time"+self.ssid) in str(aexpr2) :
            self.func_after.append(aexpr2.expr2)
        elif isinstance(aexpr2,LogicExpr):
            self.get_tran_after_cond(aexpr2)

    def get_after_func(self):
        for tran in self.out_trans:
            if ("state_time"+self.ssid) in tran.cond_vars and isinstance(tran.condition,(RelExpr,LogicExpr)):
                if isinstance(tran.condition,RelExpr):
                    self.func_after.append(tran.condition.expr2)
                elif isinstance(tran.condition,LogicExpr):
                    self.get_tran_after_cond(tran.condition)



class AND_State(SF_State):
    """Represents an AND state."""
    def __init__(self, ssid, inner_trans=(), name="", original_name="",
                 en=None, du=None, ex=None, order=0):
        super(AND_State, self).__init__(ssid, inner_trans, name,original_name, en, du, ex)
        self.order = order                # order within the parent state 
        self.func_after=list()


class Junction:
    """Represents a junction."""
    def __init__(self, ssid, out_trans, name="", junc_type="", default_tran=None):
        self.ssid = ssid
        self.out_trans = out_trans
        self.name = name
        self.original_name=""
        self.whole_name=""
        self.father = None
        self.visited = False
        self.type = junc_type
        self.processes = list()
        self.tran_acts = list()  # the queue to store transition actions
        self.default_tran = default_tran
        self.is_parse_act = False

        # Variables modified in this junction
        # self.modified_vars = sorted(list(self.get_modified_vars()))

    def __str__(self):
        result = "JUN(" + self.ssid + ") " + self.name + "\n"
        for tran in self.out_trans:
            result += "  " + str(tran) + "\n"
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

    def instantiate(self, vals=None):
        """Instantiate a procedure with given values for parameters.

        vals : [None, List[Expr]] - list of expressions as input values.
            Default to None if no input values.

        Returns Command - instantiated command.
        
        This works by replacing occurrence of parameters in the body of
        the function with the given values.
 
        """
        params=None
        if vals is None:
            vals = tuple()
        if self.params is None:
            params=tuple()
        else:
            params=self.params
        # assert len(params) == len(vals), "Function instantiation: wrong number of inputs"
        inst = dict(zip(params, vals))
        return self.cmd.subst(inst)

class Function:
    def __init__(self, name, params, return_var, script,chart_state,fun_type):
        self.name = name
        self.exprs = params
        self.return_var = return_var
        self.script = script
        self.chart_state=chart_state
        self.fun_type=fun_type
    def __str__(self):
        res = "Function(%s,%s,%s\n" % (self.name, self.exprs, self.return_var)
        res += "%s" %(self.script)
        return res

    def parse(self):
        if self.fun_type == "GRAPHICAL_FUNCTION" and self.chart_state is not None:
            return self.chart_state
        elif self.fun_type == "MATLAB_FUNCTION":
            return self.script

