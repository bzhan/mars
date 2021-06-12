"""Converting a Stateflow chart to HCSP process."""

from ss2hcsp.sl.get_hcsp import get_hcsp
from ss2hcsp.hcsp.pprint import pprint
from ss2hcsp.sf.sf_chart import get_common_ancestor
from ss2hcsp.sf.sf_state import OR_State, AND_State, Junction
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.pprint import pprint
from ss2hcsp.matlab import convert
from ss2hcsp.matlab.function import BroadcastEvent


class SFConvert:
    def __init__(self, chart):
        self.chart = chart

        # Dictionary of procedures
        self.procedures = dict()
        for fun in chart.diagram.funs:
            self.procedures[fun.name] = fun

        # Convert expression and convert command functions
        self.convert_expr = convert.convert_expr
        def convert_cmd(cmd, *, still_there=None):
            return convert.convert_cmd(cmd, raise_event=self.raise_event, procedures=self.procedures,
                                       still_there=still_there)
        self.convert_cmd = convert_cmd

        # Dictionary mapping junction ID and (init_src, init_tran_act) to the
        # pair (name, proc).
        self.junction_map = dict()
        for ssid, state in self.chart.all_states.items():
            if isinstance(state, Junction):
                self.junction_map[ssid] = dict()

    def return_val(self, val):
        return hcsp.Assign("_ret", val)

    def raise_event(self, event):
        return hcsp.seq([
            hcsp.Assign("EL", expr.FunExpr("push", [expr.AVar("EL"), expr.AConst(event.name)])),
            hcsp.Var(self.exec_name()),
            hcsp.Assign("EL", expr.FunExpr("pop", [expr.AVar("EL")]))
        ])

    def get_chain_to_ancestor(self, state, ancestor):
        """Chain of states from the current state to ancestor (not including ancestor)."""
        chain = []
        while state != ancestor:
            chain.append(state)
            state = state.father
        return chain

    def en_proc_name(self, state):
        """en action of state."""
        return "en_" + state.name

    def du_proc_name(self, state):
        """du action of state."""
        return "du_" + state.name

    def ex_proc_name(self, state):
        """ex action of state."""
        return "ex_" + state.name

    def active_state_name(self, state):
        """Variable indicating which child state of the current state is active.
        
        This variable has type string. It is applicable only if the current state
        has child OR-states. If one of the child OR-states is active, this variable
        is assigned the name of the child state. If none of the child OR-states is
        active, this variable is assigned the empty string.

        """
        return state.name + "_st"

    def history_name(self, state):
        """Name of the history variable for an OR-state with history junction."""
        return state.name + "_hist"

    def entry_proc_name(self, state):
        """Procedure for entry into state."""
        return "entry_" + state.name

    def during_proc_name(self, state):
        """Procedure for executing at state."""
        return "during_" + state.name

    def exit_proc_name(self, state):
        """Procedure for exiting from state."""
        return "exit_" + state.name

    def get_en_proc(self, state):
        if not state.en:
            return hcsp.Skip()
        return self.convert_cmd(state.en)

    def get_du_proc(self, state):
        if not state.du:
            return hcsp.Skip()
        return self.convert_cmd(state.du)

    def get_ex_proc(self, state):
        if not state.ex:
            return hcsp.Skip()
        return self.convert_cmd(state.ex)

    def get_entry_proc(self, state):
        """Entry procedure for the given state.
        
        The procedure does the following:
        - if the current state is an OR-state, assign the corresponding active state
          variable.
        - if the current state is an OR-state and its parent has history junction,
          assign the appropriate history variable.
        - call the en action of the state.

        """
        procs = []
        
        # Set the activation variable
        if isinstance(state, OR_State):
            procs.append(hcsp.Assign(self.active_state_name(state.father), expr.AConst(state.name)))
        
        # Set history junction
        if isinstance(state.father, OR_State) and state.father.has_history_junc:
            procs.append(hcsp.Assign(self.history_name(state.father), expr.AConst(state.name)))

        # Perform en action
        procs.append(hcsp.Var(self.en_proc_name(state)))
        return hcsp.seq(procs)

    def get_transition_proc(self, src, dst, middle_proc=None):
        """Get procedure for transitioning between two states.
        
        src - source state.
        dst - destination state.
        middle_proc : HCSP - procedure to execute in the middle.

        """
        ancestor = get_common_ancestor(src, dst)
        procs = []

        # Exit states from src to ancestor (not including ancestor)
        procs.append(self.get_rec_exit_proc(src))
        for state in self.get_chain_to_ancestor(src, ancestor)[1:]:
            procs.append(hcsp.Var(self.exit_proc_name(state)))
            
        if middle_proc is not None:
            procs.append(middle_proc)
            
        # Enter states from ancestor to state1
        for state in reversed(self.get_chain_to_ancestor(dst, ancestor)[1:]):
            procs.append(hcsp.Var(self.entry_proc_name(state)))
        procs.append(self.get_rec_entry_proc(dst))
            
        return hcsp.seq(procs)

    def convert_label(self, label, *, still_there_cond=None, still_there_tran=None):
        """Convert transition label to a triple of condition, condition action,
        and transition action.

        label : TransitionLabel - transition label to be converted.
        still_there_cond : BExpr - when to continue execution of condition action.
        still_there_tran : BExpr - when to continue execution of transition action.

        """
        conds, cond_act, tran_act = [], hcsp.Skip(), hcsp.Skip()
        if label is not None:
            if label.event is not None:
                if isinstance(label.event, BroadcastEvent):
                    conds.append(expr.conj(expr.RelExpr("!=", expr.AVar("EL"), expr.AConst([])),
                                           expr.RelExpr("==", expr.FunExpr("top", [expr.AVar("EL")]), expr.AConst(label.event.name))))
                else:
                    raise NotImplementedError('convert_label: currently only support broadcast events')
            if label.cond is not None:
                conds.append(self.convert_expr(label.cond))
            if label.cond_act is not None:
                cond_act = self.convert_cmd(label.cond_act, still_there=still_there_cond)
            if label.tran_act is not None:
                tran_act = self.convert_cmd(label.tran_act, still_there=still_there_tran)
        return expr.conj(*conds), cond_act, tran_act

    def get_rec_entry_proc(self, state):
        """Return the process for recursively entering into state."""
        procs = []
        procs.append(hcsp.Var(self.entry_proc_name(state)))

        # Recursively enter into child states
        if state.children:
            if isinstance(state.children[0], AND_State):
                for child in state.children:
                    procs.append(self.get_rec_entry_proc(child))
            elif isinstance(state.children[0], OR_State):
                # First, obtain what happens in default transition:
                default_tran = None
                for child in state.children:
                    if isinstance(child, OR_State) and child.default_tran:
                        cond, cond_act, tran_act = self.convert_label(child.default_tran.label)
                        assert cond == expr.true_expr, \
                            "get_rec_entry_proc: no condition on default transitions"
                        default_tran = hcsp.seq([cond_act, tran_act, self.get_rec_entry_proc(child)])
                        break
                
                # Next, check if there are history junctions
                if isinstance(state, OR_State) and state.has_history_junc:
                    conds = []
                    hist_name = self.history_name(state)
                    for child in state.children:
                        if isinstance(child, OR_State):
                            conds.append((expr.RelExpr("==", expr.AVar(hist_name), expr.AConst(child.name)),
                                          self.get_rec_entry_proc(child)))
                    procs.append(hcsp.ITE(conds, default_tran))
                else:
                    procs.append(default_tran)
            else:
                raise TypeError
        return hcsp.seq(procs)

    def get_rec_exit_proc(self, state):
        """Return the process for recursively exiting from state."""
        procs = []
        
        # Recursively exit from child states
        if state.children:
            if isinstance(state.children[0], AND_State):
                for child in reversed(state.children):
                    procs.append(self.get_rec_exit_proc(child))
            elif isinstance(state.children[0], OR_State):
                ite = []
                for child in state.children:
                    if isinstance(child, OR_State):
                        ite.append((expr.RelExpr("==", expr.AVar(self.active_state_name(state)), expr.AConst(child.name)),
                                    self.get_rec_exit_proc(child)))
                procs.append(hcsp.ITE(ite))
            else:
                raise TypeError
        
        procs.append(hcsp.Var(self.exit_proc_name(state)))
        return hcsp.seq(procs)

    def get_during_proc(self, state):
        """During procedure for the given state.
        
        The procedure performs the following steps:
        - check if there are outgoing transitions from the state. If one of them is
        valid, carry out the transition.
        - If none of the transitions are valid, perform the du action of the state.

        """
        if isinstance(state, OR_State):
            if not state.out_trans:
                return hcsp.Var(self.du_proc_name(state))

            procs = []
            done = state.name + "_done"
            still_there_cond = expr.RelExpr("==", expr.AVar(self.active_state_name(state.father)),
                                            expr.AConst(state.name))
            still_there_tran = expr.RelExpr("==", expr.AVar(self.active_state_name(state.father)),
                                            expr.AConst(""))
            procs.append(hcsp.Assign(done, expr.AConst(0)))
            for i, tran in enumerate(state.out_trans):
                src = self.chart.all_states[tran.src]
                dst = self.chart.all_states[tran.dst]
                cond, cond_act, tran_act = self.convert_label(
                    tran.label, still_there_cond=still_there_cond, still_there_tran=still_there_tran)
                act = hcsp.Sequence(
                    cond_act,
                    hcsp.Condition(still_there_cond, hcsp.seq([
                        self.get_traverse_state_proc(dst, src, tran_act),
                        hcsp.Assign(done, expr.AVar("_ret"))])))
                if i == 0:
                    procs.append(hcsp.Condition(cond, act))
                else:
                    procs.append(hcsp.Condition(
                        expr.conj(still_there_cond, expr.RelExpr("!=", expr.AVar(done), expr.AConst(1)), cond),
                        hcsp.Condition(cond, act)))
            procs.append(hcsp.Condition(expr.RelExpr("!=", expr.AVar(done), expr.AConst(1)),
                                        hcsp.Var(self.du_proc_name(state))))
            return hcsp.seq(procs)

        elif isinstance(state, AND_State):
            # For AND-states, simply execute its during action.
            return hcsp.Var(self.du_proc_name(state))

        else:
            raise TypeError("get_during_proc: state is not AND-state or OR-state.")

    def get_exit_proc(self, state):
        """Exit procedure from the given state.
        
        The procedure does only two things:
        - if the current state is an OR-state, clear the corresponding active state
        variable.
        - call the ex action of state.

        """
        procs = []
        
        # Perform ex action
        procs.append(hcsp.Var(self.ex_proc_name(state)))

        # Set the activation variable
        if isinstance(state, OR_State):
            procs.append(hcsp.Assign(self.active_state_name(state.father), expr.AConst("")))
            
        return hcsp.seq(procs)

    def get_rec_during_proc(self, state):
        """Return the process for recursively executing an state."""
        procs = []
        # First, execute the during procedure
        procs.append(hcsp.Var(self.during_proc_name(state)))
        
        # Next, recursively execute child states
        if state.children:
            if isinstance(state.children[0], AND_State):
                for child in state.children:
                    procs.append(self.get_rec_during_proc(child))
            elif isinstance(state.children[0], OR_State):
                ite = []
                for child in state.children:
                    if isinstance(child, OR_State):
                        ite.append((expr.RelExpr("==", expr.AVar(self.active_state_name(state)), expr.AConst(child.name)),
                                    self.get_rec_during_proc(child)))
                procs.append(hcsp.ITE(ite))
            else:
                raise TypeError
        return hcsp.seq(procs)

    def get_traverse_state_proc(self, state, init_src, init_tran_act):
        """Obtain the procedure for traversing a state or junction, given
        the source state and existing transition actions.

        state : [OR_State, Junction] - current state or junction.
        init_src : str - name of the initial source state.
        init_tran_act : HCSP - already accumulated transition actions.

        This function returns the code of the procedure, and memoize results
        for junctions in the dictionary junction_map.

        """
        assert isinstance(init_src, OR_State), "get_traverse_state_proc: source is not an OR_State"

        if isinstance(state, OR_State):
            # If reached an OR-state, carry out the transition from src to
            # the current state, with the accumulated transition actions in
            # the middle. Then return 1 for successfully reaching a state.        
            return hcsp.seq([self.get_transition_proc(init_src, state, init_tran_act),
                             self.return_val(expr.AConst(1))])

        elif isinstance(state, Junction):
            # If reached a junction, try each of the outgoing edges from the
            # junction.
            if not state.out_trans:
                # Transition unsuccessful.
                return self.return_val(expr.AConst(0))

            if (init_src.ssid, init_tran_act) not in self.junction_map[state.ssid]:
                # Put in placeholder and reserve name
                cur_name = "J" + state.ssid + "_" + str(len(self.junction_map[state.ssid]) + 1)
                self.junction_map[state.ssid][(init_src.ssid, init_tran_act)] = (cur_name, None)
                procs = []
                done = "J" + state.ssid + "_done"
                procs.append(hcsp.Assign(done, expr.AConst(0)))
                for i, tran in enumerate(state.out_trans):
                    src = self.chart.all_states[tran.src]
                    dst = self.chart.all_states[tran.dst]
                    cond, cond_act, tran_act = self.convert_label(tran.label)
                    act = self.get_traverse_state_proc(dst, init_src, hcsp.seq([init_tran_act, tran_act]))
                    act = hcsp.seq([cond_act, act, hcsp.Assign(done, expr.AVar("_ret"))])
                    if i == 0:
                        procs.append(hcsp.Condition(cond, act))
                    else:
                        procs.append(hcsp.Condition(expr.RelExpr("!=", expr.AVar(done), expr.AConst(1)),
                                                    hcsp.Condition(cond, act)))
                procs.append(self.return_val(expr.AVar(done)))
                proc = hcsp.seq(procs)
                self.junction_map[state.ssid][(init_src.ssid, init_tran_act)] = (cur_name, proc)
            return hcsp.Var(self.junction_map[state.ssid][(init_src.ssid, init_tran_act)][0])

        else:
            raise TypeError("get_junction_proc")

    def init_name(self):
        return "init_" + self.chart.name

    def exec_name(self):
        return "exec_" + self.chart.name

    def get_init_proc(self):
        procs = []
        # Initialize event stack
        procs.append(hcsp.Assign("EL", expr.AConst([])))

        # Initialize history junction
        for ssid, state in self.chart.all_states.items():
            if isinstance(state, OR_State) and state.has_history_junc:
                procs.append(hcsp.Assign(self.history_name(state), expr.AConst("")))

        # Recursive entry
        procs.append(self.get_rec_entry_proc(self.chart.diagram))

        return hcsp.seq(procs)

    def get_exec_proc(self):
        return self.get_rec_during_proc(self.chart.diagram)

    def get_procs(self):
        """Returns the list of procedures."""
        all_procs = dict()

        for ssid, state in self.chart.all_states.items():
            if isinstance(state, (AND_State, OR_State)):
                all_procs[self.en_proc_name(state)] = self.get_en_proc(state)
                all_procs[self.du_proc_name(state)] = self.get_du_proc(state)
                all_procs[self.ex_proc_name(state)] = self.get_ex_proc(state)
                all_procs[self.entry_proc_name(state)] = self.get_entry_proc(state)
                all_procs[self.during_proc_name(state)] = self.get_during_proc(state)
                all_procs[self.exit_proc_name(state)] = self.get_exit_proc(state)
        
        all_procs[self.init_name()] = self.get_init_proc()
        all_procs[self.exec_name()] = self.get_exec_proc()
        for ssid, junc_map in self.junction_map.items():
            for _, (name, proc) in junc_map.items():
                all_procs[name] = proc

        return all_procs

    def get_toplevel_process(self):
        """Returns the top-level process for chart."""
        return hcsp.Sequence(
            hcsp.Var(self.init_name()),
            hcsp.Loop(hcsp.Sequence(
                hcsp.Var(self.exec_name()),
                hcsp.Wait(expr.AConst(0.1))
            ))
        )
