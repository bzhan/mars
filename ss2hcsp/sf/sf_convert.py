"""Converting a Stateflow chart to HCSP process."""

from ss2hcsp.sl.get_hcsp import get_hcsp
from ss2hcsp.hcsp.pprint import pprint
from ss2hcsp.sf.sf_chart import get_common_ancestor
from ss2hcsp.sf.sf_state import OR_State, AND_State
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.pprint import pprint
from ss2hcsp.matlab import convert


class SFConvert:
    def __init__(self, chart):
        self.chart = chart

        self.procedures = dict()
        for fun in chart.diagram.funs:
            self.procedures[fun.name] = fun

        self.convert_expr = convert.convert_expr
        def convert_cmd(cmd):
            return convert.convert_cmd(cmd, raise_event=self.raise_event, procedures=self.procedures)
        self.convert_cmd = convert_cmd

    def raise_event(self, event):
        return hcsp.Var(self.exec_name())

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
        
        The procedure does only two things:
        - if the current state is an OR-state, assign the corresponding active state
        variable.
        - call the en action of the state.

        """
        procs = []
        
        # Set the activation variable
        if isinstance(state, OR_State):
            procs.append(hcsp.Assign(self.active_state_name(state.father), expr.AConst(state.name)))
        
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
                for child in state.children:
                    if child.default_tran:
                        procs.append(self.get_rec_entry_proc(child))
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
        procs = []

        if isinstance(state, OR_State) and state.out_trans:
            ite = []
            for tran in state.out_trans:
                cond, cond_act, tran_act = expr.true_expr, None, None
                src = self.chart.all_states[tran.src]
                dst = self.chart.all_states[tran.dst]
                if tran.label is not None:
                    if tran.label.event is not None:
                        raise NotImplementedError
                    if tran.label.cond is not None:
                        cond = self.convert_expr(tran.label.cond)
                    if tran.label.cond_act is not None:
                        cond_act = self.convert_cmd(tran.label.cond_act)
                    if tran.label.tran_act is not None:
                        tran_act = self.convert_cmd(tran.label.tran_act)
                tran_act = self.get_transition_proc(src, dst, tran_act)
                act = tran_act if cond_act is None else hcsp.seq([cond_act, tran_act])
                ite.append((cond, act))
            procs.append(hcsp.ITE(ite))
        procs.append(hcsp.Var(self.du_proc_name(state)))
        return hcsp.seq(procs)

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
                for child in reversed(state.children):
                    procs.append(self.get_rec_during_proc(child))
            elif isinstance(state.children[0], OR_State):
                ite = []
                for child in state.children:
                    ite.append((expr.RelExpr("==", expr.AVar(self.active_state_name(state)), expr.AConst(child.name)),
                                self.get_rec_during_proc(child)))
                procs.append(hcsp.ITE(ite))
            else:
                raise TypeError
        return hcsp.seq(procs)

    def init_name(self):
        return "init_" + self.chart.name

    def exec_name(self):
        return "exec_" + self.chart.name

    def get_init_proc(self):
        return self.get_rec_entry_proc(self.chart.diagram)

    def get_exec_proc(self):
        return self.get_rec_during_proc(self.chart.diagram)

    def get_procs(self):
        """Returns the list of procedures."""
        all_procs = []

        for ssid, state in self.chart.all_states.items():
            all_procs.append(hcsp.Procedure(self.en_proc_name(state), self.get_en_proc(state)))
            all_procs.append(hcsp.Procedure(self.du_proc_name(state), self.get_du_proc(state)))
            all_procs.append(hcsp.Procedure(self.ex_proc_name(state), self.get_ex_proc(state)))
            all_procs.append(hcsp.Procedure(self.entry_proc_name(state), self.get_entry_proc(state)))
            all_procs.append(hcsp.Procedure(self.during_proc_name(state), self.get_during_proc(state)))
            all_procs.append(hcsp.Procedure(self.exit_proc_name(state), self.get_exit_proc(state)))
        
        all_procs.extend([
            hcsp.Procedure(self.init_name(), self.get_init_proc()),
            hcsp.Procedure(self.exec_name(), self.get_exec_proc())
        ])

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
