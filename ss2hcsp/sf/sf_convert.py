"""Converting a Stateflow chart to HCSP process."""

from ss2hcsp.sl.get_hcsp import get_hcsp,translate_continuous
from ss2hcsp.hcsp.pprint import pprint
from ss2hcsp.sf.sf_chart import get_common_ancestor
from ss2hcsp.sf.sf_state import OR_State, AND_State, Junction, GraphicalFunction
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.pprint import pprint
from ss2hcsp.matlab import convert,parser
from ss2hcsp.matlab.function import BroadcastEvent, DirectedEvent, TemporalEvent, \
    AbsoluteTimeEvent, ImplicitEvent


class SFConvert:
    """Conversion from Stateflow chart to HCSP process.
    
    chart : SF_Chart
    chart_parameters - additional parameters.

    """
    def __init__(self, chart=None, *, chart_parameters=None):
        self.chart = chart
        if chart_parameters is None:
            chart_parameters = dict()
        self.chart_parameters = chart_parameters

        # List of data variables
        self.data = dict()
        if 'data' in self.chart_parameters:
            self.data = self.chart_parameters['data']

        # Sample time
        self.sample_time = 0.1
        if 'st' in self.chart_parameters and self.chart_parameters['st'] != -1:
            self.sample_time = self.chart_parameters['st']

        # Get the whole name of state
        for state in self.chart.all_states.values():
            if isinstance(state, (AND_State, OR_State)):
                state.whole_name = state.get_state_whole_name()

        # Mapping name to state
        self.name_to_state = dict()
        for ssid, state in self.chart.all_states.items():
            if isinstance(state, (AND_State, OR_State)):
                self.name_to_state[state.whole_name] = state

        # Dictionary of procedures
        self.procedures = dict()
        for fun in chart.diagram.funs:
            self.procedures[fun.name] = fun

        def get_state(state, name):
            if len(name)==0:
                return state
            n=name[0]
            for child in state.children:
                if child.name == n:
                   return get_state(child,name[1:])
        self.get_state = get_state

        def get_state_by_path(name):
            names_list = name[0]
            for ssid, state in self.chart.all_states.items():
                if state.name == names_list:
                    return self.get_state(state,name[1:])
        self.get_state_by_path = get_state_by_path

        # Functions for converting expressions and commands. Simply wrap
        # the corresponding functions in convert, but with extra arguments.
        def convert_expr(e):
            return convert.convert_expr(e, arrays=self.data.keys(), procedures=self.procedures)
        self.convert_expr = convert_expr

        def convert_cmd(cmd, *, still_there=None):
            return convert.convert_cmd(cmd, raise_event=self.raise_event, procedures=self.procedures,
                                       still_there=still_there, arrays=self.data.keys(),array_value=self.data)
        self.convert_cmd = convert_cmd

        # Dictionary mapping junction ID and (init_src, init_tran_act) to the
        # pair (name, proc).
        self.junction_map = dict()
        for ssid, state in self.chart.all_states.items():
            if isinstance(state, Junction) and not state.default_tran:
                self.junction_map[ssid] = dict()
            elif isinstance(state, Junction) and state.default_tran and not state.out_trans:
                self.junction_map[ssid] = {"J"+ssid:("J"+ssid,hcsp.Skip())}

        # Find all states which has a transition guarded by temporal event.
        self.temporal_guards = dict()
        for ssid, state in self.chart.all_states.items():
            if isinstance(state, OR_State) and state.out_trans:
                for tran in state.out_trans:
                    if tran.label is not None:
                        if isinstance(tran.label,str):
                            tran.label=parser.transition_parser.parse(tran.label)
                    if tran.label is not None and tran.label.event is not None and \
                        isinstance(tran.label.event, TemporalEvent):
                        if tran.src not in self.temporal_guards:
                            self.temporal_guards[tran.src] = []
                        self.temporal_guards[tran.src].append(tran.label.event)
            if isinstance(state, (AND_State, OR_State)) and state.inner_trans:
                for tran in state.inner_trans:
                    if tran.label is not None and isinstance(tran.label,str):
                        tran.label=parser.transition_parser.parse(tran.label)
                    if tran.label is not None and tran.label.event is not None and \
                        isinstance(tran.label.event, TemporalEvent):
                        if tran.src not in self.temporal_guards:
                            self.temporal_guards[tran.src] = []
                        self.temporal_guards[tran.src].append(tran.label.event)

        # Detect whether a state has implicit or absolute time event.
        self.implicit_events = set()
        self.absolute_time_events = set()
        for ssid in self.chart.all_states:
            if ssid in self.temporal_guards:
                for temp_event in self.temporal_guards[ssid]:
                    if isinstance(temp_event.event, ImplicitEvent):
                        self.implicit_events.add(ssid)
                    elif isinstance(temp_event.event, AbsoluteTimeEvent):
                        self.absolute_time_events.add(ssid)
        self.implicit_events = sorted(list(self.implicit_events))
        self.absolute_time_events = sorted(list(self.absolute_time_events))

    def return_val(self, val):
        return hcsp.Assign("_ret", val)

    def raise_event(self, event):
        if isinstance(event, BroadcastEvent):
            return hcsp.seq([
                hcsp.Assign("EL", expr.FunExpr("push", [expr.AVar("EL"), expr.AConst(event.name)])),
                hcsp.Var(self.exec_name()),
                hcsp.Assign("EL", expr.FunExpr("pop", [expr.AVar("EL")]))])

        elif isinstance(event, DirectedEvent):
            # First, find the innermost state name and event
            state_name_path=list()
            st_name, ev = event.state_name, event.event
            state_name_path.append(st_name)
            while isinstance(ev, DirectedEvent):
                st_name, ev = ev.state_name, ev.event
                state_name_path.append(st_name)
            dest_state=self.get_state_by_path(state_name_path)
            return hcsp.seq([
                hcsp.Assign("EL", expr.FunExpr("push", [expr.AVar("EL"), expr.AConst(ev.name)])),
                self.get_rec_during_proc(dest_state),
                hcsp.Assign("EL", expr.FunExpr("pop", [expr.AVar("EL")]))])
        
        else:
            raise TypeError("raise_event: event must be broadcast or directed.")

    def get_chain_to_ancestor(self, state, ancestor):
        """Chain of states from the current state to ancestor (not including ancestor)."""
        chain = []
        while state != ancestor:
            chain.append(state)
            state = state.father
        return chain

    def en_proc_name(self, state):
        """en action of state."""
        return "en_" + state.whole_name

    def du_proc_name(self, state):
        """du action of state."""
        return "du_" + state.whole_name

    def ex_proc_name(self, state):
        """ex action of state."""
        return "ex_" + state.whole_name

    def active_state_name(self, state):
        """Variable indicating which child state of the current state is active.
        
        This variable has type string. It is applicable only if the current state
        has child OR-states. If one of the child OR-states is active, this variable
        is assigned the name of the child state. If none of the child OR-states is
        active, this variable is assigned the empty string.

        """
        return state.whole_name + "_st"

    def history_name(self, state):
        """Name of the history variable for an OR-state with history junction."""
        return state.whole_name + "_hist"

    def entry_tick_name(self, state):
        """Counter for number of ticks since entry into state."""
        return state.whole_name + "_tick"

    def entry_time_name(self, state):
        """Counter for number of seconds since entry into state."""
        return state.whole_name + "_time"

    def entry_proc_name(self, state):
        """Procedure for entry into state."""
        return "entry_" + state.whole_name

    def during_proc_name(self, state):
        """Procedure for executing at state."""
        return "during_" + state.whole_name

    def exit_proc_name(self, state):
        """Procedure for exiting from state."""
        return "exit_" + state.whole_name

    def get_en_proc(self, state):
        if not state.en:
            return hcsp.Skip()
        return self.convert_cmd(state.en)

    def get_du_proc(self, state):
        if not state.du:
            return hcsp.Skip()

        procs = []
        if state.ssid in self.implicit_events:
            tick_name = self.entry_tick_name(state)
            procs.append(hcsp.Condition(
                    expr.RelExpr("!=", expr.AVar(tick_name), expr.AConst(-1)),
                    hcsp.Assign(
                        expr.AVar(tick_name),
                        expr.PlusExpr(["+", "+"], [expr.AVar(tick_name), expr.AConst(1)]))))
        procs_input=[]
        procs_out=[]
        procs_response=[]
        if len(state.children) == 0:
            
            # self.get_input_data(procs_input)
            
            self.get_output_data(procs_out)
            
            self.input_recieve_response(procs_response)
        return hcsp.Sequence(*procs_input,self.convert_cmd(state.du), *procs,*procs_response,*procs_out)

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
        - if the current state has implicit or absolute time event transitions, reset
          the corresponding counter to 0.
        - call the en action of the state.

        Note this does not include recursively entering into child states,
        which is handled in get_rec_entry_proc.

        """
        procs = []
        
        # Set the activation variable
        if isinstance(state, OR_State):
            procs.append(hcsp.Assign(self.active_state_name(state.father), expr.AConst(state.whole_name)))
        
        # Set history junction
        if isinstance(state.father, OR_State) and state.father.has_history_junc:
            procs.append(hcsp.Assign(self.history_name(state.father), expr.AConst(state.whole_name)))

        # Set counter for implicit or absolute time events
        if state.ssid in self.implicit_events:
            procs.append(hcsp.Assign(self.entry_tick_name(state), expr.AConst(1)))
        if state.ssid in self.absolute_time_events:
            procs.append(hcsp.Assign(self.entry_time_name(state), expr.AConst(0)))

        # Perform en action
        procs.append(hcsp.Var(self.en_proc_name(state)))
        return hcsp.seq(procs)

    def get_input_data(self,procs):
        in_chs = []
        for port_id, in_var in self.chart.port_to_in_var.items():
            line = self.chart.dest_lines[port_id]
            ch_name = "ch_" + line.name + "_" + str(line.branch)
            in_chs.append(hcsp.InputChannel(ch_name , expr.AVar(in_var)))
        if len(in_chs)>0:
            procs.extend(in_chs)
    def get_output_data(self,procs):        
        out_chs = []
        for port_id, out_var in self.chart.port_to_out_var.items():
            lines = self.chart.src_lines[port_id]
            for line in lines:
                ch_name = "ch_" + line.name + "_" + str(line.branch)
                out_chs.append(hcsp.OutputChannel(ch_name , expr.AVar(out_var)))
        if len(out_chs)>0:
            procs.extend(out_chs)
            for port_id, out_var in self.chart.port_to_out_var.items():
                lines = self.chart.src_lines[port_id]
                for line in lines:
                    ch_name = "ch_response_" + line.name + "_" + str(line.branch)
                    procs.append(hcsp.InputChannel(ch_name, expr.AVar("response"))) 
    def input_recieve_response(self,procs):
        for port_id, in_var in self.chart.port_to_in_var.items():
                line = self.chart.dest_lines[port_id]
                if line.src_block.type == "stateflow":
                    ch_name = "ch_response_" + line.name + "_" + str(line.branch)
                    procs.append(hcsp.OutputChannel(ch_name, expr.AConst(1)))
    def get_transition_proc(self, src, dst, tran_act=None):
        """Get procedure for transitioning between two states.

        The so-called "super transitions" has the following semantics:
        to transition from source S to destination T, let their common
        ancestor be A. Then, perform the following steps:
         1. recursively exit from the child states of S.
         2. exit all states from S to the direct child of A.
         3. perform any transition actions.
         4. enter all states from direct child of A to T.
         5. recursively enter child states of T.

        Note this includes special cases of inner transitions, where A may
        be the same as S or T (or both). In these cases, A is never exited
        or entered.
        
        src - source state.
        dst - destination state.
        tran_act : HCSP - transition actions to execute between exiting source
            and entering destination.

        """
        ancestor = get_common_ancestor(src, dst)
        procs = []

        # Exit states from src to ancestor (not including ancestor)
        procs.append(self.get_rec_exit_proc(src))
        for state in self.get_chain_to_ancestor(src, ancestor):
            procs.append(hcsp.Var(self.exit_proc_name(state)))

        if tran_act is not None:
            procs.append(tran_act)
            
        # Enter states from ancestor to state1
        for state in reversed(self.get_chain_to_ancestor(dst, ancestor)):
            # self.get_input_data(procs)
            procs.append(hcsp.Var(self.entry_proc_name(state)))
        procs.append(self.get_rec_entry_proc(dst))
        self.input_recieve_response(procs)
        self.get_output_data(procs)
        return hcsp.seq(procs)

    def convert_label(self, label, *, state=None, still_there_cond=None, still_there_tran=None):
        """Convert transition label to a triple of condition, condition action,
        and transition action.

        label : TransitionLabel - transition label to be converted.
        state : SF_State - current state, used only for determining temporal events
            in outgoing and inner transitions.
        still_there_cond : BExpr - when to continue execution of condition action.
        still_there_tran : BExpr - when to continue execution of transition action.

        """
        pre_acts, conds, cond_act, tran_act = [], [], hcsp.Skip(), hcsp.Skip()
        if label is not None:
           
            if isinstance(label,str):
                label=parser.transition_parser.parse(label)
            if label.event is not None:
                if isinstance(label.event, BroadcastEvent):
                    # Conversion of event condition E
                    conds.append(expr.conj(expr.RelExpr("!=", expr.AVar("EL"), expr.AConst([])),
                                           expr.RelExpr("==", expr.FunExpr("top", [expr.AVar("EL")]), expr.AConst(label.event.name))))
                elif isinstance(label.event, TemporalEvent):
                    act, e = self.convert_expr(label.event.expr)
                    pre_acts.append(act)
                    assert state is not None, "convert_label: temporal events only for edges from a state."
                    if label.event.temp_op == 'after':
                        if isinstance(label.event.event, AbsoluteTimeEvent):
                            if label.event.event.name == 'sec':
                                conds.append(expr.RelExpr(">=", expr.AVar(self.entry_time_name(state)), e))
                            else:
                                
                                raise NotImplementedError
                        elif isinstance(label.event.event,ImplicitEvent):
                            # raise NotImplementedError
                            if label.event.event.name == 'tick':
                                    conds.append(expr.RelExpr(">=",expr.AVar(self.entry_tick_name(state)),e))
                    else:
                        raise NotImplementedError
                else:
                    raise NotImplementedError('convert_label: unsupported event type')
            if label.cond is not None:
                act, hp_cond = self.convert_expr(label.cond)
                pre_acts.append(act)
                conds.append(hp_cond)
            if label.cond_act is not None:
                cond_act = self.convert_cmd(label.cond_act, still_there=still_there_cond)
            if label.tran_act is not None:
                tran_act = self.convert_cmd(label.tran_act, still_there=still_there_tran)
        return hcsp.seq(pre_acts), expr.conj(*conds), cond_act, tran_act

    def get_rec_entry_proc(self, state):
        """Return the process for recursively entering into state.
        
        Note this does not include entering into state itself, which is taken
        care of in get_entry_proc.

        """
        procs = []
        if state.children:
            if isinstance(state.children[0], AND_State):
                for child in state.children:
                    procs.append(hcsp.Var(self.entry_proc_name(child)))
                    procs.append(self.get_rec_entry_proc(child))

            elif isinstance(state.children[0], OR_State):
                # First, obtain what happens in default transition:
                default_tran = None
                for child in state.children:
                    if isinstance(child, OR_State) and child.default_tran:
                        pre_act, cond, cond_act, tran_act = self.convert_label(child.default_tran.label)
                        assert pre_act == hcsp.Skip() and cond == expr.true_expr, \
                            "get_rec_entry_proc: no condition on default transitions"
                        default_tran = hcsp.seq([
                            cond_act, tran_act, hcsp.Var(self.entry_proc_name(child)),
                            self.get_rec_entry_proc(child)])
                        break
                
                # Next, check if there are history junctions
                if isinstance(state, OR_State) and state.has_history_junc:
                    conds = []
                    hist_name = self.history_name(state)
                    for child in state.children:
                        if isinstance(child, OR_State):
                            conds.append((expr.RelExpr("==", expr.AVar(hist_name), expr.AConst(child.whole_name)),
                                          hcsp.seq([
                                              hcsp.Var(self.entry_proc_name(child)),
                                              self.get_rec_entry_proc(child)])))
                    procs.append(hcsp.ITE(conds, default_tran))
                else:
                    procs.append(default_tran)
            elif isinstance(state.children[0],Junction):
                default_tran = None
                for child in state.children:
                    if isinstance(child, Junction) and child.default_tran:
                        pre_act, cond, cond_act, tran_act = self.convert_label(child.default_tran.label)
                        assert pre_act == hcsp.Skip() and cond == expr.true_expr, \
                            "get_rec_entry_proc: no condition on default transitions"
                        default_tran = hcsp.seq([
                            cond_act, tran_act, hcsp.Var("J"+child.ssid)
                            ])
                        break
                procs.append(default_tran)
            else:
                raise TypeError
        return hcsp.seq(procs)

    def get_rec_exit_proc(self, state):
        """Return the process for recursively exiting from children of state.
        
        Note this does not include exiting from state itself, which is taken
        care of in get_exit_proc.
        
        """
        procs = []
        if state.children:
            if isinstance(state.children[0], AND_State):
                for child in reversed(state.children):
                    procs.append(self.get_rec_exit_proc(child))
                    procs.append(hcsp.Var(self.exit_proc_name(child)))
            elif isinstance(state.children[0], OR_State):
                ite = []
                for child in state.children:
                    if isinstance(child, OR_State):
                        ite.append((expr.RelExpr("==", expr.AVar(self.active_state_name(state)), expr.AConst(child.whole_name)),
                                    hcsp.seq([
                                        self.get_rec_exit_proc(child),
                                        hcsp.Var(self.exit_proc_name(child))])))
                procs.append(hcsp.ITE(ite))
            else:
                raise TypeError
        return hcsp.seq(procs)

    def get_during_proc(self, state):
        """During procedure for the given state.
        
        The procedure performs the following steps:
        - Check if there are outgoing transitions from the state. If one of them is
        valid, carry out the transition.
        - If none of the transitions are valid, perform the du action of the state.
        - Check if there are inner transitions from the state. If one of them is
        valid, carry out the transition.

        """
        if isinstance(state, OR_State):
            procs = []

            # Signal for whether one of the transitions is carried out
            done = state.whole_name + "_done"

            # Whether the state is still active
            still_there_cond = expr.RelExpr("==", expr.AVar(self.active_state_name(state.father)),
                                            expr.AConst(state.whole_name))

            # Whether the state has exited (so the parent state has no active states)
            still_there_tran = expr.RelExpr("==", expr.AVar(self.active_state_name(state.father)),
                                            expr.AConst(""))

            # First, check each of the outgoing transitions
            procs.append(hcsp.Assign(done, expr.AConst(0)))
            if state.out_trans:
                for i, tran in enumerate(state.out_trans):
                    src = self.chart.all_states[tran.src]
                    dst = self.chart.all_states[tran.dst]
                    pre_act, cond, cond_act, tran_act = self.convert_label(
                        tran.label, state=state, still_there_cond=still_there_cond,
                        still_there_tran=still_there_tran)

                    # Perform the condition action. If still in the current state
                    # afterwards, traverse the destination of the transition. Starting
                    # from the second transition, check whether still in the state.
                    act = hcsp.Sequence(
                        cond_act,
                        hcsp.Condition(still_there_cond, hcsp.seq([
                            self.get_traverse_state_proc(dst, src, tran_act),
                            hcsp.Assign(done, expr.AVar("_ret"))])))
                    if i == 0:
                        procs.append(hcsp.seq([pre_act, hcsp.Condition(cond, act)]))
                    else:
                        procs.append(hcsp.seq([pre_act, hcsp.Condition(
                            expr.conj(still_there_cond,
                                      expr.RelExpr("==", expr.AVar(done), expr.AConst(0)),
                                      cond),
                            act)]))

            # If still in the state, perform the during action.
            procs.append(hcsp.Condition(
                expr.conj(still_there_cond,
                          expr.RelExpr("==", expr.AVar(done), expr.AConst(0))),
                hcsp.Var(self.du_proc_name(state))))

            # Now, perform the inner transitions
            if state.inner_trans:
                for i, tran in enumerate(state.inner_trans):
                    src = self.chart.all_states[tran.src]
                    dst = self.chart.all_states[tran.dst]
                    pre_act, cond, cond_act, tran_act = self.convert_label(
                        tran.label, state=state, still_there_cond=still_there_cond,
                        still_there_tran=still_there_tran)

                    # Perform the condition action. If still in the current state
                    # afterwards, traverse the destination of the transition. Starting
                    # from the second transition, check whether still in the state.
                    act = hcsp.Sequence(
                        cond_act,
                        hcsp.Condition(still_there_cond, hcsp.seq([
                            self.get_traverse_state_proc(dst, src, tran_act),
                            hcsp.Assign(done, expr.AVar("_ret"))])))
                    if i == 0:
                        procs.append(hcsp.seq([pre_act, hcsp.Condition(cond, act)]))
                    else:
                        procs.append(hcsp.seq([pre_act, hcsp.Condition(
                            expr.conj(still_there_cond,
                                      expr.RelExpr("==", expr.AVar(done), expr.AConst(0)),
                                      cond),
                            act)]))

            # Set return value to done
            procs.append(self.return_val(expr.AVar(done)))
            return hcsp.seq(procs)

        elif isinstance(state, AND_State):
            # For AND-states, simply execute its during action.
            return hcsp.seq([
                hcsp.Var(self.du_proc_name(state)),
                self.return_val(expr.AConst(0))])

        else:
            raise TypeError("get_during_proc: state is not AND-state or OR-state.")

    def get_exit_proc(self, state):
        """Exit procedure from the given state.
        
        The procedure does only two things:
        - if the current state is an OR-state, clear the corresponding active state
        variable.
        - if the current state has implicit or absolute time event transitions, reset
          the corresponding counter to -1.
        - call the ex action of state.

        """
        procs = []
        
        # Perform ex action
        procs.append(hcsp.Var(self.ex_proc_name(state)))

        # Set counter for implicit or absolute time events
        if state.ssid in self.implicit_events:
            procs.append(hcsp.Assign(self.entry_tick_name(state), expr.AConst(-1)))
        if state.ssid in self.absolute_time_events:
            procs.append(hcsp.Assign(self.entry_time_name(state), expr.AConst(-1)))

        # Set the activation variable
        if isinstance(state, OR_State):
            procs.append(hcsp.Assign(self.active_state_name(state.father), expr.AConst("")))
            
        return hcsp.seq(procs)

    def get_rec_during_proc(self, state):
        """Return the process for recursively executing an state."""
        procs = []

        # First, execute the during procedure, the return value is whether
        # some transition (outgoing or inner) is carried out.
        procs.append(hcsp.Var(self.during_proc_name(state)))
        to_sub_cond = expr.RelExpr("==", expr.AVar("_ret"), expr.AConst(0))
        
        # Next, recursively execute child states
        if state.children:
            if isinstance(state.children[0], AND_State):
                for child in state.children:
                    procs.append(self.get_rec_during_proc(child))
            elif isinstance(state.children[0], OR_State):
                ite = []
                for child in state.children:
                    if isinstance(child, OR_State):
                        ite.append((expr.RelExpr("==", expr.AVar(self.active_state_name(state)), expr.AConst(child.whole_name)),
                                    self.get_rec_during_proc(child)))
                procs.append(hcsp.Condition(to_sub_cond, hcsp.ITE(ite)))
            elif isinstance(state.children[0],Junction):
                 procs.append(hcsp.Skip())
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
                    dst = self.chart.all_states[tran.dst]
                    pre_act, cond, cond_act, tran_act = self.convert_label(tran.label)
                    act = self.get_traverse_state_proc(dst, init_src, hcsp.seq([init_tran_act, tran_act]))
                    act = hcsp.seq([cond_act, act, hcsp.Assign(done, expr.AVar("_ret"))])
                    if i == 0:
                        procs.append(hcsp.seq([pre_act, hcsp.Condition(cond, act)])),
                    else:
                        procs.append(hcsp.seq([pre_act, hcsp.Condition(
                            expr.conj(expr.RelExpr("==", expr.AVar(done), expr.AConst(0)), cond),
                            act)]))
                procs.append(self.return_val(expr.AVar(done)))
                proc = hcsp.seq(procs)
                self.junction_map[state.ssid][(init_src.ssid, init_tran_act)] = (cur_name, proc)
            return hcsp.Var(self.junction_map[state.ssid][(init_src.ssid, init_tran_act)][0])

        else:
            raise TypeError("get_junction_proc")

    def convert_graphical_function_junc(self, junc):
        """Conversion for junctions in graphical functions.

        These junctions are much simpler, since the function returns when
        reaching dead-end (rather than backtracking), and there are no transition
        actions.

        """
        if not junc.out_trans:
            return hcsp.Skip()
        
        procs = []
        done = "J" + junc.ssid + "_done"
        procs.append(hcsp.Assign(done, expr.AConst(0)))
        for i, tran in enumerate(junc.out_trans):
            pre_act, cond, cond_act, tran_act = self.convert_label(tran.label)
            assert tran_act == hcsp.Skip(), \
                "convert_graphical_function_junc: no transition action in graphical functions."
            act = hcsp.seq([cond_act, hcsp.Var("J" + tran.dst),hcsp.Assign(done, expr.AConst(1))])
            if i == 0:
                procs.append(hcsp.seq([pre_act, hcsp.Condition(cond, act)]))
            else:
                procs.append(hcsp.seq([pre_act, hcsp.Condition(
                    expr.conj(expr.RelExpr("==", expr.AVar(done), expr.AConst(0)), cond),
                    act)]))
        return hcsp.seq(procs)

    def convert_graphical_function(self, proc):
        """Generate all procedures corresponding to a graphical function."""
        res = dict()
        for junc in proc.junctions:
            res["J" + junc.ssid] = self.convert_graphical_function_junc(junc)

        # Now process default transition
        pre_act, cond, cond_act, tran_act = self.convert_label(proc.default_tran.label)
        dst = proc.default_tran.dst
        assert pre_act == hcsp.Skip() and cond == expr.true_expr, \
            "convert_graphical_function: no condition on default transitions"
        assert tran_act == hcsp.Skip(), "convert_graphical_function: no transition action in graphical functions"
        res[proc.name] = hcsp.seq([cond_act, hcsp.Var("J" + proc.default_tran.dst)])
        return res

    def init_name(self):
        return "init_" + self.chart.name

    def exec_name(self):
        return "exec_" + self.chart.name

    def get_init_proc(self):
        """Initialization procedure."""
        procs = []

        # Initialize event stack
        procs.append(hcsp.Assign("EL", expr.AConst([])))
        
        # Read data store variable
        for vname, info in self.data.items():
            if info.scope == "DATA_STORE_MEMORY_DATA":
                procs.append(hcsp.InputChannel("read_" + self.chart.name + "_" + vname, expr.AVar(vname)))

        # Initialize variables
        for vname, info in self.data.items():
            if info.value is not None and info.scope != "INPUT_DATA" and info.scope != "DATA_STORE_MEMORY_DATA":
                pre_act, val = self.convert_expr(info.value)
                procs.append(hcsp.seq([pre_act, hcsp.Assign(vname, val)]))

        # Read input data
        self.get_input_data(procs)

        # Give response
        self.input_recieve_response(procs)

        # Write output data
        self.get_output_data(procs)

        # Initialize history junction
        for ssid, state in self.chart.all_states.items():
            if isinstance(state, OR_State) and state.has_history_junc:
                procs.append(hcsp.Assign(self.history_name(state), expr.AConst("")))
        
        # Initialize counter for implicit and absolute time events
        for ssid in self.implicit_events:
            tick_name = self.entry_tick_name(self.chart.all_states[ssid])
            procs.append(hcsp.Assign(expr.AVar(tick_name), expr.AConst(-1)))
        for ssid in self.absolute_time_events:
            time_name = self.entry_time_name(self.chart.all_states[ssid])
            procs.append(hcsp.Assign(expr.AVar(time_name), expr.AConst(-1)))

        # Recursive entry into diagram
        self.get_input_data(procs)
        procs.append(hcsp.Var(self.entry_proc_name(self.chart.diagram)))
        
        procs.append(self.get_rec_entry_proc(self.chart.diagram))

        self.input_recieve_response(procs)
        self.get_output_data(procs)
        
        # Write data store variable
        for vname, info in self.data.items():
            if info.scope == "DATA_STORE_MEMORY_DATA":
                procs.append(hcsp.OutputChannel("write_" + self.chart.name + "_" + vname, expr.AVar(vname)))

        return hcsp.seq(procs)

    def get_exec_proc(self):
        return self.get_rec_during_proc(self.chart.diagram)

    def get_iteration(self):
        procs = []
       
        self.get_input_data(procs)

        # Read data store variable
        for vname, info in self.data.items():
            if info.scope == "DATA_STORE_MEMORY_DATA":
                procs.append(hcsp.InputChannel("read_" + self.chart.name + "_" + vname, expr.AVar(vname)))

        # Call during procedure of the diagram
        procs.append(hcsp.Var(self.exec_name()))

        # Write data store variable
        for vname, info in self.data.items():
            if info.scope == "DATA_STORE_MEMORY_DATA":
                procs.append(hcsp.OutputChannel("write_" + self.chart.name + "_" + vname, expr.AVar(vname)))

        # Wait the given sample time
        procs.append(hcsp.Wait(expr.AConst(self.sample_time)))
        
        # Update counter for absolute time events
        for ssid in self.absolute_time_events:
            time_name = self.entry_time_name(self.chart.all_states[ssid])
            procs.append(hcsp.Condition(
                expr.RelExpr("!=", expr.AVar(time_name), expr.AConst(-1)),
                hcsp.Assign(
                    expr.AVar(time_name),
                    expr.PlusExpr(["+", "+"], [expr.AVar(time_name), expr.AConst(self.sample_time)]))))

        return hcsp.seq(procs)

    def get_procs(self):
        """Returns the list of procedures."""
        all_procs = dict()

        # Procedures for states
        for ssid, state in self.chart.all_states.items():
            if isinstance(state, (AND_State, OR_State)):
                all_procs[self.en_proc_name(state)] = self.get_en_proc(state)
                all_procs[self.du_proc_name(state)] = self.get_du_proc(state)
                all_procs[self.ex_proc_name(state)] = self.get_ex_proc(state)
                all_procs[self.entry_proc_name(state)] = self.get_entry_proc(state)
                all_procs[self.during_proc_name(state)] = self.get_during_proc(state)
                all_procs[self.exit_proc_name(state)] = self.get_exit_proc(state)

        # Procedures for junctions        
        for ssid, junc_map in self.junction_map.items():
            for _, (name, proc) in junc_map.items():
                all_procs[name] = proc

        # Procedures for graphical functions
        for name, proc in self.procedures.items():
            if isinstance(proc, GraphicalFunction):
                all_procs.update(self.convert_graphical_function(proc))

        # Initialization and iteration
        all_procs[self.init_name()] = self.get_init_proc()
        all_procs[self.exec_name()] = self.get_exec_proc()

        return all_procs

    def get_toplevel_process(self):
        """Returns the top-level process for chart."""
        return hcsp.Sequence(
            hcsp.Var(self.init_name()),
            hcsp.Loop(self.get_iteration()))


def convertDataStoreMemory(dsm, charts):
    """Conversion function for data store memory.
    
    If data store memory is present, it is responsible for synchronizing
    the order of execution of different Stateflow charts. It performs
    read-write for each chart in alphabetical order, ensuring that
    initialization and execution of charts proceed in the same order.

    """
    _, init_value = convert.convert_expr(dsm.value)
    dsm_name = dsm.dataStoreName
    chart_names = sorted(list(chart.name for chart in charts))
    cmds = []
    for name in chart_names:
        cmds.append(hcsp.OutputChannel("read_" + name + "_" + dsm_name, expr.AVar(dsm_name)))
        cmds.append(hcsp.InputChannel("write_" + name + "_" + dsm_name, expr.AVar(dsm_name)))
    return hcsp.Sequence(
        hcsp.Assign(expr.AVar(dsm.dataStoreName), init_value),
        hcsp.Loop(hcsp.seq(cmds))
    )

def get_continuous_proc(continuous): 
    return translate_continuous(continuous)
        
