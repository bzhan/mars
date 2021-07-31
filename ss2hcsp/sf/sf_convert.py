"""Converting a Stateflow chart to HCSP process."""

from ss2hcsp.sl import get_hcsp
from ss2hcsp.hcsp.pprint import pprint
from ss2hcsp.sf.sf_chart import SF_Chart
from ss2hcsp.sf.sf_state import OR_State, AND_State, Junction, GraphicalFunction
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp.parser import bexpr_parser
from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import optimize
from ss2hcsp.hcsp.pprint import pprint
from ss2hcsp.matlab import convert
from ss2hcsp.matlab import parser
from ss2hcsp.matlab import function


def get_common_ancestor(state0, state1, out_trans=True):
    if state0 == state1:
        assert state0.father == state1.father
        if out_trans:
            return state0.father
        else:  # inner_trans
            return state0

    state_to_root = []
    cursor = state0
    while cursor:
        state_to_root.append(cursor)
        cursor = cursor.father

    cursor = state1
    while cursor not in state_to_root:
        cursor = cursor.father
    return cursor


class SFConvert:
    """Conversion from Stateflow chart to HCSP process.
    
    chart : SF_Chart
    chart_parameters - additional parameters.
    has_signal : bool - whether to put start/end signals.
    translate_io : bool - whether input/output should be translated.

    """
    def __init__(self, chart=None, *, chart_parameters=None, has_signal=False,
                 shared_chans=None, translate_io=True):
        self.chart = chart
        if chart_parameters is None:
            chart_parameters = dict()
        self.chart_parameters = chart_parameters
        self.translate_io = translate_io
        self.has_signal = has_signal

        self.shared_chans = []
        if shared_chans:
            self.shared_chans = shared_chans

        # List of data variables
        self.data = dict()
        if 'data' in self.chart_parameters:
            self.data = self.chart_parameters['data']
        self.events = dict()
        if 'event_dict' in self.chart_parameters:
            self.events = self.chart_parameters['event_dict']
        self.messages = dict()
        if 'message_dict' in self.chart_parameters:
            self.messages = self.chart_parameters['message_dict']

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

        # List of all states that are parents of OR-states
        self.or_fathers = set()
        for ssid, state in self.chart.all_states.items():
            if isinstance(state, OR_State):
                self.or_fathers.add(state.father.ssid)
        self.or_fathers = sorted(list(self.or_fathers))

        def get_state(state, name):
            if len(name) == 0:
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
            return convert.convert_expr(e, arrays=self.data.keys(), procedures=self.procedures,
                                        messages=self.messages)
        self.convert_expr = convert_expr

        def convert_cmd(cmd, *, still_there=None):
            return convert.convert_cmd(
                cmd, raise_event=self.raise_event, procedures=self.procedures,
                still_there=still_there, arrays=self.data.keys(), events=self.events.keys(),
                messages=self.messages)
        self.convert_cmd = convert_cmd

        # Dictionary mapping junction ID and (init_src, tran_act) to the
        # pair (name, proc).
        self.junction_map = dict()
        for ssid, state in self.chart.all_states.items():
            if isinstance(state, Junction) and not state.default_tran:
                self.junction_map[ssid] = dict()
            elif isinstance(state, Junction) and state.default_tran and not state.out_trans:
                self.junction_map[ssid] = {"J"+ssid: ("J"+ssid, hcsp.Skip())}

        # Set of local variables. These are considered inactive at the end of
        # procedures (to help with code optimization).
        self.local_vars = set()

        # Find all states which has a transition guarded by temporal event.
        self.temporal_guards = dict()
        for ssid, state in self.chart.all_states.items():
            if isinstance(state, OR_State) and state.out_trans:
                for tran in state.out_trans:
                    ev = tran.label.event
                    if ev is not None and isinstance(ev, function.TemporalEvent):
                        if tran.src not in self.temporal_guards:
                            self.temporal_guards[tran.src] = []
                        self.temporal_guards[tran.src].append(ev)
            if isinstance(state, (AND_State, OR_State)) and state.inner_trans:
                for tran in state.inner_trans:
                    ev = tran.label.event
                    if ev is not None and isinstance(ev, function.TemporalEvent):
                        if tran.src not in self.temporal_guards:
                            self.temporal_guards[tran.src] = []
                        self.temporal_guards[tran.src].append(ev)

        # Detect whether a state has implicit or absolute time event.
        self.implicit_events = set()
        self.absolute_time_events = set()
        for ssid in self.chart.all_states:
            if ssid in self.temporal_guards:
                for temp_event in self.temporal_guards[ssid]:
                    if isinstance(temp_event.event, function.ImplicitEvent):
                        self.implicit_events.add(ssid)
                    elif isinstance(temp_event.event, function.AbsoluteTimeEvent):
                        self.absolute_time_events.add(ssid)
        self.implicit_events = sorted(list(self.implicit_events))
        self.absolute_time_events = sorted(list(self.absolute_time_events))

        # Process the derivative assignments. ode_map is a mapping from
        # states to differential equations. Each differential equation
        # x_dot = e is represented by a pair (x, e).
        self.ode_map = dict()
        for ssid, state in self.chart.all_states.items():
            state.new_du = []
            if isinstance(state, (AND_State, OR_State)) and state.du:
                for action in state.du:
                    if isinstance(action, function.Assign) and isinstance(action.lname, function.Var):
                        var_name = action.lname.name
                        if var_name.endswith("_dot"):
                            if ssid not in self.ode_map:
                                self.ode_map[ssid] = list()
                            self.ode_map[ssid].append((var_name[:len(var_name)-4], action.expr))
                        else:
                            state.new_du.append(action)
                    else:
                        state.new_du.append(action)
            state.du = state.new_du

    def return_val(self, val):
        return hcsp.Assign("_ret", val)

    def raise_event(self, event):
        
        if isinstance(event, function.BroadcastEvent):
            # Raise broadcast event
            return hcsp.seq([
                hcsp.Assign("EL", expr.FunExpr("push", [expr.AVar("EL"), expr.AConst(event.name)])),
                hcsp.Var(self.exec_name()),
                hcsp.Assign("EL", expr.FunExpr("pop", [expr.AVar("EL")]))
            ])

        elif isinstance(event, function.DirectedEvent):
            # First, find the innermost state name and event
            state_name_path = list()
            st_name, ev = event.state_name, event.event
            state_name_path.append(st_name)
            while isinstance(ev, function.DirectedEvent):
                st_name, ev = ev.state_name, ev.event
                state_name_path.append(st_name)
            dest_state = self.get_state_by_path(state_name_path)
            return hcsp.seq([
                hcsp.Assign("EL", expr.FunExpr("push", [expr.AVar("EL"), expr.AConst(ev.name)])),
                self.get_rec_during_proc(dest_state),
                hcsp.Assign("EL", expr.FunExpr("pop", [expr.AVar("EL")]))
            ])
        
        elif isinstance(event, function.Message):
            # Raise messages
            if str(event) in self.messages.keys():
                message = self.messages[str(event)]
                if message.scope == "OUTPUT_DATA":
                    for port_id, out_var in self.chart.port_to_out_var.items():
                        if str(out_var) == message.name:
                            lines = self.chart.src_lines[port_id]
                            for line in lines:
                                ch_name = "ch_" + line.name + "_" + str(line.branch) + "_out"
                                return hcsp.OutputChannel(ch_name , expr.AConst(dict(message)))
                elif message.scope == "LOCAL_DATA": 
                    return hcsp.seq([
                                hcsp.Assign("LQU", expr.FunExpr("put", [expr.AConst("LQU"),expr.AVar("LQU"), expr.AConst(dict(message))]))])

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

    def get_still_there_cond(self, state):
        """Returns the condition that signals the state is active. This is used
        as the early return check for condition actions, as well as entry and
        exit actions of a state.
        
        """
        # Find the first state in the hierarchy that is an OR-state. If
        # not found, then always true.
        while not isinstance(state, OR_State):
            if state.father is None:
                return expr.BConst(True)
            state = state.father

        return expr.RelExpr("==", expr.AVar(self.active_state_name(state.father)),
                            expr.AConst(state.whole_name))
    
    def get_ancestor_empty_cond(self, ancestor):
        """Returns the condition that the ancestor is active and none of its
        sub-state is active. This is used as the early return check for
        transition actions.
        
        """
        if any(isinstance(child, OR_State) for child in ancestor.children):
            still_there = expr.RelExpr("==", expr.AVar(self.active_state_name(ancestor)), expr.AConst(""))
        else:
            still_there = expr.BConst(True)

        return expr.LogicExpr("&&", still_there, self.get_still_there_cond(ancestor))

    def get_en_proc(self, state):
        # For entry procedure, the early return logic is that the state that
        # is entered should remain active.
        return self.convert_cmd(state.en, still_there=self.get_still_there_cond(state))

    def get_du_proc(self, state):
        procs = []
        if state.ssid in self.implicit_events:
            tick_name = self.entry_tick_name(state)
            procs.append(hcsp.Condition(
                    expr.RelExpr("!=", expr.AVar(tick_name), expr.AConst(-1)),
                    hcsp.Assign(
                        expr.AVar(tick_name),
                        expr.PlusExpr(["+", "+"], [expr.AVar(tick_name), expr.AConst(1)]))))

        return hcsp.Sequence(self.convert_cmd(state.du), *procs)

    def get_ex_proc(self, state):
        # For exit procedure, the early return logic is that the state that
        # is exited should remain active.
        return self.convert_cmd(state.ex, still_there=self.get_still_there_cond(state))

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

    def get_input_data(self):
        """Obtain a list of processes for chart input."""
        procs = []
        if self.translate_io:
            for port_id, in_var in self.chart.port_to_in_var.items():
                if str(in_var) not in self.messages.keys():
                    line = self.chart.dest_lines[port_id]
                    ch_name = "ch_" + line.name + "_" + str(line.branch)
                    if ch_name in self.shared_chans:
                        ch_name += "_in"
                    procs.append(hcsp.InputChannel(ch_name, expr.AVar(in_var)))
        return procs

    def get_output_data(self):
        """Obtain a list of processes for chart output."""
        procs = []
        if self.translate_io:
            for port_id, out_var in self.chart.port_to_out_var.items():
                if str(out_var) not in self.messages.keys():
                    lines = self.chart.src_lines[port_id]
                    for line in lines:
                        ch_name = "ch_" + line.name + "_" + str(line.branch)
                        if ch_name in self.shared_chans:
                            ch_name += "_out"
                        procs.append(hcsp.OutputChannel(ch_name, expr.AVar(out_var)))
        return procs

    def get_transition_proc(self, src, dst, tran_act=None, *, out_trans=True):
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
        ancestor = get_common_ancestor(src, dst, out_trans=out_trans)
        procs = []

        # Exit states from src to ancestor (not including ancestor)
        exit_procs = []
        exit_procs.append(self.get_rec_exit_proc(src))
        for state in self.get_chain_to_ancestor(src, ancestor):
            exit_procs.append(hcsp.Var(self.exit_proc_name(state)))

        # Whether the source state is still active
        procs.append(hcsp.Condition(self.get_still_there_cond(src), hcsp.seq(exit_procs)))

        # Perform transition action
        procs.append(self.convert_cmd(tran_act, still_there=self.get_ancestor_empty_cond(ancestor)))

        # Enter states from ancestor to state1
        entry_procs = []
        for state in reversed(self.get_chain_to_ancestor(dst, ancestor)):
            entry_procs.append(hcsp.Var(self.entry_proc_name(state)))
        entry_procs.append(self.get_rec_entry_proc(dst))

        procs.append(hcsp.Condition(self.get_ancestor_empty_cond(ancestor), hcsp.seq(entry_procs)))

        return hcsp.seq(procs)

    def convert_label(self, label, *, state=None, still_there=None):
        """Convert transition label to a triple of pre-action, condition,
        and condition action. The transition action is not converted (access the
        raw action using label.tran_act).

        label : TransitionLabel - transition label to be converted.
        state : SF_State - current state, used only for determining temporal events
            in outgoing and inner transitions.
        still_there : BExpr - when to continue execution of condition action.

        """
        pre_acts, conds, cond_act = [], [], hcsp.Skip()
        if label.event is not None:
            if isinstance(label.event, function.BroadcastEvent) and \
                str(label.event) not in self.messages.keys():
                # Conversion for event condition E
                for n,e in self.events.items():
                    if e.name == str(label.event.name):
                        if e.scope == "INPUT_EVENT" and e.trigger == "EITHER_EDGE_EVENT":
                            conds.append(expr.RelExpr("!=",expr.AVar("osag"),expr.AVar("last")))

                        else:
                            conds.append(expr.conj(expr.RelExpr("!=", expr.AVar("EL"), expr.AConst([])),
                                               expr.RelExpr("==", expr.FunExpr("top", [expr.AVar("EL")]), expr.AConst(label.event.name))))
            
            elif isinstance(label.event, function.TemporalEvent):
                # Conversion for temporal events
                act, e = self.convert_expr(label.event.expr)
                pre_acts.append(act)
                assert state is not None, "convert_label: temporal events only for edges from a state."

                # First, find the comparison operator
                if label.event.temp_op == 'after':
                    op_str = '>='
                elif label.event.temp_op == 'before':
                    op_str = '<'
                elif label.event.temp_op == 'at':
                    op_str = '=='
                else:
                    raise NotImplementedError

                # Next, find units
                if isinstance(label.event.event, function.AbsoluteTimeEvent):
                    if label.event.event.name == 'sec':
                        conds.append(expr.RelExpr(op_str, expr.AVar(self.entry_time_name(state)), e))
                    else:
                        raise NotImplementedError
                elif isinstance(label.event.event, function.ImplicitEvent):
                    if label.event.event.name == 'tick':
                        conds.append(expr.RelExpr(op_str, expr.AVar(self.entry_tick_name(state)), e))
                    else:
                        raise NotImplementedError

            elif str(label.event) in self.messages.keys():
                # Conversion for messages
                message = self.messages[str(label.event)]
                if message.scope == "INPUT_DATA":
                    conds.append(expr.conj(expr.RelExpr("!=", expr.AVar("IQU"), expr.AConst(())),
                                        expr.RelExpr(">", expr.FunExpr("exist", [expr.AConst("IQU"),expr.AVar("IQU"), expr.AConst(label.event.name)]),expr.AConst(-1))))
                   
                elif message.scope == "LOCAL_DATA":
                    conds.append(expr.conj(expr.RelExpr("!=", expr.AVar("LQU"), expr.AConst(())),
                                        expr.RelExpr(">", expr.FunExpr("exist", [expr.AConst("LQU"),expr.AVar("LQU"), expr.AConst(label.event.name)]),expr.AConst(-1))))
                  
            else:
                raise NotImplementedError('convert_label: unsupported event type')

        if label.cond is not None:
            act, hp_cond = self.convert_expr(label.cond)
            pre_acts.append(act)
            conds.append(hp_cond)

        cond_act = self.convert_cmd(label.cond_act, still_there=still_there)
        return hcsp.seq(pre_acts), expr.conj(*conds), cond_act

    def get_rec_entry_proc(self, state):
        """Return the process for recursively entering into state.
        
        Note this does not include entering into state itself, which is taken
        care of in get_entry_proc.

        """
        procs = []
        if state.children:
            if any(isinstance(child, AND_State) for child in state.children):
                for child in state.children:
                    procs.append(hcsp.Var(self.entry_proc_name(child)))
                    procs.append(self.get_rec_entry_proc(child))
            elif any(isinstance(child, OR_State) for child in state.children):
                # First, obtain what happens in default transition:
                default_tran = None
                for child in state.children:
                    if isinstance(child, OR_State) and child.default_tran:
                        pre_act, cond, cond_act = \
                            self.convert_label(child.default_tran.label)
                        tran_act = self.convert_cmd(child.default_tran.label.tran_act)
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
            else:
                pass  # Junction only
        return hcsp.seq(procs)

    def get_rec_exit_proc(self, state):
        """Return the process for recursively exiting from children of state.
        
        Note this does not include exiting from state itself, which is taken
        care of in get_exit_proc.
        
        """
        procs = []
        if state.children:
            if any(isinstance(child, AND_State) for child in state.children):
                for child in reversed(state.children):
                    procs.append(self.get_rec_exit_proc(child))
                    procs.append(hcsp.Var(self.exit_proc_name(child)))
            elif any(isinstance(child, OR_State) for child in state.children):
                ite = []
                for child in state.children:
                    if isinstance(child, OR_State):
                        ite.append((expr.RelExpr("==", expr.AVar(self.active_state_name(state)), expr.AConst(child.whole_name)),
                                    hcsp.seq([
                                        self.get_rec_exit_proc(child),
                                        hcsp.Var(self.exit_proc_name(child))])))
                procs.append(hcsp.ITE(ite))
            else:
                pass  # Junction only
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
            self.local_vars.add(done)

            # Whether the state is still active
            still_there_cond = self.get_still_there_cond(state)

            # First, check each of the outgoing transitions
            procs.append(hcsp.Assign(done, expr.AConst(0)))
            if state.out_trans:
                for i, tran in enumerate(state.out_trans):
                    src = self.chart.all_states[tran.src]
                    dst = self.chart.all_states[tran.dst]

                    ancestor = get_common_ancestor(src, dst, out_trans=True)
                    still_there_tran = self.get_ancestor_empty_cond(ancestor)
                    pre_act, cond, cond_act = self.convert_label(
                        tran.label, state=state, still_there=still_there_cond)

                    # Perform the condition action. If still in the current state
                    # afterwards, traverse the destination of the transition. Starting
                    # from the second transition, check whether still in the state.
                    act = hcsp.Sequence(
                         cond_act,
                        hcsp.Condition(still_there_cond, hcsp.seq([
                            self.get_traverse_state_proc(dst, src, tran.label.tran_act, out_trans=True),
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
                    ancestor = get_common_ancestor(src, dst, out_trans=False)
                    still_there_tran = self.get_ancestor_empty_cond(ancestor)
                    pre_act, cond, cond_act = self.convert_label(
                        tran.label, state=state, still_there=still_there_cond)

                    # Perform the condition action. If still in the current state
                    # afterwards, traverse the destination of the transition. For every
                    # transition, check whether one of the existing transitions has aleady
                    # been carried out.
                    act = hcsp.Sequence(
                        cond_act,
                        hcsp.Condition(still_there_cond, hcsp.seq([
                            self.get_traverse_state_proc(dst, src, tran.label.tran_act, out_trans=False),
                            hcsp.Assign(done, expr.AVar("_ret"))])))

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
        
        exit_procs = []
        # Set counter for implicit or absolute time events
        if state.ssid in self.implicit_events:
            exit_procs.append(hcsp.Assign(self.entry_tick_name(state), expr.AConst(-1)))
        if state.ssid in self.absolute_time_events:
            exit_procs.append(hcsp.Assign(self.entry_time_name(state), expr.AConst(-1)))

        # Set the activation variable
        if isinstance(state, OR_State):
            exit_procs.append(hcsp.Assign(self.active_state_name(state.father), expr.AConst("")))

        procs.append(hcsp.Condition(self.get_still_there_cond(state), hcsp.seq(exit_procs)))
        return hcsp.seq(procs)

    def get_rec_during_proc(self, state):
        """Return the process for recursively executing an state."""
        procs = []

        # First, execute the during procedure, the return value is whether
        # some transition (outgoing or inner) is carried out.
        procs.append(hcsp.Var(self.during_proc_name(state)))
        to_sub_cond = expr.RelExpr("==", expr.AVar("_ret"), expr.AConst(0))
        
        # Next, recursively execute child states
        if any(isinstance(child, AND_State) for child in state.children):
            for child in state.children:
                procs.append(self.get_rec_during_proc(child))
        elif any(isinstance(child, OR_State) for child in state.children):
            ite = []
            for child in state.children:
                if isinstance(child, OR_State):
                    ite.append((expr.RelExpr("==", expr.AVar(self.active_state_name(state)), expr.AConst(child.whole_name)),
                                self.get_rec_during_proc(child)))
            procs.append(hcsp.Condition(to_sub_cond, hcsp.ITE(ite)))
        else:
            pass  # Junction only
        return hcsp.seq(procs)

    def get_traverse_state_proc(self, state, init_src, tran_act, *, out_trans=False):
        """Obtain the procedure for traversing a state or junction, given
        the source state and existing transition actions.

        state : [OR_State, Junction] - current state or junction.
        init_src : str - name of the initial source state.
        tran_act : function.Command - already accumulated transition actions.
            Note this is NOT yet converted to HCSP.

        This function returns the code of the procedure, and memoize results
        for junctions in the dictionary junction_map.

        """
        assert isinstance(init_src, OR_State), "get_traverse_state_proc: source is not an OR_State"

        if isinstance(state, OR_State):
            # If reached an OR-state, carry out the transition from src to
            # the current state, with the accumulated transition actions in
            # the middle. Then return 1 for successfully reaching a state.
            return hcsp.seq([
                self.get_transition_proc(init_src, state, tran_act, out_trans=out_trans),
                self.return_val(expr.AConst(1))])

        elif isinstance(state, Junction):
            # If reached a junction, try each of the outgoing edges from the
            # junction.
            if not state.out_trans:
                # Transition unsuccessful.
                return self.return_val(expr.AConst(0))

            if (init_src.ssid, tran_act, out_trans) not in self.junction_map[state.ssid]:
                # Put in placeholder and reserve name
                cur_name = "J" + state.ssid + "_" + str(len(self.junction_map[state.ssid]) + 1)
                self.junction_map[state.ssid][(init_src.ssid, tran_act, out_trans)] = (cur_name, None)
                procs = []
                done = "J" + state.ssid + "_done"
                self.local_vars.add(done)
                procs.append(hcsp.Assign(done, expr.AConst(0)))

                # Early return logic for condition action: check whether
                # the initial source is still active.
                still_there_cond = self.get_still_there_cond(init_src)

                for i, tran in enumerate(state.out_trans):
                    dst = self.chart.all_states[tran.dst]

                    pre_act, cond, cond_act = \
                        self.convert_label(tran.label, still_there=still_there_cond)
                    # if isinstance(cond,expr.BConst):
                    #     cond=expr.RelExpr("==",expr.AVar(str(cond)),expr.AConst(1))
                    act = self.get_traverse_state_proc(
                        dst, init_src, function.seq([tran_act, tran.label.tran_act]), out_trans=out_trans)
                    act = hcsp.seq([ cond_act, act, hcsp.Assign(done, expr.AVar("_ret"))])
                    if i == 0:
                        procs.append(hcsp.seq([pre_act, hcsp.Condition(cond, act)])),
                    else:
                        procs.append(hcsp.seq([pre_act, hcsp.Condition(
                            expr.conj(expr.RelExpr("==", expr.AVar(done), expr.AConst(0)), cond),
                            act)]))
                procs.append(self.return_val(expr.AVar(done)))
                proc = hcsp.seq(procs)
                self.junction_map[state.ssid][(init_src.ssid, tran_act, out_trans)] = (cur_name, proc)
            return hcsp.Var(self.junction_map[state.ssid][(init_src.ssid, tran_act, out_trans)][0])

        else:
            raise TypeError("get_junction_proc")

    def convert_graphical_function_junc(self, junc):
        """Conversion for junctions in graphical functions.

        These junctions are much simpler, compared to junctions for
        transitioning between states, since the function returns when
        reaching dead-end (rather than backtracking), and there are no
        transition actions.

        """
        if not junc.out_trans:
            return hcsp.Skip()
        
        procs = []
        done = "J" + junc.ssid + "_done"
        self.local_vars.add(done)
        procs.append(hcsp.Assign(done, expr.AConst(0)))
        for i, tran in enumerate(junc.out_trans):
            pre_act, cond, cond_act= self.convert_label(tran.label)

            # if isinstance(cond,expr.BConst):
            #     cond=expr.RelExpr("==",expr.AVar(str(cond)),expr.AConst(1))
            assert tran.label.tran_act == function.Skip(), \
                "convert_graphical_function_junc: no transition action in graphical functions."
            act = hcsp.seq([ cond_act, hcsp.Var("J" + tran.dst),hcsp.Assign(done, expr.AConst(1))])
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
        pre_act, cond, cond_act = self.convert_label(proc.default_tran.label)
        dst = proc.default_tran.dst
        assert pre_act == hcsp.Skip() and cond == expr.true_expr, \
            "convert_graphical_function: no condition on default transitions"
        assert proc.default_tran.label.tran_act == function.Skip(), \
            "convert_graphical_function: no transition action in graphical functions"
        res[proc.name] = hcsp.seq([ cond_act, hcsp.Var("J" + proc.default_tran.dst)])
        return res

    def init_name(self):
        return "init_" + self.chart.name

    def exec_name(self):
        return "exec_" + self.chart.name

    def get_init_proc(self):
        """Initialization procedure."""
        procs = []

        # Start signal
        if self.has_signal:
            procs.append(hcsp.InputChannel("start_" + self.chart.name))

        # Initialize event stack
        procs.append(hcsp.Assign("EL", expr.AConst([])))
        procs.append(hcsp.Assign("IQU", expr.AConst(())))
        procs.append(hcsp.Assign("LQU", expr.AConst(())))
        for n,e in  self.events.items():
            if e.scope == "INPUT_EVENT" and e.trigger =="EITHER_EDGE_EVENT":
                procs.append(hcsp.InputChannel("ch_clock", expr.AVar("osag")))
                procs.append(hcsp.Assign(expr.AVar("last"),expr.AVar("osag")))

        # Input data
        procs.extend(self.get_input_data())

        # Input from DSM
        for vname, info in self.data.items():
            if info.scope == "DATA_STORE_MEMORY_DATA":
                procs.append(hcsp.InputChannel(vname + "_in", expr.AVar(vname)))
        
        # Initialize messages
        for name, info in self.messages.items():
            if info.scope in ("LOCAL_DATA", "OUTPUT_DATA"):
                procs.append(hcsp.Assign(expr.AVar(name), expr.AConst(dict(info))))

        # Initialize variables
        for vname, info in self.data.items():
            if info.value is not None and info.scope in ("LOCAL_DATA", "OUTPUT_DATA", "CONSTANT_DATA"):
                pre_act, val = self.convert_expr(info.value)
                procs.append(hcsp.seq([pre_act, hcsp.Assign(vname, val)]))

        # Initialize state
        for or_father in self.or_fathers:
            procs.append(hcsp.Assign(self.active_state_name(self.chart.all_states[or_father]), expr.AConst("")))

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

        # Read messages
        for port_id, out_var in self.chart.port_to_in_var.items():
            if str(out_var) in self.messages.keys():
                mes = self.messages[str(out_var)]
                if mes.scope == "INPUT_DATA":
                    line = self.chart.dest_lines[port_id]
                    ch_name = "ch_" + line.name + "_" + str(line.branch) + "_in"
                    procs.append(hcsp.InputChannel(ch_name , expr.AVar(out_var)))
                    procs.append(hcsp.Assign("IQU", expr.FunExpr("put", [expr.AConst("IQU"), expr.AVar("IQU"), expr.AVar(out_var)])))

        # Recursive entry into diagram
        procs.append(hcsp.Var(self.entry_proc_name(self.chart.diagram)))
        procs.append(self.get_rec_entry_proc(self.chart.diagram))
        
        # Write data store variable
        for vname, info in self.data.items():
            if info.scope == "DATA_STORE_MEMORY_DATA":
                procs.append(hcsp.OutputChannel(vname + "_out", expr.AVar(vname)))

        procs.extend(self.get_output_data())

        # End signal
        if self.has_signal:
            procs.append(hcsp.InputChannel("end_" + self.chart.name))

        return hcsp.seq(procs)

    def get_exec_proc(self):
        return self.get_rec_during_proc(self.chart.diagram)

    def get_ode(self, state, cur_states, cur_eqs):
        """Obtain the HCSP command for ODE between iterations.
        
        state - current state to process.
        cur_eqs - list of (x, expr) for already existing equations.
        
        """
        if state.ssid in self.ode_map:
            new_eqs = cur_eqs + self.ode_map[state.ssid]
        else:
            new_eqs = cur_eqs
        if any(isinstance(child, OR_State) for child in state.children):
            ite = []
            for child in state.children:
                if isinstance(child, OR_State):
                    ite.append((expr.RelExpr("==", expr.AVar(self.active_state_name(state)), expr.AConst(child.whole_name)),
                                self.get_ode(child, cur_states+[child], new_eqs)))
            return hcsp.ITE(ite)
        elif any(isinstance(child, AND_State) for child in state.children):
            raise NotImplementedError
        else:
            # Junctions only, produce the ODE. First obtain the list of boundary
            # conditions
            all_conds = []
            for cur_st in cur_states:
                if cur_st.out_trans:
                    for tran in cur_st.out_trans:
                        pre_act, cond, _ = self.convert_label(tran.label)
                        if pre_act != hcsp.Skip():
                            raise NotImplementedError
                        all_conds.append(cond)
            eqs = []
            for var, eq in new_eqs:
                pre_act, e = self.convert_expr(eq)
                if pre_act != hcsp.Skip():
                    raise NotImplementedError
                eqs.append((var, e))
            return hcsp.ODE(eqs, expr.neg_expr(expr.disj(*all_conds)))

    def get_iteration(self):
        procs = []

        # Start signal
        if self.has_signal:
            procs.append(hcsp.InputChannel("start_" + self.chart.name))
        for n,e in  self.events.items():
            if e.scope == "INPUT_EVENT" and e.trigger =="EITHER_EDGE_EVENT":
                procs.append(hcsp.InputChannel("ch_clock", expr.AVar("osag")))
                
        procs.extend(self.get_input_data())

        # Input from data store
        for vname, info in self.data.items():
            if info.scope == "DATA_STORE_MEMORY_DATA":
                procs.append(hcsp.InputChannel(vname + "_in", expr.AVar(vname)))
        
        # Call during procedure of the diagram
        procs.append(hcsp.Var(self.exec_name()))

        # Write to data store
        for vname, info in self.data.items():
            if info.scope == "DATA_STORE_MEMORY_DATA":
                procs.append(hcsp.OutputChannel(vname + "_out", expr.AVar(vname)))
        procs.extend(self.get_output_data())
        
        inputMesdicts = dict()
        for name, info in self.messages.items():
            if info.scope == "INPUT_DATA":
                inputMesdicts[name] = info
        if len(inputMesdicts) > 0:
            procs.append(hcsp.Condition(expr.RelExpr("==", expr.FunExpr("remove_InputMessage", [expr.AConst(inputMesdicts)]),expr.AConst(1)),hcsp.Skip()))
        
        for n,e in  self.events.items():
            if e.scope == "INPUT_EVENT" and e.trigger =="EITHER_EDGE_EVENT":
                procs.append(hcsp.Assign(expr.AVar("last"),expr.AVar("osag")))
        # End signal
        if self.has_signal:
            procs.append(hcsp.InputChannel("end_" + self.chart.name))

        # Wait the given sample time
        if self.ode_map:
            procs.append(self.get_ode(self.chart.diagram, cur_states=[], cur_eqs=[]))
        else:
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


def get_execute_order(charts):
    """Returns execution order of charts."""
    # Mapping from channel name to input chart
    ch_name_in = dict()
    # Mapping from channel name to output chart
    ch_name_out = dict()
    
    for chart in charts:
        for port_id, in_var in chart.port_to_in_var.items():
            line = chart.dest_lines[port_id]
            ch_name = "ch_" + line.name + "_" + str(line.branch)
            ch_name_in[ch_name] = chart.name
        for port_id, out_var in chart.port_to_out_var.items():
            lines = chart.src_lines[port_id]
            for line in lines:
                ch_name = "ch_" + line.name + "_" + str(line.branch)
                ch_name_out[ch_name] = chart.name

    # Edges between charts. Both keys are values are names
    edges = dict()
    shared_chans = []
    for chart in charts:
        edges[chart.name] = set()
    for chan in ch_name_in:
        if chan in ch_name_out:
            shared_chans.append(chan)
            chart_in, chart_out = ch_name_in[chan], ch_name_out[chan]
            edges[chart_out].add(chart_in)
    
    # Finally, compute the ordering of charts
    chart_order = []
    def rec(chart_name):
        if chart_name not in chart_order:
            chart_order.append(chart_name)
            for dest in sorted(edges[chart_name]):
                rec(dest)

    while True:
        # In each iteration, let the starting chart be the one that has
        # the least number of incoming edges, sorted alphabetically
        least_chart, least_degree = None, None
        for chart_name in sorted(edges):
            if chart_name not in chart_order:
                degree = 0
                for chart_out in edges:
                    if chart_name in edges[chart_out]:
                        degree += 1
                if least_degree is None or degree < least_degree:
                    least_chart = chart_name
                    least_degree = degree
        rec(least_chart)
        if len(chart_order) == len(edges):
            break

    return shared_chans, chart_order

def get_control_proc(chart_order):
    procs = []
    for ch_name in chart_order:
        procs.append(hcsp.OutputChannel("start_" + ch_name))
        procs.append(hcsp.OutputChannel("end_" + ch_name))
    return hcsp.Loop(hcsp.seq(procs))

def get_data_proc(comm_data):
    procs = []
    for ch_name, init_value in comm_data:
        if init_value:
            procs.append(hcsp.Assign(expr.AVar(ch_name), init_value))

    select_ios = []
    for ch_name, init_value in comm_data:
        select_ios.extend([
            (hcsp.OutputChannel(ch_name + "_in", expr.AVar(ch_name)), hcsp.Skip()),
            (hcsp.InputChannel(ch_name + "_out", expr.AVar(ch_name)), hcsp.Skip())])
    procs.append(hcsp.Loop(hcsp.SelectComm(*select_ios)))
    return hcsp.seq(procs)

def convert_diagram(diagram, print_chart=False, print_before_simp=False, print_final=False):
    """Full conversion function for Stateflow.

    diagram : SL_Diagram - input diagram.
    print_chart : bool - print parsed chart.
    print_before_simp : bool - print HCSP program before simplification.
    print_final : bool - print HCSP program after optimization.

    """
    # Initial stages
    diagram.parse_xml()
    diagram.add_line_name()
    _, continuous, charts, _, _, _, dsms, dsrs,clocks = diagram.seperate_diagram()

    # Optional: print chart
    if print_chart:
        for chart in charts:
            print(chart)

    proc_map = dict()
    converter_map = dict()

    # Obtain sample time

    sample_time = -1
    if 'st' in diagram.chart_parameters and diagram.chart_parameters['st'] != -1:
        sample_time = diagram.chart_parameters['st']
    else:
        for chart in charts: 
            chart_parameters = diagram.chart_parameters[chart.name]
            if 'st' in chart_parameters and chart_parameters['st'] != -1 and sample_time == -1:
                sample_time = chart_parameters['st']

    # Process controlling order between charts
    shared_chans, exec_order = get_execute_order(charts)
    if len(charts) > 1:
        proc_map["order_ctrl"] = (dict(), get_control_proc(exec_order))

    # Processes for charts
    has_signal = (len(charts) > 1)
    for chart in charts:
        diagram.chart_parameters[chart.name]['st'] = sample_time
        converter = SFConvert(
            chart, chart_parameters=diagram.chart_parameters[chart.name],
            has_signal=has_signal, shared_chans=shared_chans)
        hp = converter.get_toplevel_process()
        procs = converter.get_procs()
        proc_map[chart.name] = (procs, hp)
        converter_map[chart.name] = converter

    # Communicating data (DSM, channel, messages)
    comm_data = []
    for channel in shared_chans:
        comm_data.append((channel, None))
    for dsm in dsms:
        _, init_value = convert.convert_expr(dsm.value)
        comm_data.append((dsm.dataStoreName, init_value))
    
    # Process controlling data between charts
    if len(comm_data) > 0:
        proc_map["data_ctrl"] = (dict(), get_data_proc(comm_data))

    # Processes for continuous
    for i, c in enumerate(continuous):
        proc_map["Continuous" + str(i+1)] = (dict(), get_hcsp.translate_continuous(c))

    for i, c in enumerate(clocks):
        proc_map["Clock" + str(i+1)] = (dict(), c.get_hcsp())

    # Optional: print HCSP program before simplification
    if print_before_simp:
        for name, (procs, hp) in proc_map.items():
            print(name + " ::=\n" + pprint(hp))
            for name, proc in procs.items():
                print('\nprocedure ' + name + " ::=\n" + pprint(proc))
            print()

    # Reduce procedures
    for name, (procs, hp) in proc_map.items():
        if name in converter_map:
            local_vars = converter_map[name].local_vars
        else:
            local_vars = set()
        proc_map[name] = optimize.full_optimize_module(
            procs, hp, local_vars=local_vars, local_vars_proc={'_ret'}.union(local_vars))

    # Optional: print final HCSP program
    if print_final:
        for name, (procs, hp) in proc_map.items():
            print(name + " ::=\n" + pprint(hp))
            for proc_name, proc in procs.items():
                print('\nprocedure ' + proc_name + " ::=\n" + pprint(proc))
            print()

    return proc_map
