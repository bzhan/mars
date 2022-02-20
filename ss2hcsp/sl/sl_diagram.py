"""Simulink diagrams."""

import lark
from decimal import Decimal

from ss2hcsp.sl.sl_line import SL_Line
from ss2hcsp.sl.sl_block import get_gcd
from ss2hcsp.matlab import function, convert
from ss2hcsp.matlab import function
from ss2hcsp.matlab.parser import expr_parser, function_parser, \
    transition_parser, func_sig_parser, state_op_parser
from ss2hcsp.matlab import convert
from ss2hcsp.sl.Continuous.clock import Clock
from ss2hcsp.sl.port import Port
from ss2hcsp.sl.Continuous.integrator import Integrator
from ss2hcsp.sl.Continuous.constant import Constant
from ss2hcsp.sl.Continuous.signalBuilder import SignalBuilder
from ss2hcsp.sl.Continuous.source import Sine
from ss2hcsp.sl.MathOperations.product import Product
from ss2hcsp.sl.MathOperations.bias import Bias
from ss2hcsp.sl.MathOperations.gain import Gain
from ss2hcsp.sl.MathOperations.add import Add
from ss2hcsp.sl.MathOperations.my_abs import Abs
from ss2hcsp.sl.MathOperations.sqrt import Sqrt
from ss2hcsp.sl.MathOperations.square import Square
from ss2hcsp.sl.LogicOperations.logic import And, Or, Not
from ss2hcsp.sl.LogicOperations.relation import Relation
from ss2hcsp.sl.LogicOperations.reference import Reference
from ss2hcsp.sl.SignalRouting.switch import Switch
from ss2hcsp.sl.SignalRouting.scope import Scope
from ss2hcsp.sl.SubSystems.subsystem import Subsystem, Triggered_Subsystem, Enabled_Subsystem
from ss2hcsp.sl.Discontinuities.saturation import Saturation
from ss2hcsp.sl.Discrete.unit_delay import UnitDelay 
from ss2hcsp.sl.Discrete.DiscretePulseGenerator import DiscretePulseGenerator
from ss2hcsp.sl.Discrete.discrete_PID_controller import DiscretePID
from ss2hcsp.sl.MathOperations.min_max import MinMax
from ss2hcsp.sf.sf_state import AND_State, OR_State, Junction, GraphicalFunction
from ss2hcsp.sf.sf_chart import SF_Chart
from ss2hcsp.sf.sf_transition import Transition
from ss2hcsp.sf.sf_message import SF_Message,SF_Data
from ss2hcsp.sf.sf_event import SF_Event
from ss2hcsp.sl.discrete_buffer import Discrete_Buffer
from ss2hcsp.sl.mux.mux import Mux
from ss2hcsp.sl.DataStore.DataStore import DataStoreMemory, DataStoreRead
from xml.dom.minidom import parse, Element
from xml.dom.minicompat import NodeList
import operator


def parse_sample_time(sample_time):
    """Convert sample time in string to integer or decimal."""
    if sample_time is None or sample_time == 'inf':
        return -1
    elif '.' in sample_time:
        v = Decimal(sample_time)
        return int(v * 1000) / Decimal(1000)
    else:
        return int(sample_time)

def parse_value(value, default=None):
    """Parse value to integer or float."""
    if value:
        if '.' in value:
            return float(value)
        else:
            return int(value)
    else:
        return default

def replace_spaces(name):
    """Replace spaces and newlines in name with underscores."""
    return name.strip().replace(' ', '_').replace('\n', '_')

def get_attribute_value(block, attribute, name=None):
    for node in block.getElementsByTagName("P"):
        if node.getAttribute("Name") == attribute:
            if node.childNodes:
                if not name or name == node.childNodes[0].data:
                    return node.childNodes[0].data
    return None


class SL_Diagram:
    """Represents a Simulink diagram."""
    def __init__(self, location=""):
        # Dictionary of blocks indexed by name
        self.blocks_dict = dict()

        # Dictionary of STATEFLOW parameters indexed by name
        self.chart_parameters = dict()

        # XML data structure
        self.model = None

        # Name of the diagram, set by parse_xml
        self.name = None

        # Variables that needs to display
        self.outputs = list()

        # Different parts of the diagram
        self.continuous_blocks = list()
        self.discrete_blocks = list()
        self.scopes = list()
        self.dsms = list()

        self.others = list()
        
        # Parsed model of the XML file
        if location:
            with open(location) as f:
                self.model = parse(f)

    def parse_stateflow_xml(self):
        """Parse stateflow charts from XML."""

        def get_acts(acts):
            """Convert action into a sequence of actions."""
            lists = list()
            if isinstance(acts, function.Sequence):
                for act in [acts.cmd1, acts.cmd2]:
                    if isinstance(act, function.Sequence):
                        lists.extend(get_acts(act))
                    else:
                        lists.append(act)
            else:
                lists.append(acts)
            return lists

        def get_transitions(blocks):
            """Obtain the list of transitions.
            
            Returns a dictionary mapping transitions IDs to transition objects.
            
            """
            assert isinstance(blocks, NodeList)

            tran_dict = dict()
            for block in blocks:
                if block.nodeName == "transition":
                    # Obtain transition ID, label, execution order
                    tran_ssid = block.getAttribute("SSID")
                    tran_label = get_attribute_value(block, "labelString")
                    if tran_label is None:
                        tran_label = function.TransitionLabel(None, None, None, None)
                    else:
                        try:
                            tran_label = transition_parser.parse(tran_label)
                        except lark.exceptions.UnexpectedToken as e:
                            print("When parsing transition label", tran_label)
                            raise e
                    order = int(get_attribute_value(block, "executionOrder"))

                    # Each transition must have exactly one source and destination
                    assert len([child for child in block.childNodes if child.nodeName == "src"]) == 1
                    assert len([child for child in block.childNodes if child.nodeName == "dst"]) == 1
                    src_ssid, dst_ssid = None, None
                    for child in block.childNodes:
                        if child.nodeName == "src":
                            src_ssid = get_attribute_value(child, "SSID")
                        elif child.nodeName == "dst":
                            dst_ssid = get_attribute_value(child, "SSID")

                    # There should be no repeated transition IDs
                    assert tran_ssid not in tran_dict
                    tran_dict[tran_ssid] = Transition(ssid=tran_ssid, label=tran_label, order=order,
                                                      src=src_ssid, dst=dst_ssid)
            return tran_dict

        all_out_trans = dict()

        def get_children(block):
            """Get lists of children states and junctions of the current
            block.

            Returned value is:

            _states: list of SF_State objects.
            _junction: list of Junction objects.
            _functions : list of Function objects.
            
            """
            assert isinstance(block, Element)

            children = [child for child in block.childNodes if child.nodeName == "Children"]
            if not children:
                return list(), list(), list()
            assert len(children) == 1

            _states, _junctions, _functions = list(), list(), list()

            # Get list of outgoing transitions from states in children
            out_trans_dict = get_transitions(children[0].childNodes)
            
            # The number of default transitions is at most one
            assert len([tran for tran in out_trans_dict.values() if tran.src is None]) <= 1

            # Now traverse each child node. We consider two cases of child nodes:
            # states and junctions.
            for child in children[0].childNodes:
                if child.nodeName == "state":
                    ssid = child.getAttribute("SSID")
                    state_type = get_attribute_value(child, "type")

                    # There are three cases of states: FUNC_STATE (definition of functions),
                    # AND_STATE and OR_STATE.
                    if state_type == "FUNC_STATE":
                        # Extract functions
                        fun_name = get_attribute_value(child, "labelString")
                        fun_script = get_attribute_value(child, "script")
                        if fun_script:
                            # Has script, directly use parser for matlab functions
                            fun_name=function_parser.parse(fun_script).name
                            hp= convert.convert_cmd(function_parser.parse(fun_script).cmd)
                            ru=function_parser.parse(fun_script).return_var
                            exprs=function.ListExpr(function_parser.parse(fun_script).params) if function_parser.parse(fun_script).params is not None else None
                            fun_type="MATLAB_FUNCTION"
                            if isinstance(ru,(function.Var,function.FunctionCall)):
                                return_var=ru
                            elif isinstance(ru,tuple):
                                return_var=function.ListExpr(*ru)
                            _functions.append(function_parser.parse(fun_script))
                            # _functions.append(Function(fun_name,exprs,ru,hp,None,fun_type))
                        else:
                            fun_type="GRAPHICAL_FUNCTION"
                            children = [c for c in child.childNodes if c.nodeName == "Children"]
                            assert len(children) == 1
                            sub_trans = get_transitions(children[0].childNodes)
                            sub_states, sub_junctions, sub_functions = get_children(child)
                            assert len(sub_states) == 0 and len(sub_functions) == 0

                            try:
                                fun_name, fun_params, fun_return = func_sig_parser.parse(fun_name)
                            except lark.exceptions.UnexpectedToken as e:
                                print("When parsing function signature", fun_name)
                                raise e

                            chart_state1 = OR_State(ssid=ssid, name=fun_name)
                            for state in  sub_junctions:
                                state.father = chart_state1
                                chart_state1.children.append(state)
                            # _states.append(chart_state1)
                            hp=None
                            graph_fun = GraphicalFunction(fun_name, fun_params, fun_return, sub_trans, sub_junctions)
                            _functions.append(graph_fun)
                            # _functions.append(Function(fun_name,fun_params,fun_return,hp,chart_state1,fun_type))

                    elif state_type in ("AND_STATE", "OR_STATE"):
                        # Extract AND- and OR-states

                        # The format of state labels is as follows:
                        # First line is the name of the state, the remaining lines
                        # specify en, du, and ex actions.
                        labels = get_attribute_value(child, "labelString")
                        label = state_op_parser.parse(labels)
                        name = str(label.name)
                        
                        # Get en, du and ex actions
                        en = get_acts(label.en_op.op) if label.en_op is not None else []
                        du = get_acts(label.du_op.op) if label.du_op is not None else []
                        ex = get_acts(label.ex_op.op) if label.ex_op is not None else []
                        
                        # Get default_tran and out_trans
                        default_tran = None
                        out_trans = list()
                        dictMerged2 = dict(out_trans_dict)
                        dictMerged2.update(all_out_trans)
                    
                        for tran in dictMerged2.values():
                            src, dst = tran.src, tran.dst
                            if src is None and dst == ssid:  # it is a default transition
                                default_tran = tran
                            elif src == ssid:  # the src of tran is this state
                                out_trans.append(tran)
                            else:
                                all_out_trans[tran.ssid] = tran
                        out_trans.sort(key=operator.attrgetter("order"))

                        # Get inner_trans
                        inner_trans = list()
                        grandchildren = [grandchild for grandchild in child.childNodes if grandchild.nodeName == "Children"]
                        assert len(grandchildren) <= 1
                        if len(grandchildren) == 1:
                            inner_trans_dict = get_transitions(grandchildren[0].childNodes)
                            for tran in inner_trans_dict.values():
                                src, dst = tran.src, tran.dst
                                if src == ssid:
                                    inner_trans.append(tran)
                        inner_trans.sort(key=operator.attrgetter("order"))

                        # Create a state object
                        if state_type == "AND_STATE":
                            assert default_tran is None and out_trans == [], \
                                "Parse XML: AND_STATE should not have default transition or outgoing transitions."
                            order = int(get_attribute_value(child, "executionOrder"))
                            _state = AND_State(ssid=ssid, inner_trans=inner_trans, name=name, en=en, du=du, ex=ex,
                                               order=order)
                        elif state_type == "OR_STATE":
                            _state = OR_State(ssid=ssid, out_trans=out_trans, inner_trans=inner_trans, name=name,
                                            en=en, du=du, ex=ex, default_tran=default_tran)
                        else:
                            print(state_type)

                        # Get children states and junctions recursively
                        child_states, child_junctions, child_functions = get_children(child)
                        _state.funs = child_functions
                        for _child in child_states + child_junctions:
                            _child.father = _state
                            _state.children.append(_child)
                            if isinstance(_child, Junction) and _child.type == "HISTORY_JUNCTION":
                                if isinstance(_state, OR_State):
                                    _state.has_history_junc = True

                        if _state.children and isinstance(_state.children[0], AND_State):
                            _state.children.sort(key=operator.attrgetter("order"))
                        _states.append(_state)

                    else:
                        raise NotImplementedError("Unrecognized state type: %s" % state_type)
                    
                elif child.nodeName == "junction":
                    ssid = child.getAttribute("SSID")
                    junc_type = get_attribute_value(block=child, attribute="type")
                    # Get default_tran and out_trans
                    default_tran = None
                    out_trans = list()

                    dictMerged2 = dict(out_trans_dict)
                    dictMerged2.update(all_out_trans)

                    for tran in dictMerged2.values():
                        src, dst = tran.src, tran.dst
                        if src is None and dst == ssid:  # it is a default transition
                            default_tran = tran
                        elif src == ssid:  # the src of tran is this state
                            out_trans.append(tran)
                        else:
                            all_out_trans[tran.ssid] = tran
                    out_trans.sort(key=operator.attrgetter("order"))
                    # Create a junction object and put it into _junstions
                    _junctions.append(Junction(ssid=ssid, out_trans=out_trans,junc_type=junc_type, default_tran=default_tran))   
            return _states, _junctions, _functions

        # Create charts
        charts = self.model.getElementsByTagName(name="chart")
        for chart in charts:
            all_out_trans = dict()
            chart_id = chart.getAttribute("id")
            chart_name = replace_spaces(get_attribute_value(block=chart, attribute="name"))

            # A chart is wrapped into an AND-state
            chart_state = AND_State(ssid=chart_id, name=chart_name)
            states, junctions, functions = get_children(block=chart)
            # for fun in functions:
            #     if fun.type == "GRAPHICAL_FUNCTION":
            #         fun.chart_state1.father=chart_state
            #         chart_state.children.append(fun.chart_state1)
            chart_state.funs = functions
            for state in states + junctions:
                state.father = chart_state
                chart_state.children.append(state)
            if chart_state.children and isinstance(chart_state.children[0], AND_State):
                chart_state.children.sort(key=operator.attrgetter("order"))
            assert chart_state.check_children()
           
            chart_st = get_attribute_value(block=chart, attribute="sampleTime")
            if chart_st:
                if '.' in chart_st or 'e' in chart_st:
                    chart_st = Decimal(chart_st)
                else:
                    chart_st = int(chart_st)
            else:
                chart_st = -1

            chart_data = dict()
            message_dict = dict()
            event_dict = dict()
            if chart.getElementsByTagName(name="event"):
                for i, e in enumerate(chart.getElementsByTagName(name="event")):
                    event_name = get_attribute_value(e, "name")
                    event_scope = get_attribute_value(e, "scope")
                    port = i + 1
                    if get_attribute_value(e, "trigger"):
                        event_trigger = get_attribute_value(e, "trigger")
                    else:
                        event_trigger = None
                    event = SF_Event(name=event_name, scope=event_scope, trigger=event_trigger, port=port)
                    event_dict[event_name] = event

            for data in chart.getElementsByTagName(name="data"):
                var_name = data.getAttribute("name")
                value = get_attribute_value(data, "initialValue")
                if value is not None:
                    try:
                        value = expr_parser.parse(value)
                    except lark.exceptions.UnexpectedToken as e:
                        print("When parsing value:", value)
                        raise e
                else:
                    value = 0
                scope = get_attribute_value(data, "scope")
                sf_data = SF_Data(name=var_name, value=value, scope=scope)

                if data.getElementsByTagName(name="message"):
                    mesgNode = data.getElementsByTagName(name="message")[0]
                    if get_attribute_value(mesgNode, "isMessage") == "1":
                        message = SF_Message(name=var_name, data=0, scope=scope)
                        message_dict[var_name] = message
                else:
                    chart_data[var_name] = sf_data

            assert chart_name not in self.chart_parameters
            self.chart_parameters[chart_name] = {
                "state": chart_state,
                "data": chart_data,
                "st": chart_st,
                "message_dict": message_dict,
                "event_dict": event_dict
            }

    def parse_xml(self, default_SampleTimes=()):
        # Extract BlockParameterDefaults
        if not default_SampleTimes:
            default_SampleTimes = dict()
            default_para_blocks = self.model.getElementsByTagName("BlockParameterDefaults")
            assert len(default_para_blocks) == 1
            for child in default_para_blocks[0].childNodes:
                if child.nodeName == "Block":
                    child_type = child.getAttribute("BlockType")
                    assert child_type not in default_SampleTimes
                    default_SampleTimes[child_type] = get_attribute_value(child, "SampleTime")

        self.parse_stateflow_xml()

        # Extract name of the model
        models = self.model.getElementsByTagName("Model")
        assert len(models) <= 1
        self.name = ""
        if models:
            self.name = models[0].getAttribute("Name")

        system = self.model.getElementsByTagName("System")[0]

        # Add blocks
        blocks = [child for child in system.childNodes if child.nodeName == "Block"]

        # The following dictionary is used to replace port names as
        # formatted ones. The name of each port shoud be in the form of
        # port_type + port_number, such as in_0 and out_1 in order to delete
        # subsystems successfully (see function delete_subsystems in get_hcsp.py).
        port_name_dict = dict()  # mapping from old name to new name

        for block in blocks:
            # Type of block
            block_type = block.getAttribute("BlockType")

            # Block name.
            block_name = replace_spaces(block.getAttribute("Name"))

            # Sample time of block
            sample_time = get_attribute_value(block, "SampleTime")
            if (not sample_time) and block_type in default_SampleTimes:
                sample_time = default_SampleTimes[block_type]
            sample_time = parse_sample_time(sample_time)

            # For each type of block, obtain additional parameters
            if block_type == "Mux":
                inputs = get_attribute_value(block, "Inputs")
                ports = list(arg.value for arg in expr_parser.parse(get_attribute_value(block=block, attribute="Ports")).args)
                self.add_block(Mux(name=block_name, inputs=inputs, ports=ports))
            elif block_type == "DataStoreMemory":
                init_value = get_attribute_value(block=block, attribute="InitialValue")
                if init_value is not None:
                    try:
                        value = expr_parser.parse(init_value)
                    except lark.exceptions.UnexpectedToken as e:
                        print("When parsing value:", init_value)
                        raise e
                else:
                    value = 0
                dataStoreName = get_attribute_value(block, "DataStoreName")
                self.add_block(DataStoreMemory(name=block_name, value=value, dataStoreName=dataStoreName))
            elif block_type == "DataStoreRead":
                dataStoreName = get_attribute_value(block,"DataStoreName")
                self.add_block(DataStoreRead(name=block_name, dataStoreName=dataStoreName))
            elif block_type == "Constant":
                value = get_attribute_value(block, "Value")
                value = parse_value(value, default=1)
                self.add_block(Constant(name=block_name, value=value))
            elif block_type == "Integrator":
                init_value = get_attribute_value(block, "InitialCondition")
                init_value = parse_value(init_value, default=0)
                self.add_block(Integrator(name=block_name, init_value=init_value))
            elif block_type == "Logic":  # AND, OR, NOT
                op_name = get_attribute_value(block, "Operator")
                inputs = get_attribute_value(block, "Inputs")
                num_dest = int(inputs) if inputs else 2
                if op_name == "OR":
                    self.add_block(Or(name=block_name, num_dest=num_dest, st=sample_time))
                elif op_name == "NOT":
                    self.add_block(Not(name=block_name, st=sample_time))
                else:  # op_name == None, meaning it is an AND block
                    self.add_block(And(name=block_name, num_dest=num_dest, st=sample_time))
            elif block_type == "RelationalOperator":
                relation = get_attribute_value(block, "Operator")
                if relation == "~=":
                    relation = "!="
                self.add_block(Relation(name=block_name, relation=relation, st=sample_time))
            elif block_type == "Reference":
                # check if it is a discrete PID
                block_type = get_attribute_value(block, "SourceType")
                if block_type and block_type.startswith("PID"):
                    controller = get_attribute_value(block, "Controller")
                    st = eval(get_attribute_value(block, "SampleTime"))
                    assert get_attribute_value(block, "IntegratorMethod") == "Backward Euler"
                    assert get_attribute_value(block, "FilterMethod") == "Forward Euler"
                    assert get_attribute_value(block, "AntiWindupMode") == "back-calculation"
                    p = eval(get_attribute_value(block, "P"))
                    i = eval(get_attribute_value(block, "I"))
                    d = eval(get_attribute_value(block, "D"))
                    init_value = eval(get_attribute_value(block, "InitialConditionForIntegrator"))
                    upper_limit = eval(get_attribute_value(block, "UpperSaturationLimit"))
                    lower_limit = eval(get_attribute_value(block, "LowerSaturationLimit"))
                    kb = eval(get_attribute_value(block, "Kb"))
                    self.add_block(DiscretePID(name=block_name, controller=controller, st=st, pid=[p, i, d],
                                               init_value=init_value, saturation=[lower_limit, upper_limit], kb=kb))
                    continue

                relop = get_attribute_value(block, "relop")
                if relop:
                    if relop == "~=":
                        relop = "!="
                    self.add_block(Reference(name=block_name, relop=relop, st=sample_time))
                if block_type == "Digital clock":
                    period = get_attribute_value(block, "period")
                    self.chart_parameters['st']=float(period)/2

                    self.add_block(Clock(name=block_name,period=period))
            elif block_type == "Abs":
                self.add_block(Abs(name=block_name, st=sample_time))
            elif block_type == "Sqrt":
                sqrt_operator = get_attribute_value(block, "Operator")
                self.add_block(Sqrt(name=block_name, operator=sqrt_operator, st=sample_time))
            elif block_type == "Math":
                math_operator = get_attribute_value(block, "Operator")
                self.add_block(Square(name=block_name, operator=math_operator, st=sample_time))
            elif block_type == "Sum":
                inputs = get_attribute_value(block, "Inputs")
                dest_spec = inputs.replace("|", "") if inputs else "++"
                self.add_block(Add(name=block_name, dest_spec=dest_spec, st=sample_time))
            elif block_type == "Bias":
                bias = get_attribute_value(block, "Bias")
                bias = eval(bias) if bias else 0
                self.add_block(Bias(name=block_name, bias=bias, st=sample_time))
            elif block_type == "Product":
                inputs = get_attribute_value(block, "Inputs")
                dest_spec = inputs.replace("|", "") if inputs else "**"
                self.add_block(Product(name=block_name, dest_spec=dest_spec, st=sample_time))
            elif block_type == "Gain":
                factor = get_attribute_value(block, "Gain")
                factor = eval(factor) if factor else 1
                self.add_block(Gain(name=block_name, factor=factor, st=sample_time))
            elif block_type == "Sin":
                amplitude = parse_value(get_attribute_value(block, "Amplitude"), default=1)
                bias = parse_value(get_attribute_value(block, "Bias"), default=0)
                frequency = parse_value(get_attribute_value(block, "Frequency"), default=1)
                phase = parse_value(get_attribute_value(block, "Phase"), default=0)
                self.add_block(Sine(name=block_name, amplitude=amplitude, bias=bias, frequency=frequency, phase=phase, st=sample_time))
            elif block_type == "Saturate":
                upper_limit = parse_value(get_attribute_value(block, "UpperLimit"), default=0.5)
                lower_limit = parse_value(get_attribute_value(block, "LowerLimit"), default=-0.5)
                self.add_block(Saturation(name=block_name, up_lim=upper_limit, low_lim=lower_limit, st=sample_time))
            elif block_type == "UnitDelay":
                init_value = parse_value(get_attribute_value(block, "InitialCondition"), default=0)
                self.add_block(UnitDelay(name=block_name, init_value=init_value, st=sample_time))
            elif block_type == "MinMax":
                fun_name = get_attribute_value(block, "Function")
                fun_name = fun_name if fun_name else "min"
                input_num = get_attribute_value(block, "Inputs")
                input_num = int(input_num) if input_num else 1
                self.add_block(MinMax(name=block_name, num_dest=input_num, fun_name=fun_name, st=sample_time))
            elif block_type == "Switch":
                criteria = get_attribute_value(block, "Criteria")
                relation = ">" if criteria == "u2 > Threshold" else ("!=" if criteria == "u2 ~= 0" else ">=")
                threshold = get_attribute_value(block, "Threshold")
                threshold = eval(threshold) if threshold else 0
                self.add_block(Switch(name=block_name, relation=relation, threshold=threshold, st=sample_time))
            elif block_type == "DiscretePulseGenerator":
                pulseType = get_attribute_value(block, "PulseType") if get_attribute_value(block, "PulseType") else "Sample based"
                amplitude = float(get_attribute_value(block, "Amplitude")) if get_attribute_value(block, "Amplitude") else 1.0
                period = Decimal(get_attribute_value(block, "Period"))
                pulseWidth = Decimal(get_attribute_value(block, "PulseWidth"))
                phaseDelay = Decimal(get_attribute_value(block, "PhaseDelay")) if get_attribute_value(block, "PhaseDelay") else Decimal("0.0")
                self.add_block(DiscretePulseGenerator(
                    name=block_name, pulseType=pulseType, amplitude=amplitude, period=period,
                    pulseWidth=pulseWidth, phaseDelay=phaseDelay))
            elif block_type == "Inport":
                port_number = get_attribute_value(block, "Port")
                if not port_number:
                    port_number = "1"
                assert block_name not in port_name_dict
                port_name_dict[block_name] = "in_" + str(int(port_number) - 1)
                self.add_block(Port(name=port_name_dict[block_name], port_name=block_name, port_type="in_port"))
            elif block_type == "Outport":
                port_number = get_attribute_value(block=block, attribute="Port")
                if not port_number:
                    port_number = "1"
                assert block_name not in port_name_dict
                port_name_dict[block_name] = "out_" + str(int(port_number) - 1)
                self.add_block(Port(name=port_name_dict[block_name], port_name=block_name, port_type="out_port"))
            elif block_type == "Scope":
                num_dest = 0
                for child in system.childNodes:
                    if child.nodeName == "Line":
                        if get_attribute_value(block=child, attribute="DstBlock", name=block_name):
                            name = get_attribute_value(block=child, attribute="Name")
                            assert name is not None, "Scope output line is not named"
                            self.outputs.append(name)
                            num_dest += 1
                self.add_block(Scope(name=block_name, num_dest=num_dest, st=sample_time))
            elif block_type == "SubSystem":
                subsystem = block.getElementsByTagName("System")[0]

                # Check if it is a Signal Builder
                is_signal_builder = False
                for child in block.childNodes:
                    if child.nodeName == "Object" and child.getAttribute("PropName") == "MaskObject":
                        if get_attribute_value(block=child, attribute="Type") == "Sigbuilder block":
                            is_signal_builder = True
                            break
                if is_signal_builder:
                    signal_names = []
                    time_axises = []
                    data_axises = []
                    out_indexs = []
                    for node in subsystem.getElementsByTagName("Array"):
                        if node.getAttribute("PropName") == "Signals":
                            # assert node.getAttribute("Type") == "SigSuiteSignal"
                            for obj in node.getElementsByTagName("Object"):
                                signal_names.append(block_name + "_" + get_attribute_value(obj, "Name"))
                                xData = get_attribute_value(obj, "XData")
                                out_index = get_attribute_value(obj, "outIndex")
                                out_indexs.append(out_index)
                                # if "\n" in xData:
                                #     xData = xData.split("\n")[1]
                                assert xData.count('[') == xData.count(']') == 1
                                start = xData.index('[')
                                end = xData.index(']')
                                time_axises.append(tuple(parse_sample_time(e) for e in xData[start+1:end].split(',')))
                                yData = get_attribute_value(obj, "YData")
                                # if "\n" in yData:
                                #     yData = yData.split("\n")[1]
                                assert yData.count('[') == yData.count(']') == 1
                                start = yData.index('[')
                                end = yData.index(']')
                                data_axises.append(tuple(float(e) for e in yData[start+1:end].split(',')))

                    if not signal_names:
                        for node in subsystem.getElementsByTagName("Object"):
                            if node.getAttribute("PropName") == "Signals":
                                signal_names.append(block_name + "_" + get_attribute_value(node, "Name"))
                                xData = get_attribute_value(node, "XData")
                                # if "\n" in xData:
                                #     xData = xData.split("\n")[1]
                                # time_axises.append(tuple(float(e) for e in xData[1:-1].split(',')))
                                assert xData.count('[') == xData.count(']') == 1
                                start = xData.index('[')
                                end = xData.index(']')
                                time_axises.append(tuple(parse_sample_time(e) for e in xData[start + 1:end].split(',')))
                                yData = get_attribute_value(node, "YData")
                                # if "\n" in yData:
                                #     yData = yData.split("\n")[1]
                                # data_axises.append(tuple(float(e) for e in yData[1:-1].split(',')))
                                assert yData.count('[') == yData.count(']') == 1
                                start = yData.index('[')
                                end = yData.index(']')
                                data_axises.append(tuple(float(e) for e in yData[start + 1:end].split(',')))

                    assert signal_names
                    self.add_block(SignalBuilder(name=block_name, signal_names=tuple(signal_names),
                                                 time_axises=time_axises, data_axises=data_axises))
                    continue

                # Check if it is a stateflow chart
                sf_block_type = get_attribute_value(block, "SFBlockType")
                if sf_block_type == "Chart":
                    chart_paras = self.chart_parameters[block_name]
                    ports = list(arg.value for arg in expr_parser.parse(get_attribute_value(block=block, attribute="Ports")).args)
                    if len(ports) == 0:
                        ports = [0, 0]
                    elif len(ports) == 1:
                        ports.append(0)
                    num_dest, num_src = ports[:2]

                    # Check if it a triggered stateflow chart
                    triggers = [child for child in subsystem.childNodes if child.nodeName == "Block" and
                                child.getAttribute("BlockType") == "TriggerPort"]
                    assert len(triggers) <= 1
                    st = -2 if triggers else chart_paras['st']

                    stateflow = SF_Chart(name=block_name, state=chart_paras["state"], data=chart_paras["data"],
                                         num_src=num_src, num_dest=num_dest, st=st)

                    if triggers:  # it is a triggered stateflow chart
                        trigger_type = get_attribute_value(triggers[0], "TriggerType")
                        
                        if not trigger_type:
                            trigger_type = "rising"
                        assert trigger_type in ["rising", "falling", "either","function-call"]
                        stateflow.trigger_type = trigger_type
                        stateflow.num_dest += 1
                        stateflow.dest_lines.append(None)
                        # Extract the input events
                        stateflow_blocks = self.model.getElementsByTagName("Stateflow")
                        assert len(stateflow_blocks) == 1
                        charts = stateflow_blocks[0].getElementsByTagName("chart")
                        for chart in charts:
                            if get_attribute_value(block=chart, attribute="name", name=stateflow.name):
                                events = chart.getElementsByTagName("event")
                                for event in events:
                                    event_name = get_attribute_value(block=event, attribute="name")
                                    event_scope = get_attribute_value(block=event, attribute="scope")
                                    if event_scope == "INPUT_EVENT":
                                        event_trigger = get_attribute_value(block=event, attribute="trigger")
                                        if event_trigger == "RISING_EDGE_EVENT":
                                            event_trigger = "rising"
                                        elif event_trigger == "FALLING_EDGE_EVENT":
                                            event_trigger = "falling"
                                        elif event_trigger == "EITHER_EDGE_EVENT":
                                            event_trigger = "either"
                                        elif event_trigger == "FUNCTION_CALL_EVENT":
                                            event_trigger = "function-call"
                                        else:
                                            raise RuntimeError("Not implemented yet")
                                        stateflow.input_events.append((event_trigger, event_name))
                                break

                    assert stateflow.port_to_in_var == dict() and stateflow.port_to_out_var == dict()
                    for child in subsystem.childNodes:
                        if child.nodeName == "Block":
                            if child.getAttribute("BlockType") == "Inport":
                                in_var = child.getAttribute("Name")
                                port_id = get_attribute_value(child, "Port")
                                port_id = int(port_id) - 1 if port_id else 0
                                assert port_id not in stateflow.port_to_in_var
                                stateflow.port_to_in_var[port_id] = in_var
                            elif child.getAttribute("BlockType") == "Outport":
                                out_var = child.getAttribute("Name")
                                if out_var.find("()") == -1:
                                    port_id = get_attribute_value(child, "Port")
                                    port_id = int(port_id) - 1 if port_id else 0
                                    assert port_id not in stateflow.port_to_out_var
                                    stateflow.port_to_out_var[port_id] = out_var

                    self.add_block(stateflow)
                    continue

                # Check if it is a triggered or enabled subsystem
                triggers = [child for child in subsystem.childNodes if child.nodeName == "Block" and
                            child.getAttribute("BlockType") == "TriggerPort"]
                enables = [child for child in subsystem.childNodes if child.nodeName == "Block" and
                           child.getAttribute("BlockType") == "EnablePort"]
                # Enabled and triggered subsystems haven't been considered
                assert len(triggers) + len(enables) <= 1
                if triggers:  # it is a triggered subsystem
                    trigger_type = get_attribute_value(triggers[0], "TriggerType")
                    if not trigger_type:
                        trigger_type = "rising"
                    assert trigger_type in ["rising", "falling", "either", "function-call"]
                    ports = get_attribute_value(block, "Ports")
                    num_dest, num_src, _, _ = [int(port.strip("[ ]")) for port in ports.split(",")]
                    subsystem = Triggered_Subsystem(block_name, num_src, num_dest+1, trigger_type)
                    # Why num_src+1 above?
                    # A: The number of normal in-ports (num_src) + one TriggerPort
                elif enables:
                    assert get_attribute_value(enables[0], "StatesWhenEnabling") is None
                    assert get_attribute_value(enables[0], "PropagateVarSize") is None
                    ports = get_attribute_value(block, "Ports")
                    num_dest, num_src, _ = [int(port.strip("[ ]")) for port in ports.split(",")]
                    subsystem = Enabled_Subsystem(block_name, num_src, num_dest+1)
                else:  # it is a normal subsystem
                    ports = get_attribute_value(block=block, attribute="Ports")
                    num_dest, num_src = [int(port.strip("[ ]")) for port in ports.split(",")]
                    subsystem = Subsystem("subsystem", block_name, num_src, num_dest, st=sample_time)
                subsystem.diagram = SL_Diagram()
                # Parse subsystems recursively
                subsystem.diagram.model = block
                subsystem.diagram.parse_xml(default_SampleTimes)
                self.add_block(subsystem)

        # Add lines
        lines = [child for child in system.childNodes if child.nodeName == "Line"]
        for line in lines:
            line_name = get_attribute_value(block=line, attribute="Name")
            if not line_name:
                line_name = "?"
            ch_name = "?"
            src_block = replace_spaces(get_attribute_value(block=line, attribute="SrcBlock"))
            if src_block in port_name_dict:  # an input port
                ch_name = self.name + "_" + src_block
                src_block = port_name_dict[src_block]
            elif src_block not in self.blocks_dict:
                continue
            src_port = int(get_attribute_value(block=line, attribute="SrcPort")) - 1
            branches = [branch for branch in line.getElementsByTagName(name="Branch")
                        if not branch.getElementsByTagName(name="Branch")]
            if not branches:
                branches = [line]
            for branch in branches:
                dest_block = replace_spaces(get_attribute_value(block=branch, attribute="DstBlock"))
                if dest_block in port_name_dict:  # an output port
                    ch_name = self.name + "_" + dest_block
                    dest_block = port_name_dict[dest_block]
                dest_port = get_attribute_value(block=branch, attribute="DstPort")
                dest_port = -1 if dest_port in ["trigger", "enable"] else int(dest_port) - 1
                if dest_block in self.blocks_dict:
                    self.add_line(src=src_block, dest=dest_block, src_port=src_port, dest_port=dest_port,
                                  name=line_name, ch_name=ch_name)

        # The line name should keep consistent with the corresponding signals
        # if its src_block is a Signal Builder.
        for block in self.blocks_dict.values():
            if block.type == "signalBuilder":
                block.rename_src_lines()

    def add_block(self, block):
        """Add given block to the diagram."""
        assert block.name not in self.blocks_dict
        self.blocks_dict[block.name] = block

    def add_line(self, src, dest, src_port, dest_port, *, name="?", ch_name="?"):
        """Add given line to the diagram."""
        line = SL_Line(src, dest, src_port, dest_port, name=name, ch_name=ch_name)
        src_block = self.blocks_dict[line.src]
        dest_block = self.blocks_dict[line.dest]
        line.src_block = src_block
        line.dest_block = dest_block
        src_block.add_src(line.src_port, line)
        dest_block.add_dest(line.dest_port, line)

    def __str__(self):
        result = ""
        result += "\n".join(str(block) for block in self.blocks_dict.values())
        return result

    def check(self):
        """Checks the diagram is valid. Among the checks are:

        For each block, each dest port is filled, each src port has
        at least one outgoing line.

        """
        pass

    def add_line_name(self):
        """Give each group of lines a name."""

        # Set names of out-going lines from Signal Builders as the correspoding signals
        for block in self.blocks_dict.values():
            if isinstance(block, SignalBuilder):
                block.rename_src_lines()

        num_lines = 0
        for block in self.blocks_dict.values():
            # Give name to the group of lines containing each
            # incoming line (if no name is given already).
            for line in block.dest_lines:
                if line:
                    src, src_port = line.src, line.src_port
                    line_group = self.blocks_dict[src].src_lines[src_port]
                    if line_group[0].name == "?":
                        for line2 in line_group:
                            line2.name = "x" + str(num_lines)
                        num_lines += 1

            # Give name to each group of outgoing lines (if no
            # name is given already).
            for lines in block.src_lines:
                if lines and lines[0].name == "?":
                    for line in lines:
                        line.name = "x" + str(num_lines)
                    num_lines += 1

        # Add channel name for each line
        for block in self.blocks_dict.values():
            for line in block.dest_lines:
                if line:
                    assert line.name != "?"
                    if line.ch_name == "?":
                        line.ch_name = "ch_" + line.name + "_" + str(line.branch)
            for lines in block.src_lines:
                for line in lines:
                    assert line.name != "?"
                    if line.ch_name == "?":
                        line.ch_name = "ch_" + line.name + "_" + str(line.branch)

    def comp_inher_st(self):
        """Compute the sample time for each block with inherent sample time."""
        # Propagation
        terminate = False
        while not terminate:
            terminate = True
            for block in self.blocks_dict.values():
                if block.st == -1:

                    # Deal with triggered subsystems
                    if block.type == "triggered_subsystem":
                        trig_line = block.dest_lines[-1]
                        in_block = self.blocks_dict[trig_line.src]
                        if in_block.st >= 0:
                            block.st = in_block.st
                            block.is_continuous = (block.st == 0)
                            terminate = False
                        continue

                    in_st = []  # list of sample times of inputs of the block
                    for line in block.dest_lines:
                        in_block = self.blocks_dict[line.src]
                        # Xiong: Why can't in_block be a stateflow chart?
                        if not isinstance(in_block, SF_Chart) and in_block.st > 0:
                            in_st.append(in_block.st)
                        elif isinstance(in_block, Constant):
                            continue
                        else:
                            in_st = None
                            break
                    if in_st:
                        block.st = get_gcd(sample_times=in_st)
                        block.is_continuous = (block.st == 0)
                        terminate = False

        # Back-propagation
        terminate = False
        while not terminate:
            terminate = True
            for block in self.blocks_dict.values():
                if block.st == -1:
                    out_st = []  # list of sample times of outputs of the block
                    for lines in block.src_lines:
                        for line in lines:
                            out_block = self.blocks_dict[line.dest]
                            if out_block.st > 0:
                                out_st.append(out_block.st)
                            else:
                                out_st = []
                                break
                    if out_st:
                        block.st = get_gcd(sample_times=out_st)
                        block.is_continuous = (block.st == 0)
                        terminate = False
                
        # Re-classify the constant blocks
        for block in self.blocks_dict.values():
            if block.type == "constant":
                dest_block = self.blocks_dict[block.src_lines[0][0].dest]
                block.st = dest_block.st
                block.is_continuous = dest_block.is_continuous

    def inherit_to_continuous(self):
        for block in self.blocks_dict.values():
            if not isinstance(block, SF_Chart) and block.st == -1:
                block.st = 0
                block.is_continuous = True

    def delete_subsystems(self):
        """Unfold subsystems from the current diagram."""
        # Maintain list of subsystems (to be removed) and list of blocks
        # in those subsystems (to be added to self).
        subsystems = []
        blocks_in_subsystems = []

        for block in self.blocks_dict.values():
            if block.type in ["subsystem", "enabled_subsystem"]:
                # Collect all subsystems to be deleted
                subsystems.append(block.name)
                # The subsystem is treated as a diagram
                subsystem = block.diagram
                # Delete subsystems recursively
                subsystem.delete_subsystems()
                # Move all blocks except ports from the subsystem to the parent system
                for sub_block in subsystem.blocks_dict.values():
                    if sub_block.type not in ["in_port", "out_port"]:
                        blocks_in_subsystems.append(sub_block)
                # Sort the input ports in the subsystem by name
                input_ports = [sub_block for sub_block in subsystem.blocks_dict.values()
                               if sub_block.type == "in_port"]
                input_ports.sort(key=operator.attrgetter('name'))
                # Sort the output ports in the subsystem by name
                output_ports = [sub_block for sub_block in subsystem.blocks_dict.values()
                                if sub_block.type == "out_port"]
                output_ports.sort(key=operator.attrgetter('name'))

                # For each input line, find what is the source of this line
                # (in the current diagram or in other subsystems), and make the
                # new connections.
                for port_id in range(block.num_dest):
                    input_line = block.dest_lines[port_id]

                    # Find the source
                    src_block = None
                    if input_line.src in self.blocks_dict:
                        src_block = self.blocks_dict[input_line.src]
                    else:
                        for subsys in subsystems:
                            if input_line.src in self.blocks_dict[subsys].diagram.blocks_dict:
                                src_block = self.blocks_dict[subsys].diagram.blocks_dict[input_line.src]
                                break

                    # Delete the old line (input_line) from src_block
                    assert src_block is not None, "delete_subsystems: src_block not found."
                    src_block.src_lines[input_line.src_port][input_line.branch] = None

                    # Get the corresponding input port in the subsystem
                    port = input_ports[port_id]
                    assert port.name == "in_" + str(port_id)
                    for port_line in port.src_lines[0]:
                        dest_block = subsystem.blocks_dict[port_line.dest]
                        # Generate a new input line
                        new_input_line = SL_Line(src=src_block.name, dest=dest_block.name,
                                                 src_port=input_line.src_port, dest_port=port_line.dest_port)
                        new_input_line.name = input_line.name
                        # Delete the old line (port_line) and add a new one
                        dest_block.add_dest(port_id=port_line.dest_port, sl_line=new_input_line)
                        # Add a new line for src_block
                        src_block.add_src(port_id=input_line.src_port, sl_line=new_input_line)

                # For each output line, find what is the destination
                # (in the current diagram or in other diagrams), and make
                # the new connections.
                for port_id in range(block.num_src):
                    port = output_ports[port_id]

                    assert port.name == "out_" + str(port_id)
                    port_line = port.dest_lines[0]
                    src_block = subsystem.blocks_dict[port_line.src]

                    # Delete the old line (port_line) from src_block
                    src_block.src_lines[port_line.src_port][port_line.branch] = None
                    for output_line in block.src_lines[port_id]:
                        dest_block = None
                        if output_line.dest in self.blocks_dict:
                            dest_block = self.blocks_dict[output_line.dest]
                        else:
                            for subsys in subsystems:
                                if output_line.dest in self.blocks_dict[subsys].diagram.blocks_dict:
                                    dest_block = self.blocks_dict[subsys].diagram.blocks_dict[output_line.dest]
                                    break

                        # Generate a new output line
                        assert dest_block is not None, "delete_subsystems: dest_block not found"
                        new_output_line = SL_Line(src=src_block.name, dest=dest_block.name,
                                                  src_port=port_line.src_port, dest_port=output_line.dest_port)
                        new_output_line.name = output_line.name
                        # Delete the old line (output_line) and add a new one
                        dest_block.add_dest(port_id=output_line.dest_port, sl_line=new_output_line)
                        # Add a new line for src_block
                        src_block.add_src(port_id=port_line.src_port, sl_line=new_output_line)

        # Delete all the subsystems
        for name in subsystems:
            del self.blocks_dict[name]

        # Add new blocks from subsystems to block_dict
        for block in blocks_in_subsystems:
            assert block.name not in self.blocks_dict, "Repeated block name %s" % block.name
            self.blocks_dict[block.name] = block

    def separate_diagram(self):
        """Separate the diagram into the different parts, and stored in the
        corresponding variables in self.

        """
        for _, block in self.blocks_dict.items():
            # Continuous and discrete blocks contain the field is_continuous
            if hasattr(block, "is_continuous"):
                if isinstance(block, Scope):
                    self.scopes.append(block)
                elif block.is_continuous:
                    self.continuous_blocks.append(block)
                else:
                    self.discrete_blocks.append(block)
            elif isinstance(block, DataStoreMemory):
                self.dsms.append(block)
            else:
                assert False, "block: %s" % type(block)

    def seperate_diagram(self):
        """Seperate a diagram into discrete and continuous subdiagrams."""
        # delete in and out-ports
        blocks_dict = {name: block for name, block in self.blocks_dict.items()
                       if block.type not in ['in_port', 'out_port']}
        # Get stateflow charts and then delete them from block_dict
        sf_charts = [block for block in blocks_dict.values() if block.type == "stateflow"]
        for name in [block.name for block in sf_charts]:
            del blocks_dict[name]

        # Data store memory
        dataStoreMemorys = [block for block in blocks_dict.values() if block.type == "DataStoreMemory"]
        for name in [block.name for block in dataStoreMemorys]:
            del blocks_dict[name]

        # Data store read
        dataStoreReads = [block for block in blocks_dict.values() if block.type == "DataStoreRead"]
        for name in [block.name for block in dataStoreReads]:
            del blocks_dict[name]

        clocks=[block for block in blocks_dict.values() if block.type == "clock"]
        for name in [block.name for block in clocks]:
            del blocks_dict[name]

        muxs = [block for block in blocks_dict.values() if block.type == "mux"]
        for name in [block.name for block in muxs]:
            del blocks_dict[name]
        # Get buffers and then delete them from block_dict
        buffers = [block for block in blocks_dict.values() if block.type == "discrete_buffer"]
        for name in [block.name for block in buffers]:
            del blocks_dict[name]
        discretePulseGenerator=[block for block in blocks_dict.values() if block.type == "DiscretePulseGenerator"]
        for name in [block.name for block in discretePulseGenerator]:
            del blocks_dict[name]  
        # Seperating: search SCC by BFS
        discrete_subdiagrams = []
        continuous_subdiagrams = []
        while blocks_dict:
            _, block = blocks_dict.popitem()
            scc = [block]
            bs = [block]
            while bs:
                b = bs.pop(-1)
                for src_line in b.src_lines:
                    for line in src_line:
                        dest_name = line.dest
                        if dest_name in blocks_dict and blocks_dict[dest_name].is_continuous == block.is_continuous:
                            bs.append(blocks_dict[dest_name])
                            scc.append(blocks_dict[dest_name])
                            del blocks_dict[dest_name]
                for dest_line in b.dest_lines:
                    if dest_line !=None:
                        src_name = dest_line.src
                        if src_name in blocks_dict and blocks_dict[src_name].is_continuous == block.is_continuous:
                            bs.append(blocks_dict[src_name])
                            scc.append(blocks_dict[src_name])
                            del blocks_dict[src_name]
            if block.is_continuous:
                continuous_subdiagrams.append(scc)
            else:
                discrete_subdiagrams.append(scc)

        # Sort discrete blocks
        # discrete_subdiagrams_sorted = []
        # for scc in discrete_subdiagrams:
        #     scc_dict = {block.name: block for block in scc}
        #     sorted_scc = []
        #     while scc_dict:
        #         delete_blocks = []
        #         for block in scc_dict.values():
        #             src_set = set()
        #             for dest_line in block.dest_lines:
        #                 if dest_line !=None:
        #                     src_set.add(dest_line.src)
        #             if src_set.isdisjoint(set(scc_dict.keys())):
        #                 sorted_scc.append(block)
        #                 delete_blocks.append(block.name)
        #         for block_name in delete_blocks:
        #             del scc_dict[block_name]
        #     discrete_subdiagrams_sorted.append(sorted_scc)

        return discrete_subdiagrams, continuous_subdiagrams, sf_charts, buffers, \
            discretePulseGenerator, muxs, dataStoreMemorys, dataStoreReads, clocks

    def add_buffers(self):
        buffers = []
        for block in self.blocks_dict.values():
            if block.type in {"stateflow", "unit_delay"}:
                for port_id in range(len(block.dest_lines)):
                    line = block.dest_lines[port_id]
                    src_block = self.blocks_dict[line.src]
                    if not src_block.is_continuous:
                        if src_block.st == block.st:
                            continue
                        buffer = Discrete_Buffer(in_st=src_block.st, out_st=block.st)
                        buffers.append(buffer)
                        # Link src_block to buffer
                        line.dest = buffer.name
                        line.dest_port = 0
                        assert buffer.dest_lines == [None]
                        buffer.dest_lines = [line]
                        # Link buffer to block
                        line = SL_Line(src=buffer.name, dest=block.name, src_port=0, dest_port=port_id)
                        line.branch = 0
                        assert buffer.src_lines == [[]]
                        buffer.src_lines = [[line]]
                        block.dest_lines[port_id] = line
                
                for branch_list in block.src_lines:
                    for branch in branch_list:
                        dest_block = self.blocks_dict[branch.dest]
                        if not dest_block.is_continuous:
                            if block.st == dest_block.st:
                                continue
                            buffer = Discrete_Buffer(in_st=block.st, out_st=dest_block.st)
                            buffers.append(buffer)
                            # Link buffer to dest_block
                            line = SL_Line(src=buffer.name, dest=dest_block.name,
                                           src_port=0, dest_port=branch.dest_port)
                            line.branch = 0
                            assert buffer.src_lines == [[]]
                            buffer.src_lines = [[line]]
                            dest_block.dest_lines[line.dest_port] = line
                            # Link block to buffer
                            branch.dest = buffer.name
                            branch.dest_port = 0
                            assert buffer.dest_lines == [None]
                            buffer.dest_lines = [branch]
        for buffer in buffers:
            self.add_block(buffer)
        # Reset buffer number to 0
        Discrete_Buffer.num = 0
