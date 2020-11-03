from ss2hcsp.sl.sl_line import SL_Line

from ss2hcsp.sl.port import Port
from ss2hcsp.sl.Continuous.integrator import Integrator, Buffer
from ss2hcsp.sl.Continuous.constant import Constant
from ss2hcsp.sl.MathOperations.product import Product
from ss2hcsp.sl.MathOperations.bias import Bias
from ss2hcsp.sl.MathOperations.gain import Gain
from ss2hcsp.sl.MathOperations.add import Add
from ss2hcsp.sl.MathOperations.my_abs import Abs
from ss2hcsp.sl.LogicOperations.logic import And, Or, Not
from ss2hcsp.sl.LogicOperations.relation import Relation
from ss2hcsp.sl.LogicOperations.reference import Reference
from ss2hcsp.sl.SignalRouting.switch import Switch
from ss2hcsp.sl.SubSystems.subsystem import Subsystem, Triggered_Subsystem
from ss2hcsp.sl.Discontinuities.saturation import Saturation
from ss2hcsp.sl.Discrete.unit_delay import UnitDelay
from ss2hcsp.sl.MathOperations.min_max import MinMax
from ss2hcsp.sf.sf_state import AND_State, OR_State, Junction, Function
from ss2hcsp.sf.sf_chart import SF_Chart
from ss2hcsp.sf.sf_transition import Transition
from ss2hcsp.sl.discrete_buffer import Discrete_Buffer

from xml.dom.minidom import parse
from functools import reduce
from math import gcd, pow
import re
import operator

from ss2hcsp.hcsp.parser import aexpr_parser


def get_gcd(sample_times):
    assert isinstance(sample_times, (list, tuple)) and len(sample_times) >= 1
    assert all(isinstance(st, (int, float)) for st in sample_times)

    if len(sample_times) == 1:
        return sample_times[0]

    if 0 in sample_times:
        return 0
    elif -2 in sample_times:
        return -2
    elif -1 in sample_times:
        return -1

    scaling_positions = []
    for st in sample_times:
        if isinstance(st, int):
            scaling_positions.append(0)
        else:  # isinstance(st, float)
            scaling_positions.append(len(str(st)) - str(st).index(".") - 1)

    scale = pow(10, max(scaling_positions))
    scaling_sample_times = [int(st * scale) for st in sample_times]
    result_gcd = reduce(gcd, scaling_sample_times)
    if result_gcd % scale == 0:
        return result_gcd // int(scale)
    else:
        return result_gcd / scale


def get_attribute_value(block, attribute):
    for node in block.getElementsByTagName("P"):
        if node.getAttribute("Name") == attribute:
            if node.childNodes:
                return node.childNodes[0].data
    return None


class SL_Diagram:
    """Represents a Simulink diagram."""
    def __init__(self, location=""):
        # List of blocks, in order of insertion.
        self.blocks = list()

        # Dictionary of blocks indexed by name
        self.blocks_dict = dict()

        # Dictionary of STATEFLOW parameters indexed by name
        self.chart_parameters = dict()

        # XML data structure
        self.model = None
        
        # Parsed model of the XML file
        if location:
            with open(location) as f:
                self.model = parse(f)

    def parse_stateflow_xml(self):
        """Parse stateflow charts from XML."""

        def get_transitions(blocks):
            """Get a transition dictionary of the form

            {tran_ssid: Transition(...), ...}

            mapping from ID to a transition.
            
            """
            _tran_dict = dict()
            for block in blocks:
                if block.nodeName == "transition":
                    tran_ssid = block.getAttribute("SSID")
                    tran_label = get_attribute_value(block, "labelString")
                    order = int(get_attribute_value(block, "executionOrder"))
                    assert len([child for child in block.childNodes if child.nodeName == "src"]) == 1
                    assert len([child for child in block.childNodes if child.nodeName == "dst"]) == 1
                    src_ssid, dst_ssid = None, None
                    for child in block.childNodes:
                        if child.nodeName == "src":
                            src_ssid = get_attribute_value(child, "SSID")
                        elif child.nodeName == "dst":
                            dst_ssid = get_attribute_value(child, "SSID")
                    assert dst_ssid  # each transition must have a destination state
                    assert tran_ssid not in _tran_dict
                    _tran_dict[tran_ssid] = Transition(ssid=tran_ssid, label=tran_label, order=order,
                                                       src=src_ssid, dst=dst_ssid)
            return _tran_dict
#历史节点修改
        all_out_trans=dict()
        def get_children(block):
            """Get lists of children states and junctions of the current
            block.

            Returned value is:

            _states: list of SF_State objects.
            _junction: list of Junction objects.
            _functions : list of Function objects.
            
            """
            
            _states, _junctions, _functions = list(), list(), list()

            children = [child for child in block.childNodes if child.nodeName == "Children"]
            if not children:
                return _states, _junctions, _functions

            assert len(children) == 1
            # Get outgoing transitions from states in children
            out_trans_dict = get_transitions(children[0].childNodes)
            
            # The number of default transitions is less than 1 at each hierarchy
            assert len([tran for tran in out_trans_dict.values() if tran.src is None]) <= 1
            # Add out_trans and inner_trans to each state
            for child in children[0].childNodes:
                if child.nodeName == "state":
                    ssid = child.getAttribute("SSID")
                    state_type = get_attribute_value(child, "type")
                    if state_type == "FUNC_STATE":
                        # Get functions
                        fun_name = get_attribute_value(child, "labelString")
                        fun_script = get_attribute_value(child, "script")
                        _functions.append(Function(ssid, fun_name, fun_script))
                        continue

                    # Extract AND- and OR-states
                    # Get state label and name
                    labels = get_attribute_value(child, "labelString").split("\n")
                    name = labels[0]  # the name of the state

                    # Get en, du and ex
                    acts = list()  # contains en, du and ex
                    act = ""
                    for label in labels[:0:-1]:
                        act = label + act
                        if re.match(pattern="(en)|(du)|(ex)", string=act):
                            acts.append(act)
                            act = ""
                    en, du, ex = None, None, None
                    for act in acts:
                        assert "==" not in act
                        act = re.sub(pattern="=", repl=":=", string=act)
                        state_acts = [_act.strip("; ") for _act in act[act.index(":") + 1:].split(";")]
                        # state_acts = (lambda x: x[x.index(":") + 1:].split(";").strip("; "))(act)
                        if act.startswith("en"):
                            en = state_acts
                        elif act.startswith("du"):
                            du = state_acts
                        elif act.startswith("ex"):
                            ex = state_acts
                        else:
                            raise RuntimeError("Error in state actions!")

                    # Get default_tran and out_trans
                    default_tran = None
                    out_trans = list()
                    dictMerged2 = dict( out_trans_dict)
                    dictMerged2.update( all_out_trans )
                   
                    for tran in dictMerged2.values():
                        src, dst = tran.src, tran.dst
                        if src is None and dst == ssid:  # it is a default transition
                            default_tran = tran
                        elif src == ssid:  # the src of tran is this state
                            out_trans.append(tran)
                        else:
                            all_out_trans[tran.ssid]=tran
                    out_trans.sort(key=operator.attrgetter("order"))
                    # Get inner_trans     #有问题
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
                    state_type = get_attribute_value(child, "type")
                    if state_type == "AND_STATE":
                        assert default_tran is None and out_trans == []
                        order = int(get_attribute_value(child, "executionOrder"))
                        _state = AND_State(ssid=ssid, inner_trans=inner_trans, name=name, en=en, du=du, ex=ex,
                                           order=order)
                    elif state_type == "OR_STATE":
                        _state = OR_State(ssid=ssid, out_trans=out_trans, inner_trans=inner_trans, name=name,
                                          en=en, du=du, ex=ex, default_tran=default_tran)
                    else:
                        print(state_type)
                        raise RuntimeError("ErrorStates")

                    # Get children states and junctions recursively
                    child_states, child_junctions, child_functions = get_children(child)
                    _state.funs = child_functions
                    for _child in child_states + child_junctions:
                        _child.father = _state
                        _state.children.append(_child)
                        if isinstance(_child ,Junction) and _child.type == "HISTORY_JUNCTION":
                            if isinstance(_state , OR_State):
                                _state.has_history_junc=True

                    if _state.children and isinstance(_state.children[0], AND_State):
                        _state.children.sort(key=operator.attrgetter("order"))
                    _states.append(_state)
                    
                elif child.nodeName == "junction":
                    ssid = child.getAttribute("SSID")
                    junc_type=get_attribute_value(block=child, attribute="type")
                    # Get default_tran and out_trans
                    default_tran = None
                    out_trans = list()
                    for tran in out_trans_dict.values():
                        src, dst = tran.src, tran.dst
                        if src is None and dst == ssid:  # it is a default transition
                            default_tran = tran
                        elif src == ssid:  # the src of tran is this state
                            out_trans.append(tran)
                    out_trans.sort(key=operator.attrgetter("order"))
                    # Create a junction object and put it into _junstions
                    _junctions.append(Junction(ssid=ssid, out_trans=out_trans,junc_type=junc_type))
                
            return _states, _junctions, _functions

        # Create charts
        charts = self.model.getElementsByTagName(name="chart")
        for chart in charts:
            chart_id = chart.getAttribute("id")
            chart_name = get_attribute_value(block=chart, attribute="name")

            # A chart is wrapped into an AND-state
            chart_state = AND_State(ssid=chart_id, name=chart_name)
            states, junctions, functions = get_children(block=chart)
            chart_state.funs = functions
            for state in states + junctions:
                state.father = chart_state
                chart_state.children.append(state)
            if chart_state.children and isinstance(chart_state.children[0], AND_State):
                chart_state.children.sort(key=operator.attrgetter("order"))
            assert chart_state.check_children()

            chart_st = get_attribute_value(block=chart, attribute="sampleTime")
            chart_st = eval(chart_st) if chart_st else -1

            chart_data = dict()
            for data in chart.getElementsByTagName(name="data"):
                var_name = data.getAttribute("name")
                assert var_name and var_name not in chart_data
                value = get_attribute_value(data, "initialValue")
                value = eval(value) if value else 0
                chart_data[var_name] = value
            # chart_vars = [data.getAttribute("name") for data in chart.getElementsByTagName(name="data")]

            assert chart_name not in self.chart_parameters
            self.chart_parameters[chart_name] = {"state": chart_state, "data": chart_data, "st": chart_st}

    def parse_xml(self, model_name=""):
        self.parse_stateflow_xml()

        models = self.model.getElementsByTagName("Model")
        assert len(models) <= 1
        if models:
            model_name = models[0].getAttribute("Name")

        system = self.model.getElementsByTagName("System")[0]
        # Add blocks
        blocks = [child for child in system.childNodes if child.nodeName == "Block"]
        # The following dictionary is used to replace the port names as formatted ones.
        # The name of each port shoud be in the form of port_type + port_number, such as in_0 and out_1
        # in order to delete subsystems successfully (see function delete_subsystems in get_hcsp.py).
        port_name_dict = {}  # in the form {old_name: new_name}
        for block in blocks:
            block_type = block.getAttribute("BlockType")
            block_name = block.getAttribute("Name")
            sample_time = get_attribute_value(block, "SampleTime")
            sample_time = eval(sample_time) if sample_time else -1
            if block_type == "Constant":
                value = get_attribute_value(block, "Value")
                value = eval(value) if value else 1
                self.add_block(Constant(name=block_name, value=value))
            elif block_type == "Integrator":
                init_value = get_attribute_value(block, "InitialCondition")
                init_value = eval(init_value) if init_value else 0
                self.add_block(Integrator(name=block_name, init_value=init_value))
            elif block_type == "Logic":  # AND, OR, NOT
                _operator = get_attribute_value(block, "Operator")
                inputs = get_attribute_value(block, "Inputs")
                num_dest = int(inputs) if inputs else 2
                if _operator == "OR":
                    self.add_block(Or(name=block_name, num_dest=num_dest, st=sample_time))
                elif _operator == "NOT":
                    self.add_block(Not(name=block_name, st=sample_time))
                else:  # _operator == None, meaning it is an AND block
                    self.add_block(And(name=block_name, num_dest=num_dest, st=sample_time))
            elif block_type == "RelationalOperator":
                relation = get_attribute_value(block, "Operator")
                if relation == "~=":
                    relation = "!="
                self.add_block(Relation(name=block_name, relation=relation, st=sample_time))
            elif block_type == "Reference":
                relop = get_attribute_value(block, "relop")
                assert relop
                if relop == "~=":
                    relop = "!="
                self.add_block(Reference(name=block_name, relop=relop, st=sample_time))
            elif block_type == "Abs":
                self.add_block(Abs(name=block_name, st=sample_time))
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
            elif block_type == "Saturate":
                upper_limit = get_attribute_value(block, "UpperLimit")
                upper_limit = eval(upper_limit) if upper_limit else 0.5
                lower_limit = get_attribute_value(block, "LowerLimit")
                lower_limit = eval(lower_limit) if lower_limit else -0.5
                self.add_block(Saturation(name=block_name, up_lim=upper_limit, low_lim=lower_limit, st=sample_time))
            elif block_type == "UnitDelay":
                init_value = get_attribute_value(block, "InitialCondition")
                init_value = eval(init_value) if init_value else 0
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
            elif block_type == "SubSystem":
                subsystem = block.getElementsByTagName("System")[0]

                # Check if it is a stateflow chart
                sf_block_type = get_attribute_value(block, "SFBlockType")
                if sf_block_type == "Chart":     #char 名称必须是Chart改成其他名字九九不能用了
                    assert block_name in self.chart_parameters
                    chart_paras = self.chart_parameters[block_name]
                    ports = list(aexpr_parser.parse(get_attribute_value(block=block, attribute="Ports")).value)
                    if len(ports) == 0:
                        ports = [0, 0]
                    elif len(ports) == 1:
                        ports.append(0)
                    num_dest, num_src = ports
                    stateflow = SF_Chart(name=block_name, state=chart_paras["state"], data=chart_paras["data"],
                                         num_src=num_src, num_dest=num_dest, st=chart_paras["st"])
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
                                port_id = get_attribute_value(child, "Port")
                                port_id = int(port_id) - 1 if port_id else 0
                                assert port_id not in stateflow.port_to_out_var
                                stateflow.port_to_out_var[port_id] = out_var
                    self.add_block(stateflow)
                    continue

                # Check if it is a triggered subsystem
                triggers = [child for child in subsystem.childNodes if child.nodeName == "Block" and
                            child.getAttribute("BlockType") == "TriggerPort"]
                assert len(triggers) <= 1
                if triggers:  # it is a triggered subsystem
                    trigger_type = get_attribute_value(triggers[0], "TriggerType")
                    if not trigger_type:
                        trigger_type = "rising"
                    assert trigger_type in ["rising", "falling", "either"]
                    ports = get_attribute_value(block, "Ports")
                    num_dest, num_src, _, _ = [int(port.strip("[ ]")) for port in ports.split(",")]
                    subsystem = Triggered_Subsystem(block_name, num_src, num_dest, trigger_type)
                else:  # it is a normal subsystem
                    ports = get_attribute_value(block=block, attribute="Ports")
                    num_dest, num_src = [int(port.strip("[ ]")) for port in ports.split(",")]
                    subsystem = Subsystem(name=block_name, num_src=num_src, num_dest=num_dest)
                subsystem.diagram = SL_Diagram()
                # Parse subsystems recursively
                subsystem.diagram.model = block
                inner_model_name = subsystem.diagram.parse_xml(model_name)
                assert inner_model_name == model_name
                self.add_block(subsystem)
            elif block_type == "Inport":
                port_number = get_attribute_value(block, "Port")
                if not port_number:
                    port_number = "1"
                assert block_name not in port_name_dict
                port_name_dict[block_name] = "in_" + str(int(port_number) - 1)
                self.add_block(block=Port(name=port_name_dict[block_name], port_type="in_port"))
            elif block_type == "Outport":
                port_number = get_attribute_value(block=block, attribute="Port")
                if not port_number:
                    port_number = "1"
                assert block_name not in port_name_dict
                port_name_dict[block_name] = "out_" + str(int(port_number) - 1)
                self.add_block(block=Port(name=port_name_dict[block_name], port_type="out_port"))
        # Add lines
        lines = [child for child in system.childNodes if child.nodeName == "Line"]
        for line in lines:
            line_name = get_attribute_value(block=line, attribute="Name")
            if not line_name:
                line_name = "?"
            ch_name = "?"
            src_block = get_attribute_value(block=line, attribute="SrcBlock")
            if src_block in port_name_dict:  # an input port
                ch_name = model_name + "_" + src_block
                src_block = port_name_dict[src_block]
            src_port = int(get_attribute_value(block=line, attribute="SrcPort")) - 1
            branches = [branch for branch in line.getElementsByTagName(name="Branch")
                        if not branch.getElementsByTagName(name="Branch")]
            if not branches:
                branches = [line]
            # if branches:
            for branch in branches:
                dest_block = get_attribute_value(block=branch, attribute="DstBlock")
                if dest_block in port_name_dict:  # an output port
                    assert ch_name == "?"
                    ch_name = model_name + "_" + dest_block
                    dest_block = port_name_dict[dest_block]
                dest_port = get_attribute_value(block=branch, attribute="DstPort")
                dest_port = -1 if dest_port == "trigger" else int(dest_port) - 1
                if dest_block in self.blocks_dict:
                    self.add_line(src=src_block, dest=dest_block, src_port=src_port, dest_port=dest_port,
                                  name=line_name, ch_name=ch_name)

        return model_name

    def add_block(self, block):
        """Add given block to the diagram."""
        assert block.name not in self.blocks_dict
        self.blocks.append(block)
        self.blocks_dict[block.name] = block

    def add_line(self, src, dest, src_port, dest_port, *, name="?", ch_name="?"):
        """Add given line to the diagram."""
        line = SL_Line(src, dest, src_port, dest_port, name=name, ch_name=ch_name)
        src_block = self.blocks_dict[line.src]
        dest_block = self.blocks_dict[line.dest]
        
        src_block.add_src(line.src_port, line)
        dest_block.add_dest(line.dest_port, line)

    def __str__(self):
        blocks = "\n".join(str(block) for block in self.blocks_dict.values())
        # charts = "\n".join(str(chart) for chart in self.charts.values())

        result = ""
        if self.blocks_dict:
            result += "Blocks:\n" + blocks
        # if self.charts:
        #     result += "Charts:\n" + charts
        return result

    def check(self):
        """Checks the diagram is valid. Among the checks are:

        For each block, each dest port is filled, each src port has
        at least one outgoing line.

        """
        pass

    def add_line_name(self):
        # Give each group of lines a name
        num_lines = 0
        for block in self.blocks_dict.values():
            # Give name to the group of lines containing each
            # incoming line (if no name is given already).
            for i, line in enumerate(block.dest_lines):
                src, src_port = line.src, line.src_port
                line_group = self.blocks_dict[src].src_lines[src_port]
                if line_group[0].name == "?":
                    for line2 in line_group:
                        line2.name = "x" + str(num_lines)
                    num_lines += 1
            # Give name to each group of outgoing lines (if no
            # name is given already).
            for i, lines in enumerate(block.src_lines):
                if lines[0].name == "?":
                    for line in lines:
                        line.name = "x" + str(num_lines)
                    num_lines += 1
        # Add channel name for each line
        for block in self.blocks_dict.values():
            for line in block.dest_lines:
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
        terminate = False
        while not terminate:
            terminate = True
            for block in self.blocks_dict.values():
                if block.st == -1:
                    in_st = []  # list of sample times of inputs of the block
                    for line in block.dest_lines:
                        in_block = self.blocks_dict[line.src]
                        if not isinstance(in_block, SF_Chart) and in_block.st >= 0:
                            in_st.append(in_block.st)
                        else:
                            in_st = None
                            break
                    if in_st:
                        block.st = get_gcd(sample_times=in_st)
                        if block.st == 0:
                            block.is_continuous = True
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
        subsystems = []
        blocks_in_subsystems = []
        for block in self.blocks_dict.values():
            if block.type == "subsystem":
                # Collect all the subsystems to be deleted
                subsystems.append(block.name)
                # The subsytem is treated as a diagram
                subsystem = block.diagram
                # Delete subsystems recursively
                subsystem.delete_subsystems()
                # Move all the blocks except ports from the subsystem to the parent system
                for sub_block in subsystem.blocks_dict.values():
                    if sub_block.type not in ["in_port", "out_port"]:
                        blocks_in_subsystems.append(sub_block)
                # Sort the input ports in the subsystem by names
                input_ports = [sub_block for sub_block in subsystem.blocks if sub_block.type == "in_port"]
                input_ports.sort(key=operator.attrgetter('name'))
                # Sort the output ports in the subsystem by names
                output_ports = [sub_block for sub_block in subsystem.blocks if sub_block.type == "out_port"]
                output_ports.sort(key=operator.attrgetter('name'))

                # Delete old input lines and add new ones
                for port_id in range(block.num_dest):
                    input_line = block.dest_lines[port_id]

                    # src_block = blocks_dict[input_line.src]
                    src_block = None
                    if input_line.src in self.blocks_dict:
                        src_block = self.blocks_dict[input_line.src]
                    else:
                        for subsys in subsystems:
                            if input_line.src in self.blocks_dict[subsys].diagram.blocks_dict:
                                src_block = self.blocks_dict[subsys].diagram.blocks_dict[input_line.src]
                                break

                    # Delete the old line (input_line) from src_block
                    assert src_block
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

                # Delete old output lines and add new ones
                for port_id in range(block.num_src):
                    # Get the corresponding output port in the subsystem
                    port = output_ports[port_id]
                    assert port.name == "out_" + str(port_id)
                    port_line = port.dest_lines[0]
                    src_block = subsystem.blocks_dict[port_line.src]
                    # Delete the old line (port_line) from src_block
                    src_block.src_lines[port_line.src_port][port_line.branch] = None
                    for output_line in block.src_lines[port_id]:

                        # dest_block = blocks_dict[output_line.dest]
                        dest_block = None
                        if output_line.dest in self.blocks_dict:
                            dest_block = self.blocks_dict[output_line.dest]
                        else:
                            for subsys in subsystems:
                                if output_line.dest in self.blocks_dict[subsys].diagram.blocks_dict:
                                    dest_block = self.blocks_dict[subsys].diagram.blocks_dict[output_line.dest]
                                    break

                        # Generate a new output line
                        assert dest_block
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
            assert block.name not in self.blocks_dict
            self.blocks_dict[block.name] = block

    def seperate_diagram(self):
        """Seperate a diagram into discrete and continous subdiagrams."""
        # delete in and out-ports
        blocks_dict = {name: block for name, block in self.blocks_dict.items()
                       if block.type not in ['in_port', 'out_port']}

        # Get stateflow charts and then delete them from block_dict
        sf_charts = [block for block in blocks_dict.values() if block.type == "stateflow"]
        for name in [block.name for block in sf_charts]:
            del blocks_dict[name]
        # Get buffers and then delete them from block_dict
        buffers = [block for block in blocks_dict.values() if block.type == "discrete_buffer"]
        for name in [block.name for block in buffers]:
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
                    src_name = dest_line.src
                    if src_name in blocks_dict and blocks_dict[src_name].is_continuous == block.is_continuous:
                        bs.append(blocks_dict[src_name])
                        scc.append(blocks_dict[src_name])
                        del blocks_dict[src_name]
            if block.is_continuous:
                continuous_subdiagrams.append(scc)
            else:
                discrete_subdiagrams.append(scc)

        # Sort disrecte blocks
        discrete_subdiagrams_sorted = []
        for scc in discrete_subdiagrams:
            scc_dict = {block.name: block for block in scc}
            sorted_scc = []
            while scc_dict:
                delete_blocks = []
                for block in scc_dict.values():
                    src_set = set()
                    for dest_line in block.dest_lines:
                        src_set.add(dest_line.src)
                    if src_set.isdisjoint(set(scc_dict.keys())):
                        sorted_scc.append(block)
                        delete_blocks.append(block.name)
                for block_name in delete_blocks:
                    del scc_dict[block_name]
            discrete_subdiagrams_sorted.append(sorted_scc)

        return discrete_subdiagrams_sorted, continuous_subdiagrams, sf_charts, buffers
        # return dis_subdiag_with_chs, con_subdiag_with_chs

    def add_buffers(self):
        buffers = []
        for block in self.blocks_dict.values():
            if block.type == "stateflow":
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
