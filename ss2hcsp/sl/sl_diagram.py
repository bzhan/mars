from ss2hcsp.sl.sl_line import SL_Line

from ss2hcsp.sl.port import Port
from ss2hcsp.sl.Continuous.integrator import Integrator
from ss2hcsp.sl.Continuous.constant import Constant
from ss2hcsp.sl.MathOperations.divide import Divide
from ss2hcsp.sl.MathOperations.bias import Bias
from ss2hcsp.sl.MathOperations.gain import Gain
from ss2hcsp.sl.MathOperations.add import Add
from ss2hcsp.sl.MathOperations.my_abs import Abs
from ss2hcsp.sl.LogicOperations.my_and import And
from ss2hcsp.sl.LogicOperations.my_not import Not
from ss2hcsp.sl.LogicOperations.my_or import Or
from ss2hcsp.sl.LogicOperations.relation import Relation
from ss2hcsp.sl.SignalRouting.switch import Switch
from ss2hcsp.sl.SubSystems.subsystem import Subsystem
from ss2hcsp.sl.Discontinuities.saturation import Saturation
from ss2hcsp.sl.Discrete.unit_delay import UnitDelay
from ss2hcsp.sl.MathOperations.min_max import MinMax
# from ss2hcsp.hcsp import hcsp as hp

from xml.dom.minidom import parse
from functools import reduce
from math import gcd, pow
import re

from ss2hcsp.hcsp.expr import AExpr, AVar, AConst, FunExpr


def get_attribute_value(block, attribute):
    for node in block.getElementsByTagName("P"):
        if node.getAttribute("Name") == attribute:
            return node.childNodes[0].data
    return None


def get_gcd(sample_times):
    assert isinstance(sample_times, list) and len(sample_times) >= 1
    for st in sample_times:
        assert isinstance(st, (int, float))

    if len(sample_times) == 1:
        return sample_times[0]

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


class SL_Diagram:
    """Represents a Simulink diagram."""
    def __init__(self, location=""):
        # List of blocks, in order of insertion.
        self.blocks = list()

        # Dictionary of blocks indexed by name
        self.blocks_dict = dict()

        # Parsed model of the XML file
        if location:
            with open(location) as f:
                self.model = parse(f)
        else:
            self.model = None

    def parse_xml(self):
        system = self.model.getElementsByTagName(name="System")[0]
        # Add blocks
        blocks = [child for child in system.childNodes if child.nodeName == "Block"]
        # The following dictionary is used to replace the port names as formatted ones.
        # The name of each port shoud be in the form of port_type + port_number, such as in_0 and out_1
        # in order to delete subsystems successfully (see function delete_subsystems in get_hcsp.py).
        port_name_dict = {}  # in the form {old_name: new_name}
        for block in blocks:
            block_type = block.getAttribute("BlockType")
            block_name = block.getAttribute("Name")
            if block_type == "Constant":
                value = get_attribute_value(block=block, attribute="Value")
                value = eval(value) if value else 1
                self.add_block(block=Constant(name=block_name, value=value))
            elif block_type == "Integrator":
                init_value = get_attribute_value(block=block, attribute="InitialCondition")
                # init_value = eval(init_value) if init_value else 0
                self.add_block(block=Integrator(name=block_name, init_value=eval(init_value)))
            elif block_type == "Logic":  # AND, OR, NOT
                operator = get_attribute_value(block=block, attribute="Operator")
                inputs = get_attribute_value(block=block, attribute="Inputs")
                num_dest = int(inputs) if inputs else 2
                if operator == "OR":
                    self.add_block(block=Or(name=block_name, num_dest=num_dest))
                elif operator == "NOT":
                    self.add_block(block=Not(name=block_name))
                else:  # operator == None, meaning it is an AND block
                    self.add_block(block=And(name=block_name, num_dest=num_dest))
            elif block_type == "RelationalOperator":
                # operator_relation = {"&gt;": ">", "&gt;=": ">=", "&lt;": "<", "&lt;=": "<=", "~=": "!=", "==": "=="}
                relation = get_attribute_value(block=block, attribute="Operator")
                if relation == "~=":
                    relation = "!="
                self.add_block(block=Relation(name=block_name, relation=relation))
            elif block_type == "Abs":
                self.add_block(block=Abs(name=block_name))
            elif block_type == "Sum":
                inputs = get_attribute_value(block=block, attribute="Inputs")
                dest_spec = inputs.replace("|", "") if inputs else "++"
                self.add_block(block=Add(name=block_name, dest_spec=dest_spec))
            elif block_type == "Bias":
                bias = get_attribute_value(block=block, attribute="Bias")
                self.add_block(block=Bias(name=block_name, bias=eval(bias)))
            elif block_type == "Product":
                inputs = get_attribute_value(block=block, attribute="Inputs")
                dest_spec = inputs.replace("|", "") if inputs else "**"
                self.add_block(block=Divide(name=block_name, dest_spec=dest_spec))
            elif block_type == "Gain":
                factor = get_attribute_value(block=block, attribute="Gain")
                self.add_block(block=Gain(name=block_name, factor=eval(factor)))
            elif block_type == "Saturate":
                upper_limit = get_attribute_value(block=block, attribute="UpperLimit")
                upper_limit = eval(upper_limit) if upper_limit else 0.5
                lower_limit = get_attribute_value(block=block, attribute="LowerLimit")
                lower_limit = eval(lower_limit) if lower_limit else -0.5
                self.add_block(block=Saturation(name=block_name, up_lim=upper_limit, low_lim=lower_limit))
            elif block_type == "UnitDelay":
                init_value = get_attribute_value(block=block, attribute="InitialCondition")
                init_value = eval(init_value) if init_value else 0
                sample_time = get_attribute_value(block=block, attribute="SampleTime")
                sample_time = eval(sample_time) if sample_time else -1
                self.add_block(block=UnitDelay(name=block_name, init_value=init_value, delay=sample_time))
            elif block_type == "MinMax":
                fun_name = get_attribute_value(block=block, attribute="Function")
                fun_name = fun_name if fun_name else "min"
                input_num = get_attribute_value(block=block, attribute="Inputs")
                input_num = int(input_num) if input_num else 1
                self.add_block(block=MinMax(name=block_name, num_dest=input_num, fun_name=fun_name))
            elif block_type == "Switch":
                criteria = get_attribute_value(block=block, attribute="Criteria")
                relation = ">" if criteria == "u2 > Threshold" else ("!=" if criteria == "u2 ~= 0" else ">=")
                threshold = get_attribute_value(block=block, attribute="Threshold")
                threshold = eval(threshold) if threshold else 0
                self.add_block(block=Switch(name=block_name, relation=relation, threshold=threshold))
            elif block_type == "SubSystem":
                ports = get_attribute_value(block=block, attribute="Ports")
                num_dest, num_src = [int(port.strip("[ ]")) for port in ports.split(",")]
                subsystem = Subsystem(name=block_name, num_src=num_src, num_dest=num_dest)
                subsystem.diagram = SL_Diagram()
                # Parse subsystems recursively
                subsystem.diagram.model = block
                subsystem.diagram.parse_xml()
                self.add_block(block=subsystem)
            elif block_type == "Inport":
                port_number = get_attribute_value(block=block, attribute="Port")
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
            src_block = get_attribute_value(block=line, attribute="SrcBlock")
            if src_block in port_name_dict:
                src_block = port_name_dict[src_block]
            src_port = int(get_attribute_value(block=line, attribute="SrcPort")) - 1
            branches = [branch for branch in line.getElementsByTagName(name="Branch")
                        if not branch.getElementsByTagName(name="Branch")]
            if branches:
                for branch in branches:
                    dest_block = get_attribute_value(block=branch, attribute="DstBlock")
                    if dest_block in port_name_dict:
                        dest_block = port_name_dict[dest_block]
                    dest_port = int(get_attribute_value(block=branch, attribute="DstPort")) - 1
                    if dest_block in self.blocks_dict:
                        self.add_line(src=src_block, dest=dest_block, src_port=src_port, dest_port=dest_port,
                                      name=line_name)
            else:  # No branches
                dest_block = get_attribute_value(block=line, attribute="DstBlock")
                if dest_block in port_name_dict:
                    dest_block = port_name_dict[dest_block]
                dest_port = int(get_attribute_value(block=line, attribute="DstPort")) - 1
                if dest_block in self.blocks_dict:
                    self.add_line(src=src_block, dest=dest_block, src_port=src_port, dest_port=dest_port,
                                  name=line_name)

    def add_block(self, block):
        """Add given block to the diagram."""
        self.blocks.append(block)
        self.blocks_dict[block.name] = block

    def add_line(self, src, dest, src_port, dest_port, *, name="?"):
        """Add given line to the diagram."""
        line = SL_Line(src, dest, src_port, dest_port, name=name)
        src_block = self.blocks_dict[line.src]
        dest_block = self.blocks_dict[line.dest]
        
        src_block.add_src(line.src_port, line)
        dest_block.add_dest(line.dest_port, line)

    def __str__(self):
        return "\n".join(str(block) for block in self.blocks_dict.values())

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

    def comp_inher_st(self):
        """Compute the sample time for each block with inherent sample time.
        This function cannot be executed correctly until all the ports are deleted, i.e.,
        delete_ports() should precede comp_inher_st(), or let delete_port() be
        at the begining of comp_inher_st()."""
        # self.delete_ports()
        terminate = False
        while not terminate:
            terminate = True
            for block in self.blocks_dict.values():
                if block.st == -1:
                    in_st = []  # list of sample times of inputs of the block
                    for line in block.dest_lines:
                        if line.src in self.blocks_dict and self.blocks_dict[line.src].st != -1:
                            in_block = self.blocks_dict[line.src]
                            in_st.append(in_block.st)
                        else:
                            in_st = None
                            break
                    if in_st:
                        # in_st = [int(st) for st in in_st]
                        # block.st = reduce(gcd, in_st) if len(in_st) >= 2 else in_st[0]
                        block.st = get_gcd(sample_times=in_st)
                        if block.st == 0:
                            block.is_continuous = True
                        terminate = False

        # Define the sample time for each block whose sample time is still unknown
        for block in self.blocks_dict.values():
            if block.st == -1:
                known_in_st = []  # list of known sample times of inputs of the block
                unknown_in_st = []  # list of unknown sample times of inputs of the block
                for line in block.dest_lines:
                    if line.src in self.blocks_dict:
                        in_block = self.blocks_dict[line.src]
                        # if re.match("\\d+", self.blocks_dict[line.src]):
                        if re.match("\\d+", str(in_block.st)):
                            known_in_st.append(in_block.st)
                        else:
                            unknown_in_st.append(AVar(in_block.name))
                    else:  # in_block is a port, deleted at the begining
                        unknown_in_st.append(AVar(line.name))
                if known_in_st:
                    known_in_st = [AConst(get_gcd(sample_times=known_in_st))]
                    # known_in_st = [AConst(reduce(gcd, known_in_st) if len(known_in_st) >= 2 else known_in_st[0])]
                known_in_st.extend(unknown_in_st)
                if len(known_in_st) == 1:
                    block.st = known_in_st[0]
                else:  # len(known_in_st) >= 2
                    # block.st = "gcd(" + ", ".join(unknown_in_st) + ")"
                    block.st = FunExpr(fun_name="gcd", exprs=known_in_st)
        # Deal with unit_delay and constant blocks
        for block in self.blocks_dict.values():
            if block.type == "unit_delay":
                if block.delay == -1:  # the delay is unknow
                    src_block = self.blocks_dict[block.dest_lines[0].src]
                    # assert isinstance(src_block.st, AExpr)
                    block.delay = src_block.st if isinstance(src_block.st, AExpr) else AConst(src_block.st)
                else:
                    block.delay = AConst(block.delay)
            elif block.type == "constant":
                dest_block = self.blocks_dict[block.src_lines[0][0].dest]
                block.is_continuous = dest_block.is_continuous

    def delete_ports(self):
        for block in self.blocks:
            if block.type == "in_port" or block.type == "out_port":
                del self.blocks_dict[block.name]
        self.blocks = self.blocks_dict.values()
