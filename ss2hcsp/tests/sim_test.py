# Unit test for translation of Simulink diagrams

import unittest

from ss2hcsp.sl.port import Port
from ss2hcsp.sl.Continuous.integrator import Integrator
from ss2hcsp.sl.Continuous.constant import Constant
from ss2hcsp.sl.MathOperations.divide import Divide
from ss2hcsp.sl.MathOperations.bias import Bias
from ss2hcsp.sl.MathOperations.gain import Gain
from ss2hcsp.sl.MathOperations.add import Add
from ss2hcsp.sl.LogicOperations.my_and import And
from ss2hcsp.sl.LogicOperations.my_not import Not
from ss2hcsp.sl.LogicOperations.my_or import Or
from ss2hcsp.sl.LogicOperations.relation import Relation
from ss2hcsp.sl.SignalRouting.switch import Switch
from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.hcsp import hcsp
import ss2hcsp.sl.get_hcsp as get_hp


class SimTest(unittest.TestCase):
    def testVanDerPol_continuous(self):
        diagram = SL_Diagram()
        diagram.add_block(Integrator(name="intg1", init_value="3"))
        diagram.add_block(Integrator(name="intg2", init_value="7"))
        # diagram.add_block(Port(name="in1", port_type="in_port"))
        diagram.add_block(And(name="and", num_dest=2))
        diagram.add_block(Switch(name="switch", relation=">=", threshold=5))
        diagram.add_block(Switch(name="switch1", relation="<", threshold=10))
        diagram.add_block(Port(name="in0", port_type="in_port"))
        diagram.add_block(Port(name="in1", port_type="in_port"))
        diagram.add_block(Port(name="in2", port_type="in_port"))
        diagram.add_block(Port(name="out0", port_type="out_port"))
        diagram.add_line(src="in0", dest="intg1", src_port=0, dest_port=0)
        # diagram.add_line(src="intg1", dest="out1", src_port=0, dest_port=0)
        diagram.add_line("intg1", "intg2", 0, 0)
        diagram.add_line("intg2", "and", 0, 0)
        diagram.add_line("intg2", "and", 0, 1)
        diagram.add_line("and", "switch", 0, 1)
        diagram.add_line("in1", "switch", 0, 0)
        diagram.add_line("in2", "switch", 0, 2)
        diagram.add_line("switch", "switch1", 0, 1)
        diagram.add_line("in1", "switch1", 0, 0)
        diagram.add_line("in2", "switch1", 0, 2)
        diagram.add_line("switch1", "out0", 0, 0)
        diagram.add_line_name()
        # print(diagram)
        diagram.delete_ports()
        print(diagram.blocks)

        hp_init = hcsp.Sequence(hcsp.Assign("x1", "3"), hcsp.Assign("x2", "7"), hcsp.Assign("t", "0"))
        out_comms_0 = [(hcsp.InputChannel("x0"), hcsp.Skip()), (hcsp.InputChannel("x4"), hcsp.Skip()),
                       (hcsp.InputChannel("x5"), hcsp.Skip()), (hcsp.OutputChannel(var_name="x7", expr="x4"), hcsp.Skip())]
        constraint0 = "min(x2, x2)>=5&&x4<10||min(x2, x2)<5&&x5<10"
        hp_ode0 = hcsp.ODE_Comm([("x1", "x0"), ("x2", "x1"), ("t", "1")], constraint0, out_comms_0)
        # continuous_hp0 = hcsp.Sequence(hp_init, hcsp.Loop(hp_ode0))

        out_comms_1 = [(hcsp.InputChannel("x0"), hcsp.Skip()), (hcsp.InputChannel("x4"), hcsp.Skip()),
                       (hcsp.InputChannel("x5"), hcsp.Skip()), (hcsp.OutputChannel(var_name="x7", expr="x5"), hcsp.Skip())]
        constraint1 = "min(x2, x2)>=5&&x4>=10||min(x2, x2)<5&&x5>=10"
        hp_ode1 = hcsp.ODE_Comm([("x1", "x0"), ("x2", "x1"), ("t", "1")], constraint1, out_comms_1)
        # continuous_hp1 = hcsp.Sequence(hp_init, hcsp.Loop(hp_ode1))

        continuous_hp = hcsp.Sequence(hp_init, hcsp.Loop(hcsp.Sequence(hp_ode0, hp_ode1)))
        print("Expected result: ", continuous_hp)
        print("Real result: ", get_hp.translate_continuous(diagram.blocks))
        # diagram.seperate_diagram()
        self.assertEqual(get_hp.translate_continuous(diagram.blocks), continuous_hp)
        print("-" * 50)
        # get_hp.seperate_diagram(diagram.blocks_dict)

    # def testVanPerPol_discrete(self):
    #     diagram = SL_Diagram()
    #     diagram.add_block(Port(name="in0", port_type="in_port"))
    #     diagram.add_block(And(name="and", num_dest=2, st=-1))
    #     diagram.add_block(Not(name="not", st=4))
    #     diagram.add_block(Gain(name="gain", factor=-0.1, st=-1))
    #     diagram.add_block(Port(name="in1", port_type="in_port"))
    #     diagram.add_block(Or(name="or", num_dest=2, st=8))
    #     diagram.add_block(Relation(name="relation", relation="<=", st=10))
    #     diagram.add_block(Port(name="out", port_type="out_port"))
    #
    #     diagram.add_line(src="in0", dest="and", src_port=0, dest_port=0)
    #     diagram.add_line(src="in0", dest="and", src_port=0, dest_port=1)
    #     diagram.add_line(src="in0", dest="relation", src_port=0, dest_port=1)
    #     diagram.add_line(src="and", dest="not", src_port=0, dest_port=0)
    #     diagram.add_line(src="not", dest="gain", src_port=0, dest_port=0)
    #     diagram.add_line(src="in1", dest="or", src_port=0, dest_port=0)
    #     diagram.add_line(src="gain", dest="or", src_port=0, dest_port=1)
    #     diagram.add_line(src="or", dest="relation", src_port=0, dest_port=0)
    #     diagram.add_line(src="relation", dest="out", src_port=0, dest_port=0)
    #
    #     diagram.add_block(Port(name="in2", port_type="in_port"))
    #     diagram.add_block(Port(name="in3", port_type="in_port"))
    #     diagram.add_block(Port(name="in4", port_type="in_port"))
    #     diagram.add_block(Switch(name="switch", relation=">=", threshold=20, st=4))
    #     diagram.add_block(Port(name="out1", port_type="out_port"))
    #     diagram.add_line(src="in2", dest="switch", src_port=0, dest_port=0)
    #     diagram.add_line(src="in3", dest="switch", src_port=0, dest_port=1)
    #     diagram.add_line(src="in4", dest="switch", src_port=0, dest_port=2)
    #     diagram.add_line(src="switch", dest="out1", src_port=0, dest_port=0)
    #
    #     # print(diagram)
    #     diagram.add_line_name()
    #     diagram.delete_ports()
    #     diagram.comp_inher_st()
    #
    #     hp_init = hcsp.Assign(var_name="t", expr="0")
    #     # input channels
    #     hp_inputs = [hcsp.InputChannel(var_name="x0"), hcsp.InputChannel(var_name="x4"),
    #                  hcsp.InputChannel(var_name="x7"), hcsp.InputChannel(var_name="x8"),
    #                  hcsp.InputChannel(var_name="x9")]
    #     # and
    #     and_cond = "t%" + diagram.blocks_dict["and"].st + "==0"
    #     and_hp = hcsp.Assign(var_name="x1", expr="min(x0, x0)")
    #     hp_and = hcsp.Condition(cond=and_cond, hp=and_hp)
    #     # not
    #     not_cond = "t%" + diagram.blocks_dict["not"].st + "==0"
    #     # if diagram.blocks_dict["bias"].bias.startswith("-"):
    #     #     expr = "x1" + diagram.blocks_dict["bias"].bias
    #     # else:
    #     #     expr = "x1+" + diagram.blocks_dict["bias"].bias
    #     comp = hcsp.Assign(var_name="x2", expr="1-x1")
    #     hp_not = hcsp.Condition(cond=not_cond, hp=comp)
    #     # gain
    #     gain_cond = "t%" + diagram.blocks_dict["gain"].st + "==0"
    #     if diagram.blocks_dict["gain"].factor.startswith("-"):
    #         expr = "x2*(" + diagram.blocks_dict["gain"].factor + ")"
    #     else:
    #         expr = "x2*" + diagram.blocks_dict["gain"].factor
    #     comp = hcsp.Assign(var_name="x3", expr=expr)
    #     hp_gain = hcsp.Condition(cond=gain_cond, hp=comp)
    #     # or
    #     or_cond = "t%" + diagram.blocks_dict["or"].st + "==0"
    #     or_hp = hcsp.Assign(var_name="x5", expr="max(x4, x3)")
    #     hp_or = hcsp.Condition(cond=or_cond, hp=or_hp)
    #     # relation
    #     relation_cond = "t%" + diagram.blocks_dict["relation"].st + "==0"
    #     relation_hp = hcsp.Assign(var_name="x6", expr="x5<=x0")
    #     hp_relation = hcsp.Condition(cond=relation_cond, hp=relation_hp)
    #     # switch
    #     switch_cond = "t%" + diagram.blocks_dict["switch"].st + "==0"
    #     cond_hp1 = hcsp.Condition(cond="x8>=20", hp=hcsp.Assign("x10", "x7"))
    #     cond_hp2 = hcsp.Condition(cond="x8<20", hp=hcsp.Assign("x10", "x9"))
    #     hp_switch = hcsp.Condition(cond=switch_cond, hp=hcsp.Sequence(cond_hp1, cond_hp2))
    #     # output channel
    #     hp_outputs = [hcsp.OutputChannel(expr="x10"), hcsp.OutputChannel(expr="x6")]
    #     # time
    #     ode_time = hcsp.ODE(eqs=[("t", "1")], constraint="t<temp+gcd(and, 2)")
    #     hp_time = hcsp.Sequence(hcsp.Assign(var_name="temp", expr="t"), ode_time)
    #
    #     # Get loop body
    #     discrete_hps = [hp_and, hp_not, hp_gain, hp_or, hp_relation, hp_switch]
    #     loop_hps = hp_inputs + discrete_hps + hp_outputs
    #     loop_hps.append(hp_time)
    #     discrete_hp = hcsp.Sequence(hp_init, hcsp.Loop(hcsp.Sequence(*loop_hps)))
    #     print(discrete_hp)
    #     print(get_hp.translate_discrete(diagram.blocks))
    #     self.assertEqual(get_hp.translate_discrete(diagram.blocks), discrete_hp)
    #     discrete_subdiagrams_sorted, continuous_subdiagrams = get_hp.seperate_diagram(diagram.blocks_dict)
    #     get_hp.get_processes(discrete_subdiagrams_sorted, continuous_subdiagrams)

    def testVanPerPol_hybrid(self):
        diagram = SL_Diagram()

        # Add continuous blocks
        diagram.add_block(Integrator(name="intg1", init_value="1"))
        diagram.add_block(Integrator(name="intg2", init_value="10"))
        # diagram.add_block(Constant(name="con", value=10))
        # diagram.add_block(Port(name="out1", port_type="out_port"))
        # diagram.add_block(Port("out2", "out_port"))

        # Add discrete blocks
        # diagram.add_block(Port(name="in0", port_type="in_port"))
        diagram.add_block(And(name="and", num_dest=2, st=-1))
        diagram.add_block(Not(name="not", st=4))
        diagram.add_block(Gain(name="gain", factor=-0.1, st=-1))
        # diagram.add_block(Port(name="in1", port_type="in_port"))
        diagram.add_block(Or(name="or", num_dest=2, st=8))
        diagram.add_block(Relation(name="relation", relation="<=", st=10))
        # diagram.add_block(Port(name="out", port_type="out_port"))

        # Add lines
        diagram.add_line(src="relation", dest="intg1", src_port=0, dest_port=0)
        diagram.add_line(src="intg1", dest="or", src_port=0, dest_port=0)
        diagram.add_line(src="intg1", dest="intg2", src_port=0, dest_port=0)
        diagram.add_line(src="intg2", dest="and", src_port=0, dest_port=0)
        diagram.add_line(src="intg2", dest="and", src_port=0, dest_port=1)
        diagram.add_line(src="intg2", dest="relation", src_port=0, dest_port=1)
        # diagram.add_line(src="in0", dest="and", src_port=0, dest_port=0)
        # diagram.add_line(src="in0", dest="and", src_port=0, dest_port=1)
        # diagram.add_line(src="in0", dest="relation", src_port=0, dest_port=1)
        diagram.add_line(src="and", dest="not", src_port=0, dest_port=0)
        diagram.add_line(src="not", dest="gain", src_port=0, dest_port=0)
        # diagram.add_line(src="in1", dest="or", src_port=0, dest_port=0)
        diagram.add_line(src="gain", dest="or", src_port=0, dest_port=1)
        diagram.add_line(src="or", dest="relation", src_port=0, dest_port=0)
        # diagram.add_line(src="relation", dest="out", src_port=0, dest_port=0)

        diagram.add_line_name()
        diagram.comp_inher_st()
        # print(diagram)
        discrete_subdiagrams_sorted, continuous_subdiagrams = get_hp.seperate_diagram(diagram.blocks_dict)
        get_hp.get_processes(discrete_subdiagrams_sorted, continuous_subdiagrams)


if __name__ == "__main__":
    unittest.main()
