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


class SimTest(unittest.TestCase):
    def testVanDerPol_continuous(self):
        diagram = SL_Diagram()
        diagram.add_block(Integrator(name="intg1", init_value="1"))
        diagram.add_block(Integrator(name="intg2", init_value="1"))
        # diagram.add_block(Port(name="in1", port_type="in_port"))
        diagram.add_block(Constant(name="con", value=10))
        diagram.add_block(Port(name="out1", port_type="out_port"))
        diagram.add_block(Port("out2", "out_port"))
        diagram.add_line(src="con", dest="intg1", src_port=0, dest_port=0)
        diagram.add_line(src="intg1", dest="out1", src_port=0, dest_port=0)
        diagram.add_line("intg1", "intg2", 0, 0)
        diagram.add_line("intg2", "out2", 0, 0)
        diagram.add_line_name()
        # print(diagram)

        hp_init = hcsp.Sequence(hcsp.Assign("x1", "1"), hcsp.Assign("x2", "1"), hcsp.Assign("x0", "10"), hcsp.Assign('t', "0"))
        out_comms = [(hcsp.OutputChannel('x1'), hcsp.Skip()),  # (hcsp.InputChannel('x0'), hcsp.Skip()),
                     (hcsp.OutputChannel('x2'), hcsp.Skip())]
        hp_ode = hcsp.ODE_Comm([("x1", "x0"), ("x2", "x1"), ("x0", "0"), ("t", "1")], "True", out_comms)
        continuous_hp = hcsp.Sequence(hp_init, hcsp.Loop(hp_ode))
        # print(str(continuous_hp))
        # print(str(diagram.translate_continuous()))
        self.assertEqual(diagram.translate_continuous(), continuous_hp)

    def testVanPerPol_discrete(self):
        diagram = SL_Diagram()
        diagram.add_block(Port(name="in0", port_type="in_port"))
        diagram.add_block(And(name="and", num_dest=2, st=2))
        diagram.add_block(Not(name="not", st=4))
        diagram.add_block(Gain(name="gain", factor=-0.1, st=6))
        diagram.add_block(Port(name="in1", port_type="in_port"))
        diagram.add_block(Or(name="or", num_dest=2, st=8))
        diagram.add_block(Relation(name="relation", relation="<=", st=4))
        diagram.add_block(Port(name="out", port_type="out_port"))

        diagram.add_line(src="in0", dest="and", src_port=0, dest_port=0)
        diagram.add_line(src="in0", dest="and", src_port=0, dest_port=1)
        diagram.add_line(src="in0", dest="relation", src_port=0, dest_port=1)
        diagram.add_line(src="and", dest="not", src_port=0, dest_port=0)
        diagram.add_line(src="not", dest="gain", src_port=0, dest_port=0)
        diagram.add_line(src="in1", dest="or", src_port=0, dest_port=0)
        diagram.add_line(src="gain", dest="or", src_port=0, dest_port=1)
        diagram.add_line(src="or", dest="relation", src_port=0, dest_port=0)
        diagram.add_line(src="relation", dest="out", src_port=0, dest_port=0)

        diagram.add_block(Port(name="in2", port_type="in_port"))
        diagram.add_block(Port(name="in3", port_type="in_port"))
        diagram.add_block(Port(name="in4", port_type="in_port"))
        diagram.add_block(Switch(name="switch", relation=">=", threshold=20, st=4))
        diagram.add_block(Port(name="out1", port_type="out_port"))
        diagram.add_line(src="in2", dest="switch", src_port=0, dest_port=0)
        diagram.add_line(src="in3", dest="switch", src_port=0, dest_port=1)
        diagram.add_line(src="in4", dest="switch", src_port=0, dest_port=2)
        diagram.add_line(src="switch", dest="out1", src_port=0, dest_port=0)

        hp_init = hcsp.Assign(var_name="t", expr="0")
        # input channels
        hp_inputs = [hcsp.InputChannel(var_name="x0"), hcsp.InputChannel(var_name="x4"),
                     hcsp.InputChannel(var_name="x7"), hcsp.InputChannel(var_name="x8"),
                     hcsp.InputChannel(var_name="x9")]
        # and
        and_cond = "t%" + diagram.blocks_dict["and"].st + "==0"
        and_hp = hcsp.Assign(var_name="x1", expr="min(x0, x0)")
        hp_and = hcsp.Condition(cond=and_cond, hp=and_hp)
        # not
        not_cond = "t%" + diagram.blocks_dict["not"].st + "==0"
        # if diagram.blocks_dict["bias"].bias.startswith("-"):
        #     expr = "x1" + diagram.blocks_dict["bias"].bias
        # else:
        #     expr = "x1+" + diagram.blocks_dict["bias"].bias
        comp = hcsp.Assign(var_name="x2", expr="1-x1")
        hp_not = hcsp.Condition(cond=not_cond, hp=comp)
        # gain
        gain_cond = "t%" + diagram.blocks_dict["gain"].st + "==0"
        if diagram.blocks_dict["gain"].factor.startswith("-"):
            expr = "x2*(" + diagram.blocks_dict["gain"].factor + ")"
        else:
            expr = "x2*" + diagram.blocks_dict["gain"].factor
        comp = hcsp.Assign(var_name="x3", expr=expr)
        hp_gain = hcsp.Condition(cond=gain_cond, hp=comp)
        # or
        or_cond = "t%" + diagram.blocks_dict["or"].st + "==0"
        or_hp = hcsp.Assign(var_name="x5", expr="max(x4, x3)")
        hp_or = hcsp.Condition(cond=or_cond, hp=or_hp)
        # relation
        relation_cond = "t%" + diagram.blocks_dict["relation"].st + "==0"
        relation_hp = hcsp.Assign(var_name="x6", expr="x5<=x0")
        hp_relation = hcsp.Condition(cond=relation_cond, hp=relation_hp)
        # switch
        switch_cond = "t%" + diagram.blocks_dict["switch"].st + "==0"
        cond_hp1 = hcsp.Condition(cond="x8>=20", hp=hcsp.Assign("x10", "x7"))
        cond_hp2 = hcsp.Condition(cond="x8<20", hp=hcsp.Assign("x10", "x9"))
        hp_switch = hcsp.Condition(cond=switch_cond, hp=hcsp.Sequence(cond_hp1, cond_hp2))
        # output channel
        hp_outputs = [hcsp.OutputChannel(expr="x6"), hcsp.OutputChannel(expr="x10")]
        # time
        ode_time = hcsp.ODE(eqs=[("t", "1")], constraint="t<temp+2")
        hp_time = hcsp.Sequence(hcsp.Assign(var_name="temp", expr="t"), ode_time)

        # Get loop body
        discrete_hps = [hp_and, hp_not, hp_gain, hp_or, hp_relation, hp_switch]
        loop_hps = hp_inputs + discrete_hps + hp_outputs
        loop_hps.append(hp_time)
        discrete_hp = hcsp.Sequence(hp_init, hcsp.Loop(hcsp.Sequence(*loop_hps)))
        print(discrete_hp)
        print(diagram.translate_discrete())
        # diagram.add_line_name()
        # print(diagram)
        self.assertEqual(diagram.translate_discrete(), discrete_hp)


if __name__ == "__main__":
    unittest.main()
