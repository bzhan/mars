# Unit test for translation of Simulink diagrams

import unittest

from ss2hcsp.sl.port import Port
from ss2hcsp.sl.integrator import Integrator
from ss2hcsp.sl.divide import Divide
from ss2hcsp.sl.bias import Bias
from ss2hcsp.sl.gain import Gain
from ss2hcsp.sl.add import Add
from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.hcsp import hcsp


class SimTest(unittest.TestCase):
    def testVanDerPol_continuous(self):
        diagram = SL_Diagram()
        diagram.add_block(Integrator(name="intg1", init_value="1"))
        diagram.add_block(Integrator(name="intg2", init_value="1"))
        diagram.add_block(Port(name="in1", port_type="in_port"))
        diagram.add_block(Port(name="out1", port_type="out_port"))
        diagram.add_block(Port("out2", "out_port"))
        diagram.add_line(src="in1", dest="intg1", src_port=0, dest_port=0)
        diagram.add_line(src="intg1", dest="out1", src_port=0, dest_port=0)
        diagram.add_line("intg1", "intg2", 0, 0)
        diagram.add_line("intg2", "out2", 0, 0)
        # print(str(diagram))

        hp_init = hcsp.Sequence(hcsp.Assign("x0", "1"), hcsp.Assign("x1", "1"), hcsp.Assign('t', "0"))
        out_comms = [(hcsp.InputChannel('x0'), hcsp.Skip()),
                     (hcsp.OutputChannel('x1'), hcsp.Skip()),
                     (hcsp.OutputChannel('x2'), hcsp.Skip())]
        hp_ode = hcsp.ODE_Comm([("x1", "x0"), ("x2", "x1"), ("t", "1")], "True", out_comms)
        continuous_hp = hcsp.Sequence(hp_init, hcsp.Loop(hp_ode))
        # print(str(continuous_hp))
        # print(str(diagram.translate_continuous()))
        self.assertEqual(diagram.translate_continuous(), continuous_hp)

    def testVanPerPol_discrete(self):
        diagram = SL_Diagram()
        diagram.add_block(Port(name="in0", port_type="in_port"))
        diagram.add_block(Divide(name="div0", dest_spec="**", st=2))
        diagram.add_block(Bias(name="bias", bias=-1, st=4))
        diagram.add_block(Gain(name="gain", factor=-0.1, st=6))
        diagram.add_block(Port(name="in1", port_type="in_port"))
        diagram.add_block(Divide(name="div1", dest_spec="**", st=8))
        diagram.add_block(Add(name="add", dest_spec="+-", st=4))
        diagram.add_block(Port(name="out", port_type="out_port"))

        diagram.add_line(src="in0", dest="div0", src_port=0, dest_port=0)
        diagram.add_line(src="in0", dest="div0", src_port=0, dest_port=1)
        diagram.add_line(src="in0", dest="add", src_port=0, dest_port=1)
        diagram.add_line(src="div0", dest="bias", src_port=0, dest_port=0)
        diagram.add_line(src="bias", dest="gain", src_port=0, dest_port=0)
        diagram.add_line(src="in1", dest="div1", src_port=0, dest_port=0)
        diagram.add_line(src="gain", dest="div1", src_port=0, dest_port=1)
        diagram.add_line(src="div1", dest="add", src_port=0, dest_port=0)
        diagram.add_line(src="add", dest="out", src_port=0, dest_port=0)

        hp_init = hcsp.Assign(var_name="t", expr="0")
        # input channels
        hp_inputs = [hcsp.InputChannel(var_name="x0"), hcsp.InputChannel(var_name="x4")]
        # div0
        div0_cond = "t % " + diagram.blocks_dict["div0"].st + " == 0"
        div0_hp = hcsp.Assign(var_name="x1", expr="x0*x0")
        hp_div0 = hcsp.Condition(cond=div0_cond, hp=div0_hp)
        # bias
        bias_cond = "t % " + diagram.blocks_dict["bias"].st + " == 0"
        if diagram.blocks_dict["bias"].bias.startswith("-"):
            expr = "x1" + diagram.blocks_dict["bias"].bias
        else:
            expr = "x1+" + diagram.blocks_dict["bias"].bias
        comp = hcsp.Assign(var_name="x2", expr=expr)
        hp_bias = hcsp.Condition(cond=bias_cond, hp=comp)
        # gain
        gain_cond = "t % " + diagram.blocks_dict["gain"].st + " == 0"
        if diagram.blocks_dict["gain"].factor.startswith("-"):
            expr = "x2*(" + diagram.blocks_dict["gain"].factor + ")"
        else:
            expr = "x2*" + diagram.blocks_dict["gain"].factor
        comp = hcsp.Assign(var_name="x3", expr=expr)
        hp_gain = hcsp.Condition(cond=gain_cond, hp=comp)
        # div1
        div1_cond = "t % " + diagram.blocks_dict["div1"].st + " == 0"
        div1_hp = hcsp.Assign(var_name="x5", expr="x4*x3")
        hp_div1 = hcsp.Condition(cond=div1_cond, hp=div1_hp)
        # add
        add_cond = "t % " + diagram.blocks_dict["add"].st + " == 0"
        add_hp = hcsp.Assign(var_name="x6", expr="x5-x0")
        hp_add = hcsp.Condition(cond=add_cond, hp=add_hp)
        # output channel
        hp_outputs = [hcsp.OutputChannel(expr="x6")]
        # time
        ode_time = hcsp.ODE(eqs=[("t", "1")], constraint="t < temp+2")
        hp_time = hcsp.Sequence(hcsp.Assign(var_name="temp", expr="t"), ode_time)

        # Get loop body
        discrete_hps = [hp_div0, hp_bias, hp_gain, hp_div1, hp_add]
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
