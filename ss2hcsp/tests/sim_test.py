# Unit test for translation of Simulink diagrams

import unittest

from ss2hcsp.sl.port import Port
from ss2hcsp.sl.integrator import Integrator
from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.hcsp import hcsp

class SimTest(unittest.TestCase):
    def testVanDerPol1(self):
        diagram = SL_Diagram()
        diagram.add_block(Integrator(name="intg1", init_value=1))
        diagram.add_block(Integrator(name="intg2", init_value=1))
        diagram.add_block(Port(name="in1", port_type="in_port"))
        diagram.add_block(Port(name="out1", port_type="out_port"))
        diagram.add_block(Port("out2", "out_port"))
        diagram.add_line(src="in1", dest="intg1", src_port=0, dest_port=0)
        diagram.add_line(src="intg1", dest="out1", src_port=0, dest_port=0)
        diagram.add_line("intg1", "intg2", 0, 0)
        diagram.add_line("intg2", "out2", 0, 0)

        hp_init = hcsp.Sequence(hcsp.Assign("x", "1"), hcsp.Assign("y", "1"), hcsp.Assign('t', "0"))
        out_comms = [(hcsp.InputChannel("chx", 'x'), hcsp.Skip()),
                     (hcsp.OutputChannel("chy", 'y'), hcsp.Skip()),
                     (hcsp.OutputChannel("chz", 'z'), hcsp.Skip())]
        hp_ode = hcsp.ODE_Comm([("y", "x"), ("z", "y"), ("t", "1")], "True", out_comms)
        continuous_hp = hcsp.Sequence(hp_init, hcsp.Loop(hp_ode))
        print(continuous_hp)


if __name__ == "__main__":
    unittest.main()
