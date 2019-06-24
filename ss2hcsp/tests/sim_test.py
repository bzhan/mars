# Unit test for translation of Simulink diagrams

import unittest

from ss2hcsp.sl import SL_Line, Port, Integrator, SL_Diagram
from ss2hcsp.hcsp import hcsp

class SimTest(unittest.TestCase):
    def testVanDerPol1(self):
        diagram = SL_Diagram()
        diagram.add_block(Integrator("intg1", 1))
        diagram.add_block(Integrator("intg2", 1))
        diagram.add_block(Port("in1", "in_port"))
        diagram.add_block(Port("out1", "out_port"))
        diagram.add_block(Port("out2", "out_port"))
        diagram.add_block(Port("out3", "out_port"))
        diagram.add_block(Port("out4", "out_port"))
        diagram.add_line("in1", "intg1", 0, 0)
        diagram.add_line("intg1", "out1", 0, 0)
        diagram.add_line("intg1", "intg2", 0, 0)
        diagram.add_line("intg2", "out2", 0, 0)
        diagram.add_line("intg2", "out3", 0, 0)
        diagram.add_line("intg2", "out4", 0, 0)

        hp_init = hcsp.Sequence(hcsp.Assign("x", "1"), hcsp.Assign("y", "1"))
        out_comms = [hcsp.OutputChannel("chy", "y"),
                     hcsp.Sequence([hcsp.OutputChannel("chy", "y"),
                                    hcsp.OutputChannel("chz1", "z"),
                                    hcsp.OutputChannel("chz2", "z"),
                                    hcsp.OutputChannel("chz3", "z")])]
        hp_ode = hcsp.ODE_Comm([("y", "x"), ("z", "y"), ("t", "1")], "True", out_comms)
        hp = hcsp.Loop(Sequence(hcsp.InputChannel("chx", "x"), hp_ode))


if __name__ == "__main__":
    unittest.main()
