# Unit tests for modules

import unittest

from ss2hcsp.hcsp.parser import module_parser, system_parser, decls_parser
from ss2hcsp.hcsp import module


class ModuleTest(unittest.TestCase):
    def testParseModule(self):
        mod = module_parser.parse("""
            module P0():
                output x;
                begin
                    x := 0;
                    (<x_dot = 1 & true> |> [](p2c!x --> skip); c2p?x)**
                end
            endmodule
        """)

        self.assertEqual(str(mod), "P0()")
        self.assertEqual(mod.outputs, (('x',),))

    def testParseModule2(self):
        mod = module_parser.parse("""
            module P1():
                begin
                    (wait(2); p2c?x; c2p!x-1)**
                end
            endmodule
        """)

        self.assertEqual(str(mod), "P1()")
        self.assertEqual(mod.outputs, ())

    def testParseSystem(self):
        sys = system_parser.parse("""
            system
                P0() ||
                P1()
            endsystem
        """)

        self.assertEqual(str(sys), "P0() || P1()")
        self.assertEqual(repr(sys), "System(P0(); P1())")

    def testParseDecls(self):
        decls = decls_parser.parse("""
            module P0():
                output x;
                begin
                    x := 0;
                    (<x_dot = 1 & true> |> [](p2c!x --> skip); c2p?x)**
                end
            endmodule

            module P1():
                begin
                    (wait(2); p2c?x; c2p!x-1)**
                end
            endmodule

            system
                P0() ||
                P1()
            endsystem
        """)

        self.assertEqual(str(decls), "P0()\nP1()\nP0() || P1()")
        self.assertEqual(repr(decls), "Decls(\n  Module(P0)\n  Module(P1)\n  System(P0(); P1())\n)")


if __name__ == "__main__":
    unittest.main()
