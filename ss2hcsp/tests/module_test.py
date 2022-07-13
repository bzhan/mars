# Unit tests for modules

import unittest

from ss2hcsp.hcsp.expr import AConst
from ss2hcsp.hcsp.parser import hp_parser, module_parser, system_parser, decls_parser
from ss2hcsp.hcsp.module import HCSPModule, HCSPModuleInst, HCSPSystem, HCSPDeclarations, read_file
from ss2hcsp.hcsp.hcsp import Channel


class ModuleTest(unittest.TestCase):
    def testParseModule(self):
        mod = module_parser.parse("""
            module P0():
                output x;
                begin
                    x := 0;
                    { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x; }*
                end
            endmodule
        """)

        self.assertEqual(str(mod), "P0()")
        self.assertEqual(mod.outputs, (('x',),))

    def testParseModule2(self):
        mod = module_parser.parse("""
            module P1():
                begin
                    { wait(2); p2c?x; c2p!x-1; }*
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
        self.assertEqual(str(sys), "P0() ||\nP1()")
        self.assertEqual(repr(sys), "System(P0(); P1())")

    def testParseDecls(self):
        decls = decls_parser.parse("""
            %type: module

            module P0():
                output x;
                begin
                    x := 0;
                    {{x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x;}*
                end
            endmodule

            module P1():
                begin
                    { wait(2); p2c?x; c2p!x-1; }*
                end
            endmodule

            system
                P0() ||
                P1()
            endsystem
        """)

        self.assertEqual(str(decls), "P0()\nP1()\nP0() ||\nP1()")
        self.assertEqual(repr(decls), "Decls(\n  Module(P0)\n  Module(P1)\n  System(P0(); P1())\n)")

    def testParseModule3(self):
        mod = module_parser.parse("""
            module P0(p2c,c2p):
            output x;
            begin
                x := 0;
                { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x; }*
            end
            endmodule
        """)

        self.assertEqual(str(mod), "P0(p2c,c2p)")
        self.assertEqual(repr(mod), "Module(P0,p2c,c2p)")

    def testParseDecls2(self):
        decls = decls_parser.parse("""
            %type: module

            module P0(p2c,c2p):
            output x;
            begin
                x := 0;
                { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x; }*
            end
            endmodule

            module P1(p2c,c2p):
            begin
                { wait(2); p2c?x; c2p!x-1; }*
            end
            endmodule

            system
                P0a = P0(ch1,ch2) ||
                P1a = P1(ch1,ch2) ||
                P0b = P0(ch3,ch4) ||
                P1b = P1(ch3,ch4)
            endsystem
        """)

        self.assertEqual(str(decls),
            "P0(p2c,c2p)\nP1(p2c,c2p)\nP0a = P0(ch1, ch2) ||\nP1a = P1(ch1, ch2) ||\nP0b = P0(ch3, ch4) ||\nP1b = P1(ch3, ch4)")
        self.assertEqual(repr(decls),
            "Decls(\n  Module(P0,p2c,c2p)\n  Module(P1,p2c,c2p)\n  System(P0a=P0(ch1,ch2); P1a=P1(ch1,ch2); P0b=P0(ch3,ch4); P1b=P1(ch3,ch4))\n)")

    def testGenerateHCSPInfo(self):
        decls = HCSPDeclarations([
            HCSPModule("P0", "x := 0; { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x; }*",
                       params=("p2c", "c2p"), outputs=(("x",),)),
            HCSPModule("P1", "{ wait(2); p2c?x; c2p!x-1; }*",
                       params=("p2c", "c2p")),
            HCSPSystem([
                HCSPModuleInst("P0a", "P0", (Channel("ch1"), Channel("ch2"))),
                HCSPModuleInst("P1a", "P1", (Channel("ch1"), Channel("ch2"))),
                HCSPModuleInst("P0b", "P0", (Channel("ch3"), Channel("ch4"))),
                HCSPModuleInst("P1b", "P1", (Channel("ch3"), Channel("ch4"))),
            ])
        ])

        infos = decls.generateHCSPInfo()
        self.assertEqual(str(infos[0].hp), "x := 0; {{x_dot = 1 & true} |> [] (ch1!x --> skip;) ch2?x;}*")
        self.assertEqual(str(infos[1].hp), "{wait(2); ch1?x; ch2!x - 1;}*")
        self.assertEqual(str(infos[2].hp), "x := 0; {{x_dot = 1 & true} |> [] (ch3!x --> skip;) ch4?x;}*")
        self.assertEqual(str(infos[3].hp), "{wait(2); ch3?x; ch4!x - 1;}*")

    def testParseSystem2(self):
        sys = system_parser.parse("""
            system
                P0(ch1, ch2, $0) ||
                P1(ch1, ch2)
            endsystem
        """)

        self.assertEqual(str(sys), "P0(ch1, ch2, $0) ||\nP1(ch1, ch2)")
        self.assertEqual(repr(sys), "System(P0(ch1,ch2,0); P1(ch1,ch2))")

    def testGenerateHCSPInfo2(self):
        decls = HCSPDeclarations([
            HCSPModule("P0", "x := init_x; {{x_dot = slope & true} |> [](p2c!x --> skip;) c2p?x;}*",
                       params=("p2c", "c2p", "init_x", "slope"), outputs=(("x",),),),
            HCSPModule("P1", "{wait(dly); p2c?x; c2p!x-1;}*",
                       params=("p2c", "c2p", "dly")),
            HCSPSystem([
                HCSPModuleInst("P0a", "P0", (Channel("ch1"), Channel("ch2"), AConst(0), AConst(1))),
                HCSPModuleInst("P1a", "P1", (Channel("ch1"), Channel("ch2"), AConst(2))),
                HCSPModuleInst("P0b", "P0", (Channel("ch3"), Channel("ch4"), AConst(1), AConst(2))),
                HCSPModuleInst("P1b", "P1", (Channel("ch3"), Channel("ch4"), AConst(3))),
            ])
        ])

        infos = decls.generateHCSPInfo()
        self.assertEqual(str(infos[0].hp), "x := 0; {{x_dot = 1 & true} |> [] (ch1!x --> skip;) ch2?x;}*")
        self.assertEqual(str(infos[1].hp), "{wait(2); ch1?x; ch2!x - 1;}*")
        self.assertEqual(str(infos[2].hp), "x := 1; {{x_dot = 2 & true} |> [] (ch3!x --> skip;) ch4?x;}*")
        self.assertEqual(str(infos[3].hp), "{wait(3); ch3?x; ch4!x - 1;}*")

    def testReadFile(self):
        decls = decls_parser.parse(read_file('channels.txt'))
        self.assertEqual(str(decls), "asyncChannel(ch_out,ch_in)\nNone")

    def testParseDecls3(self):
        decls = decls_parser.parse("""
            %type: module

            import channels

            module input(ch_in):
            begin
            {
                ch_in?x;
            }*
            end
            endmodule

            module output(ch_out):
            begin
            x := 0;
            {
                x := x + 1;
                ch_out!x;
            }*
            end
            endmodule

            system
                input(ch_in) ||
                output(ch_out) ||
                asyncChannel(ch_out, ch_in)
            endsystem
        """)

        infos = decls.generateHCSPInfo()
        self.assertEqual(str(infos[0].hp), "{ch_in?x;}*")
        self.assertEqual(str(infos[1].hp), "x := 0; {x := x + 1; ch_out!x;}*")
        self.assertEqual(str(infos[2].hp), "{ch_out?x --> skip; $ ch_in!x --> skip;}*")


if __name__ == "__main__":
    unittest.main()
