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
from ss2hcsp.sl.SubSystems.subsystem import Subsystem
from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.sl.system import System
from ss2hcsp.hcsp import hcsp
import ss2hcsp.sl.get_hcsp as get_hp
from ss2hcsp.hcsp.parser import hp_parser


class SimTest(unittest.TestCase):
    def testVanDerPol_continuous(self):
        diagram = SL_Diagram()
        diagram.add_block(Integrator(name="intg1", init_value=3))
        diagram.add_block(Integrator(name="intg2", init_value=7))
        # diagram.add_block(Port(name="in1", port_type="in_port"))
        diagram.add_block(And(name="and", num_dest=2, st=0))
        diagram.add_block(Switch(name="switch", relation=">=", threshold=5, st=0))
        diagram.add_block(Switch(name="switch1", relation="<", threshold=10, st=0))
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
        # diagram.delete_ports()
        diagram.comp_inher_st()
        # print(diagram)
        dis_subdiag_with_chs, con_subdiag_with_chs = get_hp.seperate_diagram(diagram.blocks_dict)
        # print(dis_subdiag_with_chs, con_subdiag_with_chs)
        real_hp = get_hp.get_processes(dis_subdiag_with_chs, con_subdiag_with_chs)
        # print("R: ", real_hp)

        hp_init = hp_parser.parse("x2 := 7; x1 := 3; t := 0")
        hp_ode0 = hp_parser.parse(r"""<x2_dot = x1, x1_dot = x0, t_dot = 1 &
        x4 < 10 && min(x2, x2) >= 5 || x5 < 10 && min(x2, x2) < 5> |>
        [] (ch_x0_0?x0 --> skip, ch_x4_0?x4 --> skip, ch_x5_0?x5 --> skip, ch_x7!x4 --> skip)""")
        hp_ode1 = hp_parser.parse(r"""<x2_dot = x1, x1_dot = x0, t_dot = 1 &
        x4 >= 10 && min(x2, x2) >= 5 || x5 >= 10 && min(x2, x2) < 5> |>
        [] (ch_x0_0?x0 --> skip, ch_x4_0?x4 --> skip, ch_x5_0?x5 --> skip, ch_x7!x5 --> skip)""")
        continuous_hp = hcsp.Sequence(hp_init, hcsp.Loop(hcsp.Sequence(hp_ode0, hp_ode1)))
        continuous_hp.name = "PC0"
        expected_hp = System()
        expected_hp.continuous_processes = [continuous_hp]
        # print("E: ", expected_hp)
        self.assertEqual(real_hp, expected_hp)

    def testVanPerPol_discrete(self):
        diagram = SL_Diagram()
        diagram.add_block(Port(name="in0", port_type="in_port"))
        diagram.add_block(And(name="and", num_dest=2, st=-1))
        diagram.add_block(Not(name="not", st=4))
        diagram.add_block(Gain(name="gain", factor=2, st=-1))
        diagram.add_block(Port(name="in1", port_type="in_port"))
        diagram.add_block(Or(name="or", num_dest=2, st=8))
        diagram.add_block(Relation(name="relation", relation="<=", st=10))
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

        diagram.add_line_name()
        diagram.comp_inher_st()
        discrete_subdiagrams_sorted, continuous_subdiagrams = get_hp.seperate_diagram(diagram.blocks_dict)
        real_hp = get_hp.get_processes(discrete_subdiagrams_sorted, continuous_subdiagrams)
        # print("R: ", real_hp)

        hp0_init = hp_parser.parse("t := 0")
        hp0 = hp_parser.parse(r"""ch_x7?x7; ch_x8?x8; ch_x9?x9; t%4 == 0 ->
        (x8 >= 20 -> (x10 := x7); x8 < 20 -> (x10 := x9)); ch_x10_0!x10; temp := t; <t_dot = 1 & t < temp+4>""")
        discrete_hp0 = hcsp.Sequence(hp0_init, hcsp.Loop(hp0))
        discrete_hp0.name = "PD0"

        hp1_init = hp_parser.parse("t := 0")
        hp1 = hp_parser.parse(r"""ch_x0?x0; ch_x4?x4; t%gcd(in0, in0) == 0 ->
        (x1 := min(x0, x0)); t%4 == 0 -> (x3 := (1-x1)*2); t%8 == 0 -> (x5 := max(x4, x3));
        t%10 == 0 -> (x5 > x0 -> (x6 := 0); x5 <= x0 -> (x6 := 1)); ch_x6_0!x6;
        temp := t; <t_dot = 1 & t < temp+gcd(2, and)>""")
        discrete_hp1 = hcsp.Sequence(hp1_init, hcsp.Loop(hp1))
        discrete_hp1.name = "PD1"

        expected_hp = System()
        expected_hp.discrete_processes = [discrete_hp0, discrete_hp1]
        expected_hp.continuous_processes = []
        # print("E: ", expected_hp)
        self.assertEqual(real_hp, expected_hp)

    def testVanPerPol_hybrid(self):
        diagram = SL_Diagram()

        # Add continuous blocks
        diagram.add_block(Integrator(name="intg1", init_value=1))
        diagram.add_block(Integrator(name="intg2", init_value=10))
        # diagram.add_block(Constant(name="con", value=10))
        # diagram.add_block(Port(name="out1", port_type="out_port"))
        # diagram.add_block(Port("out2", "out_port"))

        # Add discrete blocks
        # diagram.add_block(Port(name="in0", port_type="in_port"))
        diagram.add_block(And(name="and", num_dest=2, st=-1))
        diagram.add_block(Not(name="not", st=4))
        diagram.add_block(Gain(name="gain", factor=-2.2, st=-1))
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
        real_hp = get_hp.get_processes(discrete_subdiagrams_sorted, continuous_subdiagrams)
        # print("R: ", real_hp)

        dis_init = hp_parser.parse("t := 0")
        dis_hp = hp_parser.parse(r"""ch_x1?x1; ch_x2?x2; ch_x3?x3; t%4 == 0 -> (x5 := (1-x3)*(-2.2));
        t%8 == 0 -> (x6 := max(x1, x5)); t%10 == 0 -> (x6 > x2 -> (x0 := 0); x6 <= x2 -> (x0 := 1)); ch_x0_0!x0;
        temp := t; <t_dot = 1 & t < temp+2>""")
        discrete_hp = hcsp.Sequence(dis_init, hcsp.Loop(dis_hp))
        discrete_hp.name = "PD0"

        con_init = hp_parser.parse("x2 := 10; x1 := 1; t := 0")
        con_hp = hp_parser.parse(r"""<x2_dot = x1, x1_dot = x0, t_dot = 1 & true> |>
        [] (ch_x0_0?x0 --> skip, ch_x1!x1 --> skip, ch_x2!x2 --> skip, ch_x3!min(x2, x2) --> skip)""")
        continuous_hp = hcsp.Sequence(con_init, hcsp.Loop(con_hp))
        continuous_hp.name = "PC0"

        expected_hp = System()
        expected_hp.discrete_processes = [discrete_hp]
        expected_hp.continuous_processes = [continuous_hp]
        # print("E: ", expected_hp)
        self.assertEqual(real_hp, expected_hp)

    def testVanPerPol_subsystem(self):
        diagram = SL_Diagram()
        # Add blocks
        diagram.add_block(Integrator(name="intg", init_value=2))
        diagram.add_block(Relation(name="relation", relation="<=", st=10))
        diagram.add_block(Or(name="or", num_dest=2, st=6))
        diagram.add_block(Gain(name="gain", factor=2, st=-1))
        # Add a subsystem
        subsystem = Subsystem(name="subsystem", num_src=2, num_dest=1)
        subsystem.diagram = SL_Diagram()
        diagram.add_block(subsystem)
        # Add blocks to the subsystem
        subsystem.diagram.add_block(Port(name="in_0", port_type="in_port"))
        subsystem.diagram.add_block(Port(name="out_0", port_type="out_port"))
        subsystem.diagram.add_block(Port(name="out_1", port_type="out_port"))
        subsystem.diagram.add_block(Integrator(name="subsystem_intg", init_value=3))
        # Add a subsubsystem to the subsystem
        subsubsystem = Subsystem(name="subsubsystem", num_src=1, num_dest=1)
        subsubsystem.diagram = SL_Diagram()
        subsystem.diagram.add_block(subsubsystem)
        subsubsystem.diagram.add_block(Port(name="in_0", port_type="in_port"))
        subsubsystem.diagram.add_block(Port(name="out_0", port_type="out_port"))
        subsubsystem.diagram.add_block(And(name="subsubsystem_and", num_dest=2, st=-1))
        subsubsystem.diagram.add_block(Not(name="subsubsystem_not", st=4))

        # Add lines
        diagram.add_line(src="intg", dest="subsystem", src_port=0, dest_port=0)
        diagram.add_line(src="intg", dest="or", src_port=0, dest_port=0)
        diagram.add_line(src="relation", dest="intg", src_port=0, dest_port=0)
        diagram.add_line(src="or", dest="relation", src_port=0, dest_port=0)
        diagram.add_line(src="gain", dest="or", src_port=0, dest_port=1)
        diagram.add_line(src="subsystem", dest="relation", src_port=0, dest_port=1)
        diagram.add_line(src="subsystem", dest="gain", src_port=1, dest_port=0)
        # Add lines in the subsystem
        subsystem.diagram.add_line(src="in_0", dest="subsystem_intg", src_port=0, dest_port=0)
        subsystem.diagram.add_line(src="subsystem_intg", dest="out_0", src_port=0, dest_port=0)
        subsystem.diagram.add_line(src="subsystem_intg", dest="subsubsystem", src_port=0, dest_port=0)
        subsystem.diagram.add_line(src="subsubsystem", dest="out_1", src_port=0, dest_port=0)
        # Add lines in the subsubsystem
        subsubsystem.diagram.add_line(src="in_0", dest="subsubsystem_and", src_port=0, dest_port=0)
        subsubsystem.diagram.add_line(src="in_0", dest="subsubsystem_and", src_port=0, dest_port=1)
        subsubsystem.diagram.add_line(src="subsubsystem_and", dest="subsubsystem_not", src_port=0, dest_port=0)
        subsubsystem.diagram.add_line(src="subsubsystem_not", dest="out_0", src_port=0, dest_port=0)
        get_hp.delete_subsystems(diagram.blocks_dict)
        # diagram.blocks = diagram.blocks_dict.values()
        diagram.add_line_name()
        diagram.comp_inher_st()
        # print(diagram)
        discrete_subdiagrams_sorted, continuous_subdiagrams = get_hp.seperate_diagram(diagram.blocks_dict)
        real_hp = get_hp.get_processes(discrete_subdiagrams_sorted, continuous_subdiagrams)
        # print("R: ", real_hp)

        dis_init = hp_parser.parse("t := 0")
        dis_hp = hp_parser.parse(r"""ch_x1?x1; ch_x3?x3; ch_x6?x6; t%4 == 0 -> (x4 := (1-x6)*2); 
        t%6 == 0 -> (x2 := max(x1, x4)); t%10 == 0 -> (x2 > x3 -> (x0 := 0); x2 <= x3 -> (x0 := 1)); 
        ch_x0_0!x0; temp := t; <t_dot = 1 & t < temp+2>""")
        discrete_hp = hcsp.Sequence(dis_init, hcsp.Loop(dis_hp))
        discrete_hp.name = "PD0"

        con_init = hp_parser.parse("x3 := 3; x1 := 2; t := 0")
        con_hp = hp_parser.parse(r"""<x3_dot = x1, x1_dot = x0, t_dot = 1 & true> |>
        [] (ch_x0_0?x0 --> skip, ch_x1!x1 --> skip, ch_x3!x3 --> skip, ch_x6!min(x3, x3) --> skip)""")
        continuous_hp = hcsp.Sequence(con_init, hcsp.Loop(con_hp))
        continuous_hp.name = "PC0"

        expected_hp = System()
        expected_hp.discrete_processes = [discrete_hp]
        expected_hp.continuous_processes = [continuous_hp]
        # print("E: ", expected_hp)

        self.assertEqual(real_hp, expected_hp)

    def testHCS(self):
        location = "./ss2hcsp/case_studies/hcs_test.xml"
        diagram = SL_Diagram(location=location)
        diagram.parse_xml()
        # print(diagram)
        get_hp.delete_subsystems(diagram.blocks_dict)
        # print(diagram)
        diagram.add_line_name()
        # print(diagram)
        # diagram.delete_ports()
        diagram.comp_inher_st()
        # print(diagram)
        dis_subdiag_with_chs, con_subdiag_with_chs = get_hp.seperate_diagram(diagram.blocks_dict)
        # print("D_Processes: ", dis_subdiag_with_chs)
        # print("C_Processes: ", con_subdiag_with_chs)
        # print(get_hp.translate_discrete(dis_subdiag_with_chs[0]))
        # print(diagram)
        real_hp = get_hp.get_processes(dis_subdiag_with_chs, con_subdiag_with_chs)
        # print(real_hp)

    # def test_xml_parser(self):
    #     location = "/Users/BEAR/Projects/mars/ss2hcsp/case_studies/Van_der_Pol_subsystem.xml"
    #     diagram = SL_Diagram(location=location)
    #     diagram.parse_xml()
    #     get_hp.delete_subsystems(diagram.blocks_dict)
    #     diagram.add_line_name()
    #     diagram.comp_inher_st()
    #     discrete_subdiagrams_sorted, continuous_subdiagrams = get_hp.seperate_diagram(diagram.blocks_dict)
    #     real_hp = get_hp.get_processes(discrete_subdiagrams_sorted, continuous_subdiagrams)
    #     print(real_hp)
    #     # print(diagram)

    def testIsollete(self):
        location = "./ss2hcsp/server/portParser/simulinkModel/simulink_isollete.xml"
        diagram = SL_Diagram(location=location)
        diagram.parse_xml()
        get_hp.delete_subsystems(diagram.blocks_dict)
        diagram.add_line_name()
        diagram.comp_inher_st()
        dis_subdiag_with_chs, con_subdiag_with_chs = get_hp.seperate_diagram(diagram.blocks_dict)
        real_hp = get_hp.get_processes(dis_subdiag_with_chs, con_subdiag_with_chs)
        print(real_hp)

    def testStateflow(self):
        location = "./Examples/Stateflow/early_exit/early_exit.xml"
        diagram = SL_Diagram(location=location)
        diagram.parse_stateflow_xml()
        chart = list(diagram.charts.values())[0]

        res = [
            ("M", "num := 0; (@M_main)**"),
            ("M_main", "num == 0 -> (tri?E; EL := E; NL := 1; num := 1); num == 1 -> (BC1!E $ BR1?E; EL := push(EL, E); NL := push(NL, 1); num := 1 $ BO1?NULL; num := num+1; NL := pop(NL); NL := push(NL, 1)); num == 2 -> (EL := pop(EL); NL := pop(NL); EL == NULL -> (num := 0); EL != NULL -> (E := top(EL); num := top(NL)))"),
            ("D", "@M || @S1"),
            ("S1", "a_S1 := 1; a_A := 1; a_A1 := 1; rec X.(BC1?E; @Diag_S1; BO1!)"),
            ("Diag_S1", "a_A == 1 -> (@A); a_B == 1 -> (@B)"),
            ("A", "done := 0; E == e && done == 0 -> (a_A2 == 1 -> (a_A2 := 0); a_A1 == 1 -> (a_A1 := 0); a_A := 0; a_B := 1; done := 1); done == 0 -> (@Diag_A)"),
            ("Diag_A", "a_A1 == 1 -> (@A1); a_A2 == 1 -> (@A2)"),
            ("A1", "done := 0; done == 0 -> (BR1!e; @X; a_A == 1 -> (a_A1 := 0; a_A2 := 1; done := 1)); done == 0 -> (skip)"),
            ("A2", "skip"),
            ("B", "skip"),
        ]

        process = chart.get_process()
        expected_process = hcsp.HCSPProcess()
        for name, hp in res:
            expected_process.add(name, hp_parser.parse(hp))

        self.assertEqual(process, expected_process)


if __name__ == "__main__":
    unittest.main()
