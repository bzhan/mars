# Unit test for translation of Simulink diagrams

import unittest

from ss2hcsp.sl.port import Port
from ss2hcsp.sl.Continuous.integrator import Integrator
from ss2hcsp.sl.Continuous.constant import Constant
from ss2hcsp.sl.MathOperations.product import Product
from ss2hcsp.sl.MathOperations.bias import Bias
from ss2hcsp.sl.MathOperations.gain import Gain
from ss2hcsp.sl.MathOperations.add import Add
from ss2hcsp.sl.LogicOperations.logic import And, Or, Not
from ss2hcsp.sl.LogicOperations.relation import Relation
from ss2hcsp.sl.SignalRouting.switch import Switch
from ss2hcsp.sl.SubSystems.subsystem import Subsystem, Enabled_Subsystem
from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.hcsp import hcsp
from ss2hcsp.sl.get_hcsp import get_hcsp, new_get_hcsp, get_thread_hcsp
from ss2hcsp.hcsp.parser import hp_parser


def printTofile(path, content):
    f = open(path, "w")
    print(content, file=f)
    f.close()


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
        diagram.comp_inher_st()

        real_hp = get_hcsp(*diagram.seperate_diagram())
        # print("R: ", real_hp)

        hp_init = hp_parser.parse("x2 := 7; x1 := 3; x0 := 1; x4 := 1; x5 := 1")
        hp_ode0 = hp_parser.parse(r"""
        <x2_dot = x1, x1_dot = x0 & min(x2, x2) < 5 && x5 < 10 || min(x2, x2) >= 5 && x4 < 10> |> 
            [] (ch_x0_0?x0 --> skip, ch_x4_0?x4 --> skip, ch_x4_1?x4 --> skip, 
                ch_x5_0?x5 --> skip, ch_x5_1?x5 --> skip, ch_x7_0!x4 --> skip)""")
        hp_ode1 = hp_parser.parse(r"""
        <x2_dot = x1, x1_dot = x0 & min(x2, x2) < 5 && x5 >= 10 || min(x2, x2) >= 5 && x4 >= 10> |> 
            [] (ch_x0_0?x0 --> skip, ch_x4_0?x4 --> skip, ch_x4_1?x4 --> skip, 
                ch_x5_0?x5 --> skip, ch_x5_1?x5 --> skip, ch_x7_0!x5 --> skip)""")

        continuous_hp = hcsp.Sequence(hp_init, hcsp.Loop(hcsp.Sequence(hp_ode0, hp_ode1)))
        expected_hp = hcsp.HCSPProcess()
        # expected_hp.add("P", hcsp.Var("PC0"))
        expected_hp.add("P", continuous_hp)
        # print("E: ", expected_hp)

        # self.assertEqual(real_hp, expected_hp)

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

        real_hp = get_hcsp(*diagram.seperate_diagram())
        # print("R: ", real_hp)

        expected_hp = hcsp.HCSPProcess()
        expected_hp.add("P", hcsp.Parallel(hcsp.Var("PD0"), hcsp.Var("PD1")))
        hp0_init = hp_parser.parse("t := 0")
        hp0 = hp_parser.parse(r"""t%4 == 0 -> (ch_x7_0?x7; ch_x8_0?x8; ch_x9_0?x9; 
        if x8 >= 20 then x10 := x7 else x10 := x9 endif; ch_x10_0!x10); wait(4); t := t+4""")
        discrete_hp0 = hcsp.Sequence(hp0_init, hcsp.Loop(hp0))
        expected_hp.add("PD0", discrete_hp0)

        hp1_init = hp_parser.parse("t := 0")
        hp1 = hp_parser.parse(r"""t%-1 == 0 -> (ch_x0_0?x0; ch_x0_1?x0; x1 := min(x0, x0)); 
        t%4 == 0 -> x2 := 1-x1; t%4 == 0 -> x3 := x2*2; t%8 == 0 -> (ch_x4_0?x4; x5 := max(x4, x3)); 
        t%10 == 0 -> (ch_x0_2?x0; if x5 <= x0 then x6 := 1 else x6 := 0 endif; ch_x6_0!x6); wait(-1); t := t+(-1)""")
        discrete_hp1 = hcsp.Sequence(hp1_init, hcsp.Loop(hp1))
        expected_hp.add("PD1", discrete_hp1)
        # print("E: ", expected_hp)

        # self.assertEqual(real_hp, expected_hp)

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
        real_hp = get_hcsp(*diagram.seperate_diagram())
        # print("R: ", real_hp)

        expected_hp = hcsp.HCSPProcess()
        expected_hp.add("P", hcsp.Parallel(hcsp.Var("PD0"), hcsp.Var("PC0")))
        dis_init = hp_parser.parse("t := 0")
        dis_hp = hp_parser.parse(r"""t%4 == 0 -> (ch_x3_0?x3; x4 := 1-x3); t%4 == 0 -> x5 := x4*(-2.2); 
        t%8 == 0 -> (ch_x1_0?x1; x6 := max(x1, x5)); 
        t%10 == 0 -> (ch_x2_2?x2; if x6 <= x2 then x0 := 1 else x0 := 0 endif; ch_x0_0!x0); wait(2); t := t+2""")
        discrete_hp = hcsp.Sequence(dis_init, hcsp.Loop(dis_hp))
        expected_hp.add("PD0", discrete_hp)

        con_init = hp_parser.parse("x2 := 10; x1 := 1; x0 := 1")
        con_hp = hp_parser.parse(r"""<x2_dot = x1, x1_dot = x0 & true> |> 
        [] (ch_x0_0?x0 --> skip, ch_x1_0!x1 --> skip, ch_x2_2!x2 --> skip, ch_x3_0!min(x2, x2) --> skip)""")
        continuous_hp = hcsp.Sequence(con_init, hcsp.Loop(con_hp))
        expected_hp.add("PC0", continuous_hp)
        # print("E: ", expected_hp)

        # self.assertEqual(real_hp, expected_hp)

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

        # get_hp.delete_subsystems(diagram.blocks_dict)
        diagram.delete_subsystems()
        # diagram.blocks = diagram.blocks_dict.values()
        diagram.add_line_name()
        diagram.comp_inher_st()
        # print(diagram)
        real_hp = get_hcsp(*diagram.seperate_diagram())
        # print("R: ", real_hp)

        expected_hp = hcsp.HCSPProcess()
        expected_hp.add("P", hcsp.Parallel(hcsp.Var("PD0"), hcsp.Var("PC0")))
        dis_init = hp_parser.parse("t := 0")
        dis_hp = hp_parser.parse(r"""t%4 == 0 -> (ch_x6_0?x6; x5 := 1-x6); t%4 == 0 -> x4 := x5*2; 
        t%6 == 0 -> (ch_x1_1?x1; x2 := max(x1, x4)); 
        t%10 == 0 -> (ch_x3_0?x3; if x2 <= x3 then x0 := 1 else x0 := 0 endif; ch_x0_0!x0); wait(2); t := t+2""")
        discrete_hp = hcsp.Sequence(dis_init, hcsp.Loop(dis_hp))
        expected_hp.add("PD0", discrete_hp)

        con_init = hp_parser.parse("x3 := 3; x1 := 2; x0 := 1")
        con_hp = hp_parser.parse(r"""<x3_dot = x1, x1_dot = x0 & true> |> 
        [] (ch_x0_0?x0 --> skip, ch_x1_1!x1 --> skip, ch_x3_0!x3 --> skip, ch_x6_0!min(x3, x3) --> skip)""")
        continuous_hp = hcsp.Sequence(con_init, hcsp.Loop(con_hp))
        expected_hp.add("PC0", continuous_hp)
        # print("E: ", expected_hp)

        # self.assertEqual(real_hp, expected_hp)

    def testUnitDelay(self):
        directory = "./Examples/UnitDelay/"
        xml_file = "UnitDelay2018.xml"
        diagram = SL_Diagram(location=directory+xml_file)
        diagram.parse_xml()
        diagram.delete_subsystems()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        # print(diagram)
        real_hp = get_hcsp(*diagram.seperate_diagram(), "UnitDelay")
        printTofile(path=directory+xml_file[:-3]+"txt", content=real_hp)

    def testHCS(self):
        directory = "./ss2hcsp/case_studies/"
        xml_file = "hcs_new.xml"
        diagram = SL_Diagram(location=directory+xml_file)
        diagram.parse_xml()
        diagram.delete_subsystems()
        diagram.comp_inher_st()
        diagram.add_line_name()
        diagram.inherit_to_continuous()
        # diagram.delete_ports()
        # print(diagram)
        real_hp = get_hcsp(*diagram.seperate_diagram(), "HCS")
        # print(real_hp)
        printTofile(path=directory+xml_file[:-3]+"txt", content=real_hp)

        # print("D_Processes: ", dis_subdiag_with_chs)
        # print("C_Processes: ", con_subdiag_with_chs)
        # print(get_hp.translate_discrete(dis_subdiag_with_chs[0]))
        # print(diagram)
        # real_hp = get_hp.get_processes(dis_subdiag_with_chs, con_subdiag_with_chs)
        # print(real_hp)

    # def testIsollete(self):
    #     location = "./ss2hcsp/server/portParser/simulinkModel/simulink_isollete.xml"
    #     diagram = SL_Diagram(location=location)
    #     diagram.parse_xml()
    #     get_hp.delete_subsystems(diagram.blocks_dict)
    #     diagram.add_line_name()
    #     diagram.comp_inher_st()
    #     dis_subdiag_with_chs, con_subdiag_with_chs = get_hp.seperate_diagram(diagram.blocks_dict)
    #     real_hp = get_hp.get_processes(dis_subdiag_with_chs, con_subdiag_with_chs)
    #     # print(real_hp)

    def testVanderPol(self):
        location = "./Examples/Van_der_Pol/Van_der_Pol.xml"
        diagram = SL_Diagram(location=location)
        model_name = diagram.parse_xml()
        diagram.add_line_name()
        diagram.comp_inher_st()
        real_hp = get_hcsp(*diagram.seperate_diagram(), model_name)
        # print(real_hp)

        expected_hp = hcsp.HCSPProcess()
        expected_hp.add(model_name, hcsp.Parallel(hcsp.Var("PD0"), hcsp.Var("PC0")))
        dis_init = hp_parser.parse("t := 0")
        dis_hp = hp_parser.parse(r"""t%6 == 0 -> (ch_z_0?z; ch_z_1?z; a := z*z); t%6 == 0 -> b := a+(-1); 
        t%4 == 0 -> (c := b*(-0.1); ch_c_0!c); wait(2); t := t+2""")
        discrete_hp = hcsp.Sequence(dis_init, hcsp.Loop(dis_hp))
        expected_hp.add("PD0", discrete_hp)

        con_init = hp_parser.parse("z := 1; y := 1; c := 1")
        con_hp = hp_parser.parse(r"""<z_dot = y, y_dot = y*c-z & true> |> 
        [] (ch_c_0?c --> skip, ch_z_0!z --> skip, ch_z_1!z --> skip)""")
        continuous_hp = hcsp.Sequence(con_init, hcsp.Loop(con_hp))
        expected_hp.add("PC0", continuous_hp)
        # print(expected_hp)

        # self.assertEqual(real_hp, expected_hp)

    def testIsolette(self):
        location = "./Examples/isolette/babybox.xml"
        diagram = SL_Diagram(location)
        model_name = diagram.parse_xml()
        diagram.add_line_name()
        diagram.comp_inher_st()
        diagram.inherit_to_continuous()
        real_hp = get_hcsp(*diagram.seperate_diagram(), model_name)
        # print(real_hp)

        expected_hp = hcsp.HCSPProcess()
        # expected_hp.add(model_name, hcsp.Var("PC0"))
        con_init = hp_parser.parse("q := 97; c := 100; x0 := 1")
        con_hp = hp_parser.parse("<q_dot = -1, c_dot = (-q+c)*(-0.026) & x0 <= 0> |> [] "
                                 "(babybox_heatCommand?x0 --> skip, babybox_boxTemp!c --> skip); "
                                 "<q_dot = 1, c_dot = (-q+c)*(-0.026) & x0 > 0> |> [] "
                                 "(babybox_heatCommand?x0 --> skip, babybox_boxTemp!c --> skip)")
        continuous_hp = hcsp.Sequence(con_init, hcsp.Loop(con_hp))
        expected_hp.add(model_name, continuous_hp)
        # print(expected_hp)

        # self.assertEqual(real_hp, expected_hp)

    def testLander(self):
        directory = "./CaseStudies/lander/"
        xml_file = "lander_2018a.xml"
        diagram = SL_Diagram(location=directory+xml_file)
        model_name = diagram.parse_xml()
        diagram.delete_subsystems()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        # print(diagram)
        real_hp = get_hcsp(*diagram.seperate_diagram(), model_name)
        printTofile(path=directory+xml_file[:-3]+"txt", content=real_hp)

        # expected_hp = hcsp.HCSPProcess()
        # expected_hp.add(model_name, hcsp.Var("PC0"))
        # con_init = hp_parser.parse("q := 97; c := 100; x0 := 1")
        # con_hp = hp_parser.parse("<q_dot = -1, c_dot = (-q+c)*(-0.026) & x0 <= 0> |> [] "
        #                          "(babybox_heatCommand?x0 --> skip, babybox_boxTemp!c --> skip); "
        #                          "<q_dot = 1, c_dot = (-q+c)*(-0.026) & x0 > 0> |> [] "
        #                          "(babybox_heatCommand?x0 --> skip, babybox_boxTemp!c --> skip)")
        # continuous_hp = hcsp.Sequence(con_init, hcsp.Loop(con_hp))
        # expected_hp.add(model_name, continuous_hp)
        # print(expected_hp)

        # self.assertEqual(real_hp, expected_hp)

    def testSignalBuilder(self):
        directory = "./Examples/signalBuilder/"
        xml_file = "testSignalBuilder.xml"
        diagram = SL_Diagram(location=directory + xml_file)
        model_name = diagram.parse_xml()
        diagram.add_line_name()
        diagram.comp_inher_st()
        diagram.inherit_to_continuous()
        real_hp = get_hcsp(*diagram.seperate_diagram(), model_name)
        printTofile(path=directory+xml_file[:-3]+"txt", content=real_hp)

    # def testVelocityControl(self):
    #     directory = "./Examples/signalBuilder/"
    #     xml_file = "velocity_control.xml"
    #     diagram = SL_Diagram(location=directory + xml_file)
    #     model_name = diagram.parse_xml()
    #     diagram.delete_subsystems()
    #     diagram.comp_inher_st()
    #     # diagram.add_buffers()
    #     diagram.add_line_name()
    #     # print(diagram)
    #     real_hp = get_hcsp(*diagram.seperate_diagram(), model_name)
    #     # print(real_hp)
    #     printTofile(path=directory+xml_file[:-3]+"txt", content=real_hp)

    # def testEnabledSubsystem(self):
    #     directory = "./Examples/Simulink_Triggerred_Subsystem/"
    #     xml_file = "discrete_triggerred_subsystem.xml"
    #     diagram = SL_Diagram(location=directory + xml_file)
    #     _ = diagram.parse_xml()
    #     diagram.add_line_name()
    #     for block in diagram.blocks:
    #         if isinstance(block, Enabled_Subsystem):
    #             block.add_enabled_condition_to_innerBlocks()
    #     print(diagram)

    def testDiscreteTriggeredSubsystem(self):
        directory = "./Examples/Simulink_Triggered_Subsystem/"
        xml_file = "discrete_triggered_subsystem.xml"
        diagram = SL_Diagram(location=directory + xml_file)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.inherit_to_continuous()
        discrete_diagram, continuous_diagram = diagram.new_seperate_diagram()
        result_hp = new_get_hcsp(discrete_diagram, continuous_diagram)
        printTofile(path=directory+xml_file[:-3]+"txt", content=result_hp.export())

    def testContinuousTriggeredSubsystem(self):
        directory = "./Examples/Simulink_Triggered_Subsystem/"
        xml_file = "continuous_triggered_subsystem.xml"
        diagram = SL_Diagram(location=directory + xml_file)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.inherit_to_continuous()
        discrete_diagram, continuous_diagram = diagram.new_seperate_diagram()
        result_hp = new_get_hcsp(discrete_diagram, continuous_diagram)
        printTofile(path=directory+xml_file[:-3]+"txt", content=result_hp.export())

    def testTranslateThread(self):
        directory = "./Examples/AADL/CCS/Simulink/"
        # xml_file = "comp_obs_pos_imp.xml"
        # xml_file = "velo_voter_imp.xml"
        # xml_file = "PI_ctr_imp.xml"
        xml_file = "img_acq_imp.xml"
        diagram = SL_Diagram(location=directory + xml_file)
        _ = diagram.parse_xml()
        diagram.add_line_name()
        thread_hp = get_thread_hcsp(name="img_acq_imp", discrete_diagram=list(diagram.blocks_dict.values()),
                                    deadline=0.01, max_et=0.045, prior=1)
        print(thread_hp.export())


if __name__ == "__main__":
    unittest.main()
