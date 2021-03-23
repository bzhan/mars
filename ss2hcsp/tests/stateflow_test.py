# Unit test for translation of Simulink diagrams

import unittest
from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp.parser import hp_parser, bexpr_parser
from ss2hcsp.sl.get_hcsp import *


def printTofile(path,content):
    f = open(path, "w")
    print(content, file=f)
    f.close()


class SfTest(unittest.TestCase):
    def testEarly_exit_has_function(self):
        location = "./Examples/Stateflow/early_exit/early_return_logic_eg1.xml"
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        print(process)
        printTofile("./Examples/Stateflow/early_exit/early_return_logic_eg1.txt",process) 
    def testPlus_generator_edge_trigger(self):
        location = "./Examples/trigger_subsystem/plus_generator_edge_trigger.xml"
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        print(process) 
        printTofile("./Examples/trigger_subsystem/plus_generator_edge_trigger.txt",process)
    def testFun_call_outputEvent_mulBrodcast(self):
        location = "./Examples/trigger_subsystem/fun_call_outputEvent_mulBrodcast_eg.xml"
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        print(process) 
        printTofile("./Examples/trigger_subsystem/fun_call_outputEvent_mulBrodcast_ege.txt",process)
    def testhis_junction(self):
        location = "./Examples/Stateflow/his_junction/his_junction_example.xml"
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        print(process)
        printTofile("./Examples/Stateflow/his_junction/his_junction_example.txt",process)
    def testEdge_trigger_multiplyoutputEvent(self):
        location = "./Examples/Stateflow/edge_trigger_multiplyoutputEvent_eg/edge_trigger_multiplyoutputEvent_eg.xml"
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        print(process)
        printTofile("./Examples/Stateflow/edge_trigger_multiplyoutputEvent_eg/edge_trigger_multiplyoutputEvent_eg.txt",process)
    def testSendDirect_event(self):
        location = "./Examples/Stateflow/direct_event/direct_event1_eg_2.xml"
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        printTofile("./Examples/Stateflow/direct_event/direct_event1_eg_2.txt",process)
        print(process)
    def testSendDirect_event2(self):
        location = "./Examples/Stateflow/direct_event/direct_event_eg2.xml"
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        print(process)
        printTofile("./Examples/Stateflow/direct_event/direct_event_eg2.txt",process)
    def testSendDirect_event3(self):
        location = "./Examples/Stateflow/direct_event/direct_event1_eg_1.xml"
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        print(process)
        #printTofile("./Examples/Stateflow/direct_event/direct_event1_eg_1.txt",process)
    def testSendDirect_event4(self):
        location = "./Examples/Stateflow/direct_event/direct_event1_eg_3.xml"
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        print(process)
        printTofile("./Examples/Stateflow/direct_event/direct_event1_eg_3.txt",process)
    def testSendDirect_event5(self):
        location = "./Examples/Stateflow/direct_event/direct_event1_eg_4.xml"
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        print(process)
        printTofile("./Examples/Stateflow/direct_event/direct_event1_eg_4.txt",process)
    def testMessage_eg(self):
        location = "./Examples/Stateflow/Message_eg/Message_eg.xml"
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        printTofile("./Examples/Stateflow/Message_eg/Message_eg.txt",process)
        print(process)
    def testMessage_eg2(self):
        location = "./Examples/Stateflow/Message_eg/Message_eg2.xml"
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        printTofile("./Examples/Stateflow/Message_eg/Message_eg2.txt",process)
        print(process)
    def testSend(self):
        location = "./Examples/Stateflow/early_exit/early_return_logic_eg1_1.xml"
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        print(process)
        printTofile("./Examples/Stateflow/early_exit/early_return_logic_eg1_1.txt",process)
 
    def testEarlyExit(self):
        location = "./Examples/Stateflow/early_exit/early_exit.xml"
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        print(process)
        printTofile("./Examples/Stateflow/early_exit/early_exit.txt",process)
        res = [
            ("P", "@M || @S1"),
            ("M", 'num := 0; wait(-1); (num == 0 -> (state := "";E := ""; EL := [""]; NL := [1]; num := 1); '
                  'num == 1 -> (DState1!state --> skip $ DBC1!E --> skip $ BC1!E --> skip $ BR1?E --> skip; EL := push(EL, E); NL := push(NL, 1); num := 1 $ DBR1?E --> skip;DBnum1?Dnum; num := Dnum ; DState1?state'
                  '$ DBO1? --> skip; num :=num+1 $ BO1? --> skip; num := num+1; NL := pop(NL); NL := push(NL, num)); '
                  'num == 2 -> (EL := pop(EL); NL := pop(NL); EL == [] -> (num := 0; wait(-1)); '
                  'EL != [] -> (E := top(EL); num := top(NL))))**'),
            ("S1", 'a_S1 := 0; a_A := 0; a_A1 := 0; a_A2 := 0; a_B := 0; a_S1 := 1; a_A := 1; a_A1 := 1; '
                   '(rec X.(BC1?E; skip; if a_A == 1 then done := 0; E == "e" && done == 0 -> '
                   '(a_A2 == 1 -> a_A2 := 0; a_A1 == 1 -> a_A1 := 0; a_A := 0; a_B := 1; done := 1); '
                   'done == 0 -> if a_A1 == 1 then done := 0; done == 0 -> (BR1!"e"; @X; a_A1 == 1 -> '
                   '(a_A1 := 0; a_A2 := 1; done := 1)) elif a_A2 == 1 then skip else skip endif '
                   'elif a_B == 1 then skip else skip endif; BO1!; skip))**'),
        ]
        expected_process = hcsp.HCSPProcess()
        for name, _hp in res:
            expected_process.add(name, hp_parser.parse(_hp))
        # print(expected_process)

        self.assertEqual(process, expected_process)

    def test_statelessWriter1(self):
        location = "./Examples/Stateflow/dds/statelessWriter1.xml"
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        # print(process)

        res = [
            ("P", "a := 0; cansend := 0; flag := 0; unsent := 0; a_S1 := 0; a_pushing := 0; a_idle := 0; "
                  "a_S1 := 1; unsent := 5; cansend := 1; a_idle := 1; wait(-1); "
                  "(if a_pushing == 1 then done := 0; if done == 0 && unsent <= 0 then a_pushing := 0; a_idle := 1; "
                  "done := 1 elif cansend == 1 && done == 0 then a_pushing := 0; unsent := unsent-1; a_pushing := 1; "
                  "done := 1 else flag := 0 endif elif a_idle == 1 then done := 0; if done == 0 && unsent > 0 "
                  "then a_idle := 0; a_pushing := 1; done := 1 else flag := 1 endif else skip endif; wait(-1))**"),
        ]
        expected_process = hcsp.HCSPProcess()
        for name, _hp in res:
            expected_process.add(name, hp_parser.parse(_hp))
        # print(expected_process)

        self.assertEqual(process, expected_process)

    def test_statelessWriter2_1(self):
        location = "./Examples/Stateflow/dds/statelessWriter2_1.xml"
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        #print(process)

        res = [
            ("P", "a := 0; cansend := 0; flag := 0; heartbeat := 0; heartbeatPeriod := 0; i := 0; a_S1 := 0; "
                  "a_pushing := 0; a_idle := 0; a_S1 := 1; i := 3; cansend := 1; state_time := 0; a_idle := 1; "
                  "heartbeat := 0; wait(2); (if a_pushing == 1 then done := 0; if done == 0 && i <= 0 "
                  "then a_pushing := 0; state_time := 0; a_idle := 1; heartbeat := 0; done := 1 "
                  "elif cansend == 1 && done == 0 then i := i-1; a_pushing := 0; a_pushing := 1; done := 1 "
                  "else flag := 0 endif elif a_idle == 1 then done := 0; if done == 0 && i > 0 then a_idle := 0; "
                  "a_pushing := 1; done := 1 elif done == 0 && state_time >= 3 then heartbeat := 1; a_idle := 0; "
                  "state_time := 0; a_idle := 1; heartbeat := 0; done := 1 else flag := 1 endif;"
                  "done == 0 -> (state_time := state_time+2) else skip endif; wait(2))**"),
        ]
        expected_process = hcsp.HCSPProcess()
        for name, _hp in res:
            expected_process.add(name, hp_parser.parse(_hp))
        # print(expected_process)

        self.assertEqual(process, expected_process)

    def test_statelessWriter2_2(self):
        location = "./Examples/Stateflow/dds/statelessWriter2_2.xml"
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        # diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
#         print(process)

        res = [
            ("P", "ACKNACK := 0; ResponseDelay := 0; cansend := 0; flag := 0; re_changes := 0; a_S1 := 0; "
                  "a_repairing := 0; a_must_repair := 0; a_waiting := 0; a_S1 := 1; re_changes := 0; "
                  "ACKNACK := 1; cansend := 1; a_waiting := 1; wait(2); (if a_repairing == 1 then done := 0; "
                  "if done == 0 && re_changes == 0 then a_repairing := 0; a_waiting := 1; done := 1 "
                  "elif cansend == 1 && done == 0 then a_repairing := 0; re_changes := re_changes-1; a_repairing := 1; "
                  "done := 1 else flag := 0 endif elif a_must_repair == 1 then done := 0; "
                  "if done == 0 && state_time >= 5 then a_must_repair := 0; a_repairing := 1; done := 1 "
                  "elif ACKNACK == 1 && done == 0 then a_must_repair := 0; re_changes := re_changes+1; "
                  "state_time := 0; a_must_repair := 1; done := 1 else flag := 1 endif; "
                  "done == 0 -> (state_time := state_time+2) "
                  "elif a_waiting == 1 then done := 0; if done == 0 && re_changes > 0 "
                  "then ACKNACK := 0; a_waiting := 0; state_time := 0; a_must_repair := 1; done := 1 "
                  "elif ACKNACK == 1 && done == 0 then a_waiting := 0; re_changes := re_changes+1; a_waiting := 1; "
                  "done := 1 else flag := 1 endif else skip endif; wait(2))**"),
        ]
        expected_process = hcsp.HCSPProcess()
        for name, _hp in res:
            expected_process.add(name, hp_parser.parse(_hp))
#         print(expected_process)

        self.assertEqual(process, expected_process)

    def testSimulinkStateflow(self):
        location = "./Examples/Stateflow/Simulink+Stateflow/SimulinkStateflow.xml"
        diagram = SL_Diagram(location=location)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
#         print(process)

        res = [
            ("P", "@PD0 || @PD1 || @PC0 || @PC1 || @Chart || @buffer0 || @buffer1"),
            ("PD0", "t := 0; (t%4 == 0 -> (ch_x6_0?x6; x7 := x6*1; ch_x7_0!x7); wait(4); t := t+4)**"),
            ("PD1", "t := 0; (t%2 == 0 -> (ch_x4_0?x4; x5 := x4*1; ch_x5_0!x5); wait(2); t := t+2)**"),
            ("PC0", "x1 := 2; x7 := 1; (<x1_dot = x7 & true> |> [] (ch_x7_0?x7 --> skip, ch_x1_0!x1 --> skip))**"),
            ("PC1", "x4 := 3; (<x4_dot = 1 & true> |> [] (ch_x4_0!x4 --> skip))**"),
            ("Chart", "a := 0; x := 0; y := 0; z := 0; a_S1 := 0; a_on := 0; a_off := 0; a_S1 := 1; a_on := 1; "
                      "ch_x0_0?x; ch_x1_0?a; ch_x2_0!y; wait(3); (ch_x0_0?x; ch_x1_0?a; if a_on == 1 then "
                      "done := 0; done == 0 -> (z := x+a; y := z+1; a_on := 0; a_off := 1; done := 1) "
                      "elif a_off == 1 then done := 0; done == 0 -> "
                      "(y := x-a; a_off := 0; a_on := 1; done := 1) else skip endif; "
                      "ch_x2_0!y; wait(3))**"),
            ("buffer0", "(ch_x5_0?x5; ch_x0_0!x5; wait(2); ch_x5_0?x5; wait(1); "
                        "ch_x0_0!x5; wait(1); ch_x5_0?x5; wait(2))**"),
            ("buffer1", "(ch_x2_0?x2; ch_x6_0!x2; wait(3); ch_x2_0?x2; wait(1); "
                        "ch_x6_0!x2; wait(2); ch_x2_0?x2; wait(2); ch_x6_0!x2; wait(1); ch_x2_0?x2; wait(3))**")
        ]
        expected_process = hcsp.HCSPProcess()
        for name, _hp in res:
            expected_process.add(name, hp_parser.parse(_hp))
#         print(expected_process)

        self.assertEqual(process, expected_process)

    def testInnerTrans(self):
        location = "./Examples/Stateflow/inner_trans/inner_trans.xml"
        diagram = SL_Diagram(location)
        _ = diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        # print(diagram)
        process = get_hcsp(*diagram.seperate_diagram())
        # print(process)

        res = [
            ("P", "out := 0; a_S1 := 0; a_super := 0; a_sub1 := 0; a_sub2 := 0; a_S1 := 1; a_super := 1; "
                  "out := 1; out := 3; out := 4; a_sub1 := 1; out := 7; wait(1); (a_super == 1 -> "
                  "(done := 0; out := 2; done == 0 -> (out := 5; a_sub2 == 1 -> a_sub2 := 0; a_sub1 == 1 -> "
                  "(out := 8; a_sub1 := 0); out := 6; a_sub1 := 1; out := 7; done := 1); done == 0 -> "
                  "if a_sub1 == 1 then done := 0; done == 0 -> (out := 8; a_sub1 := 0; a_sub2 := 1; "
                  "done := 1) elif a_sub2 == 1 then done := 0; done == 0 -> (a_sub2 := 0; a_sub1 := 1; "
                  "out := 7; done := 1) else skip endif); wait(1))**")
        ]
        expected_process = hcsp.HCSPProcess()
        for name, _hp in res:
            expected_process.add(name, hp_parser.parse(_hp))
        print(expected_process)

        self.assertEqual(process, expected_process)

    def testFsco(self):
        location = "./Examples/Stateflow/CTCS3/CTCS3.xml"
        diagram = SL_Diagram(location)
        _ = diagram.parse_xml()
        diagram.delete_subsystems()
        diagram.comp_inher_st()
        diagram.inherit_to_continuous()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        print(process)

    # To be implemented
    def testJunctionPriority(self):
        location = "./Examples/Stateflow/junction_priority/junction_priority.xml"
        diagram = SL_Diagram(location)
        _ = diagram.parse_xml()
        diagram.delete_subsystems()
        diagram.comp_inher_st()
        diagram.inherit_to_continuous()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        print(process)
if __name__ == "__main__":
    unittest.main()
