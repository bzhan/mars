# Unit test for translation of Simulink diagrams

import unittest
from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp.parser import hp_parser
from ss2hcsp.sl.get_hcsp import *


class SfTest(unittest.TestCase):
    def testEarlyExit(self):
        location = "./Examples/Stateflow/early_exit/early_exit.xml"
        diagram = SL_Diagram(location=location)
        diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        # print(process)

        res = [
            ("P", "@M || @S1"),
            ("M", 'num := 0; wait(-1); (num == 0 -> (E := ""; EL := [""]; NL := [1]; num := 1); '
                  'num == 1 -> (BC1!E --> skip $ BR1?E --> skip; EL := push(EL, E); NL := push(NL, 1); num := 1 '
                  '$ BO1? --> skip; num := num+1; NL := pop(NL); NL := push(NL, 1)); '
                  'num == 2 -> (EL := pop(EL); NL := pop(NL); EL == [] -> (num := 0; wait(-1)); '
                  'EL != [] -> (E := top(EL); num := top(NL))))**'),
            ("S1", 'a_S1 := 0; a_A := 0; a_A1 := 0; a_A2 := 0; a_B := 0; a_S1 := 1; a_A := 1; a_A1 := 1; '
                   'rec X.(BC1?E; skip; if a_A == 1 then done := 0; E == "e" && done == 0 -> '
                   '(a_A2 == 1 -> a_A2 := 0; a_A1 == 1 -> a_A1 := 0; a_A := 0; a_B := 1; done := 1); '
                   'done == 0 -> if a_A1 == 1 then done := 0; done == 0 -> (BR1!"e"; @X; a_A == 1 -> '
                   '(a_A1 := 0; a_A2 := 1; done := 1)); done == 0 -> skip elif a_A2 == 1 then skip else skip endif '
                   'elif a_B == 1 then skip else skip endif; BO1!; skip)'),
        ]
        expected_process = hcsp.HCSPProcess()
        for name, _hp in res:
            expected_process.add(name, hp_parser.parse(_hp))
        # print(expected_process)

        self.assertEqual(process, expected_process)

    def test_statelessWriter1(self):
        location = "./Examples/Stateflow/dds/statelessWriter1.xml"
        diagram = SL_Diagram(location=location)
        diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        # print(process)

        res = [
            ("P", "@M || @S1"),
            ("M", 'unsent := 0; cansend := 0; flag := 0; a := 0; num := 0; wait(-1); '
                  '(num == 0 -> (E := ""; EL := [""]; NL := [1]; num := 1); num == 1 -> '
                  '(BC1!E --> VOut1_unsent!unsent; VOut1_cansend!cansend; VOut1_flag!flag; VOut1_a!a '
                  '$ BR1?E --> VIn1_unsent?unsent; VIn1_cansend?cansend; VIn1_flag?flag; VIn1_a?a; '
                  'EL := push(EL, E); NL := push(NL, 1); num := 1 '
                  '$ BO1? --> VIn1_unsent?unsent; VIn1_cansend?cansend; VIn1_flag?flag; VIn1_a?a; num := num+1; '
                  'NL := pop(NL); NL := push(NL, 1)); num == 2 -> (EL := pop(EL); NL := pop(NL); '
                  'EL == [] -> (num := 0; wait(-1)); EL != [] -> (E := top(EL); num := top(NL))))**'),
            ("S1", 'a_S1 := 0; a_pushing := 0; a_idle := 0; a_S1 := 1; unsent := 5; cansend := 1; a_idle := 1; '
                   '(BC1?E; VOut1_unsent?unsent; VOut1_cansend?cansend; VOut1_flag?flag; VOut1_a?a; '
                   'if a_pushing == 1 then done := 0; done == 0 && unsent <= 0 -> '
                   '(a_pushing := 0; a_idle := 1; done := 1); cansend == 1 && done == 0 -> '
                   '(a_pushing := 0; unsent := unsent-1; a_pushing := 1; done := 1); '
                   'done == 0 -> flag := 0 elif a_idle == 1 then done := 0; done == 0 && unsent > 0 -> '
                   '(a_idle := 0; a_pushing := 1; done := 1); done == 0 -> flag := 1 else skip endif; '
                   'BO1!; VIn1_unsent!unsent; VIn1_cansend!cansend; VIn1_flag!flag; VIn1_a!a)**'),
        ]
        expected_process = hcsp.HCSPProcess()
        for name, _hp in res:
            expected_process.add(name, hp_parser.parse(_hp))
        # print(expected_process)

        self.assertEqual(process, expected_process)

    def test_statelessWriter2_1(self):
        location = "./Examples/Stateflow/dds/statelessWriter2_1.xml"
        diagram = SL_Diagram(location=location)
        diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        # print(process)

        res = [
            ("P", "@M || @S1"),
            ("M", 'i := 0; heartbeatPeriod := 0; flag := 0; cansend := 0; heartbeat := 0; a := 0; num := 0; wait(2); '
                  '(num == 0 -> (E := ""; EL := [""]; NL := [1]; num := 1); num == 1 -> '
                  '(BC1!E --> VOut1_i!i; VOut1_heartbeatPeriod!heartbeatPeriod; VOut1_flag!flag; '
                  'VOut1_cansend!cansend; VOut1_heartbeat!heartbeat; VOut1_a!a $ BR1?E --> VIn1_i?i; '
                  'VIn1_heartbeatPeriod?heartbeatPeriod; VIn1_flag?flag; VIn1_cansend?cansend; '
                  'VIn1_heartbeat?heartbeat; VIn1_a?a; EL := push(EL, E); NL := push(NL, 1); num := 1 '
                  '$ BO1? --> VIn1_i?i; VIn1_heartbeatPeriod?heartbeatPeriod; VIn1_flag?flag; VIn1_cansend?cansend; '
                  'VIn1_heartbeat?heartbeat; VIn1_a?a; num := num+1; NL := pop(NL); NL := push(NL, 1)); '
                  'num == 2 -> (EL := pop(EL); NL := pop(NL); EL == [] -> (num := 0; wait(2)); '
                  'EL != [] -> (E := top(EL); num := top(NL))))**'),
            ("S1", 'a_S1 := 0; a_pushing := 0; a_idle := 0; a_S1 := 1; i := 3; cansend := 1; state_time := 0; '
                   'a_idle := 1; heartbeat := 0; (BC1?E; VOut1_i?i; VOut1_heartbeatPeriod?heartbeatPeriod; '
                   'VOut1_flag?flag; VOut1_cansend?cansend; VOut1_heartbeat?heartbeat; VOut1_a?a; '
                   'if a_pushing == 1 then done := 0; done == 0 && i <= 0 -> (a_pushing := 0; state_time := 0; '
                   'a_idle := 1; heartbeat := 0; done := 1); cansend == 1 && done == 0 -> (i := i-1; a_pushing := 0; '
                   'a_pushing := 1; done := 1); done == 0 -> flag := 0 elif a_idle == 1 then done := 0; '
                   'done == 0 && i > 0 -> (a_idle := 0; a_pushing := 1; done := 1); done == 0 && state_time >= 3 -> '
                   '(heartbeat := 1; a_idle := 0; state_time := 0; a_idle := 1; heartbeat := 0; done := 1); '
                   'done == 0 -> (flag := 1; state_time := state_time+2) else skip endif; BO1!; VIn1_i!i; '
                   'VIn1_heartbeatPeriod!heartbeatPeriod; VIn1_flag!flag; VIn1_cansend!cansend; '
                   'VIn1_heartbeat!heartbeat; VIn1_a!a)**')
        ]
        expected_process = hcsp.HCSPProcess()
        for name, _hp in res:
            expected_process.add(name, hp_parser.parse(_hp))
        # print(expected_process)

        self.assertEqual(process, expected_process)

    def test_statelessWriter2_2(self):
        location = "./Examples/Stateflow/dds/statelessWriter2_2.xml"
        diagram = SL_Diagram(location=location)
        diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        # diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        # print(process)

        res = [
            ("P", "@M || @S1"),
            ("M", 'flag := 0; re_changes := 0; ResponseDelay := 0; cansend := 0; ACKNACK := 0; num := 0; wait(2); '
                  '(num == 0 -> (E := ""; EL := [""]; NL := [1]; num := 1); num == 1 -> (BC1!E --> VOut1_flag!flag; '
                  'VOut1_re_changes!re_changes; VOut1_ResponseDelay!ResponseDelay; VOut1_cansend!cansend; '
                  'VOut1_ACKNACK!ACKNACK $ BR1?E --> VIn1_flag?flag; VIn1_re_changes?re_changes; '
                  'VIn1_ResponseDelay?ResponseDelay; VIn1_cansend?cansend; VIn1_ACKNACK?ACKNACK; '
                  'EL := push(EL, E); NL := push(NL, 1); num := 1 $ BO1? --> VIn1_flag?flag; '
                  'VIn1_re_changes?re_changes; VIn1_ResponseDelay?ResponseDelay; VIn1_cansend?cansend; '
                  'VIn1_ACKNACK?ACKNACK; num := num+1; NL := pop(NL); NL := push(NL, 1)); '
                  'num == 2 -> (EL := pop(EL); NL := pop(NL); EL == [] -> (num := 0; wait(2)); '
                  'EL != [] -> (E := top(EL); num := top(NL))))**'),
            ("S1", 'a_S1 := 0; a_repairing := 0; a_must_repair := 0; a_waiting := 0; a_S1 := 1; re_changes := 0; '
                   'ACKNACK := 1; cansend := 1; a_waiting := 1; (BC1?E; VOut1_flag?flag; VOut1_re_changes?re_changes; '
                   'VOut1_ResponseDelay?ResponseDelay; VOut1_cansend?cansend; VOut1_ACKNACK?ACKNACK; '
                   'if a_repairing == 1 then done := 0; done == 0 && re_changes == 0 -> '
                   '(a_repairing := 0; a_waiting := 1; done := 1); cansend == 1 && done == 0 -> '
                   '(a_repairing := 0; re_changes := re_changes-1; a_repairing := 1; done := 1); '
                   'done == 0 -> flag := 0 elif a_must_repair == 1 then done := 0; done == 0 && state_time >= 5 -> '
                   '(a_must_repair := 0; a_repairing := 1; done := 1); ACKNACK == 1 && done == 0 -> '
                   '(a_must_repair := 0; re_changes := re_changes+1; state_time := 0; a_must_repair := 1; done := 1); '
                   'done == 0 -> (flag := 1; state_time := state_time+2) elif a_waiting == 1 then done := 0; '
                   'done == 0 && re_changes > 0 -> (ACKNACK := 0; a_waiting := 0; state_time := 0; '
                   'a_must_repair := 1; done := 1); ACKNACK == 1 && done == 0 -> (a_waiting := 0; '
                   're_changes := re_changes+1; a_waiting := 1; done := 1); done == 0 -> flag := 1 else skip endif; '
                   'BO1!; VIn1_flag!flag; VIn1_re_changes!re_changes; VIn1_ResponseDelay!ResponseDelay; '
                   'VIn1_cansend!cansend; VIn1_ACKNACK!ACKNACK)**')
        ]
        expected_process = hcsp.HCSPProcess()
        for name, _hp in res:
            expected_process.add(name, hp_parser.parse(_hp))

        self.assertEqual(process, expected_process)

    def testSimulinkStateflow(self):
        location = "./Examples/Stateflow/Simulink+Stateflow/SimulinkStateflow.xml"
        diagram = SL_Diagram(location=location)
        diagram.parse_xml()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        process = get_hcsp(*diagram.seperate_diagram())
        # print(process)

        res = [
            ("P", "@PD0 || @PD1 || @PC0 || @PC1 || @M || @S1 || @buffer0 || @buffer1"),
            ("PD0", "t := 0; (t%4 == 0 -> (ch_x6_0?x6; x7 := x6*1; ch_x7_0!x7); wait(4); t := t+4)**"),
            ("PD1", "t := 0; (t%2 == 0 -> (ch_x4_0?x4; x5 := x4*1; ch_x5_0!x5); wait(2); t := t+2)**"),
            ("PC0", "x1 := 2; (<x1_dot = x7 & true> |> [] (ch_x7_0?x7 --> skip, ch_x1_0!x1 --> skip))**"),
            ("PC1", "x4 := 3; (<x4_dot = 1 & true> |> [] (ch_x4_0!x4 --> skip))**"),
            ("M", "x := 0; y := 0; a := 0; z := 0; num := 0; ch_x0_0?x; ch_x1_0?a; ch_x2_0!y; wait(3); "
                  '(num == 0 -> (ch_x0_0?x; ch_x1_0?a; E := ""; EL := [""]; NL := [1]; num := 1); '
                  "num == 1 -> (BC1!E --> VOut1_x!x; VOut1_y!y; VOut1_a!a; VOut1_z!z "
                  "$ BR1?E --> VIn1_x?x; VIn1_y?y; VIn1_a?a; VIn1_z?z; EL := push(EL, E); NL := push(NL, 1); num := 1 "
                  "$ BO1? --> VIn1_x?x; VIn1_y?y; VIn1_a?a; VIn1_z?z; num := num+1; NL := pop(NL); NL := push(NL, 1)); "
                  "num == 2 -> (EL := pop(EL); NL := pop(NL); EL == [] -> (num := 0; ch_x2_0!y; wait(3)); "
                  "EL != [] -> (E := top(EL); num := top(NL))))**"),
            ("S1", "a_S1 := 0; a_on := 0; a_off := 0; a_S1 := 1; a_on := 1; "
                   "(BC1?E; VOut1_x?x; VOut1_y?y; VOut1_a?a; VOut1_z?z; "
                   "if a_on == 1 then done := 0; done == 0 -> (z := x+a; y := z+1; a_on := 0; a_off := 1; done := 1); "
                   "done == 0 -> skip elif a_off == 1 then done := 0; done == 0 -> "
                   "(y := x-a; a_off := 0; a_on := 1; done := 1); done == 0 -> skip else skip endif; "
                   "BO1!; VIn1_x!x; VIn1_y!y; VIn1_a!a; VIn1_z!z)**"),
            ("buffer0", "(ch_x5_0?x5; ch_x0_0!x5; wait(2); ch_x5_0?x5; wait(1); "
                        "ch_x0_0!x5; wait(1); ch_x5_0?x5; wait(2))**"),
            ("buffer1", "(ch_x2_0?x2; ch_x6_0!x2; wait(3); ch_x2_0?x2; wait(1); "
                        "ch_x6_0!x2; wait(2); ch_x2_0?x2; wait(2); ch_x6_0!x2; wait(1); ch_x2_0?x2; wait(3))**")
        ]
        expected_process = hcsp.HCSPProcess()
        for name, _hp in res:
            expected_process.add(name, hp_parser.parse(_hp))
        # print(expected_process)

        self.assertEqual(process, expected_process)


if __name__ == "__main__":
    unittest.main()
