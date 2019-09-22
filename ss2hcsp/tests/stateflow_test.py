# Unit test for translation of Simulink diagrams

import unittest
from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp.parser import hp_parser


class SfTest(unittest.TestCase):
    def testEarlyExit(self):
        location = "./Examples/Stateflow/early_exit/early_exit.xml"
        diagram = SL_Diagram(location=location)
        diagram.parse_stateflow_xml()
        chart = list(diagram.charts.values())[0]
        process = chart.get_process()
        # print(process)

        res = [
            ("D", "@M || @S1"),
            ("M", "num := 0; (@M_main)**"),
            ("M_main", 'num == 0 -> (E := "e"; EL := []; EL := push(EL, E); NL := []; NL := push(NL, 1); num := 1); '
                       "num == 1 -> (BC1!E --> skip $ "
                       "BR1?E --> EL := push(EL, E); NL := push(NL, 1); num := 1 $ "
                       "BO1? --> num := num+1; NL := pop(NL); NL := push(NL, 1)); "
                       "num == 2 -> (EL := pop(EL); NL := pop(NL); "
                       "EL == [] -> (num := 0); EL != [] -> (E := top(EL); num := top(NL)))"),
            ("S1", "a_S1 := 0; a_A := 0; a_A1 := 0; a_A2 := 0; a_B := 0; "
                   "a_S1 := 1; a_A := 1; a_A1 := 1; rec X.(BC1?E; @Diag_S1; BO1!)"),
            ("Diag_S1", "if a_A == 1 then @A elif a_B == 1 then @B else skip endif"),
            ("A", 'done := 0; E == "e" && done == 0 -> '
                  "(a_A2 == 1 -> (a_A2 := 0); a_A1 == 1 -> (a_A1 := 0); a_A := 0; a_B := 1; done := 1); "
                  "done == 0 -> (@Diag_A)"),
            ("Diag_A", "if a_A1 == 1 then @A1 elif a_A2 == 1 then @A2 else skip endif"),
            ("A1", "done := 0; done == 0 -> "
                   '(BR1!"e"; @X; a_A == 1 -> (a_A1 := 0; a_A2 := 1; done := 1)); done == 0 -> (skip)'),
            ("A2", "skip"),
            ("B", "skip"),
        ]

        expected_process = hcsp.HCSPProcess()
        for name, hp in res:
            expected_process.add(name, hp_parser.parse(hp))
        # print(expected_process)

        self.assertEqual(process, expected_process)

        process.substitute()
        # print(process)
        res = [
            ("D", "@M || @S1"),
            ("M", 'num := 0; (num == 0 -> (E := "e"; EL := []; EL := push(EL, E); '
                  "NL := []; NL := push(NL, 1); num := 1); "
                  "num == 1 -> (BC1!E --> skip $ BR1?E --> EL := push(EL, E); NL := push(NL, 1); num := 1 $ "
                  "BO1? --> num := num+1; NL := pop(NL); NL := push(NL, 1)); "
                  "num == 2 -> (EL := pop(EL); NL := pop(NL); EL == [] -> num := 0; "
                  "EL != [] -> (E := top(EL); num := top(NL))))**"),
            ("S1", "a_S1 := 0; a_A := 0; a_A1 := 0; a_A2 := 0; a_B := 0; "
                   "a_S1 := 1; a_A := 1; a_A1 := 1; "
                   'rec X.(BC1?E; if a_A == 1 then done := 0; E == "e" && done == 0 -> '
                   "(a_A2 == 1 -> a_A2 := 0; a_A1 == 1 -> a_A1 := 0; a_A := 0; a_B := 1; done := 1); "
                   "done == 0 -> if a_A1 == 1 then done := 0; done == 0 -> "
                   '(BR1!"e"; @X; a_A == 1 -> (a_A1 := 0; a_A2 := 1; done := 1)); done == 0 -> skip '
                   "elif a_A2 == 1 then skip else skip endif elif a_B == 1 then skip else skip endif; BO1!)"),
        ]
        expected_process = hcsp.HCSPProcess()
        for name, hp in res:
            expected_process.add(name, hp_parser.parse(hp))
        # print(expected_process)

        self.assertEqual(process, expected_process)

    def test_statelessWriter1(self):
        location = "./Examples/Stateflow/dds/statelessWriter1.xml"
        diagram = SL_Diagram(location=location)
        diagram.parse_stateflow_xml()
        chart = list(diagram.charts.values())[0]
        process = chart.get_process()
        process.substitute()
        # print(process)

        res = [
            ("D", "@M || @S1"),
            ("M", 'num := 0; (num == 0 -> (E := "e"; EL := []; EL := push(EL, E); '
                  'NL := []; NL := push(NL, 1); num := 1); num == 1 -> (BC1!E --> skip $ '
                  'BR1?E --> EL := push(EL, E); NL := push(NL, 1); num := 1 $ '
                  'BO1? --> num := num+1; NL := pop(NL); NL := push(NL, 1)); '
                  'num == 2 -> (EL := pop(EL); NL := pop(NL); '
                  'EL == [] -> num := 0; EL != [] -> (E := top(EL); num := top(NL))))**'),
            ("S1", "a_S1 := 0; a_pushing := 0; a_idle := 0; a_S1 := 1; unsent := 5; cansend := 1; a_idle := 1; "
                   "(BC1?E; if a_pushing == 1 then done := 0; unsent <= 0 && done == 0 -> "
                   "(a_pushing := 0; a_idle := 1; done := 1); cansend == 1 && done == 0 -> "
                   "(a_pushing := 0; unsent := unsent-1; a_pushing := 1; done := 1); "
                   "done == 0 -> flag := 0 elif a_idle == 1 then done := 0; unsent > 0 && done == 0 -> "
                   "(a_idle := 0; a_pushing := 1; done := 1); done == 0 -> flag := 1 else skip endif; BO1!)**"),
        ]
        expected_process = hcsp.HCSPProcess()
        for name, hp in res:
            expected_process.add(name, hp_parser.parse(hp))
        # print(expected_process)

        self.assertEqual(process, expected_process)

    def test_statelessWriter2_1(self):
        location = "./Examples/Stateflow/dds/statelessWriter2_1.xml"
        diagram = SL_Diagram(location=location)
        diagram.parse_stateflow_xml()
        chart = list(diagram.charts.values())[0]
        process = chart.get_process()
        process.substitute()
        # print(process)

        res = [
            ("D", "@M || @S1"),
            ("M", 'num := 0; (num == 0 -> (E := "e"; EL := []; EL := push(EL, E); '
                  "NL := []; NL := push(NL, 1); num := 1); num == 1 -> (BC1!E --> skip $ "
                  "BR1?E --> EL := push(EL, E); NL := push(NL, 1); num := 1 $ "
                  "BO1? --> num := num+1; NL := pop(NL); NL := push(NL, 1)); "
                  "num == 2 -> (EL := pop(EL); NL := pop(NL); "
                  "EL == [] -> num := 0; EL != [] -> (E := top(EL); num := top(NL))))**"),
            ("S1", "a_S1 := 0; a_pushing := 0; a_idle := 0; a_S1 := 1; i := 3; cansend := 1; state_time := 0; "
                   "a_idle := 1; heartbeat := 0; (BC1?E; if a_pushing == 1 then done := 0; i <= 0 && done == 0 -> "
                   "(a_pushing := 0; state_time := 0; a_idle := 1; heartbeat := 0; done := 1); "
                   "cansend == 1 && done == 0 -> (i := i-1; a_pushing := 0; a_pushing := 1; done := 1); "
                   "done == 0 -> flag := 0 elif a_idle == 1 then done := 0; i > 0 && done == 0 -> "
                   "(a_idle := 0; a_pushing := 1; done := 1); state_time >= 3 && done == 0 -> "
                   "(heartbeat := 1; a_idle := 0; state_time := 0; a_idle := 1; heartbeat := 0; done := 1); "
                   "done == 0 -> (flag := 1; state_time := state_time+2) else skip endif; BO1!)**")
        ]
        expected_process = hcsp.HCSPProcess()
        for name, hp in res:
            expected_process.add(name, hp_parser.parse(hp))
        # print(expected_process)

        self.assertEqual(process, expected_process)

    def test_statelessWriter2_2(self):
        location = "./Examples/Stateflow/dds/statelessWriter2_2.xml"
        diagram = SL_Diagram(location=location)
        diagram.parse_stateflow_xml()
        chart = list(diagram.charts.values())[0]
        process = chart.get_process()
        # print(process)

        res = [
            ("D", "@M || @S1"),
            ("M", "num := 0; (@M_main)**"),
            ("M_main", 'num == 0 -> (E := "e"; EL := []; EL := push(EL, E); NL := []; NL := push(NL, 1); num := 1); '
                       "num == 1 -> (BC1!E --> skip $ BR1?E --> EL := push(EL, E); NL := push(NL, 1); "
                       "num := 1 $ BO1? --> num := num+1; NL := pop(NL); NL := push(NL, 1)); "
                       "num == 2 -> (EL := pop(EL); NL := pop(NL); EL == [] -> num := 0; "
                       "EL != [] -> (E := top(EL); num := top(NL)))"),
            ("S1", "a_S1 := 0; a_repairing := 0; a_must_repair := 0; a_waiting := 0; a_S1 := 1; re_changes := 0; "
                   "ACKNACK := 1; cansend := 1; a_waiting := 1; (BC1?E; @Diag_S1; BO1!)**"),
            ("Diag_S1", "if a_repairing == 1 then @repairing elif a_must_repair == 1 then @must_repair "
                        "elif a_waiting == 1 then @waiting else skip endif"),
            ("repairing", "done := 0; re_changes == 0 && done == 0 -> (a_repairing := 0; a_waiting := 1; done := 1); "
                          "cansend == 1 && done == 0 -> "
                          "(a_repairing := 0; re_changes := re_changes-1; a_repairing := 1; done := 1); "
                          "done == 0 -> flag := 0"),
            ("must_repair", "done := 0; state_time >= 5 && done == 0 -> "
                            "(a_must_repair := 0; a_repairing := 1; done := 1); ACKNACK == 1 && done == 0 -> "
                            "(a_must_repair := 0; re_changes := re_changes+1; state_time := 0; a_must_repair := 1; "
                            "done := 1); done == 0 -> (flag := 1; state_time := state_time+2)"),
            ("waiting", "done := 0; re_changes > 0 && done == 0 -> "
                        "(ACKNACK := 0; a_waiting := 0; state_time := 0; a_must_repair := 1; done := 1); "
                        "ACKNACK == 1 && done == 0 -> "
                        "(a_waiting := 0; re_changes := re_changes+1; a_waiting := 1; done := 1); "
                        "done == 0 -> flag := 1"),
        ]
        expected_process = hcsp.HCSPProcess()
        for name, hp in res:
            expected_process.add(name, hp_parser.parse(hp))

        self.assertEqual(process, expected_process)

        process.substitute()
        # print(process)
        res = [
            ("D", "@M || @S1"),
            ("M", 'num := 0; (num == 0 -> (E := "e"; EL := []; EL := push(EL, E); '
                  'NL := []; NL := push(NL, 1); num := 1); num == 1 -> '
                  '(BC1!E --> skip $ BR1?E --> EL := push(EL, E); NL := push(NL, 1); num := 1 $ '
                  'BO1? --> num := num+1; NL := pop(NL); NL := push(NL, 1)); '
                  'num == 2 -> (EL := pop(EL); NL := pop(NL); EL == [] -> num := 0; '
                  'EL != [] -> (E := top(EL); num := top(NL))))**'),
            ("S1", "a_S1 := 0; a_repairing := 0; a_must_repair := 0; a_waiting := 0; a_S1 := 1; re_changes := 0; "
                   "ACKNACK := 1; cansend := 1; a_waiting := 1; "
                   "(BC1?E; if a_repairing == 1 then done := 0; re_changes == 0 && done == 0 -> "
                   "(a_repairing := 0; a_waiting := 1; done := 1); cansend == 1 && done == 0 -> "
                   "(a_repairing := 0; re_changes := re_changes-1; a_repairing := 1; done := 1); "
                   "done == 0 -> flag := 0 elif a_must_repair == 1 then done := 0; state_time >= 5 && done == 0 -> "
                   "(a_must_repair := 0; a_repairing := 1; done := 1); ACKNACK == 1 && done == 0 -> "
                   "(a_must_repair := 0; re_changes := re_changes+1; state_time := 0; a_must_repair := 1; done := 1); "
                   "done == 0 -> (flag := 1; state_time := state_time+2) elif a_waiting == 1 then done := 0; "
                   "re_changes > 0 && done == 0 -> (ACKNACK := 0; a_waiting := 0; state_time := 0; "
                   "a_must_repair := 1; done := 1); ACKNACK == 1 && done == 0 -> "
                   "(a_waiting := 0; re_changes := re_changes+1; a_waiting := 1; done := 1); "
                   "done == 0 -> flag := 1 else skip endif; BO1!)**")
        ]
        expected_process = hcsp.HCSPProcess()
        for name, hp in res:
            expected_process.add(name, hp_parser.parse(hp))

        self.assertEqual(process, expected_process)


if __name__ == "__main__":
    unittest.main()
