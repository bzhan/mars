"""Unittest for simulation of HCSP."""

import unittest

from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import simulator
from ss2hcsp.hcsp import parser


class SimulatorTest(unittest.TestCase):
    def testExecStep(self):
        test_data = [
            ("skip", {}, ("end", None), {}),
            ("x := 2", {}, ("step", "skip"), {"x": 2}),
            ("x := x + 1", {"x": 2}, ("step", "skip"), {"x": 3}),
            ("x := 2; x := x + 1", {}, ("step", "skip; x := x + 1"), {"x": 2}),
            ("skip; x := x + 1", {"x": 2}, ("step", "x := x + 1"), {"x": 2}),
            ("(x := x + 1)*", {"x": 2}, ("step", "x := x + 1; (x := x + 1)*"), {"x": 2}),
            ("(x := 2; x := x + 1)*", {"x": 2}, ("step", "x := 2; x := x + 1; (x := 2; x := x + 1)*"), {"x": 2}),
            ("ch_c?x", {}, ("comm", [("c", "?")]), {}),
            ("ch_c!x", {}, ("comm", [("c", "!")]), {}),
            ("wait(3)", {}, ("delay", 3), {}),
            ("<x_dot = 1 & true> |> [](ch_c1?x --> skip, ch_c2!y --> skip)", {},
             ("comm", [("c1", "?"), ("c2", "!")]), {}),
        ]

        for cmd, state, exp_res, state2 in test_data:
            cmd = parser.hp_parser.parse(cmd)
            if exp_res[0] == 'step':
                exp_res = (exp_res[0], parser.hp_parser.parse(exp_res[1]))
            res = simulator.exec_step(cmd, state)
            self.assertEqual(res, exp_res)
            self.assertEqual(state, state2)

    def testExecProcess(self):
        test_data = [
            ("skip", {}, "skip", {}, ("end", None)),
            ("x := 2", {}, "skip", {"x": 2}, ("end", None)),
            ("x := 2; x := x + 1", {}, "skip", {"x": 3}, ("end", None)),
            ("x := x + 1; ch_c!x", {"x": 2}, "ch_c!x", {"x": 3}, ("comm", [("c", "!")])),
            ("wait(3)", {}, "wait(3)", {}, ("delay", 3)),
            ("(x := x + 1; wait(3))*", {"x": 2}, "wait(3); (x := x + 1; wait(3))*", {"x": 3}, ("delay", 3)),
        ]

        for cmd, state, cmd2, state2, reason in test_data:
            cmd = parser.hp_parser.parse(cmd)
            cmd2 = parser.hp_parser.parse(cmd2)
            self.assertEqual(simulator.exec_process(cmd, state), (cmd2, reason))
            self.assertEqual(state, state2)


if __name__ == "__main__":
    unittest.main()
