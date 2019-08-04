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
            ("(x := x + 1)**", {"x": 2}, ("step", "x := x + 1; (x := x + 1)**"), {"x": 2}),
            ("(x := 2; x := x + 1)**", {"x": 2}, ("step", "x := 2; x := x + 1; (x := 2; x := x + 1)**"), {"x": 2}),
            ("c?x", {}, ("comm", [("c", "?")]), {}),
            ("c!x", {}, ("comm", [("c", "!")]), {}),
            ("wait(3)", {}, ("delay", 3), {}),
            ("<x_dot = 1 & true> |> [](c1?x --> skip, c2!y --> skip)", {},
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
            ("x := x + 1; c!x", {"x": 2}, "c!x", {"x": 3}, ("comm", [("c", "!")])),
            ("wait(3)", {}, "wait(3)", {}, ("delay", 3)),
            ("(x := x + 1; wait(3))**", {"x": 2}, "wait(3); (x := x + 1; wait(3))**", {"x": 3}, ("delay", 3)),
        ]

        for cmd, state, cmd2, state2, reason in test_data:
            cmd = parser.hp_parser.parse(cmd)
            cmd2 = parser.hp_parser.parse(cmd2)
            self.assertEqual(simulator.exec_process(cmd, state), (cmd2, reason))
            self.assertEqual(state, state2)

    def testExecInputComm(self):
        test_data = [
            ("c?x", {}, "c", 2, "skip", {"x": 2}),
            ("c?x; x := x + 1", {}, "c", 2, "skip; x := x + 1", {"x": 2}),
            ("c?x; x := x + 1; y := 2", {}, "c", 2, "skip; x := x + 1; y := 2", {"x": 2}),
            ("<x_dot = 1 & true> |> [](c?x --> x := x + 1)", {}, "c", 2, "x := x + 1", {"x": 2}),
            ("<x_dot = 1 & true> |> [](c?x --> skip); x := x + 2", {}, "c", 2, "skip; x := x + 2", {"x": 2})
        ]

        for cmd, state, ch_name, val, cmd2, state2 in test_data:
            cmd = parser.hp_parser.parse(cmd)
            cmd2 = parser.hp_parser.parse(cmd2)
            self.assertEqual(simulator.exec_input_comm(cmd, state, ch_name, val), cmd2)
            self.assertEqual(state, state2)

    def testExecOutputComm(self):
        test_data = [
            ("c!x", {"x": 2}, "c", "skip", 2, {"x": 2}),
            ("c!x+1", {"x": 2}, "c", "skip", 3, {"x": 2}),
            ("c!x+y; x := 3", {"x": 2, "y": 3}, "c", "skip; x := 3", 5, {"x": 2, "y": 3}),
            ("c!x*y; x := 3; y := 0", {"x": 2, "y": 3}, "c", "skip; x := 3; y := 0", 6, {"x": 2, "y": 3}),
            ("<x_dot = 1 & true> |> [](c!x --> skip)", {"x": 2}, "c", "skip", 2, {"x": 2}),
            ("<x_dot = 1 & true> |> [](c!x+1 --> skip); x := x + 1", {"x": 2}, "c", "skip; x := x + 1", 3, {"x": 2}),
        ]

        for cmd, state, ch_name, cmd2, val, state2 in test_data:
            cmd = parser.hp_parser.parse(cmd)
            cmd2 = parser.hp_parser.parse(cmd2)
            self.assertEqual(simulator.exec_output_comm(cmd, state, ch_name), (cmd2, val))
            self.assertEqual(state, state2)

    def testDelay(self):
        test_data = [
            ("skip", {}, 3, "skip", {}),
            ("wait(3)", {}, 3, "skip", {}),
            ("wait(3)", {}, 2, "wait(1)", {}),
            ("wait(3); x := x + 1", {"x": 2}, 3, "skip; x := x + 1", {"x": 2}),
            ("wait(3); x := x + 1", {"x": 2}, 2, "wait(1); x := x + 1", {"x": 2}),
            ("<x_dot = 1 & true> |> [](c!x --> skip)", {"x": 2}, 3,
             "<x_dot = 1 & true> |> [](c!x --> skip)", {"x": 5}),
            ("<x_dot = 1 & true> |> [](c!x --> skip); x := x + 1", {"x": 2}, 3,
             "<x_dot = 1 & true> |> [](c!x --> skip); x := x + 1", {"x": 5}),
        ]

        for cmd, state, delay, cmd2, state2 in test_data:
            cmd = parser.hp_parser.parse(cmd)
            cmd2 = parser.hp_parser.parse(cmd2)
            self.assertEqual(simulator.exec_delay(cmd, state, delay), cmd2)
            self.assertEqual(state, state2)

    def testExecParallel1(self):
        hp1 = parser.hp_parser.parse("(<x_dot = 1 & true> |> [](p2c!x --> skip); c2p?x)**")
        hp1_init = {"x": 0}
        hp2 = parser.hp_parser.parse("(wait(2); p2c?x; c2p!x-1)**")
        hp2_init = {}

        trace = simulator.exec_parallel(6, [(hp1, hp1_init), (hp2, hp2_init)])
        self.assertEqual(trace, ["delay 2", "IO p2c 2", "IO c2p 1", "delay 2", "IO p2c 3", "IO c2p 2"])

    def testExecParallel2(self):
        hp1 = parser.hp_parser.parse("(<x_dot = 1 & true> |> [](p2c!x --> skip); c2p?x)**")
        hp1_init = {"x": 0}
        hp2 = parser.hp_parser.parse("wait(2); p2c?x; c2p!x-1")
        hp2_init = {}

        trace = simulator.exec_parallel(6, [(hp1, hp1_init), (hp2, hp2_init)])
        self.assertEqual(trace, ["delay 2", "IO p2c 2", "IO c2p 1", "deadlock"])


if __name__ == "__main__":
    unittest.main()
