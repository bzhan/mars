"""Unittest for simulation of HCSP."""

import unittest

from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import simulator
from ss2hcsp.hcsp import parser


class SimulatorTest(unittest.TestCase):
    def testEvalAExpr(self):
        test_data = [
            ("x + 2", {"x": 1}, 3),
            ("t % 3", {"t": 7}, 1),
        ]

        for expr, state, res in test_data:
            expr = parser.aexpr_parser.parse(expr)
            self.assertEqual(simulator.eval_expr(expr, state), res)

    def testEvalBExpr(self):
        test_data = [
            ("x >= y", {"x": 3, "y": 2}, True),
            ("x >= y", {"x": 2, "y": 3}, False),
            ("x > y || x < y", {"x": 2, "y": 2}, False),
            ("x == 2 --> y == 3", {"x": 2, "y": 3}, True),
            ("x == 2 --> y == 3", {"x": 2, "y": 4}, False),
            ("x == 2 --> y == 3", {"x": 3, "y": 4}, True),
        ]

        for expr, state, res in test_data:
            expr = parser.bexpr_parser.parse(expr)
            self.assertEqual(simulator.eval_expr(expr, state), res)

    def testExecStep(self):
        test_data = [
            ("skip", (), {}, None, {}),
            ("x := 2", (), {}, None, {"x": 2}),
            ("x := x + 1", (), {"x": 2}, None, {"x": 3}),
            ("x := 2; x := x + 1", (0,), {}, (1,), {"x": 2}),
            ("skip; x := x + 1", (0,), {"x": 2}, (1,), {"x": 2}),
            ("(x := x + 1)**", (), {"x": 2}, (), {"x": 3}),
            ("(x := 2; x := x + 1)**", (0,), {"x": 1}, (1,), {"x": 2}),
            ("(x := 2; x := x + 1)**", (1,), {"x": 2}, (0,), {"x": 3}),
            ("(<x_dot = 1 & true> |> [] (p2c!x --> skip); c2p?x)**", (0, 0), {}, (1,), {}),
            ("x == 0 -> x := 2; x := 3", (0,), {"x": 0}, (0, 0), {"x": 0}),
            ("x == 0 -> x := 2; x := 3", (0,), {"x": 1}, (1,), {"x": 1}),
            ("x == 0 -> x := 2", (), {"x": 0}, (0,), {"x": 0}),
            ("x == 0 -> x := 2", (), {"x": 1}, None, {"x": 1}),
        ]

        for cmd, pos, state, pos2, state2 in test_data:
            cmd = parser.hp_parser.parse(cmd)
            info = simulator.HCSPInfo(cmd, pos=pos, state=state)
            res = info.exec_step()
            self.assertEqual(res, 'step')
            self.assertEqual(info.pos, pos2)
            self.assertEqual(info.state, state2)

    def testExecStep2(self):
        test_data = [
            ("c?x", (), "comm", [("c", "?")]),
            ("c!x", (), "comm", [("c", "!")]),
            ("wait(3)", (0,), "delay", 3),
            ("wait(3)", (1,), "delay", 2),
            ("<x_dot = 1 & true> |> [](c1?x --> skip, c2!y --> skip)", (), "comm", [("c1", "?"), ("c2", "!")]),
            ("x := 1; wait(3)", (1, 0), "delay", 3),
            ("(x := 1; wait(3))**", (1, 0), "delay", 3),
            ("(x := 1; wait(3))**", (1, 1), "delay", 2),
        ]

        for cmd, pos, reason, arg in test_data:
            cmd = parser.hp_parser.parse(cmd)
            info = simulator.HCSPInfo(cmd, pos=pos)
            res = info.exec_step()
            self.assertEqual(res, (reason, arg))
            self.assertEqual(info.pos, pos)
            self.assertEqual(info.state, dict())

    def testExecProcess(self):
        test_data = [
            ("skip", (), {}, None, {}, "end"),
            ("x := 2", (), {}, None, {"x": 2}, "end"),
            ("x := 2; x := x + 1", (0,), {}, None, {"x": 3}, "end"),
            ("x := x + 1; c!x", (0,), {"x": 2}, (1,), {"x": 3}, ("comm", [("c", "!")])),
            ("wait(3)", (0,), {}, (0,), {}, ("delay", 3)),
            ("(x := x + 1; wait(3))**", (0,), {"x": 2}, (1, 0), {"x": 3}, ("delay", 3)),
            ("x > 0 -> x := 1; x < 0 -> x := -1", (0,), {"x": 0}, None, {"x": 0}, "end"),
            ("x > 0 -> x := 1; x < 0 -> x := -1", (0,), {"x": 2}, None, {"x": 1}, "end"),
            ("x > 0 -> x := 1; x < 0 -> x := -1", (0,), {"x": -2}, None, {"x": -1}, "end"),
        ]

        for cmd, pos, state, pos2, state2, reason in test_data:
            cmd = parser.hp_parser.parse(cmd)
            info = simulator.HCSPInfo(cmd, pos=pos, state=state)
            res = info.exec_process()
            self.assertEqual(res, reason)
            self.assertEqual(info.pos, pos2)
            self.assertEqual(info.state, state2)

    def testExecInputComm(self):
        test_data = [
            ("c?x", (), {}, "c", 2, None, {"x": 2}),
            ("c?x; x := x + 1", (0,), {}, "c", 2, (1,), {"x": 2}),
            ("c?x; x := x + 1; y := 2", (0,), {}, "c", 2, (1,), {"x": 2}),
            ("<x_dot = 1 & true> |> [](c?x --> x := x + 1)", (), {}, "c", 2, (0,), {"x": 2}),
            ("<x_dot = 1 & true> |> [](c?x --> skip); x := x + 2", (0,), {}, "c", 2, (0, 0), {"x": 2})
        ]

        for cmd, pos, state, ch_name, val, pos2, state2 in test_data:
            cmd = parser.hp_parser.parse(cmd)
            info = simulator.HCSPInfo(cmd, pos=pos, state=state)
            info.exec_input_comm(ch_name, val)
            self.assertEqual(info.pos, pos2)
            self.assertEqual(info.state, state2)

    def testExecOutputComm(self):
        test_data = [
            ("c!x", (), {"x": 2}, "c", None, 2, {"x": 2}),
            ("c!x+1", (), {"x": 2}, "c", None, 3, {"x": 2}),
            ("c!x+y; x := 3", (0,), {"x": 2, "y": 3}, "c", (1,), 5, {"x": 2, "y": 3}),
            ("c!x*y; x := 3; y := 0", (0,), {"x": 2, "y": 3}, "c", (1,), 6, {"x": 2, "y": 3}),
            ("<x_dot = 1 & true> |> [](c!x --> skip)", (), {"x": 2}, "c", (0,), 2, {"x": 2}),
            ("<x_dot = 1 & true> |> [](c!x+1 --> skip); x := x + 1", (0,), {"x": 2}, "c", (0, 0), 3, {"x": 2}),
        ]

        for cmd, pos, state, ch_name, pos2, val, state2 in test_data:
            cmd = parser.hp_parser.parse(cmd)
            info = simulator.HCSPInfo(cmd, pos=pos, state=state)
            res = info.exec_output_comm(ch_name)
            self.assertEqual(res, val)
            self.assertEqual(info.pos, pos2)
            self.assertEqual(info.state, state2)

    def testExecDelay(self):
        test_data = [
            ("skip", (), {}, 3, (), {}),
            ("wait(3)", (0,), {}, 3, None, {}),
            ("wait(3)", (0,), {}, 2, (2,), {}),
            ("wait(3)", (1,), {}, 1, (2,), {}),
            ("wait(3)", (1,), {}, 2, None, {}),
            ("wait(3); x := x + 1", (0, 0), {"x": 2}, 3, (1,), {"x": 2}),
            ("wait(3); x := x + 1", (0, 0), {"x": 2}, 2, (0, 2), {"x": 2}),
            ("wait(3); x := x + 1", (0, 1), {"x": 2}, 2, (1,), {"x": 2}),
            ("<x_dot = 1 & true> |> [](c!x --> skip)", (), {"x": 2}, 3, (), {"x": 5}),
            ("<x_dot = 1 & true> |> [](c!x --> skip); x := x + 1", (0,), {"x": 2}, 3, (0,), {"x": 5}),
            ("wait(3)", "end", {}, 3, None, {}),
        ]

        for cmd, pos, state, delay, pos2, state2 in test_data:
            cmd = parser.hp_parser.parse(cmd)
            info = simulator.HCSPInfo(cmd, pos=pos, state=state)
            info.exec_delay(delay)
            self.assertEqual(info.pos, pos2)
            self.assertEqual(info.state, state2)

    def run_test(self, infos, num_steps, trace):
        for i in range(len(infos)):
            infos[i] = simulator.HCSPInfo(infos[i])

        res = simulator.exec_parallel(infos, num_steps)
        self.assertEqual(res, trace)

    def run_test_steps(self, infos, res_len, *, start_event):
        for i in range(len(infos)):
            infos[i] = simulator.HCSPInfo(infos[i])

        res = simulator.exec_parallel_steps(infos, start_event=start_event)
        self.assertEqual(len(res), res_len)

    def testExecParallel1(self):
        self.run_test([
            "x := 0; (<x_dot = 1 & true> |> [](p2c!x --> skip); c2p?x)**",
            "(wait(2); p2c?x; c2p!x-1)**",
        ], 6, ["delay 2", "IO p2c 2", "IO c2p 1", "delay 2", "IO p2c 3", "IO c2p 2"])

    def testExecParallel2(self):
        self.run_test([
            "x := 0; (<x_dot = 1 & true> |> [](p2c!x --> skip); c2p?x)**",
            "wait(2); p2c?x; c2p!x-1",
        ], 6, ["delay 2", "IO p2c 2", "IO c2p 1", "deadlock"])

    def testExecParallel3(self):
        self.run_test([
            "x := 0; x := x + 1",
            "y := 2",
        ], 6, ['deadlock'])

    def testExecParallel4(self):
        self.run_test([
            "x := 0; (<x_dot = 1 & true> |> [](p2c!x --> skip); c2p?x)**",
            "x := 0; (<x_dot = 1 & true> |> [](p2c!x --> skip); c2p?x)**",
        ], 6, ['deadlock'])

    def testExecParallel5(self):
        self.run_test([
            "z := 1; (x?x $ z!z $ y?y)",
            "y := 2; y!y",
        ], 3, ["IO y 2", "deadlock"])

    def testExecParallel6(self):
        self.run_test([
            "z := 1; (x?x $ z!z $ y?y)",
            "z?z",
        ], 3, ["IO z 1", "deadlock"])

    def testExecParallel7(self):
        self.run_test([
            "x := 1; y := 2; z := 3; wait(3); w := 4",
            "x := 11; y := 12; wait(2); z := 3"
        ], 6, ["delay 2", "delay 1", "deadlock"])

    def testExecParallelSteps1(self):
        self.run_test_steps([
            "x := 1; y := 2; z := 3; wait(3); w := 4",
            "x := 11; y := 12; wait(2); z := 3"
        ], 5, start_event=False)

    def testExecParallelSteps2(self):
        self.run_test_steps([
            "wait(1); x := 1; y := 2; z := 3; wait(3); w := 4",
            "wait(2); z := 3"
        ], 3, start_event=True)


if __name__ == "__main__":
    unittest.main()
