"""Unittest for simulation of HCSP."""

import unittest
import math

from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import simulator
from ss2hcsp.hcsp import parser


class SimulatorTest(unittest.TestCase):
    def testEvalNone(self):
        self.assertEqual(simulator.eval_expr(None, {"x": 2}), None)

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

    def testStringOfPos(self):
        test_data = [
            ("x := 1; x := x + 1", (1,), "p1"),
            ("x := 1; wait(1)", (1, 0), "p1"),
            ("rec X.(x := 1; wait(1); @X)", (), "p"),
            ("rec X.(x := 1; wait(1); @X)", (0, 2), "p0.2"),
            ("rec X.(x := 1; wait(1); @X)", (0, 2, 0), "p"),
            ("rec X.(x := 1; wait(1); @X)", (0, 2, 0, 0, 0), "p0.0"),
            ("rec X.(x := 1; wait(1); @X)", (0, 2, 0, 0, 1, 0), "p0.1"),
        ]

        for hp, pos, expected_pos in test_data:
            hp = parser.hp_parser.parse(hp)
            pos = simulator.remove_rec(hp, pos)
            self.assertEqual(simulator.string_of_pos(hp, pos), expected_pos)

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
            ("rec X.(x := 1; wait(1); @X)", (), {"x": 1}, (0, 0), {"x": 1}),
            ("rec X.(x := 1; wait(1); @X)", (0, 0), {"x": 1}, (0, 1, 0), {"x": 1}),
            ("rec X.(x := 1; wait(1); @X)", (0, 2), {"x": 1}, (0, 2, 0), {"x": 1}),
            ("rec X.(x := 1; wait(1); @X)", (0, 2, 0), {"x": 1}, (0, 2, 0, 0, 0), {"x": 1}),
            ("rec X.(x := 1; wait(1); @X)", (0, 2, 0, 0, 0), {"x": 1}, (0, 2, 0, 0, 1, 0), {"x": 1}),
            ("if x == 0 then x := 1 else x := 0 endif", (), {"x": 0}, (0,), {"x": 0}),
            ("if x == 0 then x := 1 else x := 0 endif", (), {"x": 1}, (1,), {"x": 1}),
            ("if x == 0 then x := 1 else x := 0 endif", (0,), {"x": 0}, None, {"x": 1}),
            ("if x == 0 then x := 1 else x := 0 endif", (1,), {"x": 1}, None, {"x": 0}),
            ("if x == 0 then x := 1; skip else skip endif", (0, 0), {"x": 0}, (0, 1), {"x": 1}),
        ]

        for cmd, pos, state, pos2, state2 in test_data:
            info = simulator.HCSPInfo('P0', cmd, pos=pos, state=state)
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
            ("rec X.(x := 1; wait(1); @X)", (0, 1, 0), "delay", 1),
        ]

        for cmd, pos, reason, arg in test_data:
            info = simulator.HCSPInfo('P0', cmd, pos=pos)
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
            info = simulator.HCSPInfo('P0', cmd, pos=pos, state=state)
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
            info = simulator.HCSPInfo('P0', cmd, pos=pos, state=state)
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
            info = simulator.HCSPInfo('P0', cmd, pos=pos, state=state)
            res = info.exec_output_comm(ch_name)
            self.assertEqual(res, val)
            self.assertEqual(info.pos, pos2)
            self.assertEqual(info.state, state2)

    def testExecDelay(self):
        test_data = [
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
            ("rec X.(x := 1; wait(1); @X)", (0, 1, 0), {"x": 1}, 1, (0, 2), {"x": 1}),
        ]

        for cmd, pos, state, delay, pos2, state2 in test_data:
            info = simulator.HCSPInfo('P0', cmd, pos=pos, state=state)
            info.exec_delay(delay)
            self.assertEqual(info.pos, pos2)
            self.assertEqual(info.state, state2)

    def assertAlmostEqualState(self, st1, st2):
        self.assertEqual(set(st1.keys()), set(st2.keys()))
        for k in st1:
            self.assertAlmostEqual(st1[k], st2[k], places=3)

    def testODEComm(self):
        test_data = [
            # Acceleration
            ("<x_dot = v, v_dot = a & true> |> [](c!x --> skip)",
             {"a": 1, "v": 0, "x": 0}, 3, {"a": 1, "v": 3, "x": 4.5}),

            # Acceleration with floating point numbers
            ("<x_dot = v, v_dot = a & true> |> [](c!x --> skip)",
             {"a": 1.1, "v": 0, "x": 0}, 3, {"a": 1.1, "v": 3.3, "x": 4.95}),

            # Exponential growth
            ("<x_dot = x & true> |> [](c!x --> skip)", {"x": 1}, 3, {"x": math.exp(3)}),

            # Circular motion
            ("<x_dot = -1 * y, y_dot = x & true> |> [](c!x --> skip)",
             {"x": 1, "y": 0}, 3, {"x": math.cos(3), "y": math.sin(3)}),
        ]

        for cmd, state, delay, state2 in test_data:
            info = simulator.HCSPInfo('P0', cmd, state=state)
            info.exec_delay(delay)
            self.assertAlmostEqualState(info.state, state2)

    def testODEDelay(self):
        test_data = [
            # Acceleration
            ("<x_dot = v, v_dot = a, t_dot = 1 & t < 3>", {"t": 0, "a": 1, "v": 0, "x": 0}, 3.0),

            # Acceleration, upon x reaching a certain value
            ("<x_dot = v, v_dot = a, t_dot = 1 & x < 3>",
             {"t": 0, "a": 1, "v": 0, "x": 0}, math.sqrt(6)),

            # Exponential growth
            ("<x_dot = x, t_dot = 1 & x < 3>", {"t": 0, "x": 1}, math.log(3)),

            # Circular motion
            ("<x_dot = -1 * y, y_dot = x & x > 0>", {"x": 1, "y": 0}, math.pi/2),

            # Some examples of large or infinite delay
            ("<t_dot = 0.1 & t < 6>", {"t": 0}, 60),
            ("<t_dot = 0.01 & t < 60>", {"t": 0}, 100),  # maximum is 100
            ("<x_dot = -1 * y, y_dot = x & x > -2>", {"x": 1, "y": 0}, 100),
        ]

        for cmd, state, delay in test_data:
            hp = parser.hp_parser.parse(cmd)
            res = simulator.get_ode_delay(hp, state)
            self.assertAlmostEqual(res, delay, places=3)

    def run_test(self, infos, num_io_events, trace, *, print_time_series=False, print_state=False):
        for i in range(len(infos)):
            infos[i] = simulator.HCSPInfo('P' + str(i), infos[i])

        res = simulator.exec_parallel(infos, num_io_events=num_io_events)
        res_trace = [event['str'] for event in res['trace'] if event['str'] not in ('start', 'step')]
        self.assertEqual(res_trace, trace)
        if print_time_series:
            for record in time_series:
                print("%s: %s" % (record['time'], record['states']))
        if print_state:
            for info in infos:
                print(info.state)

    def run_test_steps(self, infos, res_len, *, start_event):
        for i in range(len(infos)):
            infos[i] = simulator.HCSPInfo('P' + str(i), infos[i])

        res = simulator.exec_parallel_steps(infos, start_event=start_event)
        self.assertEqual(len(res), res_len)

    def testExecParallel1(self):
        self.run_test([
            "x := 0; (<x_dot = 1 & true> |> [](p2c!x --> skip); c2p?x)**",
            "(wait(2); p2c?x; c2p!x-1)**",
        ], 6, ["delay 2", "IO p2c 2.0", "IO c2p 1.0", "delay 2", "IO p2c 3.0", "IO c2p 2.0"])

    def testExecParallel2(self):
        self.run_test([
            "x := 0; (<x_dot = 1 & true> |> [](p2c!x --> skip); c2p?x)**",
            "wait(2); p2c?x; c2p!x-1",
        ], 6, ["delay 2", "IO p2c 2.0", "IO c2p 1.0", "deadlock"])

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
            "z := 1; (x?x --> skip $ z!z --> skip $ y?y --> skip)",
            "y := 2; y!y",
        ], 3, ["IO y 2", "deadlock"])

    def testExecParallel6(self):
        self.run_test([
            "z := 1; (x?x --> skip $ z!z --> skip $ y?y --> skip)",
            "z?z",
        ], 3, ["IO z 1", "deadlock"])

    def testExecParallel7(self):
        self.run_test([
            "x := 1; y := 2; z := 3; wait(3); w := 4",
            "x := 11; y := 12; wait(2); z := 3"
        ], 6, ["delay 2", "delay 1", "deadlock"])

    def testExecParallel8(self):
        self.run_test([
            "(x?x --> x!x+1 $ y?y --> skip); x!x+2",
            "x!3; x?x; x?x"
        ], 3, ["IO x 3", "IO x 4", "IO x 5"])

    def testExecParallel9(self):
        self.run_test([
            "x := 0; v := 0; a := 1; <x_dot = v, v_dot = a & true> |> [](c!x --> skip)",
            "wait(3); c?x"
        ], 3, ["delay 3", "IO c 4.5", "deadlock"])

    def testExecParallel10(self):
        self.run_test([
            "x := 0; v := 0; a := 1; <x_dot = v, v_dot = a & x < 3>; c!x",
            "c?x"
        ], 3, ["delay 2.449", "IO c 3.0", "deadlock"])

    def testExecParallel11(self):
        self.run_test([
            "x := 0; v := 0; a := 1; <x_dot = v, v_dot = a & x < 3>; c!x",
            "x := 0; v := 0; a := 1; <x_dot = v, v_dot = a & x < 5>; c!x",
            "c?x; c?x"
        ], 5, ["delay 2.449", "IO c 3.0", "delay 0.713", "IO c 5.0", "deadlock"])

    def testExecParallel12(self):
        self.run_test([
            "x := 0; v := 1; a := -1; (<x_dot = v, v_dot = a & x > 0>; v := -0.8 * v)**",
        ], 3, ["delay 2.0", "delay 1.6", "delay 1.28"])

    def testExecParallel13(self):
        self.run_test([
            "x := 0; rec X.(x := x + 1; wait(1); @X)"
        ], 4, ["delay 1", "delay 1", "delay 1", "delay 1"])

    def testExecParallel14(self):
        self.run_test([
            "x := 0; rec X.(x := x + 1; wait(1); x < 3 -> @X); c!x",
            "c?x"
        ], 5, ["delay 1", "delay 1", "delay 1", "IO c 3", "deadlock"])

    def testExecParallel15(self):
        self.run_test([
            "x := 1; (<x_dot = x & true> |> [](c!x --> skip))**",
            "(wait(10); c?x)**"
        ], 100, ['delay 10', 'IO c 22026.815', 'delay 10', 'IO c 485180544.948', 'delay 10', 'overflow'])

    def testExecParallel16(self):
        self.run_test([
            "EL := []; EL := push(EL, \"a\"); EL := push(EL, \"b\"); EL := pop(EL); x := top(EL); ch!x",
            "ch?x"
        ], 2, ['IO ch "a"', "deadlock"])

    def testExecParallel17(self):
        self.run_test([
            "EL := []; (in?e --> EL := push(EL, e) $ out? --> e := top(EL); outval!e; EL := pop(EL))**",
            "in!\"a\"; in!\"b\"; out!; outval?e; out!; outval?e",
        ], 7, ['IO in "a"', 'IO in "b"', 'IO out', 'IO outval "b"', 'IO out', 'IO outval "a"', 'deadlock'])

    def testExecParallel18(self):
        self.run_test([
            "num := 0; num == 0 -> (E := \"e\"; num := 1); ch!E",
            "ch?E"
        ], 2, ['IO ch "e"', 'deadlock'])

    def testExecParallel9(self):
        self.run_test([
            "num := 0; (ch_a!0 --> skip $ ch_b?x --> skip)**",
            "ch_a?y; ch_b!y"
        ], 3, ['IO ch_a 0', 'IO ch_b 0', 'deadlock'])

    def testExecParallel20(self):
        self.run_test([
            "x := 0; y := 0; (<x_dot = 1, y_dot = 1 & true> |> [](cx!x --> cy!y; x := x - 1, cy!y --> cx!x; y := y - 1))**",
            "wait(1); cx?x; cy?y; wait(1); cy?y; cx?x; wait(1); cx?x; cy?y"
        ], 10, ['delay 1', 'IO cx 1.0', 'IO cy 1.0', 'delay 1', 'IO cy 2.0', 'IO cx 1.0', 'delay 1', 'IO cx 2.0', 'IO cy 2.0', 'deadlock'])

    def testExecParallel21(self):
        self.run_test([
            "x := 0; (if x == 0 then x := 1 elif x == 1 then x := 2 else x := 0 endif; c!x)**",
            "(c?x)**"
        ], 6, ['IO c 1', 'IO c 2', 'IO c 0', 'IO c 1', 'IO c 2', 'IO c 0'])

    def testExecParallel22(self):
        self.run_test([
            "rec X.(ch_a?x; x == 0 -> (@X); ch_b!x)",
            "ch_a!0; ch_a!1; ch_b?y; ch_b?y"
        ], 5, ['IO ch_a 0', 'IO ch_a 1', 'IO ch_b 1', 'IO ch_b 1', 'deadlock'])


if __name__ == "__main__":
    unittest.main()
