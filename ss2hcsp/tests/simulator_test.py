"""Unittest for simulation of HCSP."""

import unittest
import math
import pprint

from ss2hcsp.hcsp.hcsp import Channel, Procedure, Function, Skip
from ss2hcsp.hcsp import simulator
from ss2hcsp.hcsp import parser


def run_test(self, infos, num_events, trace, *, io_filter=None,
             print_state=False, print_res=False, warning=None):
    """Test function for HCSP processes.

    infos : List[str, Tuple[Dict[str, HCSP], str] -
        Input HCSP processes. Each process can either be a single HCSP program,
        or a list of procedure specifications followed by the HCSP program.
        Each procedure is specified by a pair of name and HCSP program.

    num_events : int - number of communication or waiting events to simulate.
    trace : List[str] - expected output trace.
    io_filter : str -> bool - which IO events to remain in the trace.
    print_time_series : bool - whether to show time series.
    print_state : bool - whether to show final state.
    warning : [None, str] - if not None, execution must raise a warning whose
        text equals the given string.

    """
    # Process the input HCSP processes, converting them into SimInfo objects
    sim_infos = []
    if isinstance(infos, list):
        for i in range(len(infos)):
            if isinstance(infos[i], str):
                # Single HCSP program
                sim_infos.append(simulator.SimInfo('P' + str(i), infos[i]))
            else:
                # HCSP program with procedure and function specifications
                hp = None
                procedures = dict()
                functions = dict()
                for spec in infos[i]:
                    if isinstance(spec, str):
                        hp = spec
                    elif isinstance(spec, Procedure):
                        procedures[spec.name] = spec
                    elif isinstance(spec, Function):
                        functions[spec.name] = spec
                    else:
                        raise AssertionError("run_test: unknown info")
                sim_infos.append(simulator.SimInfo('P' + str(i), hp, procedures=procedures,
                                 functions=functions))

    elif isinstance(infos, dict):
        procedures = dict()
        for name, (procs, hp) in infos.items():
            
            for proc_name, proc_hp in procs.items():
                procedures[proc_name] = Procedure(proc_name, proc_hp)
        for name, (procs, hp) in infos.items():
            
            # for proc_name, proc_hp in procs.items():
            #     procedures[proc_name] = Procedure(proc_name, proc_hp)
            sim_infos.append(simulator.SimInfo(name, hp, procedures=procedures))
    else:
        raise TypeError

    # Perform the simulation
    res = simulator.exec_parallel(sim_infos, num_io_events=num_events)

    if io_filter is None:
        io_filter = lambda s: True

    # Extract and compare trace of events
    res_trace = [event['str'] for event in res['trace']
                 if event['str'] not in ('start', 'step') and
                    (event['type'] != 'comm' or io_filter(event['ch_name']))]

    if print_res:
        print(res_trace)

    self.assertEqual(res_trace, trace)

    # Optional: print state
    if print_state:
        for info in infos:
            print(info.state)

    # If warning string is set, expect a warning to be raised
    if warning is not None:
        self.assertTrue('warning' in res)
        self.assertEqual(res['warning'], warning)


class SimulatorTest(unittest.TestCase):
    def testEvalExpr(self):
        test_data = [
            ("x + 2", {"x": 1}, 3),
            ("t % 3", {"t": 7}, 1),
        ]

        for expr, state, res in test_data:
            expr = parser.expr_parser.parse(expr)
            info = simulator.SimInfo("P1", Skip(), state=state)
            self.assertEqual(info.eval_expr(expr), res)

    def testEvalExpr(self):
        test_data = [
            ("x >= y", {"x": 3, "y": 2}, True),
            ("x >= y", {"x": 2, "y": 3}, False),
            ("x > y || x < y", {"x": 2, "y": 2}, False),
            ("x == 2 -> y == 3", {"x": 2, "y": 3}, True),
            ("x == 2 -> y == 3", {"x": 2, "y": 4}, False),
            ("x == 2 -> y == 3", {"x": 3, "y": 4}, True),
        ]

        for expr, state, res in test_data:
            expr = parser.expr_parser.parse(expr)
            info = simulator.SimInfo("P1", Skip(), state=state)
            self.assertEqual(info.eval_expr(expr), res)

    def testExecStep(self):
        test_data = [
            ("skip;", (), {}, None, {}),
            ("x := 2;", (), {}, None, {"x": 2}),
            ("x := x + 1;", (), {"x": 2}, None, {"x": 3}),
            ("x := 2; x := x + 1;", (0,), {}, (1,), {"x": 2}),
            ("skip; x := x + 1;", (0,), {"x": 2}, (1,), {"x": 2}),
            ("{ x := x + 1; }*", (0,), {"x": 2}, (0,), {"x": 3}),
            ("{ x := 2; x := x + 1; }*", (0, 0), {"x": 1}, (0, 1), {"x": 2}),
            ("{ x := 2; x := x + 1; }*", (0, 1), {"x": 2}, (0, 0), {"x": 3}),
            ("{ {x_dot = 1 & true} |> [] (p2c!x --> skip;) c2p?x; }*", (0, 0, 0), {}, (0, 1), {}),
            ("if (x == 0) { x := 2; } x := 3;", (0,), {"x": 0}, (0, 0), {"x": 0}),
            ("if (x == 0) { x := 2; } x := 3;", (0,), {"x": 1}, (1,), {"x": 1}),
            ("if (x == 0) { x := 2; }", (), {"x": 0}, (0,), {"x": 0}),
            ("if (x == 0) { x := 2; }", (), {"x": 1}, None, {"x": 1}),
            ("if (x == 0) { x := 1; } else { x := 0; }", (), {"x": 0}, (0,), {"x": 0}),
            ("if (x == 0) { x := 1; } else { x := 0; }", (), {"x": 1}, (1,), {"x": 1}),
            ("if (x == 0) { x := 1; } else { x := 0; }", (0,), {"x": 0}, None, {"x": 1}),
            ("if (x == 0) { x := 1; } else { x := 0; }", (1,), {"x": 1}, None, {"x": 0}),
            ("if (x == 0) { x := 1; skip; } else { skip; }", (0, 0), {"x": 0}, (0, 1), {"x": 1}),
        ]

        for cmd, pos, state, pos2, state2 in test_data:
            info = simulator.SimInfo('P0', cmd, pos=pos, state=state)
            info.exec_step([])
            self.assertEqual(info.reason, None)
            self.assertEqual(info.callstack.top_pos(), pos2)
            self.assertEqual(info.state, state2)

    def testExecStep2(self):
        test_data = [
            ("c?x;", (), {}, {"comm": [(Channel("c"), "?")]}),
            ("c!x;", (), {}, {"comm": [(Channel("c"), "!")]}),
            ("wait(3);", (0,), {}, {"delay": 3}),
            ("wait(3);", (1,), {}, {"delay": 2}),
            ("{x_dot = 1 & true} |> [](c1?x --> skip;, c2!y --> skip;)", (), {},
             {"comm": [(Channel("c1"), "?"), (Channel("c2"), "!")]}),
            ("x := 1; wait(3);", (1, 0), {}, {"delay": 3}),
            ("{x := 1; wait(3);}*", (0, 1, 0), {}, {"delay": 3}),
            ("{x := 1; wait(3);}*", (0, 1, 1), {}, {"delay": 2}),
            ("{x_dot = 1 & x < 1} |> [](c1?x --> skip;, c2!y --> skip;)", (), {"x": 0},
             {"comm": [(Channel("c1"), "?"), (Channel("c2"), "!")], "delay": 1.0}),
            ("{x_dot = 1 & x < 1} |> [](c1?x --> skip;, c2!y --> skip;)", (), {"x": 0.5},
             {"comm": [(Channel("c1"), "?"), (Channel("c2"), "!")], "delay": 0.5}),
        ]

        for cmd, pos, state, reason in test_data:
            info = simulator.SimInfo('P0', cmd, pos=pos, state=state)
            info.exec_step([])
            self.assertEqual(info.reason, reason)
            self.assertEqual(info.callstack.top_pos(), pos)
            self.assertEqual(info.state, state)

    def testExecProcess(self):
        test_data = [
            ("skip;", (), {}, None, {}, "end"),
            ("x := 2;", (), {}, None, {"x": 2}, "end"),
            ("x := 2; x := x + 1;", (0,), {}, None, {"x": 3}, "end"),
            ("x := x + 1; c!x;", (0,), {"x": 2}, (1,), {"x": 3}, {"comm": [(Channel("c"), "!")]}),
            ("wait(3);", (0,), {}, (0,), {}, {"delay": 3}),
            ("{ x := x + 1; wait(3); }*", (0, 0), {"x": 2}, (0, 1, 0), {"x": 3}, {"delay": 3}),
            ("if (x > 0) { x := 1; } if (x < 0) { x := -1; }", (0,), {"x": 0}, None, {"x": 0}, "end"),
            ("if (x > 0) { x := 1; } if (x < 0) { x := -1; }", (0,), {"x": 2}, None, {"x": 1}, "end"),
            ("if (x > 0) { x := 1; } if (x < 0) { x := -1; }", (0,), {"x": -2}, None, {"x": -1}, "end"),
        ]

        for cmd, pos, state, pos2, state2, reason in test_data:
            info = simulator.SimInfo('P0', cmd, pos=pos, state=state)
            while info.callstack.top_pos() is not None:
                info.exec_step([])
                if info.reason is not None:
                    break
            if info.callstack.top_pos() is None:
                info.reason = "end"
            self.assertEqual(info.reason, reason)
            self.assertEqual(info.callstack.top_pos(), pos2)
            self.assertEqual(info.state, state2)

    def testExecInputComm(self):
        test_data = [
            ("c?x;", (), {}, "c", 2, None, {"x": 2}),
            ("c?x; x := x + 1;", (0,), {}, "c", 2, (1,), {"x": 2}),
            ("c?x; x := x + 1; y := 2;", (0,), {}, "c", 2, (1,), {"x": 2}),
            ("{x_dot = 1 & true} |> [](c?x --> x := x + 1;)", (), {}, "c", 2, (0,), {"x": 2}),
            ("{x_dot = 1 & true} |> [](c?x --> skip;) x := x + 2;", (0,), {}, "c", 2, (0, 0), {"x": 2})
        ]

        for cmd, pos, state, ch_name, val, pos2, state2 in test_data:
            info = simulator.SimInfo('P0', cmd, pos=pos, state=state)
            info.exec_input_comm(Channel(ch_name), val)
            self.assertEqual(info.callstack.top_pos(), pos2)
            self.assertEqual(info.state, state2)

    def testExecOutputComm(self):
        test_data = [
            ("c!x;", (), {"x": 2}, "c", None, 2, {"x": 2}),
            ("c!x+1;", (), {"x": 2}, "c", None, 3, {"x": 2}),
            ("c!x+y; x := 3;", (0,), {"x": 2, "y": 3}, "c", (1,), 5, {"x": 2, "y": 3}),
            ("c!x*y; x := 3; y := 0;", (0,), {"x": 2, "y": 3}, "c", (1,), 6, {"x": 2, "y": 3}),
            ("{x_dot = 1 & true} |> [](c!x --> skip;)", (), {"x": 2}, "c", (0,), 2, {"x": 2}),
            ("{x_dot = 1 & true} |> [](c!x+1 --> skip;) x := x + 1;", (0,), {"x": 2}, "c", (0, 0), 3, {"x": 2}),
        ]

        for cmd, pos, state, ch_name, pos2, val, state2 in test_data:
            info = simulator.SimInfo('P0', cmd, pos=pos, state=state)
            res = info.exec_output_comm(Channel(ch_name))
            self.assertEqual(res, val)
            self.assertEqual(info.callstack.top_pos(), pos2)
            self.assertEqual(info.state, state2)

    def testExecDelay(self):
        test_data = [
            ("wait(3);", (0,), {}, 3, None, {}),
            ("wait(3);", (0,), {}, 2, (2,), {}),
            ("wait(3);", (1,), {}, 1, (2,), {}),
            ("wait(3);", (1,), {}, 2, None, {}),
            ("wait(3); x := x + 1;", (0, 0), {"x": 2}, 3, (1,), {"x": 2}),
            ("wait(3); x := x + 1;", (0, 0), {"x": 2}, 2, (0, 2), {"x": 2}),
            ("wait(3); x := x + 1;", (0, 1), {"x": 2}, 2, (1,), {"x": 2}),
            ("{x_dot = 1 & true} |> [](c!x --> skip;)", (), {"x": 2}, 3, (), {"x": 5}),
            ("{x_dot = 1 & true} |> [](c!x --> skip;) x := x + 1;", (0,), {"x": 2}, 3, (0,), {"x": 5}),
        ]

        for cmd, pos, state, delay, pos2, state2 in test_data:
            info = simulator.SimInfo('P0', cmd, pos=pos, state=state)
            info.exec_step([])  # obtain delay value
            info.exec_delay(delay)
            self.assertEqual(info.callstack.top_pos(), pos2)
            self.assertEqual(info.state, state2)

    def assertAlmostEqualState(self, st1, st2):
        self.assertEqual(set(st1.keys()), set(st2.keys()))
        for k in st1:
            self.assertAlmostEqual(st1[k], st2[k], places=3)

    def testODEComm(self):
        test_data = [
            # Acceleration
            ("{x_dot = v, v_dot = a & true} |> [](c!x --> skip;)",
             {"a": 1, "v": 0, "x": 0}, 3, {"a": 1, "v": 3, "x": 4.5}),

            # Acceleration with floating point numbers
            ("{x_dot = v, v_dot = a & true} |> [](c!x --> skip;)",
             {"a": 1.1, "v": 0, "x": 0}, 3, {"a": 1.1, "v": 3.3, "x": 4.95}),

            # Exponential growth
            ("{x_dot = x & true} |> [](c!x --> skip;)", {"x": 1}, 3, {"x": math.exp(3)}),

            # Circular motion
            ("{x_dot = -1 * y, y_dot = x & true} |> [](c!x --> skip;)",
             {"x": 1, "y": 0}, 3, {"x": math.cos(3), "y": math.sin(3)}),
        ]

        for cmd, state, delay, state2 in test_data:
            info = simulator.SimInfo('P0', cmd, state=state)
            info.exec_step([])  # obtain delay value
            info.exec_delay(delay)
            self.assertAlmostEqualState(info.state, state2)

    def testODEDelay(self):
        test_data = [
            # Acceleration
            ("{x_dot = v, v_dot = a, t_dot = 1 & t < 3}", {"t": 0, "a": 1, "v": 0, "x": 0}, 3.0),

            # Acceleration, upon x reaching a certain value
            ("{x_dot = v, v_dot = a, t_dot = 1 & x < 3}",
             {"t": 0, "a": 1, "v": 0, "x": 0}, math.sqrt(6)),

            # Exponential growth
            ("{x_dot = x, t_dot = 1 & x < 3}", {"t": 0, "x": 1}, math.log(3)),

            # Circular motion
            ("{x_dot = -1 * y, y_dot = x & x > 0}", {"x": 1, "y": 0}, math.pi/2),

            # Some examples of large or infinite delay
            ("{t_dot = 0.1 & t < 6}", {"t": 0}, 60),
            ("{t_dot = 0.01 & t < 60}", {"t": 0}, 100),  # maximum is 100
            ("{x_dot = -1 * y, y_dot = x & x > -2}", {"x": 1, "y": 0}, 100),

            # Conjunction
            ("{x_dot = 1, y_dot = 1 & x < 3 && y < 2}", {"x": 0, "y": 0}, 2.0),
            ("{x_dot = 1, y_dot = -1 & x < 3 && y >= 0}", {"x": 0, "y": 1}, 1.0),
        ]

        for cmd, state, delay in test_data:
            hp = parser.hp_parser.parse(cmd)
            info = simulator.SimInfo("P1", Skip(), state=state)
            res = info.get_ode_delay(hp)
            self.assertAlmostEqual(res, delay, places=5)

    def testExecParallel1(self):
        run_test(self, [
            "x := 0; { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x; }*",
            "{ wait(2); p2c?x; c2p!x-1; }*",
        ], 6, ["delay 2", "IO p2c 2.0", "IO c2p 1.0", "delay 2", "IO p2c 3.0", "IO c2p 2.0"])

    def testExecParallel2(self):
        run_test(self, [
            "x := 0; { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x; }*",
            "wait(2); p2c?x; c2p!x-1;",
        ], 6, ["delay 2", "IO p2c 2.0", "IO c2p 1.0", "deadlock"])

    def testExecParallel3(self):
        run_test(self, [
            "x := 0; x := x + 1;",
            "y := 2;",
        ], 6, ['deadlock'])

    def testExecParallel4(self):
        run_test(self, [
            "x := 0; { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x; }*",
            "x := 0; { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x; }*",
        ], 6, ['deadlock'])

    def testExecParallel5(self):
        run_test(self, [
            "z := 1; {x?x --> skip; $ z!z --> skip; $ y?y --> skip;}",
            "y := 2; y!y;",
        ], 3, ["IO y 2", "deadlock"])

    def testExecParallel6(self):
        run_test(self, [
            "z := 1; {x?x --> skip; $ z!z --> skip; $ y?y --> skip;}",
            "z?z;",
        ], 3, ["IO z 1", "deadlock"])

    def testExecParallel7(self):
        run_test(self, [
            "x := 1; y := 2; z := 3; wait(3); w := 4;",
            "x := 11; y := 12; wait(2); z := 3;"
        ], 6, ["delay 2", "delay 1", "deadlock"])

    def testExecParallel8(self):
        run_test(self, [
            "{x?x --> x!x+1; $ y?y --> skip;} x!x+2;",
            "x!3; x?x; x?x;"
        ], 3, ["IO x 3", "IO x 4", "IO x 5"])

    def testExecParallel9(self):
        run_test(self, [
            "x := 0; v := 0; a := 1; {x_dot = v, v_dot = a & true} |> [](c!x --> skip;)",
            "wait(3); c?x;"
        ], 3, ["delay 3", "IO c 4.5", "deadlock"])

    def testExecParallel10(self):
        run_test(self, [
            "x := 0; v := 0; a := 1; {x_dot = v, v_dot = a & x < 3} c!x;",
            "c?x;"
        ], 3, ["delay 2.449", "IO c 3.0", "deadlock"])

    def testExecParallel11(self):
        run_test(self, [
            "x := 0; v := 0; a := 1; {x_dot = v, v_dot = a & x < 3} c!x;",
            "x := 0; v := 0; a := 1; {x_dot = v, v_dot = a & x < 5} c!x;",
            "c?x; c?x;"
        ], 5, ["delay 2.449", "IO c 3.0", "delay 0.713", "IO c 5.0", "deadlock"])

    def testExecParallel12(self):
        run_test(self, [
            "x := 0; v := 1; a := -1; { {x_dot = v, v_dot = a & x >= 0} v := -0.8 * v; }*",
        ], 3, ["delay 2.0", "delay 1.6", "delay 1.28"])

    def testExecParallel15(self):
        run_test(self, [
            "x := 1; { {x_dot = x & true} |> [](c!x --> skip;)}*",
            "{ wait(10); c?x; }*"
        ], 100, ['delay 10', 'IO c 22026.814', 'delay 10', 'IO c 485180534.947', 'delay 10', 'overflow'])

    def testExecParallel16(self):
        run_test(self, [
            "EL := []; EL := push(EL, \"a\"); EL := push(EL, \"b\"); EL := pop(EL); x := top(EL); ch!x;",
            "ch?x;"
        ], 2, ['IO ch "a"', "deadlock"])

    def testExecParallel17(self):
        run_test(self, [
            "EL := []; { in?e --> EL := push(EL, e); $ out? --> e := top(EL); outval!e; EL := pop(EL); }*",
            "in!\"a\"; in!\"b\"; out!; outval?e; out!; outval?e;",
        ], 7, ['IO in "a"', 'IO in "b"', 'IO out', 'IO outval "b"', 'IO out', 'IO outval "a"', 'deadlock'])

    def testExecParallel18(self):
        run_test(self, [
            "num := 0; if (num == 0) { E := \"e\"; num := 1; } ch!E;",
            "ch?E;"
        ], 2, ['IO ch "e"', 'deadlock'])

    def testExecParallel9(self):
        run_test(self, [
            "num := 0; {ch_a!0 --> skip; $ ch_b?x --> skip;}*",
            "ch_a?y; ch_b!y;"
        ], 3, ['IO ch_a 0', 'IO ch_b 0', 'deadlock'])

    def testExecParallel20(self):
        run_test(self, [
            "x := 0; y := 0; { {x_dot = 1, y_dot = 1 & true} |> [](cx!x --> cy!y; x := x - 1;, cy!y --> cx!x; y := y - 1;)}*",
            "wait(1); cx?x; cy?y; wait(1); cy?y; cx?x; wait(1); cx?x; cy?y;"
        ], 10, ['delay 1', 'IO cx 1.0', 'IO cy 1.0', 'delay 1', 'IO cy 2.0', 'IO cx 1.0', 'delay 1', 'IO cx 2.0', 'IO cy 2.0', 'deadlock'])

    def testExecParallel21(self):
        run_test(self, [
            "x := 0; {if (x == 0) { x := 1; } else if (x == 1) { x := 2; } else { x := 0; } c!x; }*",
            "{ c?x; }*"
        ], 6, ['IO c 1', 'IO c 2', 'IO c 0', 'IO c 1', 'IO c 2', 'IO c 0'])

    def testExecParallel24(self):
        run_test(self, [
            'x := 0; {x_dot = 1 & x < 1} |> [](c!x --> skip;) {x_dot = 1 & x < 1} |> [](c!x --> skip;) c!x;',
            'wait(0.2); c?x; wait(1.3); c?x;'
        ], 10, ['delay 0.2', 'IO c 0.2', 'delay 0.8', 'delay 0.5', 'IO c 1.0', 'deadlock'])

    def testExecParallel25(self):
        run_test(self, [
            'x := 0; { {x_dot = 1 & x < 1} |> [](c!x --> skip;)}*(x < 1) c!x;',
            'wait(0.2); c?x; wait(1.3); c?x;'
        ], 10, ['delay 0.2', 'IO c 0.2', 'delay 0.8', 'delay 0.5', 'IO c 1.0', 'deadlock'])

    def testExecParallel26(self):
        run_test(self, [
            'x := 0; y := 0; {x_dot = 1, y_dot = 2 & x < 2 && y < 3} c!x; c!y;',
            'c?x; c?x;'
        ], 4, ['delay 1.5', 'IO c 1.5', 'IO c 3.0', 'deadlock'])

    def testExecParallel27(self):
        run_test(self, [
            'xs := []; {ch_new?new; xs := push(xs, new); x := get_max(xs); ch_max!x; xs := pop_max(xs);}*',
            'ch_new![1,2]; ch_max?x; ch_new!3; ch_max?x; ch_new![]; ch_max?x;'
        ], 10, ['IO ch_new [1,2]', 'IO ch_max 2', 'IO ch_new 3', 'IO ch_max 3', 'IO ch_new []', 'IO ch_max 1', 'deadlock'])

    def testExecParallel28(self):
        run_test(self, [
            'b := 10; xs := [b, 1]; a := xs[0]; ch!a; b := xs[1]; ch!b;',
            'ch?a; ch?b;'
        ], 3, ['IO ch 10', 'IO ch 1', 'deadlock'])

    def testExecParallel29(self):
        """Test multiple assignment."""
        run_test(self, [
            'b := 10; xs := [b, 1]; (a, b) := xs; ch!a; ch!b;',
            'ch?a; ch?b;'
        ], 3, ['IO ch 10', 'IO ch 1', 'deadlock'])

    def testExecParallel30(self):
        run_test(self, [
            'x := 0; {x_dot = 0 * x & x <= 0}'
        ], 3, ['delay 100', 'deadlock'])

    def testExecParallel31(self):
        run_test(self, [
            'x := 0; {x_dot = 0 * x & x < 0}'
        ], 3, ['delay 0.0', 'deadlock'])

    def testExecParallel32(self):
        run_test(self, [
            'x := 0; v := 0; {x_dot = v, v_dot = 0 & x <= 0}'
        ], 3, ['delay 100', 'deadlock'])

    def testExecParallel33(self):
        run_test(self, [
            'x := 2; assert(x == 2);'
        ], 2, ['deadlock'])

    def testExecParallel34(self):
        run_test(self, [
            'x := 2; test(x == 3, "x should equal 3");'
        ], 3, ['warning: Test x == 3 failed (x should equal 3)', 'deadlock'],
        warning=(0, "Test x == 3 failed (x should equal 3)"))

    def testExecParallel35(self):
        run_test(self, [
            'x := 2; log("start");'
        ], 1, ['log start', 'deadlock'])

    def testExecParallel36(self):
        run_test(self, [
            'x := 0; { {x_dot = 1 & true} |> [](p2c[0]!x --> skip;) c2p[0]?x;}*',
            '{wait(2); p2c[0]?x; c2p[0]!x-1;}*'
        ], 6, ['delay 2', 'IO p2c[0] 2.0', 'IO c2p[0] 1.0', 'delay 2', 'IO p2c[0] 3.0', 'IO c2p[0] 2.0'])

    def testExecParallel37(self):
        run_test(self, [
            'x := 0; i := 0; {i := i + 1; {x_dot = 1 & true} |> [](p2c[i]!x --> skip;) c2p[i]?x;}*',
            'i := 0; {i := i + 1; wait(2); p2c[i]?x; c2p[i]!x-1;}*'
        ], 6, ['delay 2', 'IO p2c[1] 2.0', 'IO c2p[1] 1.0', 'delay 2', 'IO p2c[2] 3.0', 'IO c2p[2] 2.0'])

    def testExecParallel38(self):
        run_test(self, [
            'pt := {x:1, y:2}; pt.x := pt.y + 1; ch!pt.x; ch!pt;',
            'ch?x; ch?x;'
        ], 3, ['IO ch 3', 'IO ch {x:3,y:2}', 'deadlock'])

    def testExecParallel39(self):
        run_test(self, [
            'pt := [1, 2]; pt[0] := pt[1] + 1; ch!pt[0]; ch!pt;',
            'ch?x; ch?x;'
        ], 3, ['IO ch 3', 'IO ch [3,2]', 'deadlock'])

    def testExecParallel40(self):
        run_test(self, [
            'pt := {x:1, y:2}; pt2 := pt; pt2.y := 3; ch!pt2.y; ch!pt.y;',
            'ch?x; ch?x;'
        ], 3, ['IO ch 3', 'IO ch 2', 'deadlock'])

    def testExecParallel41(self):
        run_test(self, [
            'pt := {x:1, y:2}; ch!pt; ch!pt.y;',
            'ch?pt; pt.y := 3; ch?y;'
        ], 3, ['IO ch {x:1,y:2}', 'IO ch 2', 'deadlock'])

    def testExecParallel42(self):
        run_test(self, [
            'pt := {x:1, y:2}; ch!pt.x; ch!pt.y; ch?z; ch?z;',
            'pt := {x:2, y:3}; ch?pt.x; ch?pt.y; ch!pt.x; ch!pt.y;'
        ], 5, ['IO ch 1', 'IO ch 2', 'IO ch 1', 'IO ch 2', 'deadlock'])

    def testExecParallel43(self):
        run_test(self, [
            "x := 0; {test(x <= 2, \"x is too big\"); {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x;}*",
            "{wait(2); p2c?x; c2p!x-1;}*",
        ], 12, ["delay 2", "IO p2c 2.0", "IO c2p 1.0", "delay 2", "IO p2c 3.0", "IO c2p 2.0",
                "delay 2", "IO p2c 4.0", "IO c2p 3.0", "warning: Test x <= 2 failed (x is too big)", "delay 2", "IO p2c 5.0", "IO c2p 4.0"],
        warning=(6, "Test x <= 2 failed (x is too big)"))

    def testExecParallel44(self):
        run_test(self, [
            "status := [1]; status[0] := {x:1, y:2}; ch!status[0].x; ch!status[0].y;",
            "ch?z; ch?x;"
        ], 3, ['IO ch 1', 'IO ch 2', 'deadlock'])

    def testExecParallel45(self):
        run_test(self, [
            "a := [[1,2],[3,4]]; ch!a[1][0]; ch!a[0][1];",
            "ch?x; ch?x;"
        ], 3, ['IO ch 3', 'IO ch 2', 'deadlock'])

    def testExecParallel46(self):
        run_test(self, [
            "pt := {xs: [1, 2], ys: [3, 4]}; ch!pt.xs[1]; ch!pt.ys[0];",
            "ch?x; ch?x;"
        ], 3, ['IO ch 2', 'IO ch 3', 'deadlock'])

    def testExecParallel47(self):
        run_test(self, [
            "x := 0; {assert(x <= 2, \"x is too big\"); {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x;}*",
            "{wait(2); p2c?x; c2p!x-1;}*",
        ], 12, ["delay 2", "IO p2c 2.0", "IO c2p 1.0", "delay 2", "IO p2c 3.0", "IO c2p 2.0",
                "delay 2", "IO p2c 4.0", "IO c2p 3.0", "error: x is too big"],
        warning=(6, "x is too big"))

    def testExecParallel48(self):
        run_test(self, [
            "{x := 0; {x_dot = 1 & true} |> [](ch[_thread]? --> out!_thread;)}*",
            "ch[0]!; out?x; ch[1]!; out?x;"
        ], 4, ['IO ch[0]', 'IO out 0', 'IO ch[1]', 'IO out 1'])

    def testExecParallel49(self):
        run_test(self, [
            "a := [[0,1],[2,3]]; b := [0,1,2]; a[0][1] := 4; a[1][0] := 5; b[1] := a[1][1]; ch!a; ch!b;",
            "ch?x; ch?y;"
        ], 3, ['IO ch [[0,4],[5,3]]', 'IO ch [0,3,2]', 'deadlock'])

    def testProcedure1(self):
        run_test(self, [
            (Procedure("incr", "x := x + 1;"),
             "x := 0; @incr; @incr; ch!x;"),
            "ch?x;"
        ], 2, ['IO ch 2', 'deadlock'])

    def testProcedure2(self):
        run_test(self, [
            (Procedure("fact", "if (a > 0) { x := a * x; a := a - 1; @fact; } else { skip; }"),
             "x := 1; a := 5; @fact; ch!x;"),
            "ch?x;"
        ], 2, ['IO ch 120', 'deadlock'])

    def testProcedure3(self):
        run_test(self, [
            (Procedure("output", "if (a > 0) { a := a - 1; ch!a; @output; } else { skip; }"),
             "a := 5; @output;"),
            "{ch?x;}*"
        ], 10, ['IO ch 4', 'IO ch 3', 'IO ch 2', 'IO ch 1', 'IO ch 0', 'deadlock'])

    def testProcedure4(self):
        run_test(self, [
            (Procedure("delay", "if (a > 0) { a := a - 1; wait(2); @delay; } else { skip; }"),
             "a := 5; @delay;")
        ], 10, ['delay 2', 'delay 2', 'delay 2', 'delay 2', 'delay 2', 'deadlock'])

    def testProcedure5(self):
        run_test(self, [
            (Procedure("pa", "if (x > 0) { x := x - 1; cha!x; @pb; } else { skip; }"),
             Procedure("pb", "if (x > 0) { x := x - 1; chb!x; @pa; } else { skip; }"),
             "x := 5; @pa;"),
            "{cha?x --> { skip; } $ chb?x --> { skip; }}*"
        ], 10, ['IO cha 4', 'IO chb 3', 'IO cha 2', 'IO chb 1', 'IO cha 0', 'deadlock'])

    def testFunctions1(self):
        run_test(self, [
            (Function("bar", ["a", "b"], "2 * a + 3 * b"),
             "x := 2; y := 3; ch!bar(x, y);"),
            "ch?x;"
        ], 10, ['IO ch 13', 'deadlock'])
    
    def testFunctions2(self):
        run_test(self, [
            (Function("bar", ["a", "b"], "2 * a == b"),
             "x := 2; y := 1; if (bar(y, x)) { ch!x; } else { ch!y; }"),
            "ch?x;"
        ], 10, ['IO ch 2', 'deadlock'])

    def run_test_trace(self, infos, *, num_steps, num_show, ids=None,
                       show_interval=None, start_event=None, print_trace=False):
        for i in range(len(infos)):
            infos[i] = simulator.SimInfo('P' + str(i), infos[i])

        res = simulator.exec_parallel(
            infos, num_steps=num_steps, num_show=num_show,
            show_interval=show_interval, start_event=start_event)
        if print_trace:
            pprint.pprint(res['trace'])
        if ids:
            self.assertEqual(ids, [event['id'] for event in res['trace']])

    def testTrace1(self):
        self.run_test_trace([
            "x := 0; { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x;}*",
            "{wait(2); p2c?x; c2p!x-1;}*",
        ], num_steps=10, num_show=5, ids=[0,1,2,3,4,5])

    def testTrace2(self):
        self.run_test_trace([
            "x := 0; { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x;}*",
            "{wait(2); p2c?x; c2p!x-1;}*",
        ], num_steps=10, num_show=5, show_interval=2, ids=[0,2,4,6,8,10])

    def testTrace3(self):
        self.run_test_trace([
            "x := 0; { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x;}*",
            "{wait(2); p2c?x; c2p!x-1;}*",
        ], num_steps=10, num_show=3,
        start_event = {
            'id': 4,
            'infos': {'P0': {'pos': 'p1,0,1', 'state': {'x': 2.0}},
                      'P1': {'pos': 'p0,2', 'state': {'x': 2.0}}},
            'time': 2},
        ids=[5,6,7,8])


if __name__ == "__main__":
    unittest.main()
