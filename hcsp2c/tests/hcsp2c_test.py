import unittest
import subprocess

from ss2hcsp.hcsp import parser
from hcsp2c import transfer2c


class HCSP2CTest(unittest.TestCase):
    def run_file(self, progs, filename, expected_output, *, step_size:float = 1e-7, real_time:bool = False, maxTime:float = 5.0):
        hps = []
        for i, prog in enumerate(progs):
            hps.append(("P" + str(i+1), parser.hp_parser.parse(prog)))
        res = transfer2c.convertHps(hps, step_size=step_size, real_time=real_time, maxTime=maxTime)

        with open('hcsp2c/target/%s.c' % filename, 'w') as f:
            f.write(res)
        res = subprocess.run(
            "sudo gcc hcsp2c/target/%s.c -lpthread -o hcsp2c/output/%s.out" % (filename, filename),
            stderr=subprocess.PIPE,
            text=True,
            shell=True
        )

        # Handle exception resulting from conversion step
        if res.stderr != '':
            err = res.stderr
            raise Exception(err)

        res = subprocess.run(
            "./hcsp2c/output/%s.out" % filename,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            shell=True
        )

        if not expected_output:
            self.assertEqual(res.stdout, "")
        else:
            self.assertEqual(res.stdout, '\n'.join(expected_output) + '\n')


    def testa(self):
        progs = [
            "x := 0; { p2c!x; c2p?x; }*",
            "x := 0; y := 0; { wait(2); p2c?x; y := x - 1; c2p!y; }*"
        ]

        expected_output = [
            "delay 2.000",
            "IO p2c 0.000",
            "IO c2p -1.000",
            "delay 2.000",
            "IO p2c -1.000",
            "IO c2p -2.000"
        ]

        self.run_file(progs, "testa", expected_output)

    def testb(self):
        progs = [
            "x := \"old_str_x\"; { x := \"str_x\"; p2c!x;  c2p?x; }*",
            "x := \"\"; y := \"old_str_y\"; { wait(2); p2c?x; y := \"str_y\"; c2p!y; }*"
        ]

        expected_output = [
            "delay 2.000",
            "IO p2c \"str_x\"",
            "IO c2p \"str_y\"",
            "delay 2.000",
            "IO p2c \"str_x\"",
            "IO c2p \"str_y\""
        ]

        self.run_file(progs, "testb", expected_output)

    def testc(self):
        progs = [
            "x := 0; { p2c!x --> skip; $ c2p?x --> skip; }*",
            "x := 0; y := 0; { wait(2); p2c?x; y := x - 1; c2p!y; }*"
        ]

        expected_output = [
            "delay 2.000",
            "IO p2c 0.000",
            "IO c2p -1.000",
            "delay 2.000",
            "IO p2c -1.000",
            "IO c2p -2.000"
        ]

        self.run_file(progs, "testc", expected_output)

    def testd(self):
        progs = [
            "x := 0; y := 1; { p2c1!x --> skip; $ p2c2!y --> skip; }*",
            "x := 0; y := 0; { wait(2); p2c1?x; p2c2?y; }*"
        ]

        expected_output = [
            "delay 2.000",
            "IO p2c1 0.000",
            "IO p2c2 1.000",
            "delay 2.000",
            "IO p2c1 0.000",
            "IO p2c2 1.000"
        ]

        self.run_file(progs, "testd", expected_output)

    def teste(self):
        progs = [
            "t := 0; x := 1; y := 0; {x_dot = -y, y_dot = x, t_dot = 1 & x > 0} p2c!x; p2c!y; p2c!t;",
            "x := 0; y := 0; t := 0; p2c?x; p2c?y; p2c?t;"
        ]

        expected_output = [
            "delay 1.571",
            "IO p2c -0.000",
            "IO p2c 1.000",
            "IO p2c 1.571",
            "deadlock"
        ]

        self.run_file(progs, "teste", expected_output, step_size=1e-5)

    def testf(self):
        progs = [
            "x := 0; y := 1; z := 2; chx!x; chy!y; chz!z; {chx!x --> x := 1; $ chz!z --> z := 3; $ chy!y --> y := 2;} chx!x; chy!y; chz!z; " ,
            "x := 0; y := 0; z := 0; chx?x; chy?y; chz?z; chz?z; chx?x; chy?y; chz?z;"
        ]

        expected_output = [
            "IO chx 0.000",
            "IO chy 1.000",
            "IO chz 2.000",
            "IO chz 2.000",
            "IO chx 0.000",
            "IO chy 1.000",
            "IO chz 3.000",
            "deadlock"
        ]

        self.run_file(progs, "testf", expected_output, step_size=1e-5)
    
    def testg(self):
        progs = [
            "x := 0; v := 0; a := 1; e!; c!x; d!x; {x_dot = v, v_dot = a & true} |> [](d!x --> skip;, c!x --> skip;)",
            "x := 0; e?; c?x; d?x; wait(3); c?x;"
        ]

        expected_output = [
            "IO e",
            "IO c 0.000",
            "IO d 0.000",
            "delay 3.000",
            "IO c 4.500",
            "deadlock"
        ]

        self.run_file(progs, "testg", expected_output, step_size=1e-5)

    def test1_ori(self):
        progs = [
            "x := 0; { p2c!x; c2p?x; }*",
            "x := 0; { wait(2); p2c?x; c2p!x - 1; }*"
        ]

        expected_output = [
            "delay 2.000",
            "IO p2c 0.000",
            "IO c2p -1.000",
            "delay 2.000",
            "IO p2c -1.000",
            "IO c2p -2.000"
        ]

        self.run_file(progs, "test1_ori", expected_output)

    def test2_ori(self):
        progs = [
            "x := 0; { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x; }*",
            "x := 0; wait(2); p2c?x; c2p!x-1;"
        ]

        expected_output = [
            "delay 2.000",
            "IO p2c 2.000",
            "IO c2p 1.000"
        ]

        self.run_file(progs, "test2_ori", expected_output, step_size=1e-1)

    def test1(self):
        # TODO: support c2p!x-1 rather than y := x-1; c2p!y
        progs = [
            "x := 0; { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x; }*",
            "x := 0; y := 0; { wait(2); p2c?x; y := x-1; c2p!y; }*"
        ]

        expected_output = [
            "delay 2.000",
            "IO p2c 2.000",
            "IO c2p 1.000",
            "delay 2.000",
            "IO p2c 3.000",
            "IO c2p 2.000"
        ]

        self.run_file(progs, "test1", expected_output, step_size=1e-1)

    def test2(self):
        progs = [
            "x := 0; { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x; }*",
            "x := 0; y := 0; wait(2); p2c?x; y := x-1; c2p!y;"
        ]

        expected_output = [
            "delay 2.000",
            "IO p2c 2.000",
            "IO c2p 1.000"
        ]

        self.run_file(progs, "test2", expected_output, step_size=1e-1)

    def test3(self):
        progs = [
            "x := 0; x := x + 1;",
            "y := 2;"
        ]

        expected_output = [
            "deadlock"
        ]

        self.run_file(progs, "test3", expected_output, step_size=1e-1)

    def test4(self):
        progs = [
            "x := 0; { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x; }*",
            "x := 0; { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x; }*"
        ]

        expected_output = [
        ]

        self.run_file(progs, "test4", expected_output, step_size=1e-1)

    def test5(self):
        # TODO: changing channel names from chx, chz, chy to x, z, y reveals a bug.
        progs = [
            "x := 0; y := 0; z := 1; {chx?x --> skip; $ chz!z --> skip; $ chy?y --> skip;}",
            "y := 2; chy!y;"
        ]

        expected_output = [
            "IO chy 2.000",
            "deadlock"
        ]

        self.run_file(progs, "test5", expected_output, step_size=1e-1)

    def test6(self):
        progs = [
            "x := 0; y := 0; z := 1; {chx?x --> skip; $ chz!z --> skip; $ chy?y --> skip;}",
            "z := 0; chz?z;"
        ]

        expected_output = [
            "IO chz 1.000",
            "deadlock"
        ]

        self.run_file(progs, "test6", expected_output, step_size=1e-1)

    def test7(self):
        progs = [
            "x := 1; y := 2; z := 3; wait(3); w := 4;",
            "x := 11; y := 12; wait(2); z := 3;"
        ]

        expected_output = [
            "deadlock"
        ]

        self.run_file(progs, "test7", expected_output, step_size=1e-1)

    def test8(self):
        # TODO: changing chy to chx reveals a bug.
        # We can make an assumption that each direction of communication channel is used
        # by only one process.
        progs = [
            "x := 0; y := 0; {chx?x --> y := x+1; chy!y; $ chy?y --> skip;} y := x+2; chx!y;",
            "x := 0; y := 3; chx!y; chy?x; chx?x;"
        ]

        expected_output = [
            "IO chx 3.000",
            "IO chy 4.000",
            "IO chx 5.000",
            "deadlock"
        ]

        self.run_file(progs, "test8", expected_output, step_size=1e-1)

    def test9(self):
        progs = [
            "x := 0; v := 0; a := 1; {x_dot = v, v_dot = a & true} |> [](c!x --> skip;)",
            "x := 0; wait(3); c?x;"
        ]

        expected_output = [
            "delay 3.000",
            "IO c 4.500",
            "deadlock"
        ]

        self.run_file(progs, "test9", expected_output, step_size=1e-5)

    def test10(self):
        progs = [
            "x := 0; v := 0; a := 1; {x_dot = v, v_dot = a & x < 3} c!x;",
            "x := 0; c?x;"
        ]

        expected_output = [
            "delay 2.449",
            "IO c 3.000",
            "deadlock"
        ]

        self.run_file(progs, "test10", expected_output, step_size=1e-5)

    def test11(self):
        # There are no bugs here, but there are problems like test8.
        progs = [
            "x := 0; v := 0; a := 1; {x_dot = v, v_dot = a & x < 3} c!x;",
            "x := 0; v := 0; a := 1; {x_dot = v, v_dot = a & x < 5} c!x;",
            "x := 0; c?x; c?x;"
        ]

        expected_output = [
            "delay 2.449", 
            "IO c 3.000", 
            "delay 0.713", 
            "IO c 5.000", 
            "deadlock"
        ]

        self.run_file(progs, "test11", expected_output, step_size=1e-5)

    def test12(self):
        # This example cannot be tested without communication.
        # I introduced function recordAndPrintTime(); to deal with it, 
        # but it is not used at present.
        # See "hcsp.h" for the reason.
        progs = [
            "x := 0; v := 1; a := -1; { x := 0; {x_dot = v, v_dot = a & x >= 0} chx!x; v := -0.8 * v; }*",
            "x := 0; {chx?x;}*"
        ]

        expected_output = [
            "delay 2.000", 
            "IO chx -0.000",
            "delay 1.600", 
            "IO chx -0.000",
            "delay 1.280",
            "IO chx -0.000"
        ]

        self.run_file(progs, "test12", expected_output, step_size=1e-5)

    def test15(self):
        # Original output is 22026.814 and 485180534.947,
        # I do not know how big the error is.
        # Maybe we need an error limit.
        progs = [
            "x := 1; { {x_dot = x & true} |> [](c!x --> skip;)}*",
            "x := 0; { wait(10); c?x; }*"
        ]

        expected_output = [
            'delay 10.000', 
            'IO c 22026.686', 
            'delay 10.000', 
            'IO c 485174898.811'
        ]

        self.run_file(progs, "test15", expected_output, step_size=1e-5, maxTime=30.0)

    # TODO: test16 and 17

    def test18(self):
        progs = [
            "num := 0; if (num == 0) { E := \"e\"; num := 1; } ch!E;",
            "E := \"\"; ch?E;"
        ]

        expected_output = [
            'IO ch "e"', 
            'deadlock'
        ]

        self.run_file(progs, "test18", expected_output, step_size=1e-5)

    def test19(self):
        progs = [
            "x := 0; num := 0; {ch_a!x --> skip; $ ch_b?x --> skip;}*",
            "y := 0; ch_a?y; ch_b!y;"
        ]

        expected_output = [
            'IO ch_a 0.000', 
            'IO ch_b 0.000', 
            'deadlock'
        ]

        self.run_file(progs, "test19", expected_output, step_size=1e-5)

    def test20(self):
        progs = [
            "x := 0; y := 0; { {x_dot = 1, y_dot = 1 & true} |> [](cx!x --> cy!y; x := x - 1;, cy!y --> cx!x; y := y - 1;)}*",
            "x := 0; y := 0; wait(1); cx?x; cy?y; wait(1); cy?y; cx?x; wait(1); cx?x; cy?y;"
        ]

        expected_output = [
            'delay 1.000', 
            'IO cx 1.000', 
            'IO cy 1.000', 
            'delay 1.000', 
            'IO cy 2.000', 
            'IO cx 1.000', 
            'delay 1.000', 
            'IO cx 2.000', 
            'IO cy 2.000'
        ]

        self.run_file(progs, "test20", expected_output, step_size=1e-5, maxTime=10)

    def test21(self):
        progs = [
            "x := 0; {if (x == 0) { x := 1; } else if (x == 1) { x := 2; } else { x := 0; } c!x; }*",
            "x := 0; {wait(1);  c?x; }*"
        ]

        expected_output = [
            'delay 1.000',
            'IO c 1.000', 
            'delay 1.000',
            'IO c 2.000', 
            'delay 1.000',
            'IO c 0.000', 
            'delay 1.000',
            'IO c 1.000', 
            'delay 1.000',
            'IO c 2.000', 
            'delay 1.000',
            'IO c 0.000'
        ]

        self.run_file(progs, "test21", expected_output, step_size=1e-5, maxTime=6)

    def test24(self):
        progs = [
            'x := 0; {x_dot = 1 & x < 1} |> [](c!x --> skip;) {x_dot = 1 & x < 1} |> [](c!x --> skip;) c!x;',
            'x := 0; wait(0.2); c?x; wait(1.3); c?x;'
        ]

        expected_output = [
            'delay 0.200', 
            'IO c 0.200', 
            'delay 1.300', 
            'IO c 1.000', 
            'deadlock'
        ]

        self.run_file(progs, "test24", expected_output, step_size=1e-5)

    def test25(self):
        progs = [
            'x := 0; { {x_dot = 1 & x < 1} |> [](c!x --> skip;)}*(x < 1) c!x;',
            'x := 0; wait(0.2); c?x; wait(1.3); c?x;'
        ]

        expected_output = [
            'delay 0.200', 
            'IO c 0.200', 
            'delay 1.300', 
            'IO c 1.000', 
            'deadlock'
        ]

        self.run_file(progs, "test25", expected_output, step_size=1e-5)

    def test26(self):
        progs = [
            'x := 0; y := 0; {x_dot = 1, y_dot = 2 & x < 2 && y < 3} c!x; c!y;',
            'x := 0; c?x; c?x;'
        ]

        expected_output = [
            'delay 1.500', 
            'IO c 1.500', 
            'IO c 3.000', 
            'deadlock'
        ]

        self.run_file(progs, "test26", expected_output, step_size=1e-5)

    # TODO: test27~29
    # test30~35 is meaningless

if __name__ == "__main__":
    unittest.main()
