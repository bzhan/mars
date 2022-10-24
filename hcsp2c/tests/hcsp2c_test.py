import unittest
import subprocess

from ss2hcsp.hcsp import parser
from hcsp2c import transfer2c


class HCSP2CTest(unittest.TestCase):
    def run_file(self, progs, filename, expected_output, *, step_size: float = 1e-7):
        hps = []
        for i, prog in enumerate(progs):
            hps.append(("P" + str(i+1), parser.hp_parser.parse(prog)))
        res = transfer2c.convertHps(hps, step_size=step_size)

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

        self.assertEqual(res.stdout, '\n'.join(expected_output) + '\n')


    def testa(self):
        progs = [
            "x := 0; { p2c!x; c2p?x; }*",
            "x := 0; y := 0; { wait(2); p2c?x; y := x - 1; c2p!y; }*"
        ]

        expected_output = [
            "IO p2c 0.000",
            "IO c2p -1.000",
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
            "IO p2c str_x",
            "IO c2p str_y",
            "IO p2c str_x",
            "IO c2p str_y"
        ]

        self.run_file(progs, "testb", expected_output)

    def testc(self):
        progs = [
            "x := 0; { p2c!x --> skip; $ c2p?x --> skip; }*",
            "x := 0; y := 0; { wait(2); p2c?x; y := x - 1; c2p!y; }*"
        ]

        expected_output = [
            "IO p2c 0.000",
            "IO c2p -1.000",
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
            "IO p2c1 0.000",
            "IO p2c2 1.000",
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
            "IO p2c -0.000",
            "IO p2c 1.000",
            "IO p2c 1.571",
            "deadlock"
        ]

        self.run_file(progs, "teste", expected_output, step_size=1e-5)

    def test1(self):
        progs = [
            "x := 0; { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x; }*",
            "x := 0; y := 0; { wait(2); p2c?x; y := x-1; c2p!y; }*"
        ]

        expected_output = [
            "IO p2c 2.000",
            "IO c2p 1.000",
            "IO p2c 3.000",
            "IO c2p 2.000"
        ]

        self.run_file(progs, "test1", expected_output, step_size=1e-1)

    def test2(self):
        progs = [
            "x := 0; { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x; }*",
            "x := 0; y := 0; wait(2); p2c?x; y := x-1; c2p!y;",
        ]

        expected_output = [
            "IO p2c 2.000",
            "IO c2p 1.000"
        ]

        self.run_file(progs, "test2", expected_output, step_size=1e-1)



if __name__ == "__main__":
    unittest.main()
