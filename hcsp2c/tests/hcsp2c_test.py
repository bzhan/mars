import unittest
import subprocess

from ss2hcsp.hcsp import parser
from hcsp2c import transfer2c


class HCSP2CTest(unittest.TestCase):
    def run_file(self, progs, filename, expected_output):
        hps = []
        for i, prog in enumerate(progs):
            hps.append(("P" + str(i+1), parser.hp_parser.parse(prog)))
        res = transfer2c.convertHps(hps)

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
            "IO c2p -2.000",
            "IO p2c -2.000",
            "IO c2p -3.000"
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
            "IO c2p str_y",
            "IO p2c str_x",
            "IO c2p str_y"
        ]

        self.run_file(progs, "testb", expected_output)

    def test1(self):
        progs = [
            "x := 0; { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x; }*",
            "x := 0; { wait(2); p2c?x; c2p!x-1; }*"
        ]

        expected_output = [
            "IO p2c 2.000",
            "IO c2p 1.000",
            "IO p2c 3.000",
            "IO c2p 2.000"
        ]

        self.run_file(progs, "test1", expected_output)


if __name__ == "__main__":
    unittest.main()
