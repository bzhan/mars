import unittest

from ss2hcsp.hcsp import parser
from hcsp2c import transfer2c



class HCSP2CTest(unittest.TestCase):
    def test1(self):
        progs = [
            "x := 0; { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x; }*",
            "{ wait(2); p2c?x; c2p!x-1; }*"
        ]

        hps = [parser.hp_parser.parse(prog) for prog in progs]
        res = transfer2c.convertHps(hps)
        with open('hcsp2c/target/test1.c', 'w') as f:
            f.write(res)


if __name__ == "__main__":
    unittest.main()
