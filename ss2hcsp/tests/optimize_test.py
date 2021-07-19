"""Test of HCSP optimization."""

import unittest

from ss2hcsp.hcsp.optimize import full_optimize
from ss2hcsp.hcsp.parser import hp_parser


class OptimizeTest(unittest.TestCase):
    def testOptimize(self):
        test_data = [
            ("x := 0; x := 1",
             "x := 1"),

            ("a[0] := 0; a[1] := 0",
             "a[0] := 0; a[1] := 0"),
        ]

        for s, res in test_data:
            hp = hp_parser.parse(s)
            res_hp = hp_parser.parse(res)
            opt_hp = full_optimize(hp)
            self.assertEqual(res_hp, opt_hp)


if __name__ == "__main__":
    unittest.main()
