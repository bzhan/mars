"""Test of HCSP optimization."""

import unittest

from ss2hcsp.hcsp.optimize import full_optimize
from ss2hcsp.hcsp.parser import hp_parser


class OptimizeTest(unittest.TestCase):
    def testOptimize(self):
        test_data = [
            ("x := 0; x := 1;",
             "x := 1;"),

            ("a[0] := 0; a[1] := 0;",
             "a[0] := 0; a[1] := 0;"),

            ("x := 0; x := x + 1;",
             "x := 0 + 1;"),

            ("x := 0; x := x + 1; y := x + 1;",
             "x := 0 + 1; y := x + 1;"),

            ("s := 0; log(s+\"\\n\"); s := 1;",
             "log(0+\"\\n\"); s := 1;"),

            ("x := 0; a[x] := 1; x := 1;",
             "a[0] := 1; x := 1;"),

            ("x := 0; ch?a[x]; x := 1;",
             "ch?a[0]; x := 1;"),

            ("x := 0; ch!a[x]; x := 1;",
             "ch!a[0]; x := 1;"),

            ("if (x == 0) { if (x == 0) { x := 1; } }",
             "if (x == 0) { x := 1; }"),

            ("if (0 == 0) { x := 1; }",
             "x := 1;"),

            ("x := 1; y := 1; if (z == 0) {x := 2;} y := 2;",
             "x := 1; if (z == 0) {x := 2;} y := 2;")
        ]

        for s, res in test_data:
            hp = hp_parser.parse(s)
            res_hp = hp_parser.parse(res)
            opt_hp = full_optimize(hp)
            self.assertEqual(res_hp, opt_hp, "%s != %s" % (str(res_hp), str(opt_hp)))


if __name__ == "__main__":
    unittest.main()
