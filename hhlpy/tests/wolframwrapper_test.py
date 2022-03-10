"""Unit test for wolframengine_wrapper"""

import unittest

from hhlpy.wolframengine_wrapper import wl_simplify, wl_polynomial_div
from hhlpy.wolframengine_wrapper import session
from ss2hcsp.hcsp.parser import bexpr_parser, aexpr_parser

class WolframWrapperTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        try:
            session.start()
        except Exception as e:
            session.start()

    @classmethod
    def tearDownClass(cls):
        session.terminate()

    def testWlSimplify(self):
        test_case_bexpr = {
            "~(x > 1)"          :"x <= 1",
            "~(~(x > 1))"       :"x > 1",
            "x > 1 || x > 0"    :"x > 0",
            "x > 1 && x > 2"    :"x > 2",
            "x > 1 && x > 2 && x > 3"   :"x > 3",
            "x > 2 --> 2 < x"   :"true",
            "x > 2 <--> 2 < x"  :"true"
        }
        for k, e in test_case_bexpr.items():
            k = bexpr_parser.parse(k)
            e = bexpr_parser.parse(e)

            self.assertTrue(wl_simplify(k) == e)

    def testWlPolynomialDiv(self):
        test_case = {
            ("x^2 + 1", "x")        :(("x", "1"),),
            ("x^3 + 1", "x^2 - 1")  :(("x", "1 + x"),)
        }

        for k, vals in test_case.items():
            p = aexpr_parser.parse(k[0])
            q = aexpr_parser.parse(k[1])
            quot_remains = wl_polynomial_div(p, q)

            for val in vals:
                val0 = aexpr_parser.parse(val[0])
                val1 = aexpr_parser.parse(val[1])

                self.assertTrue(quot_remains[val0] == val1)

if __name__ == "__main__":
    unittest.main()
