"""Unit test for wolframengine_wrapper"""

import unittest

from hhlpy.wolframengine_wrapper import wl_simplify, wl_polynomial_div, wl_is_polynomial
from hhlpy.wolframengine_wrapper import session
from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.parser import expr_parser, expr_parser

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
            "!(x > 1)"          :"x <= 1",
            "!(!(x > 1))"       :"x > 1",
            "x > 1 || x > 0"    :"x > 0",
            "x > 1 && x > 2"    :"x > 2",
            "x > 1 && x > 2 && x > 3"   :"x > 3",
            "x > 2 -> 2 < x"   :"true",
            "x > 2 <-> 2 < x"  :"true"
        }
        for k, e in test_case_bexpr.items():
            k = expr_parser.parse(k)
            e = expr_parser.parse(e)

            self.assertTrue(wl_simplify(k) == e)

    def testWlPolynomialDiv(self):
        test_cases = {
            ("x^2 + 1", "x")        :(("x", "1"),),
            ("x^3 + 1", "x^2 - 1")  :(("x", "1 + x"),)
        }

        for k, vals in test_cases.items():
            p = expr_parser.parse(k[0])
            q = expr_parser.parse(k[1])
            quot_remains = wl_polynomial_div(p, q)

            for val in vals:
                val0 = expr_parser.parse(val[0])
                val1 = expr_parser.parse(val[1])

                self.assertTrue(quot_remains[val0] == val1)

    def testWlIsPolynomial(self):
        test_cases = [
            ("x^3 - 2*x/y + 3*x*z", {"y"}, True),
            ("x^3 - 2*x/y + 3*x*z", set(), False),
            # ("x^2 + a*x*y^2 - b*Sin[c]", {"a", "b", "c"}): True,
            # ("x^2 + a*x*y^2 - b*Sin[c]", {"a", "b"}): False
        ]

        for case in test_cases:
            e = case[0]
            constants = case[1]
            result = case[2]

            e = expr_parser.parse(e)

            self.assertTrue(wl_is_polynomial(e, constants) == result)


if __name__ == "__main__":
    unittest.main()
