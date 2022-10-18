"""Unit Test for SymPy wrapper"""
import unittest

from ss2hcsp.hcsp.parser import expr_parser, expr_parser
from hhlpy.sympy_wrapper import sp_simplify, sp_polynomial_div, sp_is_polynomial

class SympyWrapperTest(unittest.TestCase):
    def testSimplifyBexpr(self):
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

            self.assertTrue(sp_simplify(k) == e)

    def testSimplifyAexpr(self):
        test_case_aexpr = {
            "(x * y + z * y) / y"       :"x + z",
            "x ^ y - x ^ y"             :"0"
        }
        for k, e in test_case_aexpr.items():
            k = expr_parser.parse(k)
            e = expr_parser.parse(e)

            self.assertTrue(sp_simplify(k) == e)

    def testSpPolynomialDiv(self):
        test_case = {
            ("x^2 + 1", "x")        :("x", "1"),
            ("x^3 + 1", "x^2 - 1")  :("x", "1 + x")
        }

        for k, e in test_case.items():
            p = expr_parser.parse(k[0])
            q = expr_parser.parse(k[1])
            e0 = expr_parser.parse(e[0])
            e1 = expr_parser.parse(e[1])

            quot_remains = sp_polynomial_div(p, q)
            self.assertTrue(quot_remains[e0] == e1)

    def testSpIsPolynomial(self):
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
           
            self.assertTrue(sp_is_polynomial(e, constants) == result)