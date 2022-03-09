"""Unit Test for SymPy wrapper"""
import unittest

from ss2hcsp.hcsp.parser import bexpr_parser, aexpr_parser
from hhlpy.sympy_wrapper import sp_simplify

class SympyWrapperTest(unittest.TestCase):
    def testSimplifyBexpr(self):
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

            # print(sp_simplify(k))
            self.assertTrue(sp_simplify(k) == e)

    def testSimplifyAexpr(self):
        test_case_aexpr = {
            "(x * y + z * y) / y"       :"x + z",
            "x ^ y - x ^ y"             :"0"
        }
        for k, e in test_case_aexpr.items():
            k = aexpr_parser.parse(k)
            e = aexpr_parser.parse(e)

            # print(sp_simplify(k))
            self.assertTrue(sp_simplify(k) == e)