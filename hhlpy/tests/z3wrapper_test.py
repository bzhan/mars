"""Unit test for Z3 wrapper."""

import unittest

from ss2hcsp.hcsp.parser import expr_parser
from hhlpy.z3wrapper import z3_prove, convert


class Z3WrapperTest(unittest.TestCase):
    def testZ3Prove(self):
        test_case = [
            "x >= 0 -> x + 1 >= 1",
            "x >= 1 -> x + 1 >= 1",
            "x >= 1 -> x + 1 >= 1 && x >= 1",
            "x >= 0 -> x + 1 >= 1 || x >= 1",
            "\\forall x. x^2 >= 0",
            "\\forall {x, y}. x^2 + y^2 >= 0",
            "(\\exists y. x * y * y == 1) -> x > 0",
            "x >= 0 -> 0 < 1 -> (\\exists {y, z}. y * z^2 == 1 && x * y >= 0)"
        ]

        for e in test_case:
            e = expr_parser.parse(e)
            self.assertTrue(z3_prove(e))
    
    def testZ3ProveFail(self):
        test_case = [
            "x >= 0 -> x >= 1",
            "x >= 0 -> x + 1 >= 1 && x >= 1",
        ]

        for e in test_case:
            e = expr_parser.parse(e)
            self.assertFalse(z3_prove(e))


if __name__ == "__main__":
    unittest.main()
