"""Unit test for wolframengine_wrapper"""

import unittest

from hhlpy.wolframengine_wrapper import wl_simplify
from hhlpy.wolframengine_wrapper import session
from ss2hcsp.hcsp.parser import bexpr_parser

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
            # "x > 2 <--> 2 < x"  :"true"
        }
        for k, e in test_case_bexpr.items():
            k = bexpr_parser.parse(k)
            e = bexpr_parser.parse(e)

            print(wl_simplify(k))
            self.assertTrue(wl_simplify(k) == e)

if __name__ == "__main__":
    unittest.main()
