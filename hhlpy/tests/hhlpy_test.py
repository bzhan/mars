"""Unit test for hhlpy."""

import unittest

from ss2hcsp.hcsp.parser import bexpr_parser, hp_parser
from hhlpy.hhlpy import compute_wp


class HHLPyTest(unittest.TestCase):
    def testComputeWp1(self):
        # {x >= 0} x := x + 1 {x >= 1}
        post = bexpr_parser.parse("x >= 1")
        hp = hp_parser.parse("x := x + 1")
        pre, vcs = compute_wp(hp, post)
        expected_pre = bexpr_parser.parse("x + 1 >= 1")
        self.assertEqual(pre, expected_pre)
        self.assertEqual(vcs, [])


if __name__ == "__main__":
    unittest.main()
