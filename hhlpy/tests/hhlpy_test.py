"""Unit test for hhlpy."""

import unittest

from ss2hcsp.hcsp.parser import aexpr_parser, bexpr_parser, hp_parser
from hhlpy.hhlpy import compute_diff, compute_wp, compute_vcs, verify


def runWpTest(self, *, post, hp, expected_pre, expected_vcs=None):
    if expected_vcs is None:
        expected_vcs = []

    post = bexpr_parser.parse(post)
    hp = hp_parser.parse(hp)
    expected_pre = bexpr_parser.parse(expected_pre)
    expected_vcs = [bexpr_parser.parse(vc) for vc in expected_vcs]

    pre, vcs = compute_wp(hp, post)
    self.assertEqual(pre, expected_pre)
    self.assertEqual(vcs, expected_vcs)

def runVerify(self, *, pre, hp, post):
    pre = bexpr_parser.parse(pre)
    hp = hp_parser.parse(hp)
    post = bexpr_parser.parse(post)
    self.assertTrue(verify(pre, hp, post))


class HHLPyTest(unittest.TestCase):
    def testComputeDiff(self):
        e1 = bexpr_parser.parse("x >= 0")
        res = compute_diff(e1, {'x': aexpr_parser.parse("2")})
        expected = bexpr_parser.parse("2 >= 0")
        self.assertEqual(res, expected)

    def testComputeWp1(self):
        # {x >= 0} x := x + 1 {x >= 1}
        runWpTest(self, post="x >= 1", hp="x := x+1", expected_pre="x + 1 >= 1")

    def testComputeWp2(self):
        # {x >= 0} x := x+1 ++ x := x+2 {x >= 1}
        runWpTest(self, post="x >= 1", hp="x := x+1 ++ x := x+2",
                  expected_pre="x + 1 >= 1 && x + 2 >= 1")

    def testComputeWp3(self):
        # {x >= 0} x := x+1; y := x+2 {x >= 1 && y >= 3}
        runWpTest(self, post="x >= 1 && y >= 3", hp="x := x+1; y := x+2",
                  expected_pre="x+1 >= 1 && x+1+2 >= 3")

    def testComputeWp4(self):
        # {x >= 0} x := x+1; x := x+1 ++ y := x+1 {x >= 1}
        runWpTest(self, post="x >= 1", hp="x := x+1; x := x+1 ++ y := x+1",
                  expected_pre="x+1+1 >= 1 && x+1 >= 1")

    def testComputeWp5(self):
        # {x >= 0} (x := x+1)** {x >= 0}
        runWpTest(self, post="x >= 0", hp="(x := x+1)**",
                  expected_pre="x >= 0", expected_vcs=["x >= 0 --> x + 1 >= 0"])

    def testComputeWp6(self):
        # {x >= 0} x := x+1; (x := x+1)** {x >= 1}
        runWpTest(self, post="x >= 1", hp="x := x+1; (x := x+1)**",
                  expected_pre="x+1 >= 1", expected_vcs=["x >= 1 --> x + 1 >= 1"])

    def testComputeWp7(self):
        # {x >= 0} <x_dot=2 & x < 10> {x >= 0}
        runWpTest(self, post="x >= 0", hp="<x_dot=2 & x < 10>",
                  expected_pre="x >= 0", expected_vcs=["2 >= 0"])

    def testComputeVC(self):
        # {x >= 0} x := x+1; (x := x+1)** {x >= 1}
        pre = bexpr_parser.parse("x >= 0")
        hp = hp_parser.parse("x := x+1; (x := x+1)**")
        post = bexpr_parser.parse("x >= 1")
        vcs = compute_vcs(pre, hp, post)
        expected_vcs = [bexpr_parser.parse("x >= 1 --> x+1 >= 1"),
                        bexpr_parser.parse("x >= 0 --> x+1 >= 1")]
        self.assertEqual(vcs, expected_vcs)

    def testVerify1(self):
        # Basic benchmark, problem 1
        runVerify(self, pre="x >= 0", hp="x := x+1", post="x >= 1")

    def testVerify2(self):
        # Basic benchmark, problem 2
        runVerify(self, pre="x >= 0", hp="x := x+1; x := x+1 ++ y := x+1", post="x >= 1")

    def testVerify3(self):
        # Basic benchmark, problem 3
        runVerify(self, pre="x >= 0", hp="x := x+1; (x := x+1)**", post="x >= 1")

    def testVerify4(self):
        # Basic benchmark, problem 4
        runVerify(self, pre="x >= 0", hp="x := x+1; <x_dot=2 & x < 10>", post="x >= 1")


if __name__ == "__main__":
    unittest.main()
