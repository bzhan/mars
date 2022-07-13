"""Unit test for hhlpy."""

import unittest

from ss2hcsp.hcsp.parser import expr_parser, expr_parser, hp_parser
from hhlpy.hhlpy import compute_diff, compute_wp, compute_vcs, verify


def runWpTest(self, *, post, hp, expected_pre, expected_vcs=None, print_res=False):
    if expected_vcs is None:
        expected_vcs = []

    post = expr_parser.parse(post)
    hp = hp_parser.parse(hp)
    expected_pre = expr_parser.parse(expected_pre)
    expected_vcs = [expr_parser.parse(vc) for vc in expected_vcs]

    pre, vcs = compute_wp(hp, post)
    if print_res:
        print("pre", pre)
        for vc in vcs:
            print("vc", vc)
    self.assertEqual(pre, expected_pre)
    self.assertEqual(vcs, expected_vcs)

def runVerify(self, *, pre, hp, post):
    pre = expr_parser.parse(pre)
    hp = hp_parser.parse(hp)
    post = expr_parser.parse(post)
    self.assertTrue(verify(pre, hp, post))


class HHLPyTest(unittest.TestCase):
    def testComputeDiff(self):
        e1 = expr_parser.parse("x >= 0")
        res = compute_diff(e1, {'x': expr_parser.parse("2")})
        expected = expr_parser.parse("2 >= 0")
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
        runWpTest(self, post="x >= 0", hp="(x := x+1)**@invariant(x >= 0)",
                  expected_pre="x >= 0", expected_vcs=["x >= 0 --> x + 1 >= 0", "x >= 0 --> x >= 0"])

    def testComputeWp6(self):
        # {x >= 0} x := x+1; (x := x+1)** {x >= 1}
        runWpTest(self, post="x >= 1", hp="x := x+1; (x := x+1)**@invariant(x >= 1)", 
                  expected_pre="x+1 >= 1", expected_vcs=["x >= 1 --> x + 1 >= 1", "x >= 1 --> x >= 1"])

    def testComputeWp7(self):
        # {x >= 0} <x_dot=2 & x < 10>@invariant(x >= 0) {x >= 0}
        runWpTest(self, post="x >= 0", hp="<x_dot=2 & x < 10>@invariant(x >= 0)", 
                  expected_pre="x >= 0", expected_vcs=["2 >= 0", "x >= 0 --> x >= 0"])

    def testComputeWp8(self):
        # {x * x + y * y == 1} <x_dot=y, y_dot=-x & x > 0> {x * x + y * y = 1}
        runWpTest(self, post="x * x + y * y == 1", 
                  hp="<x_dot=y, y_dot=-x & x > 0>@invariant(x * x + y * y  == 1)", 
                  expected_pre="x * x + y * y == 1",
                  expected_vcs=["x * y + y * x + (y * -x + -x * y) == 0", "x * x + y * y == 1 --> x * x + y * y == 1"])

    def testComputeWp9(self):
        # {x >= 0} x >= -2 -> x := x+1 {x >= 1}
        runWpTest(self, post="x >= 1", 
                  hp="x >= -2 -> x := x+1",
                  expected_pre="x >= -2 --> x + 1 >= 1")

    def testComputeWp10(self):
        # {x >= 0} x := x+1; y := {y >= x} {y >= 1}        
        runWpTest(self, post="y >= 1", hp="x := x+1; y := {y >= x}", 
                  expected_pre="y0 >= x + 1 --> y0 >= 1")  

    def testComputeVC(self):
        # {x >= 0} x := x+1; (x := x+1)** {x >= 1}
        pre = expr_parser.parse("x >= 0")
        hp = hp_parser.parse("x := x+1; (x := x+1)**@invariant(x >= 1)")
        post = expr_parser.parse("x >= 1")
        vcs = compute_vcs(pre, hp, post)
        expected_vcs = [expr_parser.parse("x >= 1 --> x+1 >= 1"),
                        expr_parser.parse("x >= 1 --> x >= 1"),
                        expr_parser.parse("x >= 0 --> x+1 >= 1")]
        self.assertEqual(vcs, expected_vcs)

    def testVerify1(self):
        # Basic benchmark, problem 1
        runVerify(self, pre="x >= 0", hp="x := x+1", post="x >= 1")

    def testVerify2(self):
        # Basic benchmark, problem 2
        runVerify(self, pre="x >= 0", hp="x := x+1; x := x+1 ++ y := x+1", post="x >= 1")

    def testVerify3(self):
        # Basic benchmark, problem 3
        runVerify(self, pre="x >= 0", hp="x := x+1; (x := x+1)**@invariant(x >= 1)", post="x >= 1")

    def testVerify4(self):
        # Basic benchmark, problem 4
        runVerify(self, pre="x >= 0", hp="x := x+1; <x_dot=2 & x < 10>@invariant(x >= 1)", post="x >= 1")

    def testVerify5(self):
        runVerify(self, pre="x * x + y * y == 1", hp="<x_dot=y, y_dot=-x & x > 0>@invariant(x * x + y *  y == 1)",post="x * x + y * y == 1")

    def testVerify6(self):
        # Basic Benchmark, problem5
        runVerify(self, pre="x >= 0", hp="x := x+1; x := {x >= 1}", post="x >= 1")
    
    def testVerify7(self):
        # {x >= 0} x := x+1; y := {y >= x} {y >= 1}
        runVerify(self, pre="x >= 0", hp="x := x+1; y := {y >= x}", post="y >= 1")

    def testVerify9(self):
        # Basic Benchmark, problem7
        # confusion about the inv of loop
        # {x >= 0 && y >= 1} 
        # x := x + 1; (x := x + 1)**@invariant(x >= 1) ++ y:= x + 1; <y_dot = 2>@invariant(y >= 1); x := y
        # {x >= 1}
        runVerify(self, pre="x >= 0 && y >= 1", hp="x := x + 1; (x := x + 1)**@invariant(x >= 1 && y >= 1) ++ y:= x + 1; <y_dot = 2 & y <= 10>@invariant(y >= 1); x := y", post="x >= 1")

    def testVerify10(self):
        # Basic benchmark, problem8
        # {x > 0 && y > 0} <x_dot = 5 & x < 10>@invariant(x > 0); (x := x + 3)**@invariant(x > 0) ++ y := x; {x > 0 && y > 0}
        runVerify(self, pre="x > 0 && y > 0", hp="<x_dot = 5 & x < 10>@invariant(x > 0 && y > 0); (x := x + 3)**@invariant(x > 0 && y > 0) ++ y := x", post="x > 0 && y > 0")

if __name__ == "__main__":
    unittest.main()
