"""Unit test for hhlpy."""

import unittest

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.parser import aexpr_parser, bexpr_parser, hp_parser
from hhlpy.hhlpy2 import CmdVerifier


def runVerify(self, *, pre, hp, post, invariants=None, diff_invariants=None,
              ghost_invariants=None, print_vcs=False, expected_vcs=None):
    # Parse pre-condition, HCSP program, and post-condition
    pre = bexpr_parser.parse(pre)
    hp = hp_parser.parse(hp)
    post = bexpr_parser.parse(post)

    # Initialize the verifier
    verifier = CmdVerifier(pre=pre, hp=hp, post=post)

    # Place input invariants
    if invariants:
        for pos, inv in invariants.items():
            if isinstance(inv, str):
                inv = bexpr_parser.parse(inv)
            verifier.add_invariant(pos, inv)

    # Place differential invariants
    if diff_invariants:
        for pos, diff_inv in diff_invariants.items():
            if isinstance(diff_inv, str):
                diff_inv = bexpr_parser.parse(diff_inv)
            verifier.add_diff_invariant(pos, diff_inv)

    # Place ghost invariants
    if ghost_invariants:
        for pos, ghost_inv in ghost_invariants.items():
            if isinstance(ghost_inv, str):
                ghost_inv = bexpr_parser.parse(ghost_inv)
            verifier.add_ghost_invariant(pos, ghost_inv)

    # Compute wp and verify
    verifier.compute_wp()

    # Optional: Print verification conditions
    if print_vcs:
        for pos, vcs in verifier.get_all_vcs().items():
            print("%s:" % str(pos))
            for vc in vcs:
                print(vc)

    # Use SMT to verify all verification conditions
    self.assertTrue(verifier.verify())

    # Optional: check the verification conditions are expected
    def is_trivial(vc):
        if isinstance(vc, expr.LogicExpr) and vc.op == "-->" and vc.exprs[0] == vc.exprs[1]:
            return True
        else:
            return False

    if expected_vcs:
        for pos, vcs in expected_vcs.items():
            vcs = [bexpr_parser.parse(vc) for vc in vcs]
            actual_vcs = [vc for vc in verifier.infos[pos].vcs if not is_trivial(vc)]
            self.assertEqual(set(vcs), set(actual_vcs))


class HHLPyTest(unittest.TestCase):
    def testVerify1(self):
        # {x >= 0} x := x + 1 {x >= 1}
        runVerify(self, pre="x >= 0", hp="x := x+1", post="x >= 1",
                  expected_vcs={(): ["x >= 0 --> x + 1 >= 1"]})

    def testVerify2(self):
        # {x >= 0} x := x+1 ++ x := x+2 {x >= 1}
        runVerify(self, pre="x >= 0", hp="x := x+1 ++ x := x+2", post="x >= 1",
                  expected_vcs={(): ["x >= 0 --> x + 1 >= 1 && x + 2 >= 1"]})

    def testVerify3(self):
        # {x >= 0} x := x+1; y := x+2 {x >= 1 && y >= 3}
        runVerify(self, pre="x >= 0", hp="x := x+1; y := x+2", post="x >= 1 && y >= 3",
                  expected_vcs={(): ["x >= 0 --> x + 1 >= 1 && x + 1 + 2 >= 3"]})

    def testVerify4(self):
        # {x >= 0} x := x+1; x := x+1 ++ y := x+1 {x >= 1}
        runVerify(self, pre="x >= 0", hp="x := x+1; x := x+1 ++ y := x+1", post="x >= 1",
                  expected_vcs={(): ["x >= 0 --> x + 1 + 1 >= 1 && x + 1 >= 1"]})

    def testVerify5(self):
        # {x >= 0} (x := x+1)** {x >= 0}
        runVerify(self, pre="x >= 0", hp="(x := x+1)**", post="x >= 0",
                  invariants={(): "x >= 0"},
                  expected_vcs={(): ["x >= 0 --> x + 1 >= 0"]})

    def testVerify6(self):
        # {x >= 0} x := x+1; (x := x+1)** {x >= 1}
        # Invariant for loop is x >= 1.
        runVerify(self, pre="x >= 0", hp="x := x+1; (x := x+1)**", post="x >= 1", 
                  invariants={(1,): "x >= 1"},
                  expected_vcs={(): ["x >= 0 --> x + 1 >= 1"],
                                (1,): ["x >= 1 --> x + 1 >= 1"]})

    def testVerify7(self):
        # {x >= 0} <x_dot=2 & x < 10> {x >= 0}
        # Invariant for ODE is x >= 0.
        runVerify(self, pre="x >= 0", hp="<x_dot=2 & x < 10>", post="x >= 0",
                  diff_invariants={(): "x >= 0"},
                  expected_vcs={(): ["2 >= 0"]})

    def testVerify8(self):
        # {x * x + y * y == 1} <x_dot=y, y_dot=-x & x > 0> {x * x + y * y = 1}
        # Invariant for ODE is x * x + y * y == 1
        runVerify(self, pre="x * x + y * y == 1", 
                  hp="<x_dot=y, y_dot=-x & x > 0>",
                  post="x * x + y * y == 1",
                  diff_invariants={(): "x * x + y * y == 1"},
                  expected_vcs={(): ["x * y + y * x + (y * -x + -x * y) == 0"]})

    def testVerify9(self):
        # Test case containing ghost variables
        runVerify(self, pre="x > 0", hp="t := 0; <x_dot=-x, t_dot=1 & t < 1>", post="x > 0",
                  invariants={(1,): "x > 0"},
                  ghost_invariants={(1,): "x * y * y == 1"},
                  expected_vcs={(1,): ["x > 0 --> (EX y. x * y * y == 1)",
                                       "x * y * y == 1 --> x > 0"]})


if __name__ == "__main__":
    unittest.main()
