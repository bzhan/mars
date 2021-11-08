"""Unit test for hhlpy."""

import unittest

from ss2hcsp.hcsp.parser import aexpr_parser, bexpr_parser, hp_parser
from hhlpy.hhlpy2 import CmdVerifier


def runVerify(self, *, pre, hp, post):
    pre = bexpr_parser.parse(pre)
    hp = hp_parser.parse(hp)
    post = bexpr_parser.parse(post)

    verifier = CmdVerifier(pre=pre, hp=hp, post=post)
    verifier.compute_wp()
    print('\n'.join(str(vc) for vc in verifier.get_all_vcs()))
    self.assertTrue(verifier.verify())


class HHLPyTest(unittest.TestCase):
    def testVerify1(self):
        # {x >= 0} x := x + 1 {x >= 1}
        runVerify(self, pre="x >= 0", hp="x := x+1", post="x >= 1")

    def testVerify2(self):
        # {x >= 0} x := x+1 ++ x := x+2 {x >= 1}
        runVerify(self, pre="x >= 0", hp="x := x+1 ++ x := x+2", post="x >= 1")

    def testVerify3(self):
        # {x >= 0} x := x+1; y := x+2 {x >= 1 && y >= 3}
        runVerify(self, pre="x >= 0", hp="x := x+1; y := x+2", post="x >= 1 && y >= 3")

    def testVerify4(self):
        # {x >= 0} x := x+1; x := x+1 ++ y := x+1 {x >= 1}
        runVerify(self, pre="x >= 0", hp="x := x+1; x := x+1 ++ y := x+1", post="x >= 1")


if __name__ == "__main__":
    unittest.main()
