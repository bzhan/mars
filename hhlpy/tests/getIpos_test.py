"""Unit test for get_i_pos function"""
import unittest

from hhlpy.hhlpy import CmdVerifier
from ss2hcsp.hcsp.parser import parse_expr_with_meta, parse_hp_with_meta

def runTest(self, hp, pre="true", post="true"):

    pre = parse_expr_with_meta(pre)
    hp = parse_hp_with_meta(hp)
    post = parse_expr_with_meta(post)

    verifier = CmdVerifier(pre=pre, hp=hp, post=post)
    verifier.get_i_pos(hp)
    print(verifier.pos2i_hp)

class GetIPosTest(unittest.TestCase):
    def testPos1(self):
        runTest(self, hp="if x < 5 then x := x + 1 else x := x endif")

    def testPos2(self):
        runTest(self, hp="x := x+1 ++ x := x+2")

    def testPos3(self):
        runTest(self, hp="if x < 5 \
                          then \
                                (if x < 0 \
                                 then x := x - 1 \
                                 else x := x + 1 \
                                 endif) \
                          else x := x \
                          endif")
    def testPos4(self):
        runTest(self, hp="if x < 5 then x := x + 1 else x := x endif; \
                          if x > 0 then x := x - 1 else x := x endif")
