# Unit test for HCSP programs

import unittest

from ss2hcsp.hcsp.expr import AConst
from ss2hcsp.hcsp.hcsp import HCSPInfo, get_concrete_chs, convert_to_concrete_chs
from ss2hcsp.hcsp.parser import hp_parser

class HCSPTest(unittest.TestCase):
    def testFindComms(self):
        data = [
            "x := 0; ch[0]!x; ch[1]!x;",
            "c := 0; x := 0; ch[c]?x;"
        ]

        infos = []
        for i, s in enumerate(data):
            infos.append(HCSPInfo("P" + str(i+1), hp_parser.parse(s)))

        self.assertEqual(get_concrete_chs(infos), {'ch': [(AConst(0),), (AConst(1),)]})

    def testConvertToConcreteChs(self):
        concrete_chs = {'ch': [(AConst(0),), (AConst(1),)]}
        hp = hp_parser.parse("ch[c]?x;")
        self.assertEqual(convert_to_concrete_chs(hp, concrete_chs),
                         hp_parser.parse("if (c == 0) { ch[0]?x; } else if (c == 1) { ch[1]?x; }"))

    def testConvertToConcreteChs2(self):
        concrete_chs = {'ch': [(AConst(0),), (AConst(1),)]}
        hp = hp_parser.parse("ch[c]!x;")
        self.assertEqual(convert_to_concrete_chs(hp, concrete_chs),
                         hp_parser.parse("if (c == 0) { ch[0]!x; } else if (c == 1) { ch[1]!x; }"))

    def testConvertToConcreteChs3(self):
        concrete_chs = {'ch': [(AConst(0),), (AConst(1),)],
                        'dh': [(AConst(2),), (AConst(3),)]}
        hp = hp_parser.parse("ch[_c]!x --> y := _c; $ dh[_c]!x --> y := _c;")
        self.assertEqual(convert_to_concrete_chs(hp, concrete_chs),
                         hp_parser.parse("ch[0]!x --> y := 0; $ ch[1]!x --> y := 1; $ dh[2]!x --> y := 2; $ dh[3]!x --> y := 3;"))


if __name__ == "__main__":
    unittest.main()
