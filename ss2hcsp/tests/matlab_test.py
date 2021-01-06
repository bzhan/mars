"""Unit test for parsing and conversion of matlab functions."""

import unittest

from ss2hcsp.matlab import parser
from ss2hcsp.matlab import convert


class MatlabTest(unittest.TestCase):
    def testParser(self):
        s = """
        function enA
          x=0;
          x=x+1;
          fprintf("enA is executing"+x);
        """

        func = parser.function_parser.parse(s)
        self.assertEqual(repr(func),
            """Function(enA,Assign(x,0),Assign(x,Fun(+,x,1)),Print(Fun(+,"enA is executing",x)))""")

    def testConvert(self):
        s = """
        function enA
          x=0;
          x=x+1;
          fprintf("enA is executing"+x);
        """

        func = parser.function_parser.parse(s)
        hp = convert.convert_function(func)
        self.assertEqual(repr(hp),
            """Seq(Assign(x,0), Assign(x,x+1), Log(AConst("enA is executing"),AVar(x)))""")


if __name__ == "__main__":
    unittest.main()
