import unittest

from ss2hcsp.matlab import parser
from ss2hcsp.matlab import convert


import html


class MatlabTest(unittest.TestCase):
    def testParser(self):
        s = """
        [chance(a.b)==10 && i>1]{y=chance(E,A.B);i=i+1;}/{   i=1;
            y=8;}
        """
        func = parser.transition_parser.parse(html.unescape(s))
        
        print(func.cond)
        print(func.cond_act.cmd1)

if __name__ == "__main__":
    unittest.main()