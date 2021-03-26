import unittest

from ss2hcsp.sf.sf_parser import parser
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
        print(func.cond_act.hps[0].exprs)

if __name__ == "__main__":
    unittest.main()