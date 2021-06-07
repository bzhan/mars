"""Unit test for parsing and conversion of matlab functions."""

import unittest

from ss2hcsp.matlab import parser
from ss2hcsp.matlab import convert


class MatlabTest(unittest.TestCase):
    def testParseCmd(self):
        test_data = [
            "x = 1",
            "x = -1",
            "z = x + y",
            "st = \"a\"",
            "msg = \"a\" + \"b\"",
            "z = min(x,y)",
            "fprintf(\"abc\")",
            "fprintf(\"abc\" + \"\\n\")",
            "x = 1;\ny = 1",
            "if x == 1\n  x = x + 1\nelse\n  x = x - 1",
            "if x == 1\n  if y == 1\n    z = 1\n  else\n    z = 2\nelse\n  z = 3",
            "if x == 1\n  y = 1;\n  z = 2\nelse\n  y = 2;\n  z = 1",
        ]

        for s in test_data:
            cmd = parser.cmd_parser.parse(s)
            self.assertEqual(str(cmd), s)

    def testParseFunction(self):
        test_data = [
            "function bar()\n  x = 0",
            "function y=bar()\n  y = 0",
            "function [x,y]=bar()\n  x = 0;\n  y = 0",
            "function y=bar(x)\n  y = x",
            "function [x,y]=bar(z)\n  x = z;\n  y = 2 * z",
        ]

        for s in test_data:
            func = parser.function_parser.parse(s)
            self.assertEqual(str(func), s)

    def testParseFunctionName(self):
        s = "function bar\n  x = 0"
        s2 = "function bar()\n  x = 0"
        func = parser.function_parser.parse(s)
        self.assertEqual(str(func), s2)

    def testParseFunctionPrint(self):
        s = "function enA()\n  x = 0;\n  x = x + 1;\n  fprintf(\"enA is executing\" + x)"
        func = parser.function_parser.parse(s)
        self.assertEqual(str(func), s)

    def testParseFunctionRecursive(self):
        s = "function y=enA()\n  y = en(A)"
        func = parser.function_parser.parse(s)
        self.assertEqual(str(func), s)

    def testConvertExpression(self):
        test_data = [
            ("a + b", "a+b"),
            ("a * b", "a*b"),
            ("-a * b", "-a*b"),
            ("-(a + b)", "-(a+b)"),
            ("a % 2", "a%2"),
            ("min(a,b)", "min(a,b)"),
            ("rand()", "uniform(0,1)"),
        ]

        for s, res in test_data:
            e = parser.expr_parser.parse(s)
            expr = convert.convert_expr(e)
            self.assertEqual(str(expr), res)

    def testConvertCondition(self):
        test_data = [
            ("a < b", "a < b"),
            ("a < 1 && b < 1", "a < 1 && b < 1"),
            ("~(a < 1)", "~(a < 1)")
        ]

        for s, res in test_data:
            cond = parser.cond_parser.parse(s)
            cond_expr = convert.convert_expr(cond)
            self.assertEqual(str(cond_expr), res)

    def testConvertCommand(self):
        test_data = [
            ("x = 0", "x := 0"),
            ("fprintf(\"abc\")", "log(\"abc\")"),
            ("z = min(x,y)", "z := min(x,y)"),
            ("if x == 1\n  x = x + 1\nelse\n  x = x - 1", "if x == 1 then x := x+1 else x := x-1 endif"),
            ("x = 1; y = 1", "x := 1; y := 1"),
        ]

        for s, res in test_data:
            cmd = parser.cmd_parser.parse(s)
            hp = convert.convert_cmd(cmd)
            self.assertEqual(str(hp), res)

    def testConvertPrint(self):
        s = """
        function enA
          x=0;
          x=x+1;
          fprintf("enA is executing"+x);
        """
        res = "x := 0; x := x+1; log(\"enA is executing\"+x)"

        func = parser.function_parser.parse(s)
        hp = convert.convert_function(func)
        self.assertEqual(str(hp), res)

    def testConvertFunction(self):
        s = """
        function y=enA()
          y=rand();
          if x>0.6
            if x>0.6
              y=1;
            else
              y=0; 
            end 
          else
            y=0; 
          end 
        """
        res = "y := uniform(0,1); if x > 0.6 then if x > 0.6 then y := 1 else y := 0 endif else y := 0 endif"
        func = parser.function_parser.parse(s)
        hp = convert.convert_function(func)
        self.assertEqual(str(hp), res)


if __name__ == "__main__":
    unittest.main()
