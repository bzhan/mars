"""Unit test for parsing and conversion of matlab functions."""

import unittest

from ss2hcsp.matlab import function
from ss2hcsp.matlab import parser
from ss2hcsp.matlab import convert
from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp import hcsp


class MatlabTest(unittest.TestCase):
    def testParseExpr(self):
        test_data = [
            ("0", function.AConst(0)),
            ("[0,0,0,0,0]", function.ListExpr(*([function.AConst(0)] * 5))),
            ("pi / 3", function.OpExpr("/", function.FunExpr("pi"), function.AConst(3))),
        ]

        for s, expected_expr in test_data:
            expr = parser.expr_parser.parse(s)
            self.assertEqual(expr, expected_expr)

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
            "x = 1; y = 1",
            "if x == 1  x = x + 1 else x = x - 1",
            "if x == 1  if y == 1  z = 1 else z = 2 else z = 3",
            "if x == 1  y = 1; z = 2 else y = 2; z = 1",
            "a(1) = b(1)",
            "[a,b] = [b,a]",
            "[a(1),a(2)] = [a(2),a(1)]",
            'a(1,2) = a(2,1)',
        ]

        for s in test_data:
            cmd = parser.cmd_parser.parse(s)
            self.assertEqual(str(cmd), s)

    def testParseFunction(self):
        test_data = [
            "function bar()\n  x = 0",
            "function y=bar()\n  y = 0",
            "function [x,y]=bar()\n  x = 0; y = 0",
            "function y=bar(x)\n  y = x",
            "function [x,y]=bar(z)\n  x = z; y = 2 * z",
        ]

        for s in test_data:
            func = parser.function_parser.parse(s)
            self.assertEqual(str(func), s)

    def testParseEvent(self):
        test_data = [
            ("after(5, sec)", "TemporalEvent('after',AConst(5),AbsoluteTimeEvent('sec'))"),
            ("before(3, tick)", "TemporalEvent('before',AConst(3),ImplicitEvent('tick'))"),
            ("at(m+3, E)", "TemporalEvent('at',OpExpr('+',Var(m),AConst(3)),BroadcastEvent('E'))"),
            ("every(f(2), E)", "TemporalEvent('every',FunExpr('f',AConst(2)),BroadcastEvent('E'))"),
        ]

        for s, res in test_data:
            e = parser.event_parser.parse(s)
            self.assertEqual(repr(e), res)

    def testParseFunctionName(self):
        s = "function bar\n  x = 0"
        s2 = "function bar()\n  x = 0"
        func = parser.function_parser.parse(s)
        self.assertEqual(str(func), s2)

    def testParseFunctionPrint(self):
        s = "function enA()\n  x = 0; x = x + 1; fprintf(\"enA is executing\" + x)"
        func = parser.function_parser.parse(s)
        self.assertEqual(str(func), s)

    def testParseFunctionRecursive(self):
        s = "function y=enA()\n  y = en(A)"
        func = parser.function_parser.parse(s)
        self.assertEqual(str(func), s)

    def testConvertExpression(self):
        test_data = [
            ("a + b", "a + b"),
            ("a * b", "a * b"),
            ("-a * b", "-(a * b)"),
            ("-(a + b)", "-(a + b)"),
            ("a % 2", "a % 2"),
            ("min(a,b)", "min(a,b)"),
            ("rand()", "uniform(0,1)"),
            ("pi / 3", "pi / 3"),
        ]

        for s, res in test_data:
            e = parser.expr_parser.parse(s)
            _, expr = convert.convert_expr(e)
            self.assertEqual(str(expr), res)

    def testConvertCondition(self):
        test_data = [
            ("a < b", "a < b"),
            ("a < 1 && b < 1", "a < 1 && b < 1"),
            ("~(a < 1)", "!a < 1")
        ]

        for s, res in test_data:
            cond = parser.cond_parser.parse(s)
            _, cond_expr = convert.convert_expr(cond)
            self.assertEqual(str(cond_expr), res)

    def testConvertCommand(self):
        test_data = [
            ("x = 0", "x := 0;"),
            ("fprintf(\"abc\")", "log(\"abc\");"),
            ("z = min(x,y)", "z := min(x,y);"),
            ("if x == 1\n  x = x + 1\nelse\n  x = x - 1", "if (x == 1) { x := x + 1; } else { x := x - 1; }"),
            ("x = 1; y = 1", "x := 1; y := 1;"),
            ("a(1) = b(1)", "a[0] := b[0];"),
            ("a(1) = f(1)", "a[0] := f(1);"),
        ]

        for s, res in test_data:
            cmd = parser.cmd_parser.parse(s)
            hp = convert.convert_cmd(cmd, arrays={'a', 'b'})
            self.assertEqual(str(hp), res)

    def testConvertPrint(self):
        s = """
        function enA
          x=0;
          x=x+1;
          fprintf("enA is executing"+x);
        """
        res = "x := 0; x := x + 1; log(\"enA is executing\" + x);"

        func = parser.function_parser.parse(s)
        hp = convert.convert_cmd(func.instantiate()[0])
        self.assertEqual(str(hp), res)

    def testConvertEvent(self):
        s = "x = 0; E; x = 1"
        def raise_event(e):
            return hcsp.Log(expr.AConst(e.name))
        res = "x := 0; log(\"E\"); x := 1;"

        cmd = parser.cmd_parser.parse(s)
        hp = convert.convert_cmd(cmd, raise_event=raise_event)
        self.assertEqual(str(hp), res)

    def testConvertFunctionCall(self):
        s = "x = 0; f()"
        procedures = {'f': parser.function_parser.parse("function f\n  x = x + 1;")}
        res = "x := 0; x := x + 1;"

        cmd = parser.cmd_parser.parse(s)
        hp = convert.convert_cmd(cmd, procedures=procedures)
        self.assertEqual(str(hp), res)

    def testConvertFunctionCallWithParam(self):
        s = "f(\"A\")"
        procedures = {'f': parser.function_parser.parse("function f(x)\n  fprintf(x+\"\\n\");")}
        res = "x := \"A\"; log(x + \"\\n\");"

        cmd = parser.cmd_parser.parse(s)
        hp = convert.convert_cmd(cmd, procedures=procedures)
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
        res = "y := uniform(0,1); if (x > 0.6) { if (x > 0.6) { y := 1; } else { y := 0; } } else { y := 0; }"
        func = parser.function_parser.parse(s)
        hp = convert.convert_cmd(func.instantiate()[0])
        self.assertEqual(str(hp), res)

    def testConvertFunctionWithParam(self):
        s = """
        function f(s)
          fprintf(s + "\\n");
        """
        res = 's := "A1"; log(s + "\\n");'
        func = parser.function_parser.parse(s)
        cmd, params = func.instantiate([function.AConst("A1")])
        hp = hcsp.seq([convert.convert_cmd(params),convert.convert_cmd(cmd)])
        self.assertEqual(str(hp), res)

    def testParseTransition(self):
        test_data = [
            "",
            "E",
            "[x == 0]",
            "E[x == 0]",
            "{x = 1}",
            "E{x = 1}",
            "[x == 0]{x = 1}",
            "E[x == 0]{x = 1}",
            "/{x = 1}",
            "E/{x = 1}",
            "[x == 0]/{x = 1}",
            "E[x == 0]/{x = 1}",
            "{x = 1}/{y = 1}",
            "E{x = 1}/{y = 1}",
            "[x == 0]{x = 1}/{y = 1}",
            "E[x == 0]{x = 1}/{y = 1}",
        ]

        for s in test_data:
            tran = parser.transition_parser.parse(s)
            self.assertEqual(str(tran), s)

    def testParseTransitionEvent(self):
        test_data = [
            "E{E}",
            "E/{E}",
            "E{E}/{E}",
            "E{E; x = x + 1}",
            "E{x = x + 1; E}",
            "E{if x == 0  E else F}",
        ]

        for s in test_data:
            tran = parser.transition_parser.parse(s)
            self.assertEqual(str(tran), s)


if __name__ == "__main__":
    unittest.main()
