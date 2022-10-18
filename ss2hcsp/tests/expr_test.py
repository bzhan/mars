# Unit tests for expressions

import unittest

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.expr import true_expr, AVar, AConst
from ss2hcsp.hcsp.parser import expr_parser, expr_parser, hp_parser
from ss2hcsp.hcsp import hcsp


class ExprTest(unittest.TestCase):
    def testGetRange(self):
        self.assertEqual(expr.get_range(0.1, 0.4), [0.1, 0.2, 0.3, 0.4])
        self.assertEqual(expr.get_range(0.03, 0.41), [0.03, 0.1, 0.2, 0.3, 0.4, 0.41])
        self.assertEqual(expr.get_range(0.1, 0.41), [0.1, 0.2, 0.3, 0.4, 0.41])
        self.assertEqual(expr.get_range(0.03, 0.4), [0.03, 0.1, 0.2, 0.3, 0.4])

    def testExprParser(self):
        test_data = [
            "a + 1",
            "a * b",
            "a - b",
            "min(a,b)",
            "a * b + c",
            "a * (b + c)",
            "a + b - c",
            "a + (b - c)",
            "[]",
            "\"a\"",
            "[b,0]",
            "a[0]",
            "-x",
            "-x + y",
            "(a - b) % m",
            "(a > 0 ? a : -a)",
            "(a > 0 ? (b > 0 ? b : -b) : -a)"
        ]
        
        for s in test_data:
            expr = expr_parser.parse(s)
            self.assertEqual(str(expr), s)

    def testExprParser(self):
        test_data = [
            "a < 1",
            "a == 1 && true",
            "a == 1 && b == 2 && c == 3",
            "(a == 1 && b == 2) && c == 3",
            "a == 1 && b == 2 || c == 3",
            "a == 1 || b == 2 && c == 3",
            "(a == 1 || b == 2) && c == 3",
            "(a == 1 || b == 2 || c == 3) && d == 4",
        ]

        for s in test_data:
            expr = expr_parser.parse(s)
            self.assertEqual(str(expr), s)

    def assertConditionalInst(self, test_data, res):
        inst = expr.Conditional_Inst()
        for var_name, cond_inst_str in test_data:
            cond_inst = [(expr_parser.parse(cond), expr_parser.parse(inst))
                         for cond, inst in cond_inst_str]
            inst.add(var_name, cond_inst)

        res_inst = dict()
        for var_name, cond_inst_str in res:
            cond_inst = [(expr_parser.parse(cond), expr_parser.parse(inst))
                         for cond, inst in cond_inst_str]
            res_inst[var_name] = cond_inst
        self.assertEqual(inst.data, res_inst)

    def testConditionalInst1(self):        
        test_data = [
            ("x", [("true", "a + 1")]),
            ("y", [("a >= 1", "x"), ("a < 1", "x - 1")]), 
        ]

        res = [
            ("x", [("true", "a + 1")]),
            ("y", [("a >= 1", "a + 1"), ("a < 1", "(a + 1) - 1")])
        ]

        self.assertConditionalInst(test_data, res)

    def testConditionalInst2(self):
        test_data = [
            ("w", [("in >= 5", "a"), ("in < 5", "b")]),
            ("z", [("w >= 10", "x"), ("w < 10", "y")]),
        ]

        res = [
            ("w", [("in >= 5", "a"), ("in < 5", "b")]),
            ("z", [("a >= 10 && in >= 5 || b >= 10 && in < 5", "x"),
                   ("a < 10 && in >= 5 || b < 10 && in < 5", "y")]),
        ]

        self.assertConditionalInst(test_data, res)

    def testParseHCSP(self):
        test_data = [
            "x1 := 3;",
            "x1 := 3; x2 := 5;",
            "x1 := 3; x2 := 5; skip;",
            "{skip;}*",
            "x1?x1;",
            "x1!x2;",
            "{x_dot = x + 1, y_dot = y + 1 & x < 3} |> [] (x?x --> skip;, y!y --> skip;)",
            "x?x --> skip; $ y!y --> x := 2;",
            "@A; @B; || @C;",
            "@A; @B; || @C; @D;",
            "if (x == 0) { @A; }",
            "if (x == 0) { @A; @B; }",
            "if (x == 0) { @A; @B; }",
            "x?; y?; || z?;",
            "if (x == 1) { x := 0; } else { x := 1; }",
            "if (x == 0) { x := 1; } else if (x == 1) { x := 0; } else { skip; }",
            'E := "x";',
            'EL := ["x"];',
            'EL := ["x","y"];',
            'NL := [1];',
            'NL := [1,2.1];',
            "{x := x + 1;}*(x < 3)",
            "(a, b) := xs;",
            "x := -x;",
            "x := -x + y;",
            "assert(x == 2);",
            "assert(x == 2,\"message\");",
            "log(\"start\");",
            "pt.x := pt.y + 1;",
            "ch!pt.y;",
            "pt := {x:1,y:2};",
            "ch!a[1][2];",
            "ch!pt.x[2];",
            "a[1][2]!x;",
            "a[1][2]?pt.x[1];",
            "@X;",
            "x := (a - b) % m;",
            "x := x + 1; ++ y := y + 1;",
        ]

        for s in test_data:
            hp = hp_parser.parse(s)
            self.assertEqual(str(hp), s)

    def testSubstAllFuncs(self):
        funcs = {'f': hcsp.Function('f', ['x'], "x + 1"),
                 'g': hcsp.Function('g', ['x'], "f(x) + 2")}

        test_data = [
            ("f(x)", "x + 1"),
            ("f(y)", "y + 1"),
            ("g(y)", "y + 1 + 2"),
            ("g(y) * 5", "(y + 1 + 2) * 5"),
            ("f(x) >= 0", "x + 1 >= 0"),
            ("f(x) >= 0 && g(x) >= 0", "x + 1 >= 0 && x + 1 + 2 >= 0")
        ]
       
        for s1, s2 in test_data:
            e1 = expr_parser.parse(s1)
            e1 = expr.subst_all_funcs(e1, funcs)
            self.assertEqual(str(e1), s2)


if __name__ == "__main__":
    unittest.main()
