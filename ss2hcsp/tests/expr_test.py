# Unit tests for expressions

import unittest

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.expr import true_expr, AVar, AConst, PlusExpr
from ss2hcsp.hcsp.parser import aexpr_parser, bexpr_parser, hp_parser
from ss2hcsp.hcsp import hcsp


class ExprTest(unittest.TestCase):
    def testGetRange(self):
        self.assertEqual(expr.get_range(0.1, 0.4), [0.1, 0.2, 0.3, 0.4])
        self.assertEqual(expr.get_range(0.03, 0.41), [0.03, 0.1, 0.2, 0.3, 0.4, 0.41])
        self.assertEqual(expr.get_range(0.1, 0.41), [0.1, 0.2, 0.3, 0.4, 0.41])
        self.assertEqual(expr.get_range(0.03, 0.4), [0.03, 0.1, 0.2, 0.3, 0.4])

    def testAExprParser(self):
        test_data = [
            ("a + 1", "Plus(+Var(a), +Const(1))"),
            ("a * b", "Times(*Var(a), *Var(b))"),
            ("a - b", "Plus(+Var(a), -Var(b))"),
            ("min(a, b)", "Fun(min, Var(a), Var(b))"),
            ("a * b + c", "Plus(+Times(*Var(a), *Var(b)), +Var(c))"),
            ("a * (b + c)", "Times(*Var(a), *Plus(+Var(b), +Var(c)))"),
            ("a + b - c", "Plus(+Plus(+Var(a), +Var(b)), -Var(c))"),
            ("a + (b - c)", "Plus(+Var(a), +Plus(+Var(b), -Var(c)))"),
        ]
        
        for s, res in test_data:
            expr = aexpr_parser.parse(s)
            self.assertEqual(repr(expr), res)

    def testBExprParser(self):
        test_data = [
            ("a < 1", "Rel(<, Var(a), Const(1))"),
            ("a == 1 && true", "Logic(&&, Rel(==, Var(a), Const(1)), BConst(True))")
        ]

        for s, res in test_data:
            expr = bexpr_parser.parse(s)
            self.assertEqual(repr(expr), res)

    def assertConditionalInst(self, test_data, res):
        inst = expr.Conditional_Inst()
        for var_name, cond_inst_str in test_data:
            cond_inst = [(bexpr_parser.parse(cond), aexpr_parser.parse(inst))
                         for cond, inst in cond_inst_str]
            inst.add(var_name, cond_inst)

        res_inst = dict()
        for var_name, cond_inst_str in res:
            cond_inst = [(bexpr_parser.parse(cond), aexpr_parser.parse(inst))
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
            ("y", [("a < 1", "(a + 1) - 1"), ("a >= 1", "a + 1")])
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
            ("x1 := 3", "Assign(x1,3)"),
            ("x1 := 3; x2 := 5", "Seq(Assign(x1,3), Assign(x2,5))"),
            ("x1 := 3; x2 := 5; skip", "Seq(Assign(x1,3), Assign(x2,5), Skip())"),
            ("(skip)**", "Loop(Skip())"),
            ("x1?x1", "InputC(x1,x1)"),
            ("x1!x2", "OutputC(x1)"),
            ("<x_dot = x+1, y_dot = y+1 & x < 3> |> [] (x?x --> skip, y!y --> skip)",
             "ODEComm(x, x+1, y, y+1, x < 3, x?x, skip, y!y, skip)"),
            ("x?x --> skip $ y!y --> x := 2", "SelectComm(InputC(x,x),Skip(),OutputC(y),Assign(x,2))"),
            ("@A; @B || @C", "Parallel(Seq(Var(A), Var(B)), Var(C))"),
            ("@A; @B || @C; @D", "Parallel(Seq(Var(A), Var(B)), Seq(Var(C), Var(D)))"),
            ("x == 0 -> @A", "Condition(x == 0, Var(A))"),
            ("x == 0 -> @A; @B", "Seq(Condition(x == 0, Var(A)), Var(B))"),
            ("x == 0 -> (@A; @B)", "Condition(x == 0, Seq(Var(A), Var(B)))"),
            ("x?; y? || z?", "Parallel(Seq(InputC(x), InputC(y)), InputC(z))"),
        ]

        for s, res in test_data:
            hp = hp_parser.parse(s)
            self.assertEqual(repr(hp), res)
            self.assertEqual(str(hp), s)


if __name__ == "__main__":
    unittest.main()
