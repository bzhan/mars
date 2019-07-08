# Unit tests for expressions

import unittest

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.expr import true_expr, AVar, AConst, PlusExpr
from ss2hcsp.hcsp.parser import aexpr_parser, bexpr_parser


class ExprTest(unittest.TestCase):
    def testAExprParser(self):
        test_data = [
            ("a + 1", "Plus(+Var(a),+Const(1))"),
            ("a * b", "Times(*Var(a),*Var(b))"),
            ("a - b", "Plus(+Var(a),-Var(b))"),
        ]
        
        for s, res in test_data:
            expr = aexpr_parser.parse(s)
            self.assertEqual(repr(expr), res)

    def testBExprParser(self):
        test_data = [
            ("a < 1", "Rel(<,Var(a),Const(1))"),
            ("a == 1 & true", "Logic(&,Rel(==,Var(a),Const(1)),BConst(True))")
        ]

        for s, res in test_data:
            expr = bexpr_parser.parse(s)
            self.assertEqual(repr(expr), res)

    def assertConditionalInst(self, test_data, res):
        inst = expr.Conditional_Inst()
        for var_name, cond_inst_str in test_data:
            cond_inst = [(bexpr_parser.parse(cond), aexpr_parser.parse(inst)) \
                         for cond, inst in cond_inst_str]
            inst.add(var_name, cond_inst)

        res_inst = dict()
        for var_name, cond_inst_str in res:
            cond_inst = [(bexpr_parser.parse(cond), aexpr_parser.parse(inst)) \
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
            ("z", [("a >= 10 & in >= 5 | b >= 10 & in < 5", "x"),
                   ("a < 10 & in >= 5 | b < 10 & in < 5", "y")]),
        ]

        self.assertConditionalInst(test_data, res)



if __name__ == "__main__":
    unittest.main()
