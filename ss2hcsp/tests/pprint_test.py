"""Unit test for pretty-printing."""

import unittest

from ss2hcsp.hcsp import parser
from ss2hcsp.hcsp.pprint import pprint_lines


class PPrintTest(unittest.TestCase):
    def run_test(self, s, res_list, *, max_line=None):
        hp = parser.hp_parser.parse(s)
        self.assertEqual(pprint_lines(hp, max_line=max_line), res_list)

    def test1(self):
        self.run_test("x := 1; y := 2; z := 3", [
            "x := 1;",
            "y := 2;",
            "z := 3"
        ])
    
    def test2(self):
        self.run_test("x == 0 -> (x := 1; y := 2)", [
            "x == 0 -> (",
            "  x := 1;",
            "  y := 2",
            ")"
        ])

    def test3(self):
        self.run_test("x == 0 -> x := 1", [
            "x == 0 -> x := 1"
        ])

    def test4(self):
        self.run_test("x == 0 -> (x := 1; y := 2); x == 1 -> (x := 0; y := 1)", [
            "x == 0 -> (",
            "  x := 1;",
            "  y := 2",
            ");",
            "x == 1 -> (",
            "  x := 0;",
            "  y := 1",
            ")",
        ])

    def test5(self):
        self.run_test("x? $ y?", [
            "x? $",
            "y?"
        ])

    def test6(self):
        self.run_test("x?; y? $ x!; y!", [
            "x?;",
            "  y? $",
            "x!;",
            "  y!"
        ])

    def test7(self):
        self.run_test("@A || @B", [
            "@A ||",
            "@B"
        ])

    def test8(self):
        self.run_test("x := 1; y := 2; z := 3", [
            "x := 1; y := 2; z := 3"
        ], max_line=22)

    def test8(self):
        self.run_test("x := 1; y := 2; z := 3", [
            "x := 1;",
            "y := 2;",
            "z := 3"
        ], max_line=21)

    def test9(self):
        self.run_test("num == 0 -> (tri?E; EL := E; NL := 1; num := 1); num == 1 -> (BC1!E $ BR1?E; EL := push(EL, E); NL := push(NL, 1); num := 1 $ BO1?NULL; num := num+1; NL := pop(NL); NL := push(NL, 1)); num == 2 -> (EL := pop(EL); NL := pop(NL); EL == NULL -> (num := 0); EL != NULL -> (E := top(EL); num := top(NL)))", [
            'num == 0 -> (tri?E; EL := E; NL := 1; num := 1);',
            'num == 1 -> (',
            '  BC1!E $',
            '  BR1?E;',
            '    EL := push(EL, E);',
            '    NL := push(NL, 1);',
            '    num := 1 $',
            '  BO1?NULL;',
            '    num := num+1;',
            '    NL := pop(NL);',
            '    NL := push(NL, 1)',
            ');',
            'num == 2 -> (',
            '  EL := pop(EL);',
            '  NL := pop(NL);',
            '  EL == NULL -> num := 0;',
            '  EL != NULL -> (E := top(EL); num := top(NL))',
            ')'
        ], max_line=50)


if __name__ == "__main__":
    unittest.main()
