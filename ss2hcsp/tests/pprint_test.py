"""Unit test for pretty-printing."""

import unittest

from ss2hcsp.hcsp import parser
from ss2hcsp.hcsp.pprint import pprint_lines


class PPrintTest(unittest.TestCase):
    def run_test(self, s, res_list, *, max_line=None):
        hp = parser.hp_parser.parse(s)
        lines, mapping = pprint_lines(hp, max_line=max_line, record_pos=True)
        self.assertEqual(lines, res_list)

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
            "@A || @B",
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

    def test10(self):
        self.run_test("x := 0; (<x_dot = 1 & true> |> [] (p2c!x --> skip); c2p?x)**", [
            'x := 0;',
            '(',
            '  <x_dot = 1 & true> |> [] (',
            '    p2c!x -->',
            '      skip',
            '  );',
            '  c2p?x',
            ')**'
        ])

    def test11(self):
        self.run_test("(wait(2); p2c?x; c2p!x-1)**", [
            '(',
            '  wait(2);',
            '  p2c?x;',
            '  c2p!x-1',
            ')**'
        ])

    def testVanPerPol_continuous1(self):
        self.run_test("t := 0; (ch_x1?x1; ch_x2?x2; ch_x3?x3; t%4 == 0 -> x5 := (1-x3)*(-2.2); t%8 == 0 -> x6 := max(x1, x5); t%10 == 0 -> (x6 > x2 -> x0 := 0; x6 <= x2 -> x0 := 1); ch_x0_0!x0; temp := t; <t_dot = 1 & t < temp+2>)**", [
            't := 0;',
            '(',
            '  ch_x1?x1;',
            '  ch_x2?x2;',
            '  ch_x3?x3;',
            '  t%4 == 0 -> x5 := (1-x3)*(-2.2);',
            '  t%8 == 0 -> x6 := max(x1, x5);',
            '  t%10 == 0 -> (',
            '    x6 > x2 -> x0 := 0;',
            '    x6 <= x2 -> x0 := 1',
            '  );',
            '  ch_x0_0!x0;',
            '  temp := t;',
            '  <t_dot = 1 & t < temp+2>',
            ')**'
        ])

    def testVanPerPol_continuous2(self):
        self.run_test("x2 := 10; x1 := 1; t := 0; (<x2_dot = x1, x1_dot = x0, t_dot = 1 & true> |> [] (ch_x0_0?x0 --> skip, ch_x1!x1 --> skip, ch_x2!x2 --> skip, ch_x3!min(x2, x2) --> skip))**", [
            'x2 := 10;',
            'x1 := 1;',
            't := 0;',
            '(',
            '  <x2_dot = x1, x1_dot = x0, t_dot = 1 & true> |> [] (',
            '    ch_x0_0?x0 -->',
            '      skip',
            '    ch_x1!x1 -->',
            '      skip',
            '    ch_x2!x2 -->',
            '      skip',
            '    ch_x3!min(x2, x2) -->',
            '      skip',
            '  )',
            ')**'            
        ])

    def testVanPerPol_discrete1(self):
        self.run_test("t := 0; (ch_x7?x7; ch_x8?x8; ch_x9?x9; t%4 == 0 -> (x8 >= 20 -> x10 := x7; x8 < 20 -> x10 := x9); ch_x10_0!x10; temp := t; <t_dot = 1 & t < temp+4>)**", [
            't := 0;',
            '(',
            '  ch_x7?x7;',
            '  ch_x8?x8;',
            '  ch_x9?x9;',
            '  t%4 == 0 -> (',
            '    x8 >= 20 -> x10 := x7;',
            '    x8 < 20 -> x10 := x9',
            '  );',
            '  ch_x10_0!x10;',
            '  temp := t;',
            '  <t_dot = 1 & t < temp+4>',
            ')**'
        ])

    def testVanPerPol_discrete2(self):
        self.run_test("t := 0; (ch_x0?x0; ch_x4?x4; t%gcd(in0, in0) == 0 -> x1 := min(x0, x0); t%4 == 0 -> x3 := (1-x1)*2; t%8 == 0 -> x5 := max(x4, x3); t%10 == 0 -> (x5 > x0 -> x6 := 0; x5 <= x0 -> x6 := 1); ch_x6_0!x6; temp := t; <t_dot = 1 & t < temp+gcd(2, and)>)**", [
            't := 0;',
            '(',
            '  ch_x0?x0;',
            '  ch_x4?x4;',
            '  t%gcd(in0, in0) == 0 -> x1 := min(x0, x0);',
            '  t%4 == 0 -> x3 := (1-x1)*2;',
            '  t%8 == 0 -> x5 := max(x4, x3);',
            '  t%10 == 0 -> (',
            '    x5 > x0 -> x6 := 0;',
            '    x5 <= x0 -> x6 := 1',
            '  );',
            '  ch_x6_0!x6;',
            '  temp := t;',
            '  <t_dot = 1 & t < temp+gcd(2, and)>',
            ')**'
        ])


if __name__ == "__main__":
    unittest.main()