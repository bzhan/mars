"""Unit test for hhlpy."""

import unittest
from wolframclient.evaluation import WolframLanguageSession

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.parser import parse_aexpr_with_meta, parse_bexpr_with_meta, parse_hp_with_meta
from hhlpy.hhlpy2 import CmdVerifier
from hhlpy.wolframengine_wrapper import session

path = "D:\Program Files\Wolfram Research\Wolfram Engine\\13.0\MathKernel.exe"
# session = WolframLanguageSession(path)


def runVerify(self, *, pre, hp, post, constants=set(),
              wolfram_engine = False, z3 = True,
              andR_rule=None,
              print_vcs=False, expected_vcs=None):
    # Parse pre-condition, HCSP program, and post-condition
    pre = parse_bexpr_with_meta(pre)
    hp = parse_hp_with_meta(hp)
    post = parse_bexpr_with_meta(post)

    # Initialize the verifier
    verifier = CmdVerifier(pre=pre, hp=hp, post=post, constants=constants, 
                           wolfram_engine=wolfram_engine, z3=z3)
    
    if andR_rule:
        for pos, andR in andR_rule.items():
            if isinstance(andR, str):
                andR = parse_bexpr_with_meta(andR)
            verifier.set_andR_rule(pos, andR)
    # Compute wp and verify
    verifier.compute_wp()

    # Optional: Print verification conditions
    if print_vcs:
        for pos, vcs in verifier.get_all_vcs().items():
            print("%s:" % str(pos))
            for vc in vcs:
                print(vc.expr, 
                "pos:", vc.pos, 
                "seq_labels:", [str(lb) for lb in vc.seq_labels], 
                "nest_label:", vc.nest_label,
                "annot_pos:", vc.annot_pos,
                "categ:", vc.categ,
                "branch_label:", str(vc.branch_label),
                "comp_label:", str(vc.comp_label))

    # Use SMT to verify all verification conditions
    self.assertTrue(verifier.verify())

    # Optional: check the verification conditions are expected
    def is_trivial(vc):
        if isinstance(vc, expr.LogicExpr) and vc.op == "->" and vc.exprs[0] == vc.exprs[1]:
            return True
        else:
            return False

    if expected_vcs:
        for pos, vcs in expected_vcs.items():
            vcs = [parse_bexpr_with_meta(vc) for vc in vcs]
            actual_vcs = [vc.expr for vc in verifier.infos[pos].vcs if not is_trivial(vc.expr)]
            self.assertEqual(set(vcs), set(actual_vcs), 
            "\nExpect: {}\nActual: {}".format([str(vc) for vc in vcs],[str(vc) for vc in actual_vcs]))


class BasicHHLPyTest(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        try:
            session.start()
        except Exception as e:
            session.start()

    @classmethod
    def tearDownClass(cls):
        session.terminate()

    def testVerify1(self):
        # Baisc benchmark, problem 1 
        # {x >= 0} x := x + 1 {x >= 1}
        runVerify(self, pre="x >= 0.12345", hp="x := x+1.23456;", post="x >= 1")
                  #expected_vcs={((), ()): ["x >= 0 -> x + 1 >= 1"]})

    def testVerify2(self):
        # {x >= 0} x := x+1 ++ x := x+2 {x >= 1}
        runVerify(self, pre="x >= 0", hp="x := x+1; ++ x := x+2;", post="x >= 1",
                  expected_vcs={((), ()): ["x >= 0 -> x + 1 >= 1", "x >= 0 -> x + 2 >= 1"]},
                  print_vcs=False)

    def testVerify2_1(self):
        # {x >= 0} x := x+1 ++ x := x+2 ++ x := x + 3 {x >= 1}
        runVerify(self, pre="x >= 0", hp="x := x+1; ++ x := x+2; ++ x := x+3;", post="x >= 1",
        print_vcs=False)

    def testVerify2_2(self):
        # {x >= 0} x := x+1 ++ x := x+2; x := x+1 ++ x := x+2 ++ x := x + 3 {x >= 1}
        runVerify(self, pre="x >= 0", 
                  hp="x := x+1; ++ x := x+2; x := x + 1; x := x+3; ++ x := x+4; ++ x := x+5;", 
                  post="x >= 2",
                print_vcs=False)

    def testVerify3(self):
        # {x >= 0} x := x+1; y := x+2 {x >= 1 & y >= 3}
        runVerify(self, pre="x >= 0", hp="x := x+1; y := x+2;", post="x >= 1 & y >= 3",
                  expected_vcs={((), ()): ["x >= 0 -> x + 1 >= 1 & x + 1 + 2 >= 3"]})

    def testVerify4(self):
        # Basic benchmark, problem 2
        # {x >= 0} x := x+1; x := x+1 ++ y := x+1 {x >= 1}
        runVerify(self, pre="x >= 0", hp="x := x+1; x := x+1; ++ y := x+1;", post="x >= 1",
                  expected_vcs={((), ()): ["x >= 0 -> x + 1 + 1 >= 1", "x >= 0 -> x + 1 >= 1"]})

    def testVerify4_1(self):
        #  {x >= 0} x := x+1; (x := x+1 ++ y := x+1)** {x >= 1}
        runVerify(self, pre="x >= 0", 
                  hp="x := x+1; {x := x+1; ++ y := x+1;}* invariant[x >= 1];", 
                  post="x >= 1",
                  print_vcs=False)

    def testVerify4_2(self):
        # ITE
        # {x == 1}
        # if (x > 0){
        #   if (x > 1){
        #        x := x - 1;
        #   }
        #    else{
        #        skip;
        #    }
        # }
        # else {
        #    x := x + 1;
        # }
        # {x >= 0}
        runVerify(self, pre="x == 1",
                  hp="if (x > 0){ \
                        if (x > 1){ \
                            x := x - 1; \
                        } \
                        else {\
                            skip; \
                        } \
                      } \
                      else { \
                        x := x + 1; \
                      }",
                  post="x >= 0",
                  print_vcs=False)

    def testVerify5(self):
        # {x >= 0} (x := x+1)** {x >= 0}
        runVerify(self, pre="x >= 0", hp="{x := x+1;}* invariant [x >= 0]{{init 1.1(2).skip: z3}};", post="x >= 0", print_vcs=True,
                  expected_vcs={((), (0,)): ["x >= 0 -> x + 1 >= 0"]})

    def testVerify5_1(self):
        # {x >= 0 & y >= 0} (x := x + 1; y := y + 1)** {x >= 0 & y >= 0}
        runVerify(self, pre="x >= 0 & y >= 0",
                  hp="{x := x + 1; y := y + 1;}* invariant[x >= 0] [y >= 0];",
                  post="x >= 0 & y >= 0",
                  print_vcs=False)

    def testVerify5_2(self):
        # {x >= 0} (x := x + 1)**;  x := x + 1; (x := x + 2)** {x >= 1}
        runVerify(self, pre="x >= 0",
                  hp="{x := x + 1;}* invariant[x >= 0]; x := x + 1; {x := x + 2;}* invariant[x >= 1];",
                  post="x >= 1",
                  print_vcs=False)

    def testVerify5_3(self):
         runVerify(self, pre="x >= 0 & y >= 0",
                  hp="{x := x + 1; y := y + 1;}* invariant[x >= 0][y >= 0]; \
                      x := x + 1; \
                      y := y + 1; \
                      {x := x + 2; y := y + 2;}* invariant[x >= 1] [y >= 1];",
                  post="x >= 1 & y >= 1",
                  print_vcs=False)

    def testVerify6(self):
        # Basic benchmark, problem 3
        # {x >= 0} x := x+1; (x := x+1)** {x >= 1}
        # Invariant for loop is x >= 1.
        runVerify(self, pre="x >= 0", hp="x := x+1; {x := x+1;}* invariant [x >= 1];", post="x >= 1",
                  expected_vcs={((), ()): ["x >= 0 -> x + 1 >= 1"],
                                ((1,), (0,)): ["x >= 1 -> x + 1 >= 1"]})

    def testVerify7(self):
        # {x >= 0} <x_dot=2 & x < 10> {x >= 0}
        # Use the boundary x == 10 to imply the post x >= 0.
        # No invariant attached.
        runVerify(self, pre="x >= 0", hp="<x_dot=2 & x < 10>", post="x >= 0", print_vcs=True)

    # TODO: 
    # def testVerify7_1(self):
    #     # {true} <x_dot = 2 & x < 10> {true}
    #     runVerify(self, pre="true", hp="<x_dot = 2 & x < 10>", post="true", print_vcs=True)

    def testVerify7_2(self):
        # {x > 2} <x_dot = 1 & x < 1> {x > 2}
        runVerify(self, pre="x > 2",    
                  hp="<x_dot = 1 & x < 1> invariant [false];", 
                  post="x > 2",
                  print_vcs=False)

    def testVerify8(self):
        # {x * x + y * y == 1} <x_dot=y, y_dot=-x & x > 0> {x * x + y * y = 1}
        # Invariant for ODE is x * x + y * y == 1
        runVerify(self, pre="x * x + y * y == 1", 
                  hp="<x_dot=y, y_dot=-x & x > 0> \
                      invariant [x * x + y * y == 1] {di};",
                  post="x * x + y * y == 1",
                  print_vcs=True)

    def testVerify9(self):
        # Basic benchmark, problem 4
        # {x >= 0} x := x+1; <x_dot=2 & x < 10> {x >= 1}
        runVerify(self, pre="x >= 0", 
                  hp="x := x+1; <x_dot=2 & x < 10> invariant [x >= 1];", 
                  post="x >= 1",
                  print_vcs=False)

    def testVerify9_1(self):
        # Basic bencmark, problem10
        # Several ODEs in sequence.
        # {x > 0} <x_dot = 5>; <x_dot = 2> {x > 0}
        runVerify(self, pre="x > 0",
                  hp="<x_dot = 5 & x < 1> invariant [x > 0]; \
                      <x_dot = 2 & x < 2> invariant [x > 0];",
                  post="x > 0",
                  print_vcs=True)

    def testVerify10(self):
        # Basic Benchmark, problem5
        # {x >= 0} x := x+1; x := {x >= 1} {x >= 1}
        runVerify(self, pre="x >= 0", hp="x := x+1; x := *(x >= 1);", post="x >= 1",
                  expected_vcs={((), ()): ["x >= 0 -> x0 >= 1 -> x0 >= 1"]})

    def testVerify11(self):
        # {x0 >= 0} x := x+1; x := {x >= 1} {x >= 1}
        runVerify(self, pre="x0 >= 0", hp="x := x+1; x := *(x >= 1);", post="x >= 1",
                  expected_vcs={((), ()): ["x0 >= 0 -> x0 >= 0 -> x1 >= 1 -> x1 >= 1"]})

    def testVerify12(self):
        # {x >= 0} x := x+1; y := {y >= x} {y >= 1}
        runVerify(self, pre="x >= 0", hp="x := x+1; y := *(y >= x);", post="y >= 1",
                  expected_vcs={((), ()): ["x >= 0 -> y0 >= x + 1 -> y0 >= 1"]})

    def testVerify13(self):
        # {x >= 0} x := x+1; y := {y >= x}; y := {y >= x + 1} {y >= 2}
        runVerify(self, pre="x >= 0", hp="x := x+1; y := *(y >= x); y := *(y >= x+1);", post="y >= 2",
                  expected_vcs={((), ()): ["x >= 0 -> y1 >= x + 1 ->y0 >= x + 1 + 1 -> y0 >= 2"]})

    # TODO: Basic benchmark problem 6 is hard to translate into HCSP program.

    def testVerify14(self):
        # Basic Benchmark, problem7
        # confusion about the inv of loop
        # {x >= 0 & y >= 1} 

        # x := x + 1; 
        # (x := x + 1)**@invariant(x >= 1) ++ y:= x + 1; 
        # <y_dot = 2>@invariant(y >= 1);
        #  x := y

        # {x >= 1}
        runVerify(self, pre="x >= 0 & y >= 1", 
                  hp="x := x + 1; \
                    {x := x + 1;}* invariant [x >= 1] [y >= 1]; ++ y := x + 1; \
                    <y_dot = 2 & y < 10> invariant [y >= 1]; \
                    x := y;", 
                  post="x >= 1") 

    def testVerify14_1(self):
         # {x >= 0 & y >= 1} 

        # x := x + 1; 
        # (x := x + 1)**@invariant(x >= 1) ++ y:= x + 1; 

        # {x >= 1 & y >= 1}
        runVerify(self, pre="x >= 0 & y >= 1", 
                  hp="x := x + 1; \
                    {x := x + 1;}* invariant [x >= 1] [y >= 1]; ++ y := x + 1;", 
                  post="x >= 1 & y >= 1",
                  print_vcs=False) 

    def testVerify15(self):
        # Basic benchmark, problem8
        # {x > 0 & y > 0} 

        # <x_dot = 5 & x < 10>@invariant(x > 0); 
        # (x := x + 3)**@invariant(x > 0) ++ y := x

        # {x > 0 & y > 0}
        runVerify(self, pre="x > 0 & y > 0", 
                  hp="<x_dot = 5 & x < 10> invariant [x > 0] [y > 0]; \
                      {x := x + 3;}* invariant [x > 0] [y > 0]; ++ y := x;", 
                  post="x > 0 & y > 0")

    def testVerify16(self):
        # Test case containing ghost variables
        # Basic benchmark, problem15
        # dG Rule
        # {x > 0} <x_dot = -x> {x > 0}
        runVerify(self, pre="x > 0", hp="t := 0; <x_dot = -x, t_dot=1 & t < 1> invariant ghost y [x * y * y == 1];", post="x > 0",
                expected_vcs={((), ()): ["x > 0 -> 0 < 1 -> (\exists y. x * y * y == 1)", \
                                         "x > 0 -> 0 >= 1 -> x > 0"],
                              ((1,), ()): ["(\exists y. x * y * y == 1) & t == 1 -> x > 0"]})

    def testVerify17(self):
        # Basic benchmark, problem9
        # dG Rule
        # {x>0 & y>0} 
        #
        #   t := 0; 
        #   <x_dot = -x, t_dot = 1 & t < 1>;
        #   (x := x+3)**@invariant(x > 0) ++ y := x 
        #
        # {x>0 & y>0}
        runVerify(self, pre="x > 0 & y > 0", 
                  hp="t := 0; \
                      <x_dot = -x, t_dot = 1 & t < 1> \
                      invariant \
                          ghost z \
                          [x * z * z == 1] \
                          [x > 0] \
                          [y > 0]; \
                      {x := x+3;}* invariant [x > 0] [y > 0]; ++ y := x;",
                  post="x > 0 & y > 0")

    def testVerify18(self):
        # Basic bencmark, problem10
        # dG Rule
        # {x > 0} <x_dot = 5>; <x_dot = 2>; <x_dot = x> {x > 0}
        runVerify(self, pre="x > 0",
                  hp="<x_dot = 5 & x < 1> invariant [x > 0]; \
                      <x_dot = 2 & x < 2> invariant [x > 0]; \
                      <x_dot = x & x < 5> invariant ghost y [x * y * y == 1];",
                  post="x > 0",
                  print_vcs=False)

    def testVerify19(self):
        # Basic benchmark, problem11
        # {x = 0} <x_dot = 1 & x < 10> {x >= 0}
        runVerify(self, pre="x == 0", hp="<x_dot = 1 & x < 10> invariant [x >= 0];", post="x >= 0",)

    def testVerify20(self):
        # Basic benchmark, problem12
        # dC Rule
        # {x >= 0 & y >= 0} <x_dot = y> {x >= 0}
        runVerify(self, pre="x >= 0 & y >= 0", 
                  hp="<x_dot = y & x < 10> invariant [y >= 0] [x >= 0];", 
                  post="x >= 0",
                  expected_vcs={((), ()): ["y >= 0 -> x >= 0 & y >= 0 -> \
                                            x < 10 -> y >= 0 & x >= 0",
                                           "y >= 0 -> x >= 0 & y >= 0 -> \
                                            x >= 10 -> x >= 0",
                                           "y >= 0 -> (y >= 0 & x >= 0) & x == 10 ->\
                                            x >= 0"]})

    def testVerify21(self):
        # Basic benchmark, problem13
        # dC Rule
        # {x >= 0 & y >= 0 & z >= 0} <x_dot = y, y_dot = z & x < 10> {x >= 0}
        runVerify(self, pre="x >= 0 & y >= 0 & z >= 0", 
                  hp="<x_dot = y, y_dot = z & x < 10> invariant [z >= 0] [y >= 0] [x >= 0];", post="x >= 0")


    def testVerify22(self):
        # Basic benchmark, problem14
        # dC Rule
        # {x >= 0 & y >= 0 & z >= 0 & j >= 0} 
        # <x_dot = y, y_dot = z, z_dot = j, j_dot = j * j & x < 10>
        # {x >= 0}
        runVerify(self, pre="x >= 0 & y >= 0 & z >= 0 & j >= 0",
                  hp="<x_dot = y, y_dot = z, z_dot = j, j_dot = j * j & x < 10> \
                      invariant [j >= 0] [z >= 0] [y >= 0] [x >= 0];", post="x >= 0")

    # Basic benchmark problem15 is verified in testVerify16

    def testVerify23(self):
        # Basic benchmark, problem16
        # dbx inequality Rule
        # {x > 0} t := 0; <x_dot = -x + 1, t_dot = 1 & t < 10> {x > 0}
        runVerify(self, pre="x > 0", hp="t := 0; <x_dot = -x + 1, t_dot = 1 & t < 10> invariant [x > 0] {dbx -1};", post="x > 0")

    def testVerify24(self):
        # Basic benchmark, problem17
        # {x > 0 & y > 0} t := 0; <x_dot = -y * x, t_dot = 1 & t < 10> {x > 0}
        runVerify(self, pre="x > 0 & y > 0", 
                  hp="t := 0; \
                      <x_dot = -y * x, t_dot = 1 & t < 10> \
                      invariant ghost z [x * z * z == 1];", 
                  post="x > 0",
                  expected_vcs={((), ()): ["y > 0 -> x > 0 & y > 0 -> \
                                            (0 < 10 -> (\exists z. x * z * z == 1))",
                                            "y > 0 -> x > 0 & y > 0 -> \
                                            (0 >= 10 -> x > 0)"],
                                ((1,), ()): ["y > 0 -> (\exists z. x * z * z == 1) & t == 10 \
                                              -> x > 0"]})

    def testVerify25(self):
        # Basic benchmark, problem 18
        # {x >= 0} <x_dot = x & x < 10> {x >= 0}
        # dG and Conjunction Rule
        # Question remained: the form of ghost_equations.
        runVerify(self, pre="x >= 0", 
                hp="<x_dot = x & x < 10> \
                    invariant \
                        ghost <y_dot = - y> \
                        ghost z \
                        [y * z * z == 1] \
                        [y > 0] \
                        [x * y >= 0];",
                post="x >= 0")

    def testVerify26(self):
        # Basic benchmark, problem 19
        # dC Rule
        # {x >= 0 & y >= 0} <x_dot = y, y_dot = y * y & x < 10> {x >= 0}
        runVerify(self, pre="x >= 0 & y >= 0",
                  hp="<x_dot = y, y_dot = y * y & x < 10> invariant [y >= 0] [x >= 0];", post="x >= 0")

    # TODO: Basic benchmark, problem 20. The expression is not a polynomial.

    def testVerify28(self):
        # Basic benchmark, problem 21
        # dI Rule
        # {x >= 1} <x_dot = x ^ 2 + 2 * x ^ 4 & x < 10> {x ^ 3 >= x ^ 2}
        runVerify(self, pre="x >= 1", 
                  hp="<x_dot = x ^ 2 + 2 * x ^ 4 & x < 10> invariant [x >= 1];",
                  post="x ^ 3 >= x ^ 2")

    def testVerify29(self):
        # Basic benchmark, problem 22
        # dI Rule
        # {x * x + y * y == 1} t := 0; <x_dot = -y, y_dot = x, t_dot = 1 & t < 10> {x * x + y * y == 1}
        runVerify(self, pre="x * x + y * y == 1", 
                  hp="t := 0; <x_dot = -y, y_dot = x, t_dot = 1 & t < 10> invariant [x * x + y * y == 1];",
                  post="x * x + y * y == 1")

    def testVerify30(self):
        # Basic benchmark, problem 23
        # dC and dI rule
        # {x^2 + y^2 == 1 & e == x} 
        # t:=0; <x_dot = -y, y_dot = e, e_dot = -y, t_dot = 1 & t < 10>
        # {x^2 + y^2 == 1 & e == x}
        runVerify(self, pre="x^2 + y^2 == 1 & e == x",
                  hp="t:=0; \
                      <x_dot = -y, y_dot = e, e_dot = -y, t_dot = 1 & t < 10> \
                      invariant \
                        [e == x] [x^2 + y^2 == 1];",
                  post="x^2 + y^2 == 1 & e == x")

    def testVerify31(self):
        # Basic benchmark, problem 24
        # Conjunction rule and dI rule
        # {d1^2 + d2^2 == w^2 * p^2 & d1 == -w * x2 & d2 == w * x1}
        # t := 0; <x1_dot = d1, x2_dot = d2, d1_dot = -w * d2, d2_dot = w * d1, t_dot = 1 & t < 10>
        # {d1^2 + d2^2 == w^2 * p^2 & d1 == -w * x2 & d2 == w * x1}
        runVerify(self, pre="d1^2 + d2^2 == w^2 * p^2 & d1 == -w * x2 & d2 == w * x1",
                  hp="t := 0; \
                      <x1_dot = d1, x2_dot = d2, d1_dot = -w * d2, d2_dot = w * d1, t_dot = 1 & t < 10>\
                      invariant [d1^2 + d2^2 == w^2 * p^2] [d1 == -w * x2 & d2 == w * x1];",
                  post="d1^2 + d2^2 == w^2 * p^2 & d1 == -w * x2 & d2 == w * x1")

    def testVerify32(self):
        # Benchmark, problem 25
        # dC rule? and dI rule
        # {w >= 0 & x == 0 & y == 3} 
        # t := 0; <x_dot = y, y_dot = -w^2 * x - 2 * w * y, t_dot = 1 & t < 10>
        # {w^2 * x^2 + y^2 <= 9}
        runVerify(self, pre="w >= 0 & x == 0 & y == 3",
                  hp="t := 0; \
                      <x_dot = y, y_dot = -w^2 * x - 2 * w * y, t_dot = 1 & t < 10> \
                      invariant [w >= 0] [w^2 * x^2 + y^2 <= 9];",
                  post="w^2 * x^2 + y^2 <= 9")

    def testVerify33(self):
    # Benchmark, problem 26
    # Barrier Rule
    # {x^3 > 5 & y > 2} 
    # t := 0; <x_dot = x^3 + x^4, y_dot = 5 * y + y^2, t_dot = 1 & t < 10>
    # {x^3 > 5 & y > 2}
        runVerify(self, pre="x^3 > 5 & y > 2",
                  hp="t := 0; \
                      <x_dot = x^3 + x^4, y_dot = 5 * y + y^2, t_dot = 1 & t < 10> \
                      invariant [x^3 > 5] {bc} [y > 2] {bc};",
                  post="x^3 > 5 & y > 2")

    def testVerify34(self):
        # Benchmark, problem 27
        # dW rule
        # {x >= 1 & y == 10 & z == -2} 
        # <x_dot = y, y_dot = z + y^2 - y & y > 0>
        # {x >= 1 & y >= 0}
        runVerify(self, pre="x >= 1 & y == 10 & z == -2", 
                  hp="<x_dot = y, y_dot = z + y^2 - y & y > 0> \
                      invariant \
                        [x >= 1];",
                  post="x >= 1 & y >= 0",
                  expected_vcs={((),()): ["z == -2 -> x >= 1 & y == 0 -> x >= 1 & y >= 0", 
                                          # `y == 0` comes from implicit dW
                                          "z == -2 -> y > 0 -> y >= 0", 
                                          # This is from dI (condition implies differential of invariant)
                                          "z == -2 -> x >= 1 & y == 10 & z == -2 ->\
                                          (y > 0 -> x >= 1)", 
                                          "z == -2 -> x >= 1 & y == 10 & z == -2 -> \
                                          (y <= 0 -> x >= 1 & y >= 0)"]}) 
                                          # `y <= 0 -> x >= 1 & y >= 0` is the dW precondition

    def testVerify35(self):
        # Benchmark, problem 28
        # {x1^4 * x2^2 + x1^2 * x2^4 - 3 * x1^2 * x2^2 + 1 <= c}
        # t := 0;
        # <x1_dot = 2 * x1^4 * x2 + 4 * x1^2 * x2^3 - 6 * x1^2 * x2, 
        # x2_dot = -4 * x1^3 * x2^2 - 2 * x1 * x2^4 + 6 * x1 * x2^2, 
        # t_dot = 1 & t < 10>
        # {x1^4 * x2^2 + x1^2 * x2^4 - 3 * x1^2 * x2^2 + 1 <= c}
        runVerify(self, pre="x1^4 * x2^2 + x1^2 * x2^4 - 3 * x1^2 * x2^2 + 1 <= c",
                  hp="t := 0;\
                  <x1_dot = 2 * x1^4 * x2 + 4 * x1^2 * x2^3 - 6 * x1^2 * x2, \
                   x2_dot = -4 * x1^3 * x2^2 - 2 * x1 * x2^4 + 6 * x1 * x2^2, \
                   t_dot = 1 & t < 10> \
                       invariant [x1^4 * x2^2 + x1^2 * x2^4 - 3 * x1^2 * x2^2 + 1 <= c];",
                  post="x1^4 * x2^2 + x1^2 * x2^4 - 3 * x1^2 * x2^2 + 1 <= c")

    def testVerify36(self):
        # Benchmark, problem 29
        # constants: {"B()"}
        # {x + z == 0} 
        # t := 0; <x_dot = (A * x^2 + B() * x), z_dot = A * z * x + B() * z, t_dot = 1 & t < 10> 
        # {0 == -x - z}
        runVerify(self, pre="x + z == 0", 
                  hp="t := 0; <x_dot = (A * x^2 + B() * x), z_dot = A * z * x + B() * z, t_dot = 1 & t < 10> invariant [x + z == 0] {dbx};",
                  post="0 == -x - z",)
                #   constants={"B()"})

    # TODO: Benchmark, problem 30, 32 are hard to translate into hcsp programs.

    def testVerify38(self):
        # Basic benchmark, problem 31
        # {x + z >= 0} 
        # <x_dot = x^2, z_dot = z * x + y & y > x^2>
        # {x + z >= 0}
        # tag, info, str1 = 
        runVerify(self, pre="x + z >= 0",
                  hp="<x_dot = x^2, z_dot = z * x + y & y > x^2> invariant [x + z >= 0] {dbx x};",
                  post="x + z >= 0")

    def testVerify40(self):
        # Condition rule
        # {x >= 0} x >= -2 -> (x := x+1 ++ x := x+2; x := x+1) {x >= 2}
        runVerify(self, pre="x >= 0", hp="if (x >= -2) { x := x+1; ++ x := x+2; x := x+1;}", post="x >= 2")

    def testVerify41(self):
        # Benchmark, problem 33
        # {w>=0 & d>=0
        #   & -2<=a&a<=2
        #   & b^2>=1/3
        #   & w^2*x^2+y^2 <= c}
        #   [{
        #     {x'=y, y'=-w^2*x-2*d*w*y};
        #     {  { ?(x=y*a); w:=2*w; d:=d/2; c := c * ((2*w)^2+1^2) / (w^2+1^2); }
        #     ++ { ?(x=y*b); w:=w/2; d:=2*d; c := c * (w^2+1^2) / ((2*w^2)+1^2); }
        #     ++ { ?true; } }
        #    }*@invariant(w^2*x^2+y^2<=c&d>=0&w>=0)
        #   ] 
        # {w^2*x^2+y^2 <= c}
        runVerify(self, 
                  pre="w >= 0 & d >= 0 & -2 <= a & a <= 2 & b^2 >= 1/3 & w^2 * x^2 + y^2 <= c",
                  hp="t := 0; \
                      <x_dot = y, y_dot = -w^2 * x - 2 * d * w * y, t_dot = 1 & t < 10> \
                      invariant [w >= 0 & d >= 0] [w^2 * x^2 + y^2 <= c] [d >= 0] [w >= 0] [-2 <= a] [a <= 2] [b^2 >= 1/3]; \
                      {if (x == y * a) {w := 2 * w; d := d/2; c := c * ((2 * w)^2 + 1^2) / (w^2 + 1^2);}\
                      ++ if (x == y * b) {w := w/2; d := 2 * d; c := c * (w^2 + 1^2) / ((2 * w^2) + 1^2);} \
                      ++ skip;}* \
                      invariant [w^2 * x^2 + y^2 <= c] [d >= 0] [w >= 0] [-2 <= a] [a <= 2] [b^2 >= 1/3];",
                  post="w^2 * x^2 + y^2 <= c")

    def testVerify42(self):
        runVerify(self,
                  pre="w >= 0 & d >= 0 & -2 <= a & a <= 2 & b^2 >= 1/3 & w^2 * x^2 + y^2 <= c",
                  hp=
                   "{if (x == y * a) {w := 2 * w; d := d/2; c := c * ((2 * w)^2 + 1^2) / (w^2 + 1^2);}\
                  ++ if (x == y * b) {w := w/2; d := 2*d; c := c * (w^2+1^2) / ((2*w^2)+1^2);}}*\
                  invariant [w^2 * x^2 + y^2 <= c] [d >= 0] [w >= 0] [-2 <= a] [a <= 2] [b^2 >= 1/3];",
                  post="w^2 * x^2 + y^2 <= c")


    def testVerify43(self):
        # Basic benchmark, problem 34
        # {x^3 >= -1} <x_dot = (x-3)^4 + a & a > 0> x^3 >= -1
        runVerify(self, pre="x^3 >= -1", hp="<x_dot = (x-3)^4 + a & a > 0> invariant [x^3 >= -1];", post="x^3 >= -1")

    def testVerify44(self):
        # Basic benchmark, problem 35
        # {x1 + x2^2 / 2 == a} 
        # t := 0; <x1_dot = x1 * x2 , x2_dot = -x1, t_dot = 1 & t < 10> 
        # {x1 + x2^2 / 2 == a}
        runVerify(self, pre="x1 + x2^2 / 2 == a",
                  hp="t := 0; <x1_dot = x1 * x2 , x2_dot = -x1, t_dot = 1 & t < 10>\
                        invariant [x1 + x2^2 / 2 == a];",
                  post="x1 + x2^2 / 2 == a")

    def testVerify45(self):
        # Basic benchmark, problem 36
        # {x1^2 / 2 - x2^2 / 2 >= a}
        # <x1_dot = x2 + x1 * x2^2, x2_dot = -x1 + x1^2 * x2 & x1 > 0 & x2 > 0>
        # {x1^2 / 2 - x2^2 / 2 >= a}
        runVerify(self, pre="x1^2 / 2 - x2^2 / 2 >= a", 
                  hp="<x1_dot = x2 + x1 * x2^2, x2_dot = -x1 + x1^2 * x2 & x1 > 0 & x2 > 0>\
                        invariant [x1^2 / 2 - x2^2 / 2 >= a];",
                  post="x1^2 / 2 - x2^2 / 2 >= a")

    def testVerify46(self):
        # Basic benchmark, problem 37
        # {-x1 * x2 >= a}
        # t := 0; <x1_dot = x1 - x2 + x1 * x2, x2_dot = -x2 - x2^2, t_dot = 1 & t < 10>
        # {-x1 * x2 >= a}
        runVerify(self, pre="-x1 * x2 >= a", 
                  hp="t := 0; <x1_dot = x1 - x2 + x1 * x2, x2_dot = -x2 - x2^2, t_dot = 1 & t < 10> \
                      invariant [-x1 * x2 >= a];",
                  post="-x1 * x2 >= a")

    def testVerify47(self):
        # Basic benchmark, problem 38
        # {2 * x^3 >= 1/4} t := 0; <x_dot = x^2 + x^4, t_dot = 1 & t < 10> {2 * x^3 >= 1/4}
        runVerify(self, pre="2 * x^3 >= 1/4",
                  hp="t := 0; <x_dot = x^2 + x^4, t_dot = 1 & t < 10> \
                        invariant [2 * x^3 >= 1/4];",
                  post="2 * x^3 >= 1/4")

    def testVerify48(self):
        # Basic benchmark, problem 39
        # {x^3 >= -1 & y^5 >= 0} 
        # t := 0; <x_dot = (x - 3)^4 + y^5, y_dot = y^2, t_dot = 1 & t < 10> 
        # {x^3 >= -1 & y^5 >= 0}
        runVerify(self, pre="x^3 >= -1 & y^5 >= 0",
                  hp="t := 0; \
                      <x_dot = (x - 3)^4 + y^5, y_dot = y^2, t_dot = 1 & t < 10> \
                      invariant \
                        [y^5 >= 0] \
                        [x^3 >= -1];",
                  post="x^3 >= -1 & y^5 >= 0")

    def testVerify49(self):
        # Basic benchmark, problem 40
        # A is a constant.
        # {v >= 0 & A > 0} <x_dot = v, v_dot = A & x < 10> {v >= 0}
        runVerify(self, pre="v >= 0 & A > 0", 
                  hp="<x_dot = v, v_dot = A & x < 10> \
                      invariant [A > 0] [v >= 0];",
                  post="v >= 0", )
                #   constants={'A'})

    def testVerify50(self):
        # Basic bencnmark, problem 41
        # A, B are constants.
        # {v >= 0 & A > 0 & B > 0}
        # (
        #  a := A ++ a := 0 ++ a := -B; 
        #  <x_dot = v, v_dot = a & v > 0>
        # )**
        # {v >= 0}
        runVerify(self, pre="v >= 0 & A > 0 & B > 0",
                  hp="{a := A; ++ a := 0; ++ a := -B; <x_dot = v, v_dot = a & v > 0> invariant [true];}*\
                      invariant [v >= 0];",
                  post="v >= 0",)
                #   constants={'A', 'B'})

    def testVerify51(self):
        # ITE
        # {x >= 0} if (x < 5) x := x + 1; else x := x; {x > 0}
        runVerify(self, pre="x >= 0", hp="if (x < 5) { x := x + 1; } else { x := x; }",
                  post="x > 0")

    def testVerify52(self):
        # Basic benchmark, problem 42 
        # constants = {'A', 'B', 'S'}

        # another version
        # {v >= 0 & A > 0 & B > 0 & x + v^2 / (2*B) < S}
        # 
        # (if x + v^2 / (2*B) < S 
        #     then a := A; <x_dot = v, v_dot = a & v > 0 & x + v^2 / (2*B) < S>
        #  elif v == 0
        #     then a := 0
        #  else a := -B; <x_dot = v, v_dot = a & v > 0>
        #  endif
        # )**
        #
        # {x <= S}
        runVerify(self, pre="v >= 0 & A > 0 & B > 0 & x + v^2 / (2*B) < S",
                  hp="{\
                        if (x + v^2 / (2*B) < S) {\
                            a := A; \
                            <x_dot = v, v_dot = a & v > 0 & x + v^2 / (2*B) < S> \
                                invariant [true]; \
                        } else if (v == 0) { \
                            a := 0; \
                        } else {\
                            a := -B; \
                            <x_dot = v, v_dot = a & v > 0> \
                            invariant [a == -B] [x+v^2/(2*B) <= S]; \
                        } \
                      }* \
                      invariant [v >= 0] [x+v^2/(2*B) <= S];",
                  post="x <= S",)
                #   constants={'A', 'B', 'S'})

    def testVerify52_1(self):
         runVerify(self, pre="v >= 0 & A > 0 & B > 0 & x + v^2 / (2*B) < S",
                  hp="{a := -B; \
                       <x_dot = v, v_dot = a & v > 0> \
                           invariant [a == -B] [x+v^2/(2*B) <= S]; \
                      }* \
                      invariant [x+v^2/(2*B) <= S] [v >= 0];",
                  post="x <= S")

    def testVerify53(self):
        # Basic benchmark, problem 43
        # contants = {'A', 'V'}
        # {v <= V & A > 0}
        #
        # (   if v == V then a := 0 else a := A endif
        #  ++ if v != V then a := A else a := 0 endif;

        #     <x_dot = v, v_dot = a & v <= V>
        # )**@invariant(v <= V)
        #
        # {v <= V}
        runVerify(self, pre="v <= V & A > 0", 
                  hp="{   if (v == V) { a := 0; } else { a := A; } \
                       ++ if (v != V) { a := A; } else { a := 0; } \
                          <x_dot = v, v_dot = a & v < V> \
                          invariant [true]; \
                      }* \
                      invariant [v <= V];",
                  post="v <= V",)
                #   constants={'A', 'V'})

    def testVerify54(self):
        # Basic benchmark, problem 44
        # constants = {'A', 'V'}
        # {v <= V & A > 0}
        #
        # (a := A;
        #  <x_dot = v, v_dot = a & v < V>
        # )**
        #
        # {v <= V}
        runVerify(self, pre="v <= V & A > 0", 
                  hp="{a := A;\
                      <x_dot = v, v_dot = a & v < V>\
                      invariant [true]; \
                       }*\
                       invariant [v <= V];",
                  post="v <= V",)
                #   constants={'A', 'V'})

    def testVerify55(self):
        # Basic benchmark, problem 45
        # constants = {'A', 'V'}
        # {v <= V & A > 0}
        #     (
        #         if v == V then a := 0; t := 0; <x_dot = v, v_dot = a & t < 10>
        #         else a := A; <x_dot = v, v_dot = a & v < V>
        #         endif        
        #     )**@invariant(v <= V)
        # {v <= V}
        runVerify(self, pre="v <= V & A > 0",
                  hp="{if (v == V) { \
                           a := 0; t := 0; \
                           <x_dot = v, v_dot = a & t < 10> \
                           invariant [a == 0] [v <= V];\
                       } else { \
                           a := A; \
                           <x_dot = v, v_dot = a & v < V> \
                           invariant [true];\
                       } \
                       }* \
                       invariant [v <= V];",
                  post="v <= V",
                  constants={'A', 'V'}
                ) 

    def testVerify36_1(self):
        # Benchmark, problem 29
        # constants: {"B()"}
        # {x + z == 0} 
        # t := 0; <x_dot = (A * x^2 + B() * x), z_dot = A * z * x + B() * z, t_dot = 1 & t < 10> 
        # {0 == -x - z}
        runVerify(self, pre="x + z == 0", 
                  hp="t := 0; <x_dot = (A * x^2 + B() * x), z_dot = A * z * x + B() * z, t_dot = 1 & t < 10> invariant [x + z == 0] {dbx};",
                  post="0 == -x - z",
                  constants={"B()"},
                  wolfram_engine=True)

    def testVerify56(self):
        # Basic benchcmark, problem 46
        # constants = {'A', 'B', 'S', 'ep'}
        # {v >= 0 & A > 0 & B > 0 & x + v^2 / (2*B) <= S & ep > 0}
        #     (      if x+v^2/(2*B) + (A/B+1)*(A/2*ep^2+ep*v) <= S then a := A 
        #               else a := -B endif
        #         ++ if v == 0 then a := 0 else a := -B endif
        #         ++ a := -B
        #         ;

        #         c := 0;
        #         < x_dot = v, v_dot = a, c_dot = 1 & v > 0 & c < ep >
        #     )**@invariant(v >= 0 & x+v^2/(2*B) <= S)
        # {x <= S}
        runVerify(self,  pre="v >= 0 & A > 0 & B > 0 & x + v^2 / (2*B) <= S & ep > 0",
                  hp="{   if (x+v^2/(2*B) + (A/B+1)*(A/2*ep^2+ep*v) <= S) { a := A; } else { a := -B; } \
                       ++ if (v == 0) { a := 0; } else { a := -B; } \
                       ++ a := -B; \
                        c := 0; \
                        < x_dot = v, v_dot = a, c_dot = 1 & v > 0 & c < ep > \
                        invariant [x+v^2/(2*B) <= S] {sln};\
                     }* \
                     invariant [v >= 0] [x+v^2/(2*B) <= S];",
                  post="x <= S",
                #   constants={'A', 'B', 'S', 'ep'},
                  wolfram_engine=True)

    def testVerify56_1(self):
        # Test the andR Rule
        # {x >= 1 & y >= 0 & a == 1}
        #   (x := x + a)**
        # {x >= 0 & y >= 0}
        runVerify(self, pre="x >= 1 & y >= 0 & a == 1",
                  hp="{x := x + a; }* invariant [x >= 0] [y >= 0];",
                  post="x >= 0 & y >= 0",
                  andR_rule={((), ()): "true"})

    def testVerify57(self):
        # Basic benchcmark, problem 47
        # constants = {'A', 'B', 'S', 'ep'}
        # {v >= 0 & A > 0 & B > 0 & x + v^2 / (2*B) <= S & ep > 0}
        #     (      if x+v^2/(2*B) + (A/B+1)*(A/2*ep^2+ep*v) <= S then a := {-B <= a & a <= A}
        #              else a := -B endif
        #         ++ if v == 0 then a := 0 else a := -B endif
        #         ++ a := -B
        #         ;

        #         c := 0;
        #         < x_dot = v, v_dot = a, c_dot = 1 & v > 0 & c < ep >
        #     )**@invariant(v >= 0 & x+v^2/(2*B) <= S)
        # {x <= S}
        runVerify(self,  pre="v >= 0 & A > 0 & B > 0 & x + v^2 / (2*B) <= S & ep > 0",
                  hp="{   if (x+v^2/(2*B) + (A/B+1)*(A/2*ep^2+ep*v) <= S) {\
                            a := *(-B <= a & a <= A); \
                          } else { a := -B; } \
                       ++ if (v == 0) { a := 0; } else { a := -B; } \
                       ++ a := -B; \
                        c := 0; \
                        < x_dot = v, v_dot = a, c_dot = 1 & v > 0 & c < ep > \
                        invariant [x+v^2/(2*B) <= S] {sln};\
                      }* \
                      invariant [v >= 0] [x+v^2/(2*B) <= S];",
                  post="x <= S",
                  constants={'A', 'B', 'S', 'ep'},
                  andR_rule={((), ()): "true"},
                  wolfram_engine=True)

    def testVerify58(self):
        # Basic benchmark, problem 48
        #         v >= 0 & A > 0 & B >= b & b > 0 & x+v^2/(2*b) <= S & ep > 0
        #  -> [
        #       { {   ?x+v^2/(2*b) + (A/b+1)*(A/2*ep^2+ep*v) <= S; a :=*; ?-B <= a & a <= A;
        #          ++ ?v=0; a := 0;
        #          ++ a :=*; ?-B <=a & a <= -b;
        #         };

        #         c := 0;
        #         { x' = v, v' = a, c' = 1 & v >= 0 & c <= ep }
        #       }*@invariant(v >= 0 & x+v^2/(2*b) <= S)
        #     ] x <= S
        runVerify(self, pre="v >= 0 & A > 0 & B >= b & b > 0 & x+v^2/(2*b) <= S & ep > 0",
                  hp="{   if (x+v^2/(2*b) + (A/b+1)*(A/2*ep^2+ep*v) <= S) {\
                            a := *(-B <= a & a <= A); \
                          } else { \
                            a := *(-B <= a & a <= -b); \
                          } \
                       ++ if (v == 0) { a := 0; } else { a := *(-B <= a & a <= -b); } \
                       ++ a := *(-B <= a & a <= -b); \
                        c := 0; \
                        < x_dot = v, v_dot = a, c_dot = 1 & v > 0 & c < ep > \
                        invariant [x+v^2/(2*b) <= S] {sln};\
                      }* \
                      invariant [x+v^2/(2*b) <= S] [v >= 0];",
                  post="x <= S",
                #   constants={'A', 'B', 'b', 'S', 'ep'},
                  andR_rule={((), ()): "true"},
                  wolfram_engine=True
        )

    def testVerify59(self):
        # Basic benchmark, problem 49
        # Constants = {'Kp()', 'Kd()', 'xr()', 'c()'}
        # {v >= 0 & c() > 0 & Kp() == 2 & Kd() == 3 & 5/4*(x1-xr())^2 + (x1-xr())*v/2 + v^2/4 < c()}
        # t := 0; 
        # <x1_dot = v, v_dot = -Kp()*(x1-xr()) - Kd()*v, t_dot = 1 & t < 10>
        # {5/4*(x1-xr())^2 + (x1-xr())*v/2 + v^2/4 < c()}
        runVerify(self, \
                  pre="v >= 0 & c() > 0 & Kp() == 2 & Kd() == 3 \
                      & 5/4*(x1-xr())^2 + (x1-xr())*v/2 + v^2/4 < c()",
                  hp="t := 0; \
                      <x1_dot = v, v_dot = -Kp()*(x1-xr()) - Kd()*v, t_dot = 1 & t < 10> \
                      invariant [5/4*(x1-xr())^2 + (x1-xr())*v/2 + v^2/4 < c()];",
                  post="5/4*(x1-xr())^2 + (x1-xr())*v/2 + v^2/4 < c()",
                #   constants={'Kp()', 'Kd()', 'xr()', 'c()'}
                  )

    def testVerify60(self):
        # Basic benchmark, problem 50
        #         v >= 0 & xm <= x2 & x2 <= S & xr = (xm + S)/2 & Kp = 2 & Kd = 3
        #            & 5/4*(x2-xr)^2 + (x2-xr)*v/2 + v^2/4 < ((S - xm)/2)^2
        #  -> [ { {  xm := x2;
        #            xr := (xm + S)/2;
        #            ?5/4*(x2-xr)^2 + (x2-xr)*v/2 + v^2/4 < ((S - xm)/2)^2;
        #         ++ ?true;
        #         };
        #         {{ x2' = v, v' = -Kp*(x2-xr) - Kd*v & v >= 0 }
        #           @invariant(
        #             xm<=x2,
        #             5/4*(x2-(xm+S())/2)^2 + (x2-(xm+S())/2)*v/2 + v^2/4 < ((S()-xm)/2)^2
        #          )
        #         }
        #       }*@invariant(v >= 0 & xm <= x2 & xr = (xm + S)/2 & 5/4*(x2-xr)^2 + (x2-xr)*v/2 + v^2/4 < ((S - xm)/2)^2)
        #     ] x2 <= S
        runVerify(self, \
                  pre="v >= 0 & xm <= x2 & x2 <= S & xr == (xm + S)/2 & Kp == 2 & Kd == 3 \
                    & 5/4*(x2-xr)^2 + (x2-xr)*v/2 + v^2/4 < ((S - xm)/2)^2",\
                  hp="{ \
                        if (5/4*(x2-(x2 + S)/2)^2 + (x2-(x2 + S)/2)*v/2 + v^2/4 < ((S - x2)/2)^2) {\
                            xm := x2; \
                            xr := (xm + S)/2; \
                        } else {\
                            skip; \
                        } \
                        ++ \
                        skip; \
                        <x2_dot = v, v_dot = -Kp * (x2 - xr) - Kd * v & v > 0> \
                        invariant [xm <= x2] \
                                  [xr == (xm + S)/2] \
                                  [5/4*(x2-(xm+S)/2)^2 + (x2-(xm+S)/2)*v/2 + v^2/4 < ((S-xm)/2)^2]; \
                      }* \
                      invariant [v >= 0] [xm <= x2] [xr == (xm + S)/2]\
                                [5/4*(x2-xr)^2 + (x2-xr)*v/2 + v^2/4 < ((S - xm)/2)^2];",
                  post="x2 <= S",
                  constants={'Kp', 'Kd', 'S'})

    # TODO: Basic benchmark, problem 51. The ODE invariant cannot imply loop invariant.
    # def testVerify61(self):
    #     # Basic benchmark, problem 51
    #     # TODO: to implement abs, old(v)
    #     #         v >= 0 & A > 0 & B >= b & b > 0 & ep > 0 & lw > 0 & y = ly & r != 0 & dx^2 + dy^2 = 1
    #     #            & abs(y-ly) + v^2/(2*b) < lw
    #     #  -> [
    #     #       { {   ?abs(y-ly) + v^2/(2*b) + (A/b+1)*(A/2*ep^2+ep*v) < lw;
    #     #             a :=*; ?-B <= a & a <= A;
    #     #             w :=*; r :=*; ?r != 0 & w*r = v;
    #     #          ++ ?v=0; a := 0; w := 0;
    #     #          ++ a :=*; ?-B <=a & a <= -b;
    #     #         }

    #     #         c := 0;
    #     #         {
    #     #         { x' = v*dx, y' = v*dy, v' = a, dx' = -dy*w, dy' = dx*w, w'=a/r, c' = 1 & v >= 0 & c <= ep }
    #     #         @invariant(
    #     #           c>=0,
    #     #           dx^2+dy^2=1,
    #     #           (v'=0 -> v=old(v)),
    #     #           (v'=0 -> -c*v <= y - old(y) & y - old(y) <= c*v),
    #     #           (v'=a -> v=old(v)+a*c),
    #     #           (v'=a -> -c*(v-a/2*c) <= y - old(y) & y - old(y) <= c*(v-a/2*c))
    #     #         )
    #     #         }
    #     #       }*@invariant(v >= 0 & dx^2+dy^2 = 1 & r != 0 & abs(y-ly) + v^2/(2*b) < lw)
    #     #     ] abs(y-ly) < lw
    #     runVerify(self, pre="v >= 0 & A > 0 & B >= b & b > 0 & ep > 0 & lw > 0 & \
    #               y == ly & r != 0 & dx^2 + dy^2 == 1 & \
    #               y-ly < lw - v^2/(2*b) & y-ly > -lw + v^2/(2*b)",
    #               hp="( \
    #                         if y-ly < - (v^2/(2*b) + (A/b+1)*(A/2*ep^2+ep*v)) + lw &\
    #                            y-ly > (v^2/(2*b) + (A/b+1)*(A/2*ep^2+ep*v)) - lw \
    #                         then \
    #                             a := {-B <= a & a <= A}; \
    #                             r := {r != 0}; \
    #                             w := v/r \
    #                         else \
    #                             a := {-B <=a & a <= -b} \
    #                         endif \
    #                     ++  if v == 0 \
    #                         then a := 0; w := 0 \
    #                         else a := {-B <=a & a <= -b} \
    #                         endif \
    #                     ++  a := {-B <=a & a <= -b}; \
    #                     c := 0; \
    #                     v0 := v; \
    #                     y0 := y; \
    #                     <x_dot = v*dx, y_dot = v*dy, v_dot = a, dx_dot = -dy*w, dy_dot = dx*w, w_dot=a/r, c_dot = 1 & v > 0 & c < ep> \
    #                     invariant \
    #                         [c >= 0] \
    #                         [dx^2+dy^2 == 1] \
    #                         [r != 0] \
    #                         [v == v0 + a*c] \
    #                         [-c*(v-a/2*c) <= y - y0] \
    #                         [y - y0 <= c*(v-a/2*c)] \
    #                 )** invariant \
    #                         [v >= 0 & dx^2+dy^2 == 1 & r != 0 & \
    #                         y-ly < lw - v^2/(2*b) & y-ly > -lw + v^2/(2*b)]",
    #                 post="y-ly < lw - v^2/(2*b) & y-ly > -lw + v^2/(2*b)",
    #                 constants={'A', 'B', 'b', 'ep', 'lw', 'ly'},
    #                 wolfram_engine=True)

    def testVerify62(self):
        # Basic benchmark, problem 52
        # {v >= 0 & a >= 0}
        # <x_dot = v, v_dot = a & v > 0>
        # {v >= 0}
        runVerify(self, pre="v >= 0 & a >= 0",
                  hp="<x_dot = v, v_dot = a & v > 0> invariant [true];",
                  post="v >= 0")

    def testVerify63(self):
        # Basic benchmark, problem 53
        #         v>=0  & A>=0 & b>0
        #  -> [
        #       {
        #         {a:=A; ++ a:=-b;}
        #         {x'=v, v'=a & v>=0}
        #       }*@invariant(v>=0)
        #     ] v>=0
        runVerify(self, pre="v >= 0 & A >= 0 & b > 0",
                  hp="{ \
                        a := A; ++ a := -b; \
                        <x_dot = v, v_dot = a & v > 0> invariant [true];\
                      }* invariant [v >= 0];",
                  post="v >= 0",
                  constants={'A', 'b'})

    def testVerify64(self):
        # Basic benchmark, problem 54
        # {v >= 0 & A >= 0 & b > 0}
        # (
        #    {  ?(m-x>=2); a := A;
        #   ++ a := -b;
        #   };
        #   {x' = v, v' = a & v >= 0}
        #  )**@invariant(v >= 0)
        # {v >= 0}
        runVerify(self, pre="v >= 0 & A >= 0 & b > 0",
                  hp="{ \
                      if (m-x >= 2) { \
                          a := A; \
                          t := 0; \
                          <x_dot = v, v_dot = a & t < 10> \
                          invariant [a >= 0] [v >= 0 & A >= 0]; \
                      } else {\
                          a := -b; <x_dot = v, v_dot = a & v > 0> \
                          invariant [A >= 0]; \
                      } \
                      }* \
                      invariant [v >= 0] [A >= 0];",
                  post="v >= 0")

    def testVerify65(self):
        # Solution Axiom
        # {v >= 0}
        # <v_dot = 1 & v < 10>
        # {v >= 0}
        runVerify(self, pre="v >= 0",
                  hp="<v_dot = 1 & v < 10> invariant [v >= 0] {sln};",
                  post="v >= 0")

    def testVerify66(self):
        # Solution Axiom
        # {x >= 0 & v >= 0 & a >= 0}
        # <x_dot = v, v_dot = a & x < 10>
        # {x >= 0}
        runVerify(self, pre="x >= 0 & v >= 0 & a >= 0",
                  hp="<x_dot = v, v_dot = a & x < 10> invariant [x >= 0] {sln};",
                  post="x >= 0")

    def testVerify67(self):
        # Solution Axiom
        # {x >= 0 & v >= 0 & a >= 0 & c == 0}
        # <x_dot = v, v_dot = a, c_dot = 1 & c < 10>
        # {x >= 0}
        runVerify(self, pre="x >= 0 & v >= 0 & a >= 0 & c == 0",
                  hp="<x_dot = v, v_dot = a, c_dot = 1 & c < 10> invariant [x >= 0] {sln};",
                  post="x >= 0")

    def testVerify68(self):
        # Strengthened post
        # {x == 0}
        # t := 0; <x_dot = 2, t_dot = 1 & t < 1>
        # stren_post: {x == 2*t & t == 1}
        # {x == 2}
        runVerify(self, pre="x == 0",
                  hp="t := 0; <x_dot = 2, t_dot = 1 & t < 1> invariant [x == 2 * t];",
                  post="x == 2")

    def testVerify69(self):
        # Basic benchmark, problem 55
        # {v^2 <= 2*b*(m-x) & v >= 0  & A >= 0 & b > 0}
        #     (
        #         if 2*b*(m-x) >= v^2 + (A+b)*(A*ep^2+2*ep*v) then a := A else a := -b endif 
        #      ++ a := -b; 
        #         t := 0;
        #         <x_dot = v, v_dot = a, t_dot = 1 & v > 0 & t < ep>
        #     )**@invariant(v^2 <= 2*b*(m-x))
        # {x <= m}
        runVerify(self, pre="v^2 <= 2*b*(m-x) & v >= 0  & A >= 0 & b > 0",
                  hp="{ \
                        if (2*b*(m-x) >= v^2 + (A+b)*(A*ep^2+2*ep*v)) { a := A; } else { a := -b; } \
                    ++ a := -b; \
                        t := 0; \
                        <x_dot = v, v_dot = a, t_dot = 1 & v > 0 & t < ep> invariant [v^2 <= 2*b*(m-x)] {sln};\
                    }* invariant [v^2 <= 2*b*(m-x)];",
                  post="x <= m",
                  constants={'b', 'A', 'ep'},
                  wolfram_engine=True
                  )
    
    # TODO: Basic benchmark, problem 56 - 60, cannot be written into hcsp program.


class NonlinearHHLPyTest(unittest.TestCase):
    
    @classmethod
    def setUpClass(cls):
        try:
            session.start()
        except Exception as e:
            session.start()

    @classmethod
    def tearDownClass(cls):
        session.terminate()
  
    def testNonlinear1(self):
        # Nonlinear benchmark, problem 1
        #  {0.5 <= x & x <= 0.7 & 0 <= y & y <= 0.3}
        #  t := 0; <x_dot = -x + x * y , y_dot = -y, t_dot = 1 & t < 10>
        #  {!(-0.8 >= x & x >= -1 & -0.7 >= y & y >= -1)}
        runVerify(self,pre="0.5 <= x & x <= 0.7 & 0 <= y & y <= 0.3",
                  hp="t := 0; \
                      <x_dot = -x + x * y , y_dot = -y, t_dot = 1 & t < 10> \
                      invariant [x >= 0] {dbx} [y >= 0] {dbx};",
                  post="!(-0.8 >= x & x >= -1 & -0.7 >= y & y >= -1)")
    
    def testNonlinear2(self):
        # Nonlinear benchmark, problem 2
        # {x == 1 & y == 1/8}
        # t := 0; <x_dot = x - y^2, y_dot = y * (x - y^2) & t < 10>@invariant(y^2 < x)
        # {!(x < 0)}
        runVerify(self, pre="x == 1 & y == 1/8",
                  hp="t := 0; \
                      <x_dot = x - y^2, y_dot = y * (x - y^2) & t < 10> \
                      invariant [y^2 < x] {dbx};",
                  post="!(x < 0)")

    def testNonlinear3(self):
        # Nonlinear benchmark, problem 3
        # {x == 1 & y == -1}
        #     t := 0;
        #     <x_dot = x^2 + (x+y)/2, y_dot = (-x + 3*y)/2 & t < 10>@invariant(y-x+1<=0 & y<=0)
        # {!(y>0)}
        runVerify(self, pre="x == 1 & y == -1",
                  hp="t := 0; \
                      <x_dot = x^2 + (x+y)/2, y_dot = (-x + 3*y)/2 & t < 10> \
                      invariant [y-x+1 <= 0] {dbx 1} [y <= 0] {dbx 1};",
                  post="!(y>0)")

    def testNonlinear4(self):
        # Nonlinear benchmark, problem 4
        # {-1/5000 + (1/20+x)^2 + (3/200 + y)^2 <= 0}
        #     t := 0;
        #     <x_dot = (-3 * x^2) / 2 - x^3 / 2 - y, y_dot = 3 * x - y & t < 10>@invariant(0.073036*x^6-0.014461*x^5*y+0.059693*x^4*y^2-0.0063143*x^3*y^3+0.029392*x^2*y^4+0.0036316*y^6+0.064262*x^5+0.24065*x^4*y-0.082711*x^3*y^2+0.28107*x^2*y^3-0.015542*x*y^4+0.036437*y^5+0.47415*x^4-0.56542*x^3*y+1.1849*x^2*y^2-0.22203*x*y^3+0.19053*y^4-0.59897*x^3+1.8838*x^2*y-0.59653*x*y^2+0.47413*y^3+1.0534*x^2-0.51581*x*y+0.43393*y^2-0.35572*x-0.11888*y-0.25586<=0)
        # {!(49/100 + x + x^2 + y + y^2 <= 0)}
        runVerify(self, pre="-1/5000 + (1/20+x)^2 + (3/200 + y)^2 <= 0",
                  hp="t := 0; \
                     <x_dot = (-3 * x^2) / 2 - x^3 / 2 - y, y_dot = 3 * x - y & t < 10> \
                     invariant [0.073036*x^6-0.014461*x^5*y+0.059693*x^4*y^2-0.0063143*x^3*y^3+0.029392*x^2*y^4+0.0036316*y^6+0.064262*x^5+0.24065*x^4*y-0.082711*x^3*y^2+0.28107*x^2*y^3-0.015542*x*y^4+0.036437*y^5+0.47415*x^4-0.56542*x^3*y+1.1849*x^2*y^2-0.22203*x*y^3+0.19053*y^4-0.59897*x^3+1.8838*x^2*y-0.59653*x*y^2+0.47413*y^3+1.0534*x^2-0.51581*x*y+0.43393*y^2-0.35572*x-0.11888*y-0.25586<=0] \
                       {bc};",
                  post="!(49/100 + x + x^2 + y + y^2 <= 0)",
                  wolfram_engine=True)

    def testNonlinear5(self):
        # Nonlinear benchmark, problem 5
        # {-1/20 + (5/4+x)^2 + (-5/4+y)^2 <= 0}
        #     t := 0;
        #     <x_dot = 7/8 + x - x^3/3 - y, y_dot = (2 * (7/10 + x - (4*y)/5)) / 25, t_dot = 1 & t < 10>
        #           @invariant(x * ((-73) + 23*x) < 157 + y * (134 + 81*y))
        # {!(36/5 + 5*x + x^2 + 2*y + y^2 <= 0)}
        runVerify(self, pre="-1/20 + (5/4+x)^2 + (-5/4+y)^2 <= 0",
                  hp="t := 0; \
                      <x_dot = 7/8 + x - x^3/3 - y, y_dot = (2 * (7/10 + x - (4*y)/5)) / 25, t_dot = 1 & t < 10> \
                      invariant [x * ((-73) + 23*x) < 157 + y * (134 + 81*y)] {bc};",
                  post="!(36/5 + 5*x + x^2 + 2*y + y^2 <= 0)")

    def testNonlinear6(self):
        # Nonlinear benchmark, problem 6
        # {x^2 + (-1/2 + y)^2 < 1/24}
        #     <x_dot = -x + 2*x^3*y^2, y_dot = -y & x^2*y^2 < 1>
        # @invariant(4*x*(1821+5601250*x)+4827750*x*y+125*(76794+(-45619)*x^3)*y^2 < 1375*(4891+3332*y))
        # {!(x <= -2 | y <= -1)}
        runVerify(self, pre="x^2 + (-1/2 + y)^2 < 1/24",
                  hp="<x_dot = -x + 2*x^3*y^2, y_dot = -y & x^2*y^2 < 1> \
                      invariant [4*x*(1821+5601250*x)+4827750*x*y+125*(76794+(-45619)*x^3)*y^2 < 1375*(4891+3332*y)] {bc};",
                  post="!(x <= -2 | y <= -1)",
                  wolfram_engine=True)

    def testNonlinear7(self):
        # Nonlinear benchmark, problem 7
        # {(2+x)^2 + (-1+y)^2 <= 1/4}
        #     t := 0;
        #     <x_dot = x^2 + 2*x*y + 3*y^2, y_dot = 2*y*(2*x+y), t_dot = 1 & t < 10>@invariant(x<y, x+y<0)
        # {!(x > 0)}
        runVerify(self, pre="(2+x)^2 + (-1+y)^2 <= 1/4", 
                  hp="t := 0; \
                      <x_dot = x^2 + 2*x*y + 3*y^2, y_dot = 2*y*(2*x + y), t_dot = 1 & t < 10> \
                      invariant [x < y] {dbx} [x + y < 0] {dbx};",
                  post="!(x > 0)")
    
    def testNonlinear8(self):
        # Nonlinear benchmark, problem 8
        # {x^2 + (2+y)^2 <= 1}
        #     t := 0;
        #     <x_dot = 2 * x - x * y, y_dot = 2 * x^2 - y, t_dot = 1 & t < 10>@invariant(0.0052726*x^10+0.013182*x^8*y^2+0.013181*x^6*y^4+0.0065909*x^4*y^6+0.0016477*x^2*y^8+0.00016477*y^10-0.060426*x^8*y-0.11666*x^6*y^3-0.08401*x^4*y^5-0.02829*x^2*y^7-0.0026618*y^9-0.0093935*x^8+0.25715*x^6*y^2+0.35556*x^4*y^4+0.18385*x^2*y^6+0.017843*y^8-0.22922*x^6*y-0.82409*x^4*y^3-0.6654*x^2*y^5-0.072582*y^7+0.38533*x^6+1.6909*x^4*y^2+1.7759*x^2*y^4+0.20099*y^6+1.8855*x^4*y-0.83113*x^2*y^3-0.10854*y^5-4.9159*x^4-11.581*x^2*y^2-1.9047*y^4+6.644*x^2*y+7.8358*y^3+1.5029*x^2-13.2338*y^2+10.8962*y-3.4708 <= 0
        # & 
        # 0.10731*x^10+0.26827*x^8*y^2+0.26827*x^6*y^4+0.13413*x^4*y^6+0.033534*x^2*y^8+0.0033532*y^10-1.2677*x^8*y-2.4914*x^6*y^3-1.8208*x^4*y^5-0.59588*x^2*y^7-0.057773*y^9-0.82207*x^8+4.1107*x^6*y^2+6.7924*x^4*y^4+3.4828*x^2*y^6+0.36938*y^8+6.8306*x^6*y-0.93431*x^4*y^3-5.9328*x^2*y^5-0.95223*y^7+2.2556*x^6-17.4284*x^4*y^2-6.4448*x^2*y^4-0.33741*y^6-1.2936*x^4*y+16.8675*x^2*y^3+8.8828*y^5-16.1915*x^4-39.7751*x^2*y^2-25.8126*y^4+43.7284*x^2*y+39.2116*y^3-12.7866*x^2-33.0675*y^2+15.2878*y-3.1397 <= 0)
        # !(x^2 + (-1+y)^2 <= 9/100)
        runVerify(self, pre="x^2 + (2+y)^2 <= 1",
                  hp="t := 0; \
                      <x_dot = 2 * x - x * y, y_dot = 2 * x^2 - y, t_dot = 1 & t < 10> \
                      invariant \
                        [0.0052726*x^10+0.013182*x^8*y^2+0.013181*x^6*y^4+0.0065909*x^4*y^6+0.0016477*x^2*y^8+0.00016477*y^10-0.060426*x^8*y-0.11666*x^6*y^3-0.08401*x^4*y^5-0.02829*x^2*y^7-0.0026618*y^9-0.0093935*x^8+0.25715*x^6*y^2+0.35556*x^4*y^4+0.18385*x^2*y^6+0.017843*y^8-0.22922*x^6*y-0.82409*x^4*y^3-0.6654*x^2*y^5-0.072582*y^7+0.38533*x^6+1.6909*x^4*y^2+1.7759*x^2*y^4+0.20099*y^6+1.8855*x^4*y-0.83113*x^2*y^3-0.10854*y^5-4.9159*x^4-11.581*x^2*y^2-1.9047*y^4+6.644*x^2*y+7.8358*y^3+1.5029*x^2-13.2338*y^2+10.8962*y-3.4708 <= 0] \
                          {bc} \
                        [0.10731*x^10+0.26827*x^8*y^2+0.26827*x^6*y^4+0.13413*x^4*y^6+0.033534*x^2*y^8+0.0033532*y^10-1.2677*x^8*y-2.4914*x^6*y^3-1.8208*x^4*y^5-0.59588*x^2*y^7-0.057773*y^9-0.82207*x^8+4.1107*x^6*y^2+6.7924*x^4*y^4+3.4828*x^2*y^6+0.36938*y^8+6.8306*x^6*y-0.93431*x^4*y^3-5.9328*x^2*y^5-0.95223*y^7+2.2556*x^6-17.4284*x^4*y^2-6.4448*x^2*y^4-0.33741*y^6-1.2936*x^4*y+16.8675*x^2*y^3+8.8828*y^5-16.1915*x^4-39.7751*x^2*y^2-25.8126*y^4+43.7284*x^2*y+39.2116*y^3-12.7866*x^2-33.0675*y^2+15.2878*y-3.1397 <= 0] \
                          {bc};",
                  post="!(x^2 + (-1+y)^2 <= 9/100)",
                  wolfram_engine=True)

    def testNonlinear9(self):
        # Nonlinear benchmark, problem 9
        # {(1+x)^2 + (-2+y)^2 <= 4/25}
        #     t := 0;
        #     <x_dot = y, y_dot = 2*x-x^3-y-x^2*y, t_dot = 1 & t < 10>@invariant(0.23942*x^6 + 0.097208*x^5*y + 0.06013*x^4*y^2 - 0.0076888*x^3*y^3 - 0.022097*x^2*y^4 + 0.067444*x*y^5 + 0.063249*y^6 - 0.11511*x^5 - 0.093461*x^4*y - 0.061763*x^3*y^2 + 0.065902*x^2*y^3 + 0.053766*x*y^4 - 0.1151*y^5 - 0.95442*x^4 + 0.38703*x^3*y + 0.46309*x^2*y^2 - 0.14691*x*y^3 + 0.11756*y^4 - 0.021196*x^3 - 0.40047*x^2*y - 0.28433*x*y^2 - 0.028468*y^3 - 0.020192*x^2 - 0.37629*x*y - 0.13713*y^2 + 1.9803*x - 1.4121*y - 0.51895 <= 0)
        # {!((-1+x)^2 + y^2 <= 1/25)}
        runVerify(self, pre="(1+x)^2 + (-2+y)^2 <= 4/25",
                  hp="t := 0; \
                      <x_dot = y, y_dot = 2*x-x^3-y-x^2*y, t_dot = 1 & t < 10> \
                      invariant [0.23942*x^6 + 0.097208*x^5*y + 0.06013*x^4*y^2 - 0.0076888*x^3*y^3 - 0.022097*x^2*y^4 + 0.067444*x*y^5 + 0.063249*y^6 - 0.11511*x^5 - 0.093461*x^4*y - 0.061763*x^3*y^2 + 0.065902*x^2*y^3 + 0.053766*x*y^4 - 0.1151*y^5 - 0.95442*x^4 + 0.38703*x^3*y + 0.46309*x^2*y^2 - 0.14691*x*y^3 + 0.11756*y^4 - 0.021196*x^3 - 0.40047*x^2*y - 0.28433*x*y^2 - 0.028468*y^3 - 0.020192*x^2 - 0.37629*x*y - 0.13713*y^2 + 1.9803*x - 1.4121*y - 0.51895 <= 0] \
                        {bc};",
                  post="!((-1+x)^2 + y^2 <= 1/25)",
                  wolfram_engine=True)

    # TODO: Nonlinear benchmark, problem 10.
    # Cannot proved by keymaera following tactic.
#     x^2+y^2<=1
#   ->
#   [
#     {x'=3*(-4+x^2), y'=3+x*y-y^2}
#     @invariant(
#       (-0.0013138)*x^5+0.00048141*x^4*y+0.000828*x^2*y^3-0.0016748*x*y^4+0.0008106*y^5+0.010722*x^4-0.0018729*x^3*y+0.0041383*x^2*y^2-0.013911*x*y^3+0.0085091*y^4-0.039948*x^3-0.0060006*x^2*y-0.046355*x*y^2+0.054433*y^3-0.028132*x^2+0.13217*x*y+0.10916*y^2+0.62004*x-0.88775*y-1.1161<=0&(-0.00011438)*x^4*y^2+0.00015105*x^2*y^4-0.0018063*x^5+0.0012699*x^3*y^2+0.0014498*x^2*y^3-0.0014334*x*y^4+0.0013001*y^5+0.017567*x^4+0.0050023*x^3*y-0.0016674*x^2*y^2-0.015315*x*y^3+0.01038*y^4-0.072259*x^3-0.035874*x^2*y-0.050558*x*y^2+0.058708*y^3-0.05097*x^2+0.042626*x*y+0.19257*y^2+1.3148*x+0.014613*y-1.2585<=0,
#       x^2+y^2-16<=0)
#   ] !(x < -4 | y < -4 | x>4 | y>4) 
    
    def testNonlinear11(self):
        # Nonlinear benchmark, problem 11.
        # {-1/20 + (5/4 + x)^2 + (-5/4 + y)^2 <= 0}
        #     t := 0; 
        #     <x_dot = x + y, y_dot = x * y - y^2 / 2, t_dot = 1 & t < 10>@invariant(y>0, y*((-104420)+(-73565)*x+18407*y) < 44444)
        # {!((5/2 + x)^2 + (-4/5 + y)^2 <= 1/20)}
        runVerify(self, pre="-1/20 + (5/4 + x)^2 + (-5/4 + y)^2 <= 0",
                  hp="t := 0; \
                      <x_dot = x + y, y_dot = x * y - y^2 / 2, t_dot = 1 & t < 10> \
                      invariant \
                        [y > 0] {dbx} \
                        [y*((-104420)+(-73565)*x+18407*y) < 44444] {bc};",
                  post="!((5/2 + x)^2 + (-4/5 + y)^2 <= 1/20)",
                  wolfram_engine=True)

    def testNonlinear12(self):
        # Nonlinear benchmark, problem 12
        # {x^2 + y^2 < 1/4}
        #     t := 0;
        #     <x_dot = -70-100*x+70*x^2+100*x^3-200*y+200*x^2*y, 
        #      y_dot = 146*x+100*y+140*x*y+100*x^2*y+200*x*y^2,
        #      t_dot = 1
        #      & t < 10>
        #     @invariant(1+x>0, x < 1)
        # {!(2*x >= 3 | x <= -3/2)}
        runVerify(self, pre="x^2 + y^2 < 1/4",
                  hp="t := 0; \
                      <x_dot = -70-100*x+70*x^2+100*x^3-200*y+200*x^2*y, \
                      y_dot = 146*x+100*y+140*x*y+100*x^2*y+200*x*y^2, \
                      t_dot = 1 \
                      & t < 10> \
                      invariant \
                        [1 + x > 0] {dbx} \
                        [x < 1] {dbx};",
                  post="!(2*x >= 3 | x <= -3/2)")

    def testNonlinear13(self):
        # Nonlinear benchmark, problem 13
        # {(-1 + x)^2 + (1 + y)^2 < 1/4}
        #     t := 0;
        #     <x_dot = 1+x+x^2+x^3+2*y+2*x^2*y, 
        #      y_dot = -y+2*x*y+x^2*y+2*x*y^2, 
        #      t_dot = 1
        #      & t < 1>@invariant(y<0)
        # {!(y >= 1)}
        runVerify(self, pre="(-1 + x)^2 + (1 + y)^2 < 1/4",
                  hp="t := 0;\
                      <x_dot = 1+x+x^2+x^3+2*y+2*x^2*y, \
                      y_dot = -y+2*x*y+x^2*y+2*x*y^2, \
                      t_dot = 1\
                      & t < 1> \
                      invariant [y < 0] {dbx};",
                  post="!(y >= 1)")

    def testNonlinear14(self):
        # Nonlinear benchmark, problem 14
        # {x > -1 & x < -3/4 & y <= 3/2 & y >= 1}
        #     t := 0;
        #     <x_dot = -42*x^7+50*x^2*y+156*x^3*y+258*x^4*y-46*x^5*y+68*x^6*y+20*x*y^6-8*y^7,
        #      y_dot = y*(1110*x^6-3182*x^4*y-220*x^5*y+478*x^3*y^3+487*x^2*y^4-102*x*y^5-12*y^6),
        #      t_dot = 1
        #      & t < 10>@invariant(y>0)
        # {!(x > 1 + y)}
        runVerify(self, pre="x > -1 & x < -3/4 & y <= 3/2 & y >= 1",
                  hp="t := 0; \
            <x_dot = -42*x^7+50*x^2*y+156*x^3*y+258*x^4*y-46*x^5*y+68*x^6*y+20*x*y^6-8*y^7,\
            y_dot = y*(1110*x^6-3182*x^4*y-220*x^5*y+478*x^3*y^3+487*x^2*y^4-102*x*y^5-12*y^6),\
            t_dot = 1\
            & t < 10> \
            invariant [y > 0] {dbx} [!(x > 1 + y)] {dbx};",
                  post="!(x > 1 + y)")

    def testNonlinear15(self):
        # Nonlinear benchmark, problem 15
        # {x > -1 & x < -1/2 & y <= -1/10 & y >= -3/10}
        #     t := 0;
        #     <x_dot = 315*x^7+477*x^6*y-113*x^5*y^2+301*x^4*y^3-300*x^3*y^4-192*x^2*y^5+128*x*y^6-16*y^7,
        #      y_dot = y*(2619*x^6-99*x^5*y-3249*x^4*y^2+1085*x^3*y^3+596*x^2*y^4-416*x*y^5+64*y^6)
        #      t_dot = 1 & t < 10>@invariant(x<y)
        # {!(x > 1 + y)}
        runVerify(self, pre="x > -1 & x < -1/2 & y <= -1/10 & y >= -3/10",
                  hp="t := 0; \
                      <x_dot = 315*x^7+477*x^6*y-113*x^5*y^2+301*x^4*y^3- \
                      300*x^3*y^4-192*x^2*y^5+128*x*y^6-16*y^7, \
                       y_dot = y*(2619*x^6-99*x^5*y-3249*x^4*y^2+1085*x^3*y^3 \
                      +596*x^2*y^4-416*x*y^5+64*y^6), \
                       t_dot = 1 & t < 10> \
                        invariant [x < y] {dbx};",
                  post="!(x > 1 + y)")

    def testNonlinear16(self):
        # Nonlinear benchmark, problem 16
        # {(-1 + x)^2 + (1 + y)^2 < 1/4}
        #      t := 0;
        #     <x_dot = x^4+2*x*y^2-6*x^2*y^2+y^4+x*(x^2-y^2), 
        #      y_dot = 2*x^2*y-4*x^3*y+4*x*y^3-y*(x^2-y^2),
        #      t_dot = 1 & t  < 10>@invariant(y < 0)>
        # {!(y >= 1)}
        runVerify(self, pre="(-1 + x)^2 + (1 + y)^2 < 1/4",
                  hp="t := 0; \
                      <x_dot = x^4+2*x*y^2-6*x^2*y^2+y^4+x*(x^2-y^2), \
                       y_dot = 2*x^2*y-4*x^3*y+4*x*y^3-y*(x^2-y^2), \
                       t_dot = 1 & t < 10> \
                        invariant [y < 0] {dbx};",
                  post="!(y >= 1)")

    def testNonlinear17(self):
        # Nonlinear benchmark, problem 17
        # {x > -1/2 & x < -1/3 & y < 0 & y >= -1/2}
        #     t := 0;
        #     <x_dot = 2*x-x^5-x*y^4, 
        #      y_dot = y-x^2*y-y^3,
        #      t_dot = 1 & t < 10>@invariant(x < 0, y < 0)
        # {!(x + y > 0)}
        runVerify(self, pre="x > -1/2 & x < -1/3 & y < 0 & y >= -1/2",
                  hp="t := 0; \
                      <x_dot = 2*x-x^5-x*y^4, \
                       y_dot = y-x^2*y-y^3, \
                       t_dot = 1 & t < 10> \
                        invariant \
                          [x < 0] {dbx} \
                          [y < 0] {dbx};",
                  post="!(x + y > 0)")

    def testNonlinear18(self):
        # Nonlinear benchmark, problem 18
        # {x>-1/2 & x < -1/3 & y<0 & y>=-1/2}
        #     t := 0;
        #     <x_dot = x*(1-x^2-y^2)+y*((-1+x^2)^2+y^2), 
        #      y_dot = y*(1-x^2-y^2)-y*((-1+x^2)^2+y^2),
        #      t_dot = 1 & t < 10>@invariant(y < 0, x+y < 0)
        # {!(x>=0)}
        runVerify(self, pre="x>-1/2 & x < -1/3 & y<0 & y>=-1/2",
                  hp="t := 0; \
                      <x_dot = x*(1-x^2-y^2)+y*((-1+x^2)^2+y^2), \
                       y_dot = y*(1-x^2-y^2)-y*((-1+x^2)^2+y^2), \
                       t_dot = 1 & t < 10> \
                        invariant \
                        [y < 0] {dbx} \
                        [x + y < 0] {dbx} \
                        [!(x >= 0)] {dbx};",
                  post="!(x>=0)")

    # TODO: Nonlinear benchmark, problem 19, 20. The ODE rule is not clear.

    def testNonlinear21(self):
        # Nonlinear benchmark, problem 21
        # {-1<=a & a<=-0.5 & 1<=y & y<=1.5}
        #      t := 0;
        #     <a_dot = 7/8+a-a^3/3-y, 
        #      y_dot = (2*(7/10+a-(4*y)/5))/25,
        #      t_dot = 1 & t < 10>@invariant(0.12152*a^4+0.22807*a^3*y+0.214*a^2*y^2-0.71222*y^4-0.27942*a^3-0.48799*a^2*y-0.2517*a*y^2-0.3366*y^3-0.21526*a^2+0.16728*a*y-0.44613*y^2+0.35541*a-0.21594*y-0.72852<=0)
        # {!(-2.5<=a & a<=-2 & -2<=y & y<=-1.5)}
        runVerify(self, pre="-1<=a & a<=-0.5 & 1<=y & y<=1.5",
                  hp=" t := 0; \
                       <a_dot = 7/8+a-a^3/3-y, \
                        y_dot = (2*(7/10+a-(4*y)/5))/25, \
                        t_dot = 1 & t < 10> \
                            invariant [0.12152*a^4+0.22807*a^3*y+0.214*a^2*y^2-0.71222*y^4-0.27942*a^3-0.48799*a^2*y-0.2517*a*y^2-0.3366*y^3-0.21526*a^2+0.16728*a*y-0.44613*y^2+0.35541*a-0.21594*y-0.72852<=0] {bc};",
                  post="!(-2.5<=a & a<=-2 & -2<=y & y<=-1.5)",
                  wolfram_engine=True)

    def testNonlinear22(self):
        # Nonlinear benchmark, problem 22
        # {x^2 + (-2 + y)^2 < 1/24}
        #      t := 0;
        #     <x_dot = -x+2*x^2*y, y_dot = -y, t_dot = 1 & t < 10>@invariant(y>0, 12299+9595*x>0)
        # {!(x <= -2 | y <= -1)}
        runVerify(self, pre="x^2 + (-2 + y)^2 < 1/24",
                  hp="t := 0; \
                      <x_dot = -x+2*x^2*y, y_dot = -y, t_dot = 1 & t < 10> \
                      invariant \
                          [y > 0] {dbx} \
                          [12299+9595*x > 0] {bc};",
                  post="!(x <= -2 | y <= -1)")

    def testNonlinear23(self):
        # Nonlinear benchmark, problem 23
        # {x^2 + (-1 + y)^2 < 1/8}
        #      t := 0;
        #     <x_dot = -2*x+y^4, y_dot = -y+3*x*y^3, t_dot = 1 & t < 10>@invariant(y>0)
        # {!(y <= -1)}
        runVerify(self, pre="x^2 + (-1 + y)^2 < 1/8",
                  hp="t := 0; \
                     <x_dot = -2*x+y^4, y_dot = -y+3*x*y^3, t_dot = 1 & t < 10> \
                      invariant \
                          [y > 0] {dbx};",
                  post="!(y <= -1)")
                  
    # TODO: Nonlinear benchmark, problem 24. ODE rule not clear.

    def testNonlinear25(self):
        # Nonlinear benchmark, problem 25
        # {(x-9)^2+(y-20)^20 <= 4}
        #     <x_dot = y^2+10*y+25, 
        #      y_dot = 2*x*y+10*x-40*y-200 
        #      & 5<x & x<35>@invariant(5133+8*((-40)+x)*x>=4*y*(10+y))
        # {y <= 48}
        runVerify(self, pre="(x-9)^2+(y-20)^20 <= 4",
                  hp="<x_dot = y^2+10*y+25, \
                       y_dot = 2*x*y+10*x-40*y-200 \
                       & 5<x & x<35> \
                      invariant \
                          [5133+8*((-40)+x)*x>=4*y*(10+y)];",
                  post="y <= 48")

    def testNonlinear26(self):
        # Nonlinear benchmark, problem 26
        # {(x-9)^2+(y-20)^20 <= 4}
        #     <x_dot = -y^2-10*y-25, 
        #      y_dot = 8*x*y+40*x-160*y-800 
        #      & 5<x & x<35>@invariant(1961/13+x^2+1/8*y*(10+y)<=40*x)
        # {y <= 48}
        runVerify(self, pre="(x-9)^2+(y-20)^20 <= 4",
                  hp="<x_dot = -y^2-10*y-25, \
                       y_dot = 8*x*y+40*x-160*y-800 \
                       & 5<x & x<35> \
                      invariant \
                          [1961/13+x^2+1/8*y*(10+y)<=40*x];",
                  post="y <= 48")

    def testNonlinear27(self):
        # Nonlinear benchmark, problem 27
        # {(x+15)^2+(y-17)^2-1 <= 0}
        #      t := 0;
        #     <x_dot = y^2, y_dot = x*y, t_dot = 1 & t < 10>@invariant(4490/41+x^2>=y^2)
        # {!((x-11)^2+(y-16.5)^2-1 <= 0)}
        runVerify(self, pre="(x+15)^2+(y-17)^2-1 <= 0",
                  hp="t := 0; \
                      <x_dot = y^2, y_dot = x*y, t_dot = 1 & t < 10> \
                      invariant [4490/41+x^2>=y^2];",
                  post="!((x-11)^2+(y-16.5)^2-1 <= 0)")

    def testNonlinear28(self):
        # Nonlinear benchmark, problem 28
        # {1-(x+6)^2 - (y+6)^2 >= 0}
        #      t := 0;
        #     <x_dot = y^2-2*y, y_dot = x^2+2*x, t_dot = 1 & t < 10>@invariant(3*x^2*(3+x)<=1181+3*((-3)+y)*y^2)
        # {!(1-(x-8.2)^2 - (y-4)^2 >= 0)}
        runVerify(self, pre="1-(x+6)^2 - (y+6)^2 >= 0",
                  hp="t := 0; \
                  <x_dot = y^2-2*y, y_dot = x^2+2*x, t_dot = 1 & t < 10> \
                  invariant [3*x^2*(3+x) <= 1181+3*((-3)+y)*y^2];",
                  post="!(1-(x-8.2)^2 - (y-4)^2 >= 0)")

    def testNonlinear29(self):
        # Nonlinear benckmark, problem29
        # {x^2 <= 1/2 & (y + 2)^2 <= 1/3}
        #      t := 0;
        #     <x_dot = -x + y - x^3, 
        #      y_dot = -x - y + y^2,
        #      t_dot = 1 & t < 10>@invariant(2*x^2+(y+3/2)^2-4<=0)
        # {((-1 + x)^2 + (-3/2 + y)^2 > 1/4)}
        runVerify(self, pre="x^2 <= 1/2 & (y + 2)^2 <= 1/3",
                  hp="t := 0;\
                      <x_dot = -x + y - x^3, \
                       y_dot = -x - y + y^2, \
                       t_dot = 1 & t < 10> \
                      invariant [2*x^2+(y+3/2)^2-4 <= 0] {bc};",
                  post="((-1 + x)^2 + (-3/2 + y)^2 > 1/4)")

    def testNonlinear30(self):
        # Nonlinear benchmark, problem 30
        # {x^2 <= 1/2 & y^2 <= 1/3}
        #      t := 0;
        #     <x_dot = y - x^7*(x^4 + 2*y^2 - 10), 
        #      y_dot = -x^3 - 3*(y^5)*(x^4 + 2*y^2 - 10),
        #      t_dot = 1 & t < 10>
        #     @invariant(x^4 + 2*y^2 <= 10)
        # {((-2 + x)^2 + (-3 + y)^2 > 1/4)}
        runVerify(self, pre="x^2 <= 1/2 & y^2 <= 1/3",
                  hp="t := 0; \
                     <x_dot = y - x^7*(x^4 + 2*y^2 - 10), \
                      y_dot = -x^3 - 3*(y^5)*(x^4 + 2*y^2 - 10), \
                      t_dot = 1 & t < 10> \
                      invariant [x^4 + 2*y^2 <= 10] {dbx};",
                  post="((-2 + x)^2 + (-3 + y)^2 > 1/4)")

    def testNonlinear31(self):
        # Nonlinear benchmark, problem 31
        # {x^2 + y^2 <= 1/4}
        #      t := 0;
        #     <x_dot = -y+2*x^2*y, y_dot = y+2*x*y^2, t_dot = 1 & t < 10>
        #    @invariant(2*x^2 < 1)
        # {!(x > 3)}
        runVerify(self, pre="x^2 + y^2 <= 1/4",
                  hp="t := 0; \
                      <x_dot = -y+2*x^2*y, y_dot = y+2*x*y^2, t_dot = 1 & t < 10> \
                      invariant [2*x^2 < 1] {dbx};",
                  post="!(x > 3)")

    def testNonlinear32(self):
        # Nonlinear benchmark, problem 32
        # {x1>=2 & x2^2<=1}
        #      t := 0;
        #      <x1_dot = -x2^3, x2_dot = x1-x1^3, t_dot = 1 & t < 10>
        #     @invariant(x1^4>=50000/7143+2*x1^2+x2^4)
        # {x1 >= 1}
        runVerify(self, pre="x1>=2 & x2^2<=1",
                  hp="t := 0; \
                      <x1_dot = -x2^3, x2_dot = x1-x1^3, t_dot = 1 & t < 10> \
                      invariant \
                          [x1^4 >= 50000/7143+2*x1^2+x2^4] \
                          [x1 >= 1] {bc};",
                  post="x1 >= 1")

    def testNonlinear33(self):
        # Nonlinear benchmark, problem 33
        # {1.1<=x1 & x1 <= -0.7 & 0.5<=x2 & x2<=0.9}
        #       t := 0;
        #      <x1_dot = -x2^3, x2_dot = x1-x1^3, t_dot = 1 & t < 10>
        #       @invariant(1-x1^2-x2^2 >= 0 & 1-x1^2+x2^2 >= 0)
        # {x1^2+x2-3 < 0}
        runVerify(self, pre="1.1<=x1 & x1 <= -0.7 & 0.5<=x2 & x2<=0.9",
                  hp="t := 0; \
                      <x1_dot = -x2^3, x2_dot = x1-x1^3, t_dot = 1 & t < 10> \
                      invariant \
                          [1-x1^2-x2^2 >= 0] {dbx} \
                          [1-x1^2+x2^2 >= 0] {dbx};",
                  post="x1^2+x2-3 < 0")

    def testNonlinear34(self):
        # Nonlinear benchmark, problem 34
        # {Il == 1 & Vc == 1}
        #     t := 0;
        #     <Il_dot = -Vc-1/5*Vc^2, Vc_dot = -2*Il-Il^2+Il^3, t_dot = 1 & t < 10>
        #       @invariant(4993/2416+Il^4+2*Vc^2+4/15*Vc^3<=4/3*Il^2*(3+Il))
        # {Vc <= 3}
        runVerify(self, pre="Il == 1 & Vc == 1",
                  hp="t := 0; \
                      <Il_dot = -Vc-1/5*Vc^2, Vc_dot = -2*Il-Il^2+Il^3, \
                      t_dot = 1 & t < 10> \
                      invariant \
                          [4993/2416+Il^4+2*Vc^2+4/15*Vc^3 <= 4/3*Il^2*(3+Il)];",
                  post="Vc <= 3")

    def testNonlinear35(self):
        # Nonlinear benchmark, problem 35
        # {(-3/2 + x)^2 + y^2 <= 1/4}
        #      t := 0;
        #     <x_dot = x, y_dot = -x+x^3/3-y, t_dot = 1 & t < 10>@invariant(x>0)
        # {!((1 + x)^2 + (1 + y)^2 <= 4/25)}
        runVerify(self, pre="(-3/2 + x)^2 + y^2 <= 1/4",
                  hp="t := 0; \
                      <x_dot = x, y_dot = -x+x^3/3-y, t_dot = 1 & t < 10> \
                      invariant [x > 0] {dbx};",
                  post="!((1 + x)^2 + (1 + y)^2 <= 4/25)")

    def testNonlinear36(self):
        # Nonlinear benchmark, problem 36
        # {a^2 + y^2 < 1/16}
        #     t := 0;
        #     <a_dot = a-a^3+y-a*y^2, 
        #      y_dot = -a+y-a^2*y-y^3,
        #      t_dot = 1 & t < 10>@invariant(a^2+y^2<=1)
        # {!(a < -1 | y < -1 | a > 1 | y > 1)}
        runVerify(self, pre="a^2 + y^2 < 1/16",
                  hp="t := 0; \
                      <a_dot = a-a^3+y-a*y^2, \
                       y_dot = -a+y-a^2*y-y^3, \
                       t_dot = 1 & t < 10> \
                      invariant [a^2+y^2 <= 1] {dbx};",
                  post="!(a < -1 | y < -1 | a > 1 | y > 1)")

    def testNonlinear37(self):
        # Nonlinear benchmark, problem 37
        # {x > -4/5 & x < -1/3 & y < 3/2 & y >= 1}
        #      t := 0;
        #     <x_dot = -x+x*(x^2+y^2), 
        #      y_dot = x+y*(x^2+y^2),
        #      t_dot = 1 & t < 10>@invariant(3305*(x+y)>596)
        # {!(x < -1/3 & y >= 0 & 2*y < 1 & x > -4/5)}
        runVerify(self, pre="x > -4/5 & x < -1/3 & y < 3/2 & y >= 1",
                  hp="t := 0; \
                     <x_dot = -x+x*(x^2+y^2), \
                      y_dot = x+y*(x^2+y^2), \
                      t_dot = 1 & t < 10> \
                      invariant [3305*(x+y) > 596] {bc};",
                  post="!(x < -1/3 & y >= 0 & 2*y < 1 & x > -4/5)")

    def testNonlinear38(self):
        # Nonlinear benchmark, problem 38
        # {2*(-1/3 + x)^2 + y^2 < 1/16}
        #      t := 0;
        #     <x_dot = x^2*y, y_dot = x^2-y^2, t_dot = 1 & t < 10>@invariant(x>0)
        # {!(x <= -2)}
        runVerify(self, pre="2*(-1/3 + x)^2 + y^2 < 1/16",
                  hp="t := 0; \
                     <x_dot = x^2*y, y_dot = x^2-y^2, t_dot = 1 & t < 10> \
                      invariant [x > 0] {dbx};",
                  post="!(x <= -2)")

    def testNonlinear39(self):
        # Nonlinear benckmark, problem 39
        # {(-1/3 + x)^2 + 2*(-1/3 + y)^2 < 1/25}
        #      t := 0;
        #     <x_dot = x*(2-x-y), y_dot = x-y, t_dot = 1 & t < 10>
        #       @invariant(x>0, 19801*x^2+10*y*((-22888)+11079*y)+x*(64611+33500*y) < 97121)
        # {!(x >= 2 | x <= -2)}
        runVerify(self, pre="(-1/3 + x)^2 + 2*(-1/3 + y)^2 < 1/25",
                  hp="t := 0; \
                      <x_dot = x*(2-x-y), y_dot = x-y, t_dot = 1 & t < 10> \
                      invariant \
                          [x > 0] {dbx}\
                          [19801*x^2+10*y*((-22888)+11079*y)+x*(64611+33500*y) < 97121] {bc};",
                  post="!(x >= 2 | x <= -2)")

    def testNonlinear40(self):
        # Nonlinear benchmark, problem 40
        # {(-1/3 + x)^2 + y^2 < 1/25}
        #      t := 0;
        #     <x_dot = 2*x*y, y_dot = -x^2+y^2, t_dot = 1 & t < 10>@invariant(x>0)
        # {!(x <= -2)}
        runVerify(self, pre="(-1/3 + x)^2 + y^2 < 1/25",
                  hp="t := 0; \
                     <x_dot = 2*x*y, y_dot = -x^2+y^2, t_dot = 1 & t < 10> \
                         invariant [x > 0] {dbx};",
                  post="!(x <= -2)")

    def testNonlinear41(self):
        # Nonlinear benchmark, problem 41
        # {(-1/3 + x)^2 + (-1/3 + y)^2 < 1/16}
        #      t := 0;
        #     <x_dot = (1-x^2)*y, y_dot = 1-y^2, t_dot = 1 & t < 10>@invariant(1+x>0, x<1)
        # {!(x >= 2 | x <= -2)}
        runVerify(self, pre="(-1/3 + x)^2 + (-1/3 + y)^2 < 1/16",
                  hp="t := 0; \
                     <x_dot = (1-x^2)*y, y_dot = 1-y^2, t_dot = 1 & t < 10> \
                      invariant \
                          [1 + x > 0] {dbx}\
                          [x < 1] {dbx};",
                  post="!(x >= 2 | x <= -2)",)

    def testNonlinear42(self):
        # Nonlinear benchmark, problem 42
        # {(-1/3 + x)^2 + (-1/3 + y)^2 < 1/16}
        #      t := 0;
        #     <x_dot = y, y_dot = -x+y*(1-x^2-y^2), t_dot = 1 & t < 10>
        #       @invariant(x^2+y^2 < 1, 346400*(x^2+y^2)>8503)
        # {!(x^2 + y^2 == 0 | x >= 2 | x <= -2)}
        runVerify(self, pre="(-1/3 + x)^2 + (-1/3 + y)^2 < 1/16",
                  hp="t := 0; \
                     <x_dot = y, y_dot = -x+y*(1-x^2-y^2), t_dot = 1 & t < 10> \
                      invariant \
                          [x^2+y^2 < 1] {dbx}\
                          [346400*(x^2+y^2)>8503] {dbx};",
                  post="!(x^2 + y^2 == 0 | x >= 2 | x <= -2)")

    def testNonlinear43(self):
        # Nonlinear benchmark, problem 43
        # {(-1/3 + x)^2 + (-1/3 + y)^2 < 1/16}
        #      t := 0;
        #     <x_dot = -x-y+x*(x^2+2*y^2), 
        #      y_dot = x-y+y*(x^2+2*y^2),
        #      t_dot = 1 & t < 10>@invariant(x^2+y^2>0, 5*x^2+2*x*y+7*y^2 < 4)
        # {!((x == 0 & y == 0) | x <= -2 |y <= -1)}
        runVerify(self, pre="(-1/3 + x)^2 + (-1/3 + y)^2 < 1/16",
                  hp="t := 0; \
                     <x_dot = -x-y+x*(x^2+2*y^2), \
                      y_dot = x-y+y*(x^2+2*y^2), \
                      t_dot = 1 & t < 10> \
                      invariant \
                          [x^2+y^2 > 0] {dbx} \
                          [5*x^2+2*x*y+7*y^2 < 4] {dbx};",
                  post="!((x == 0 & y == 0) | x <= -2 |y <= -1)")

    def testNonlinear44(self):
        # Nonlinear benchmark, problem 44
        # {b == 1/2 & y == 1/2}
        #      t := 0;
        #     <b_dot = -b+b^3-y+b*y^2, 
        #      y_dot = b-y+b^2*y+y^3,
        #      t_dot = 1 & t < 10>@invariant(b^2+y^2 < 1)
        # {!(b^2 + y^2 > 2)}
        runVerify(self, pre="b == 1/2 & y == 1/2",
                  hp="t := 0; \
                     <b_dot = -b+b^3-y+b*y^2, \
                      y_dot = b-y+b^2*y+y^3, \
                      t_dot = 1 & t < 10> \
                      invariant [b^2+y^2 < 1] {dbx};",
                  post="!(b^2 + y^2 > 2)")

    def testNonlinear45(self):
        # Nonlinear benchmark, problem 45
        # {x^2 <= 1/2 & y^2 <= 1/3}
        #      t := 0;
        #     <x_dot = -x - (1117*y)/500 + (439*y^3)/200 - (333*y^5)/500, 
        #      y_dot = x + (617*y)/500 - (439*y^3)/200 + (333*y^5)/500,
        #      t_dot = 1 & t < 10>
        #     @invariant(x^2 + x*y + y^2 - 111/59 <= 0)
        # {x - 4*y < 8}
        runVerify(self, pre="x^2 <= 1/2 & y^2 <= 1/3",
                  hp="t := 0; \
                     <x_dot = -x - (1117*y)/500 + (439*y^3)/200 - (333*y^5)/500, \
                      y_dot = x + (617*y)/500 - (439*y^3)/200 + (333*y^5)/500, \
                      t_dot = 1 & t < 10> \
                      invariant \
                          [x^2 + x*y + y^2 - 111/59 <= 0] {bc};",
                  post="x - 4*y < 8")

    def testNonlinear46(self):
        # Nonlinear benchmark, problem 46
        # {(-1/3 + x)^2 + (-1/3 + y)^2 < 1/16}
        #      t := 0;
        #     <x_dot = (2+x)*(-((1-x)*x)+y), y_dot = -y, t_dot = 1 & t < 10>@invariant(2+x>0)
        # {!(x <= -5/2)}
        runVerify(self, pre="(-1/3 + x)^2 + (-1/3 + y)^2 < 1/16",
                  hp="t := 0; \
                     <x_dot = (2+x)*(-((1-x)*x)+y), y_dot = -y, t_dot = 1 & t < 10> \
                      invariant [2 + x > 0] {dbx};",
                  post="!(x <= -5/2)")

    def testNonlinear47(self):
        # Nonlinear benchmark, problem 47
        # {(-1/3 + x)^2 + (-1/3 + y)^2 < 1/16}
        #      t := 0;
        #     <x_dot = -x+2*y+x^2*y+x^4*y^5, 
        #      y_dot = -y-x^4*y^6+x^8*y^9,
        #      t_dot = 1 & t < 10>@invariant(y>0)
        # {!(x <= -1 | y <= -1)}
        runVerify(self, pre="(-1/3 + x)^2 + (-1/3 + y)^2 < 1/16",
                  hp="t := 0; \
                     <x_dot = -x+2*y+x^2*y+x^4*y^5, \
                      y_dot = -y-x^4*y^6+x^8*y^9, \
                      t_dot = 1 & t < 10> \
                      invariant \
                          [y > 0] {dbx} \
                          [x > 0] {dbx};",
                  post="!(x <= -1 | y <= -1)")

    def testNonlinear48(self):
        # Nonlinear benchmark, problem 48
        # {4 <= x1 & x1 <= 4.5 & 1 <= x2 & x2 <= 2}
        #     <x1_dot = -11/2*x2 + x2^2 , 
        #      x2_dot = 6*x1-x1^2 &
        #     1 <= x1 & x1 <= 5 & 1 <= x2 & x2 <= 5>
        #       @invariant(349+4*((-9)+x1)*x1^2+x2^2*((-33)+4*x2)<=0)
        # {!(1 <= x1 & x1 <= 2 & 2 <= x2 & x2 <= 3)}
        runVerify(self, pre="4 <= x1 & x1 <= 4.5 & 1 <= x2 & x2 <= 2",
                  hp="<x1_dot = -11/2*x2 + x2^2, \
                       x2_dot = 6*x1-x1^2 \
                       & 1 < x1 & x1 < 5 & 1 < x2 & x2 < 5> \
                      invariant \
                          [349+4*((-9)+x1)*x1^2+x2^2*((-33)+4*x2)<=0];",
                  post="!(1 <= x1 & x1 <= 2 & 2 <= x2 & x2 <= 3)")

    def testNonlinear49(self):
        # Nonlinear benchmark, problem 49
        # {-1/5 <= x1 & x1 <= 1/5 & 
        #  3/10 <= x2 & x2 <= 7/10}
        #     <x1_dot = -x1 + 2*x1^3*x2^2,
        #      x2_dot = -x2 &
        #     -2 < x1 & x1 < 2 &
        #     -2 < x2 & x2 < 2>@invariant(x1*x2 < 1)
        # {!(
        #     -2 <= x1 & x1 <= -1 &
        #     -2 <= x2 & x2 <= -1
        #   )}
        runVerify(self, pre="-1/5 <= x1 & x1 <= 1/5 & \
                             3/10 <= x2 & x2 <= 7/10",
                  hp="<x1_dot = -x1 + 2*x1^3*x2^2, \
                       x2_dot = -x2 & \
                       -2 < x1 & x1 < 2 & \
                       -2 < x2 & x2 < 2> \
                      invariant \
                        [x1*x2 < 1] {dbx};",
                  post="!( \
                            -2 <= x1 & x1 <= -1 & \
                            -2 <= x2 & x2 <= -1 \
                        )")

    def testNonlinear50(self):
        # Nonlinear benchmark, problem 50
        #  {-1 <= x1 & x1 <= 0 &
        #   -1 <= x2 & x2 <= 0}
        #     <x1_dot = -1 + x1^2 + x2^2, 
        #      x2_dot = 5*(-1 + x1*x2) &
        #     -2 < x1 & x1 < 2 &
        #     -2 < x2 & x2 < 2>@invariant(22667*x1^2+x2*(257910+6221*x2)+x1*(141840+15973*x2) < 42786)
        #  {!(
        #     1 <= x1 & x1 <= 2 &
        #     1 <= x2 & x2 <= 2
        #   )}
        runVerify(self, pre="-1 <= x1 & x1 <= 0 & \
                             -1 <= x2 & x2 <= 0",
                  hp="<x1_dot = -1 + x1^2 + x2^2, \
                       x2_dot = 5*(-1 + x1*x2) & \
                       -2 < x1 & x1 < 2 & \
                       -2 < x2 & x2 < 2> \
                      invariant [22667*x1^2+x2*(257910+6221*x2)+x1*(141840+15973*x2) < 42786] {bc};",
                  post="!( \
                            1 <= x1 & x1 <= 2 & \
                            1 <= x2 & x2 <= 2 \
                        )")

    def testNonlinear51(self):
        # Nonlinear benchmark, problem 51
        #  {-1/10 <= x1 & x1 <= 1/10 &
        #   -1/10 <= x2 & x2 <= 1/10}
        #     <x1_dot = -2*x1 + x1^2 + x2, 
        #      x2_dot = x1 - 2*x2 + x2^2 &
        #     -1 < x1 & x1 < 1 &
        #     -1 < x2 & x2 < 1>@invariant(x1*(189+111470000*x1)+x2*(189+111470000*x2) < 43801000)
        #  {!(
        #     1/2 <= x1 & x1 <= 1 &
        #     1/2 <= x2 & x2 <= 1
        #   )}
        runVerify(self, pre="-1/10 <= x1 & x1 <= 1/10 & \
                             -1/10 <= x2 & x2 <= 1/10",
                  hp="<x1_dot = -2*x1 + x1^2 + x2, \
                       x2_dot = x1 - 2*x2 + x2^2 & \
                       -1 < x1 & x1 < 1 & \
                       -1 < x2 & x2 < 1> \
                      invariant [x1*(189+111470000*x1)+x2*(189+111470000*x2) < 43801000] {bc};",
                  post="!( \
                            1/2 <= x1 & x1 <= 1 & \
                            1/2 <= x2 & x2 <= 1 \
                        )"   
                )
    def testNonlinear52(self):
        # Nonlinear benchmark, problem 52
        #  {-3/2 <= x1 & x1 <= -1/2 &
        #   -3/2 <= x2 & x2 <= -1/2}
        #     <x1_dot = -x1 + x1*x2, x2_dot = -x2 &
        #     -2 <= x1 & x1 <= 2 &
        #     -2 <= x2 & x2 <= 2>@invariant(x2 < 0)
        #  {!(
        #     -1/2 <= x1 & x1 <= 1/2 &
        #      1/2 <= x2 & x2 <= 3/2
        #   )}
        runVerify(self, pre="-3/2 <= x1 & x1 <= -1/2 & \
                             -3/2 <= x2 & x2 <= -1/2",
                  hp="<x1_dot = -x1 + x1*x2, x2_dot = -x2 & \
                        -2 < x1 & x1 < 2 & \
                        -2 < x2 & x2 < 2> \
                      invariant \
                          [x2 < 0] {dbx};",
                  post="!( \
                           -1/2 <= x1 & x1 <= 1/2 & \
                            1/2 <= x2 & x2 <= 3/2 \
                        )")

    def testNonlinear53(self):
        # Nonlinear benchmark, problem 53
        #  {-3/2 <= x1 & x1 <= -1/2 &
        #   -3/2 <= x2 & x2 <= -1/2}
        #     <x1_dot = -x1 + x1*x2, x2_dot = -x2 &
        #     -2 <= x1 & x1 <= 2 &
        #     -2 <= x2 & x2 <= 2>@invariant(x2 < 0)
        #  {!(
        #     -1/2 <= x1 & x1 <= 1/2 &
        #      1/2 <= x2 & x2 <= 3/2
        #   )}
        runVerify(self, pre="-3/2 <= x1 & x1 <= -1/2 & \
                             -3/2 <= x2 & x2 <= -1/2",
                  hp="<x1_dot = -x1 + x1*x2, x2_dot = -x2 & \
                        -2 < x1 & x1 < 2 & \
                        -2 < x2 & x2 < 2> \
                      invariant [x2 < 0] {dbx};",
                  post="!( \
                            -1/2 <= x1 & x1 <= 1/2 & \
                            1/2 <= x2 & x2 <= 3/2 \
                        )")

    # TODO: Problem 54, invariant unknown

    def testNonlinear55(self):
        # Nonlinear benchmark, problem 55
        # {(-3/2 + x)^2 + y^2 <= 1/4}
        #      t := 0;
        #     <x_dot = x, y_dot = -x+x^3/3-y, t_dot = 1 & t < 10>
        #     @invariant(x>=0)
        # {!((1 + x)^2 + (1 + y)^2 <= 4/25)}
        runVerify(self, pre="(-3/2 + x)^2 + y^2 <= 1/4",
                  hp="t := 0; \
                      <x_dot = x, y_dot = -x+x^3/3-y, t_dot = 1 & t < 10> \
                      invariant [x >= 0] {dbx};",
                  post="!((1 + x)^2 + (1 + y)^2 <= 4/25)")

    # TODO: nonlinear problem 56, ODE rule is not clear. Not proved by keymaerax yet.
    # def testNonlinear56(self):
    #     # Nonlinear benchmark, problem 56
    #     # {-3<=x & x<=-2 & -3<=y & y<=-2}
    #     #      t := 0;
    #     #     <x_dot = 4 + 21*x - 7*y + 42*x^2 - 24*x*y + 4*y^2 + 27*x^3 - 9*x^2*y + 6*x^4,
    #     #      y_dot = 12 + 71*x -21*y + 150*x^2 -80*x*y + 12*y^2 + 99*x^3 - 39*x^2*y + 2*x*y^2 + 18*x^4, 
    #     #      t_dot = 1 & t < 10>
    #     #     @invariant(3+x>=0, 3+y>=0, 4+3*x*(1+x)*(7+x*(7+2*x))+4*y^2>(7+3*x*(8+3*x))*y, 1+x*(3+x)>y, 1+3*x*(2+x)>2*y, 2+3*x < y, x < 0, y < 0)
    #     # {!(x >= 0 | y >= 0)}
    #     runVerify(self, pre="-3<=x & x<=-2 & -3<=y & y<=-2",
    #               hp="t := 0; \
    #                 <x_dot = 4 + 21*x - 7*y + 42*x^2 - 24*x*y + 4*y^2 + 27*x^3 - 9*x^2*y + 6*x^4, \
    #                 y_dot = 12 + 71*x -21*y + 150*x^2 -80*x*y + 12*y^2 + 99*x^3 - 39*x^2*y + 2*x*y^2 + 18*x^4, \
    #                 t_dot = 1 & t < 10>",
    #               post="!(x >= 0 | y >= 0)",
    #               diff_cuts={((1,), ()): ["3+x >= 0", "3+y>=0", "4+3*x*(1+x)*(7+x*(7+2*x))+4*y^2>(7+3*x*(8+3*x))*y", "..."]},
    #               darboux_rule={((1,), (0,)): "true",
    #                             ((1,), (1,)): "true",
    #                             ((1,), (2,)): "true"},
    #               wolfram_engine=True)

    # TODO: Problem 57. Invariant not known.

    def testNonlinear58(self):
        # Nonlinear benchmark, problem 58
        # {(x + 2)^2 + (y + 2)^2 <= 5}
        #    t := 0;
        #   <x_dot = x+2*y-y^2, y_dot = -y+y^2, t_dot = 1 & t < 10>
        #   @invariant(x+y < 0, x < ((-2)+y)*y)
        # {2*x+y < 0}
        runVerify(self, pre="(x + 2)^2 + (y + 2)^2 <= 5",
                  hp="t := 0; \
                      <x_dot = x+2*y-y^2, y_dot = -y+y^2, t_dot = 1 & t < 10> \
                      invariant \
                          [x+y < 0] {dbx} \
                          [x < ((-2)+y)*y] {bc} \
                          [2*x+y < 0];",
                  post="2*x+y < 0")

    def testNonlinear59(self):
        # Nonlinear benchmark, problem 59
        # {(x - 4)^2 + y^2 <= 1}
        #    t := 0;
        #   <x_dot = x+2*y-y^2, y_dot = -y+y^2, t_dot = 1 & t < 10>
        #   @invariant(y<=1, 273630+y*((-32671)+81001*y) < 123190*x)
        # {!(x < 2 | y > 1)}
        runVerify(self, pre="(x - 4)^2 + y^2 <= 1",
                  hp="t := 0; \
                      <x_dot = x+2*y-y^2, y_dot = -y+y^2, t_dot = 1 & t < 10> \
                      invariant \
                        [y<=1] {dbx} \
                        [273630+y*((-32671)+81001*y) < 123190*x] {bc};",
                  post="!(x < 2 | y > 1)")

    def testNonlinear60(self):
        # Nonlinear benchmark, problem 60
        # {(x+3)^2+(y+3)^2<=1}
        #   <x_dot = 3*x+y^2, y_dot = 5*y 
        #       & -6<=x & x<= 6 & -6 <= y & y<=6>
        #       @invariant(63232*x^3+x^2*((-66727)+176350*y)+10*x*(42940+y*(55669+25688*y))+10*(808140+y*(289690+9*y*(9466+1595*y))) < 0)
        # {x + y < -2}
        runVerify(self, pre="(x+3)^2+(y+3)^2<=1",
                  hp="<x_dot = 3*x+y^2, y_dot = 5*y \
                        & -6 < x & x < 6 & -6 < y & y < 6> \
                      invariant [63232*x^3+x^2*((-66727)+176350*y)+10*x*(42940+y*(55669+25688*y))+10*(808140+y*(289690+9*y*(9466+1595*y))) < 0] {bc};",
                  post="x + y < -2")

    # TODO: Nonlinear problem 61. Invariants unknown.

    def testNonlinear62(self):
        # Nonlinear benchmark, problem 62
        # {(x + 3)^2 + (y + 3)^2 <= 1}
        #    t := 0;
        #   <x_dot = x+y+x^2, y_dot = x*(1+y), t_dot = 1 & t < 10>
        #   @invariant(1+y < 0, 70030000+331*x^2+5*y*(4429100+61943*y) < 50*x*((-629110)+27787*y))]
        # {x+y < -2}
        runVerify(self, pre="(x + 3)^2 + (y + 3)^2 <= 1",
                  hp="t := 0; \
                     <x_dot = x+y+x^2, y_dot = x*(1+y), t_dot = 1 & t < 10> \
                      invariant [1+y < 0] {dbx} [70030000+331*x^2+5*y*(4429100+61943*y) < 50*x*((-629110)+27787*y)] {bc};",
                  post="x+y < -2")

    def testNonlinear63(self):
        # Nonlinear benchmark, problem 63
        # {(x - 4)^2 + (y - 4)^2 <= 1}
        #    t := 0;
        #   <x_dot = x+y+x^2, y_dot = x*(1+y), t_dot = 1 & t < 10>
        #   @invariant(1+y>0, x^2 < y*(x+y), 387150000+426*x^2+85*y < 36465000*x*y)
        # {(x - 2)^2 + (y - 2)^2 > 3}
        runVerify(self, pre="(x - 4)^2 + (y - 4)^2 <= 1",
                  hp="t := 0; \
                     <x_dot = x+y+x^2, y_dot = x*(1+y), t_dot = 1 & t < 10> \
                      invariant [1+y>0] {dbx} [x^2 < y*(x+y)] {dbx} [387150000+426*x^2+85*y < 36465000*x*y] {bc};",
                  post="(x - 2)^2 + (y - 2)^2 > 3")

    def testNonlinear64(self):
        # Nonlinear benchmark, problem 64
        # {(x + 1)^2 + (y - 4)^2 <= 1}
        #    t := 0;
        #   <x_dot = x+y+x^2, y_dot = x*(1+y), t_dot = 1 & t < 10>
        #       @invariant(1+y>0, 23921*x+18696*y+2089*x*y>5916)
        # {(x + 2)^2 + (y + 2)^2 > 2}
        runVerify(self, pre="(x + 1)^2 + (y - 4)^2 <= 1",
                  hp="t := 0; \
                     <x_dot = x+y+x^2, y_dot = x*(1+y), t_dot = 1 & t < 10> \
                      invariant [1+y>0] {dbx} [23921*x+18696*y+2089*x*y>5916] {bc};",
                  post="(x + 2)^2 + (y + 2)^2 > 2")

    # TODO: Nonlinear 65, 66, 67. Invariants unknown.

    def testNonlinear68(self):
        # Nonlinear benchmark, problem 68
        # {(x-1)^2+y^2<=0.04 &
        #   u1 == -1 & u2 == 3}
        #   <x_dot = u1*y-3/2*x^2-1/2*x^3, y_dot = u2*x-y 
        #       & -2<=x & x<=2 & -2<=y & y<=2>
        #    @invariant(x*((-26090)+x*(34696+12539*x))+38464*y < 61620)
        # {!((x+1.8)^2+y^2 <= 0.16)}
        runVerify(self, pre="(x-1)^2+y^2<=0.04 & u1 == -1 & u2 == 3",
                  hp="<x_dot = u1*y-3/2*x^2-1/2*x^3, y_dot = u2*x-y \
                      & -2<x & x<2 & -2<y & y<2> \
                      invariant [x*((-26090)+x*(34696+12539*x))+38464*y < 61620] {bc};",
                  post="!((x+1.8)^2+y^2 <= 0.16)",
                  constants={'u1', 'u2'})

    def testNonlinear69(self):
        # Nonlinear benchmark, problem 69
        # {(x1+1.125)^2 + (x2-0.625)^2 - 0.0125 <= 0}
        #    t := 0;
        #   <x1_dot = -x1+x1*x2, x2_dot = -x2, t_dot = 1 & t < 10>@invariant(x1 < 0)
        # {!((x1-0.875)^2 + (x2-0.125)^2 - 0.0125 <= 0)}
        runVerify(self, pre="(x1+1.125)^2 + (x2-0.625)^2 - 0.0125 <= 0",
                  hp="t := 0; \
                     <x1_dot = -x1+x1*x2, x2_dot = -x2, t_dot = 1 & t < 10> \
                      invariant [x1 < 0] {dbx};",
                  post="!((x1-0.875)^2 + (x2-0.125)^2 - 0.0125 <= 0)")

    # TODO: Nonlinear 70. Invariants unknown.

    def testNonlinear71(self):
        # Nonlinear benchmark, problem 71
        # {x == 1 & y == 1 & z == 1}
        #    t := 1;
        #   <x_dot = x*y-x*z, y_dot = y*z-y*x, z_dot = z*x-z*y, 
        #    t_dot = 1 & t < 10>@invariant(x>0, y>0, z>0)
        # {x + 2*y + z^3 > 0}
        runVerify(self, pre="x == 1 & y == 1 & z == 1",
                  hp="t := 1; \
                    <x_dot = x*y-x*z, y_dot = y*z-y*x, z_dot = z*x-z*y, \
                     t_dot = 1 & t < 10> \
                      invariant [x>0] {dbx} [y>0] {dbx} [z>0] {dbx};",
                  post="x + 2*y + z^3 > 0")

    def testNonlinear72(self):
        # Nonlinear benchmark, problem 72
        # {x == -1 & y == -1 & z == -1}
        #    t := 0;
        #   <x_dot = x*y-x*z, y_dot = y*z-y*x, z_dot = z*x-z*y, 
        #    t_dot = 1 & t < 10>@invariant(x<0, y<0, z<0)
        # {x^5 + 12*y + z^3 < 0}
        runVerify(self, pre="x == -1 & y == -1 & z == -1",
                  hp="t := 0; \
                     <x_dot = x*y-x*z, y_dot = y*z-y*x, z_dot = z*x-z*y, \
                      t_dot = 1 & t < 10> \
                      invariant [x<0] {dbx} [y<0] {dbx} [z<0] {dbx};",
                  post="x^5 + 12*y + z^3 < 0")

    def testNonlinear73(self):
        # Nonlinear benchmark, problem 73
        # {x == 1 & y == 1 & z == -1}
        #    t := 0;
        #   <x_dot = x*y-x*z, y_dot = y*z-y*x, z_dot = z*x-z*y,
        #    t_dot = 1 & t < 10>@invariant(x>0, y>0, z<0)
        # {x + y - z > -2}
        runVerify(self, pre="x == 1 & y == 1 & z == -1",
                  hp="t := 0; \
                     <x_dot = x*y-x*z, y_dot = y*z-y*x, z_dot = z*x-z*y, \
                      t_dot = 1 & t < 10> \
                      invariant [x>0] {dbx} [y>0] {dbx} [z<0] {dbx};",
                  post="x + y - z > -2")

    def testNonlinear74(self):
        # Nonlinear benchmark, problem 74
        # {x == 1 & y == 0 & z == 0}
        #    t := 0;
        #   <x_dot = x*z , y_dot = y*z , z_dot = -x^2-y^2 & t < 10>
        #   @invariant(x^2+y^2+z^2 == 1, x+y>0)
        # {!((x > -1 -> x^2 > 2) | z > 1)}
        runVerify(self, pre="x == 1 & y == 0 & z == 0",
                  hp="t := 0; \
                     <x_dot = x*z , y_dot = y*z , z_dot = -x^2-y^2 & t < 10> \
                      invariant [x^2+y^2+z^2 == 1] \
                                [x + y > 0] {dbx};",
                  post="!((x > -1 -> x^2 > 2) | z > 1)")

    def testNonlinear75(self):
        # Nonlinear benchmark, problem 75
        # {x1 == 0 & x2 == 0 & x3 == 0}
        #    t := 0;
        #   <x1_dot = 1 - x1 - (x1*x2)/4, 
        #    x2_dot = x2*(-1 + 2*x3), 
        #    x3_dot = x1/4 - 2*x3^2,
        #    t_dot = 1 & t < 10>@invariant(x2==0, x1<=5)
        # {x1 <= 5 & x2 <= 5 & x3 <= 5}
        # In this problem, sympy.div cannot compute the right quotient and remainder
        # for the last cut, so we use wolfram engine or offer the cofactors.
        runVerify(self, pre="x1 == 0 & x2 == 0 & x3 == 0",
                  hp="t := 0; \
                     <x1_dot = 1 - x1 - (x1*x2)/4, \
                      x2_dot = x2*(-1 + 2*x3), \
                      x3_dot = x1/4 - 2*x3^2, \
                      t_dot = 1 & t < 10> \
                      invariant [x2==0] {dbx} [x1<=5] {dbx} [x3 <= 5] {dbx -10 - 2*x3};",
                  post="x1 <= 5 & x2 <= 5 & x3 <= 5" 
                #   wolfram_engine=True,
                )

    def testNonlinear76(self):
        # Nonlinear benchmark, problem 76
        # {x == 1/4 & y == 1/8 & z == 1/10}
        #      t := 0;
        #     <x_dot = x^2-x*(x^3+y^3+z^3), 
        #      y_dot = y^2-y*(x^3+y^3+z^3), 
        #      z_dot = z^2-z*(x^3+y^3+z^3),
        #      t_dot = 1 & t < 10>@invariant(x^2+y^2+z^2 < 1)
        # {!(x > 10 | y > 5 | z <= -20)}
        runVerify(self, pre="x == 1/4 & y == 1/8 & z == 1/10",
                  hp="t := 0; \
                     <x_dot = x^2-x*(x^3+y^3+z^3), \
                      y_dot = y^2-y*(x^3+y^3+z^3), \
                      z_dot = z^2-z*(x^3+y^3+z^3), \
                      t_dot = 1 & t < 10> \
                      invariant [x^2+y^2+z^2 < 1] {dbx};",
                  post="!(x > 10 | y > 5 | z <= -20)")

    def testNonlinear77(self):
        # Nonlinear benchmark, problem 77
        # {x == 1 & y == 2 & z == 3} 
        #      t := 0;
        #     <x_dot = y*z, y_dot = x*z, z_dot = x*y,
        #      t_dot = 1 & t < 10>@invariant(5+y^2==z^2)
        # {!(x==5 & y^2==27 & z^2==34)}
        runVerify(self, pre="x == 1 & y == 2 & z == 3",
                  hp="t := 0; \
                     <x_dot = y*z, y_dot = x*z, z_dot = x*y, \
                      t_dot = 1 & t < 10> \
                      invariant [5+y^2==z^2];",
                   post="!(x==5 & y^2==27 & z^2==34)")

    # Nonlinear problem 78 is the same with problem 77.

    def testNonlinear79(self):
        # Nonlinear benchmark, problem 79
        # {x == 2 & y == 0 & r == 2}
        #     t := 0;
        #    <x_dot = -y*omega, y_dot = x*omega, omega_dot = -g/r^2*x,
        #     t_dot = 1 & t < 10>@invariant(x^2+y^2>=4)
        # {2*x^2+y^2 > 3}
        runVerify(self, pre="x == 2 & y == 0 & r == 2",
                  hp="t := 0; \
                     <x_dot = -y*omega, y_dot = x*omega, omega_dot = -g/r^2*x, \
                      t_dot = 1 & t < 10> \
                      invariant [x^2+y^2>=4];",
                  post="2*x^2+y^2 > 3")

    def testNonlinear80(self):
        # Nonlinear benchmark, problem 80
        # {x == 5 & y == 3 & z == -4}
        #     t := 0;
        #    <x_dot = y, y_dot = x-y-x*z, z_dot = x^2-z,
        #     t_dot = 1 & t < 10>@invariant(z>=-5)
        # {!(z < 0 & z^2 > 26+x^2)}
        runVerify(self, pre="x == 5 & y == 3 & z == -4",
                  hp="t := 0; \
                     <x_dot = y, y_dot = x-y-x*z, z_dot = x^2-z, \
                      t_dot = 1 & t < 10> \
                      invariant [z >= -5] {dbx};",
                  post="!(z < 0 & z^2 > 26+x^2)",
                  wolfram_engine=True)

    def testNonlinear81(self):
        # Nonlinear benchmark, problem 81
        #  {-0.25 <= x1 & x1 <= 0.75 &
        #   -0.25 <= x2 & x2 <= 0.75 &
        #   -0.75 <= x3 & x3 <= 0.25}
        #     <x1_dot = -x2, x2_dot = -x3, x3_dot = -x1 - 2*x2 - x3 + x1^3 &
        #     -2 <= x1 & x1 <= 2 &
        #     -2 <= x2 & x2 <= 2 &
        #     -2 <= x3 & x3 <= 2>
        #       @invariant(7*x1*(425300+3161*x1^2) < 5*(909080+23721*x2+295290*x3))
        #  {!(
        #      1 <= x1 & x1 <= 2 &
        #     -2 <= x2 & x2 <= -1 &
        #     -2 <= x3 & x3 <= -1
        #   )}
        runVerify(self, pre="-0.25 <= x1 & x1 <= 0.75 & \
                             -0.25 <= x2 & x2 <= 0.75 & \
                             -0.75 <= x3 & x3 <= 0.25",
                  hp="<x1_dot = -x2, x2_dot = -x3, x3_dot = -x1 - 2*x2 - x3 + x1^3 & \
                      -2 < x1 & x1 < 2 & \
                      -2 < x2 & x2 < 2 & \
                      -2 < x3 & x3 < 2> \
                      invariant [7*x1*(425300+3161*x1^2) < 5*(909080+23721*x2+295290*x3)] {bc};",
                  post="!( \
                            1 <= x1 & x1 <= 2 & \
                            -2 <= x2 & x2 <= -1 & \
                            -2 <= x3 & x3 <= -1 \
                        )")

    # TODO: Nonlinear problem 82, Proving invariant stuck.

    def testNonlinear83(self):
        # Nonlinear benchmark, problem 83
        # {(x-1.5)^2+y^2+z^2 <= 0.0625 &
        #   u1 == -1 & u2 == 1 & u3 == 4.75}
        #   <x_dot = u1*x+y-z, y_dot = -x*(z+1)-u2*y, z_dot = -0.77*x-u3*z 
        #    & -2<=x & x<=2 & -2<=y & y<=2 & -2<=z & z<=2>
        #    @invariant(12583*x+97936*z < 60051)
        # {!(x+1)^2+(y+1)^2+(z-1)^2 <= 0.0625}
        runVerify(self, pre="(x-1.5)^2+y^2+z^2 <= 0.0625 & \
                             u1 == -1 & u2 == 1 & u3 == 4.75",
                  hp="<x_dot = u1*x+y-z, \
                       y_dot = -x*(z+1)-u2*y, \
                       z_dot = -0.77*x-u3*z \
                        & -2<x & x<2 & \
                          -2<y & y<2 & \
                          -2<z & z<2> \
                      invariant [12583*x+97936*z < 60051] {bc};",
                  post="!(x+1)^2+(y+1)^2+(z-1)^2 <= 0.0625",
                  constants={"u1", "u2", "u3"})

    # TODO: Nonlinear problem 84, invariant not implied by precondition

    def testNonlinear85(self):
        # Nonlinear benchamark, problem 85
        # {0<=x1 & x1<=0.5 & 0<=x2 & x2<=0.5 & -0.5<=x3 & x3<=0 &
        #   u1 == -0.85 & u2 == -1.15 & u3 == -1.16 & u4 == 2.2}
        #     <x1_dot = u1*x2, x2_dot = u2*x3, x3_dot = u3*x1-u4*x2-x3+x1^3 
        #       & -2<=x1 & x1<=2 & -2<=x2 & x2<=2 & -2<=x3 & x3<=2>
        #    @invariant(722620*x1+17021*x1^3 < 890220+33020*x2+318530*x3)
        # {!(0.5<=x1 & x1<=2 & -2<=x2 & x2<=-1.5 & -2<=x3 & x3<=-1.5)}
        runVerify(self, pre="0<=x1 & x1<=0.5 & 0<=x2 & x2<=0.5 & -0.5<=x3 & x3<=0 & \
                             u1 == -0.85 & u2 == -1.15 & u3 == -1.16 & u4 == 2.2",
                  hp="<x1_dot = u1*x2, x2_dot = u2*x3, x3_dot = u3*x1-u4*x2-x3+x1^3 \
                     & -2<x1 & x1<2 & -2<x2 & x2<2 & -2<x3 & x3<2> \
                      invariant [722620*x1+17021*x1^3 < 890220+33020*x2+318530*x3] {bc};",
                  post="!(0.5<=x1 & x1<=2 & -2<=x2 & x2<=-1.5 & -2<=x3 & x3<=-1.5)",
                  constants={"u1", "u2", "u3", "u4"})

    # TODO: Program 86 should also be proved by dbx automatically. 
    # But now it can only proved by dI or by offering the parameter g.
    def testNonlinear86(self):
        # Nonlinear benchmark, problem 86
        # {x1^2 + x2^2 + x3^2 >= 5}
        #     t := 0;
        #    <x1_dot = 2*x1+x2,
        #     x2_dot = x1+3*x2-x3,
        #     x3_dot = -x1+2*x2+3*x3,
        #     t_dot = 1 & t < 10>
        # {!(x1^2+x2^2+x3^2 < 1)}
        runVerify(self, pre="x1^2 + x2^2 + x3^2 >= 5",
                  hp="t := 0; \
                     <x1_dot = 2*x1+x2, \
                      x2_dot = x1+3*x2-x3, \
                      x3_dot = -x1+2*x2+3*x3, \
                      t_dot = 1 & t < 10> \
                      invariant [x1^2+x2^2+x3^2 >= 1] {di};",
                  post="!(x1^2+x2^2+x3^2 < 1)")

    def testNonlinear87(self):
        # Nonlinear benchmark, problem 87
        # {x2 < x1 & x2 < x3 & x3 > 0 & x3 < 12}
        #    t := 0;
        #    <x1_dot=4*x1-5*x2+2*x3,
        #     x2_dot=5*x1-7*x2+3*x3,
        #     x3_dot=6*x1-9*x2+4*x3,
        #     t_dot = 1 & t < 10>@invariant(x1+x3>=2*x2)
        # {!(x1 < 0.5 & x3 < 0.5 & x2 > 1)}
        runVerify(self, pre="x2 < x1 & x2 < x3 & x3 > 0 & x3 < 12",
                  hp="t := 0; \
                     <x1_dot=4*x1-5*x2+2*x3, \
                      x2_dot=5*x1-7*x2+3*x3, \
                      x3_dot=6*x1-9*x2+4*x3, \
                      t_dot = 1 & t < 10> \
                    invariant [x1+x3>=2*x2] {dbx};",
                  post="!(x1 < 0.5 & x3 < 0.5 & x2 > 1)")

    def testNonlinear88(self):
        # Nonlinear benchmark, problem 88
        # {(x2 >= 0 & 2*x2 < x3 & 3*x2 < x1) | 
        #  (x2 <= 0 & x1 >= -0.4 & x3 > 0.5)}
        #     t := 0;
        #    <x1_dot=4*x1-x2,
        #     x2_dot=3*x1+x2-x3,
        #     x3_dot=x1+x3>@invariant(x1+x3>x2)
        # {!(4*x1 < x2 & x3 < x1 & x2 > 0.5)}
        runVerify(self, pre="(x2 >= 0 & 2*x2 < x3 & 3*x2 < x1) | \
                             (x2 <= 0 & x1 >= -0.4 & x3 > 0.5)",
                  hp="t := 0; \
                     <x1_dot=4*x1-x2, \
                      x2_dot=3*x1+x2-x3, \
                      x3_dot=x1+x3, \
                      t_dot = 1 & t < 10> \
                      invariant [x1+x3>x2] {dbx};",
                  post="!(4*x1 < x2 & x3 < x1 & x2 > 0.5)")
    
    def testNonlinear89(self):
        # Nonlinear benchmark, problem 89
        # {x3 > 1 & x1 > (x1 - x3)^2 & x3 > x2}
        #     t := 0;
        #    <x1_dot=4*x1-x2,
        #     x2_dot=3*x1+x2-x3,
        #     x3_dot=x1+x3,
        #     t_dot = 1 & t < 10>@invariant((x1-x3)^2-2*x3*(x1-x2+x3) < 0)
        # {!(x3 < 0 & x1 - x2 + x3 > 0)}
        runVerify(self, pre="x3 > 1 & x1 > (x1 - x3)^2 & x3 > x2",
                  hp="t := 0; \
                     <x1_dot=4*x1-x2, \
                      x2_dot=3*x1+x2-x3, \
                      x3_dot=x1+x3, \
                      t_dot = 1 & t < 10> \
                    invariant [(x1-x3)^2-2*x3*(x1-x2+x3) < 0] {dbx};",
                  post="!(x3 < 0 & x1 - x2 + x3 > 0)")

    def testNonlinear90(self):
        # Nonlinear benchmark, problem 90
        # {x1 > 0 & x2 > 0 & x3 > 0 & x1 > x2 & x3 > x1}
        #     t := 0;
        #    <x1_dot = 4*x1-x2,
        #     x2_dot = 3*x1+x2-x3,
        #     x3_dot = x1+x3,
        #     t_dot = 1 & t < 10>@invariant((x1-x3)^2-2*x3*(x1-x2+x3) < (x1-x2+x3)^2)
        # {!(x2 == x3 & x3 > 5 & x1 < 1/5)}
        runVerify(self, pre="x1 > 0 & x2 > 0 & x3 > 0 & x1 > x2 & x3 > x1",
                  hp="t := 0; \
                     <x1_dot = 4*x1-x2, \
                      x2_dot = 3*x1+x2-x3, \
                      x3_dot = x1+x3, \
                      t_dot = 1 & t < 10> \
                      invariant [(x1-x3)^2-2*x3*(x1-x2+x3) < (x1-x2+x3)^2] {dbx};",
                  post="!(x2 == x3 & x3 > 5 & x1 < 1/5)")

    # TODO: Nonlinear benchmark, problem 91. Invariants unknown.

    # TODO: Nonlinear benchmark, problem 92, 93, 94, 95. ODE rule unknown.

    def testNonlinear96(self):
        # Nonlinear benchmark, problem 96
        # {2*y^2 + z5^2 <= 0.5 & b==1 & r==0}
        #     t := 0;
        #    <x_dot = s*(y-x),
        #     y_dot = r*x-y-x*z5,
        #     z5_dot = -b*z5+x*y,
        #     t_dot = 1 & t < 10>@invariant(y^2+z5^2<=1)
        # {y^2 + 2*z5^2 <= 5}
        runVerify(self, pre="2*y^2 + z5^2 <= 0.5 & b==1 & r==0",
                  hp="t := 0; \
                     <x_dot = s*(y-x), \
                      y_dot = r*x-y-x*z5, \
                      z5_dot = -b*z5+x*y, \
                      t_dot = 1 & t < 10> \
                      invariant [y^2+z5^2<=1] {bc};",
                  post="y^2 + 2*z5^2 <= 5",
                  constants={'b', 'r', 's'})

    def testNonlinear97(self):
        # Nonlinear benchmark, problem 97
        # {y^2 + 2*z6^2 <= 1 & b==1 & r==0 & s==1}
        #     t := 0;
        #    <x_dot=s*(y-x),
        #     y_dot=r*x-y-x*z6,
        #     z6_dot=-b*z6+x*y,
        #     t_dot = 1 & t < 10
        #    >@invariant(y^2+z6^2 <= 2)
        # {y^2 + 0.5*z6^2 <= 3}
        runVerify(self, pre="y^2 + 2*z6^2 <= 1 & b==1 & r==0 & s==1",
                  hp="t := 0; \
                     <x_dot=s*(y-x), \
                      y_dot=r*x-y-x*z6, \
                      z6_dot=-b*z6+x*y, \
                      t_dot = 1 & t < 10> \
                    invariant [y^2+z6^2 <= 2] {bc};",
                  post="y^2 + 0.5*z6^2 <= 3",
                  constants={"b", "r", "s"})

    # TODO:Nonlinear problem 98. How to define a function.
    def testNonlinear98(self):
        # Nonlinear benchmark, problem 98
        #     {x1==0
        #   & v1==0
        #   & x2==7/8
        #   & v2==0
        #   & k1==-1
        #   & k2==-1
        #   & k==-1
        #   & m1==5
        #   & m2==1
        #   & u10==0
        #   & u1==0
        #   & u8==320/49}
        #     t := 0;
        #     <x1_dot=v1, v1_dot=-k1/m1*x1-k2/m1*(x1-x2), 
        #     x2_dot=v2, v2_dot=-k2/m2*(x2-x1),
        #     t_dot = 1 & t < 10>
        #       @invariant(v1*v2+(-3)/10*v2^2+1/2*x1^2+(-1)*x1*x2+2/5*x2^2>=358/1169)
        # {!u8*v1*v2+k2*x1*x2*(m1*u8-2*m2*u10)/(m1*m2) + u10*v1^2+u1
        # + 1/2*v2^2*(k1*m2*u8-k2*m1*u8+k2*m2*u8+2*k2*m2*u10)/(k2*m1)
        # + 1/2*(2*k1*m2*u10-k2*m1*u8+2*k2*m2*u10)*x1^2/(m1*m2)
        # + 1/2*(k1*m2*u8-k2*m1*u8+2*k2*m2*u10)*x2^2/(m1*m2) < -v1^2}
        runVerify(self, pre="x1==0 \
                          & v1==0 \
                          & x2==7/8 \
                          & v2==0 \
                          & k1==-1 \
                          & k2==-1 \
                          & k==-1 \
                          & m1==5 \
                          & m2==1 \
                          & u10==0 \
                          & u1==0 \
                          & u8==320/49",
                  hp="t := 0; \
                     <x1_dot=v1, v1_dot=-k1/m1*x1-k2/m1*(x1-x2), \
                      x2_dot=v2, v2_dot=-k2/m2*(x2-x1), \
                      t_dot = 1 & t < 10> \
                      invariant [v1*v2+(-3)/10*v2^2+1/2*x1^2+(-1)*x1*x2+2/5*x2^2 \
                                 >=358/1169];",
                  post="!u8*v1*v2+k2*x1*x2*(m1*u8-2*m2*u10)/(m1*m2) + u10*v1^2+u1 \
                        + 1/2*v2^2*(k1*m2*u8-k2*m1*u8+k2*m2*u8+2*k2*m2*u10)/(k2*m1) \
                        + 1/2*(2*k1*m2*u10-k2*m1*u8+2*k2*m2*u10)*x1^2/(m1*m2) \
                        + 1/2*(k1*m2*u8-k2*m1*u8+2*k2*m2*u10)*x2^2/(m1*m2) < -v1^2",
                  constants={'m1', 'm2', 'k1', 'k2', 'k', 'u1', 'u8', 'u10'})

    # TODO:Nonlinear problem 99. No tactic offered.

    # TODO:Nonlinear problem 100, result is false.
    # def testNonlinear100(self):
    #     # Nonlinear benchmark, problem 100
    #     # {x1 == 1/20 & x2 == 1/32 & sint==0 & cost==1} /* t==0 initially */
    #     #    t := 0;
    #     #   <x1_dot=x2, x2_dot=-x2-(2+sint)*x1, sint_dot=cost, cost_dot=-sint,
    #     #    t_dot = 1 & t < 10>
    #     #   @invariant(cost^2+sint^2<=100000/99999, cost^2+sint^2>=1)
    #     # {98*x1^2 + 24*x1*x2 + 24*x2*x1 + 55*x2^2 < 1}
    #     runVerify(self, pre="x1 == 1/20 & x2 == 1/32 & sint==0 & cost==1",
    #               hp="t := 0; \
    #                  <x1_dot=x2, x2_dot=-x2-(2+sint)*x1, sint_dot=cost, cost_dot=-sint, \
    #                  t_dot = 1 & t < 10>",
    #               post="98*x1^2 + 24*x1*x2 + 24*x2*x1 + 55*x2^2 < 1",
    #               diff_cuts={((1,), ()): ["cost^2+sint^2<=100000/99999", 
    #                                        "cost^2+sint^2>=1",
    #                                        "98*x1^2 + 24*x1*x2 + 24*x2*x1 + 55*x2^2 < 1"]},
    #               darboux_rule={((1,), (2,)): "true"},
    #               wolfram_engine=True)

    # TODO: Nonlinear problem 101. No tactic. Post not implied by inv.

    def testNonlinear102(self):
        # Nonlinear benchmark, problem 102
        # {x1 == 1 & x2 == 1 & x3 == 1 & x4 == 1}
        #     t := 0;
        #    <x1_dot=x1 - 2*x2 - x4,
        #     x2_dot=-x1 + 4*x2 - x3 + 2*x4,
        #     x3_dot=2*x2 + x3 + x4,
        #     x4_dot=2*x1 - 4*x2 + 2*x3 - 2*x4,
        #     t_dot = 1 & t < 10>@invariant(x1+x3 == x2+x4)
        # {!(x1 == 10 & x2 == 0 & x3 == 2 & x4 == 3)}
        runVerify(self, pre="x1 == 1 & x2 == 1 & x3 == 1 & x4 == 1",
                  hp="t := 0; \
                     <x1_dot=x1 - 2*x2 - x4, \
                      x2_dot=-x1 + 4*x2 - x3 + 2*x4, \
                      x3_dot=2*x2 + x3 + x4, \
                      x4_dot=2*x1 - 4*x2 + 2*x3 - 2*x4, \
                      t_dot = 1 & t < 10> \
                      invariant [x1+x3 == x2+x4] {dbx};",
                  post="!(x1 == 10 & x2 == 0 & x3 == 2 & x4 == 3)")

    def testNonlinear103(self):
        # Nonlinear benchmark, problem 103
        # {0.5*(x1 + x3 + 2*x4)^2 > 3}
        #     t := 0;
        #    <x1_dot=-3*x1+x2+4*x3+2*x4,
        #     x2_dot=8*x1-3*x2-2*x3+6*x4,
        #     x3_dot=-9*x1+3*x2+4*x3-4*x4,
        #     x4_dot=6*x1-3*x2-4*x3+2*x4,
        #     t_dot = 1 & t < 10>@invariant((-x2 + x4)^2 + (x1 + x3 + 2*x4)^2 > 3)
        # {(-x2 + x4)^2 + 2*(x1 + x3 + 2*x4)^2 > 1}
        runVerify(self, pre="0.5*(x1 + x3 + 2*x4)^2 > 3",
                  hp="t := 0; \
                     <x1_dot=-3*x1+x2+4*x3+2*x4, \
                      x2_dot=8*x1-3*x2-2*x3+6*x4, \
                      x3_dot=-9*x1+3*x2+4*x3-4*x4, \
                      x4_dot=6*x1-3*x2-4*x3+2*x4, \
                      t_dot = 1 & t < 10> \
                      invariant [(-x2 + x4)^2 + (x1 + x3 + 2*x4)^2 > 3] {dbx};",
                  post="(-x2 + x4)^2 + 2*(x1 + x3 + 2*x4)^2 > 1")

    def testNonlinear104(self):
        # Nonlinear benchmark, problem 104
        # {3*(x1 - x2 + 2*x4)^2 + 2*(-x1 + 2*x2 + 2*x3)^2 < 1.5}
        #     t := 0;
        #    <x1_dot=-3*x1+x2+4*x3+2*x4,
        #     x2_dot=8*x1-3*x2-2*x3+6*x4,
        #     x3_dot=-9*x1+3*x2+4*x3-4*x4,
        #     x4_dot=6*x1-3*x2-4*x3+2*x4,
        #     t_dot = 1 & t < 10>@invariant((x1 - x2 + 2*x4)^2 + (-x1 + 2*x2 + 2*x3)^2 < 2)
        # {!(x2 > 1 & x1 > 4*x2 & x4 > 0)}
        runVerify(self, pre="3*(x1 - x2 + 2*x4)^2 + 2*(-x1 + 2*x2 + 2*x3)^2 < 1.5",
                  hp="t := 0; \
                     <x1_dot=-3*x1+x2+4*x3+2*x4, \
                      x2_dot=8*x1-3*x2-2*x3+6*x4, \
                      x3_dot=-9*x1+3*x2+4*x3-4*x4, \
                      x4_dot=6*x1-3*x2-4*x3+2*x4, \
                      t_dot = 1 & t < 10> \
                      invariant [(x1 - x2 + 2*x4)^2 + (-x1 + 2*x2 + 2*x3)^2 < 2] {dbx};",
                  post="!(x2 > 1 & x1 > 4*x2 & x4 > 0)")

    # TODO: Nonlinear problem 105, 106, 107. No tactic offered.

    # TODO: Nonlinear problem 108. Auto rule unknown. Too slow to give a result.

    def testNonlinear109(self):
        # Nonlinear benchmark, problem 109
        # {x2 > 0 & x2 < 1 & u1 > 0 & u1 < 1 & u2 > -1/2 & u2 < 1 &
        #   theta == 1 & lp == 1 & g == 10 &
        #   u1^2+u2^2 == 1}
        #     t := 0;
        #    <x1_dot = x2,
        #     x2_dot = theta^2*u1*u2 - g/lp*u1,
        #     u1_dot = x2*u2,
        #     u2_dot = -x2*u1,
        #     t_dot = 1 & t < 10>
        #    @invariant(((-20)+u2)*u2+x2^2<=45/4)
        # {!(u2 < -0.75 & x2 == 4)}
        runVerify(self, pre="x2 > 0 & x2 < 1 & u1 > 0 & u1 < 1 & u2 > -1/2 & u2 < 1 & \
                             theta == 1 & lp == 1 & g == 10 & \
                             u1^2+u2^2 == 1",
                  hp="t := 0; \
                     <x1_dot = x2, \
                      x2_dot = theta^2*u1*u2 - g/lp*u1, \
                      u1_dot = x2*u2, \
                      u2_dot = -x2*u1, \
                      t_dot = 1 & t < 10> \
                    invariant [((-20)+u2)*u2+x2^2<=45/4];",
                  post="!(u2 < -0.75 & x2 == 4)",
                  constants={"theta", "g", "lp"})

    # TODO: Nonlinear problem 110, 111. Definitions and no tactic.

    def testNonlinear112(self):
        # Nonlinear benchmark, problem 112
        # {x1 > 1 & x3 > x1 & x4 > x3}
        #     t := 0;
        #    <x1_dot=2*(x1-3*x2+2*x3+x5),
        #     x2_dot=2*x1-x2+2*x3+2*x4,
        #     x3_dot=x2-x3,
        #     x4_dot=-3*x1+5*x2-4*x3-x4-2*x5,
        #     x5_dot=4*x2-2*x3+x4,
        #     t_dot = 1 & t < 10>
        #    /*@invariant(x1 + x3 + x4 > 0)*/
        # {!(x1 < -5 & x3 == -x4)}
        runVerify(self, pre="x1 > 1 & x3 > x1 & x4 > x3",
                  hp="t := 0; \
                     <x1_dot=2*(x1-3*x2+2*x3+x5), \
                      x2_dot=2*x1-x2+2*x3+2*x4, \
                      x3_dot=x2-x3, \
                      x4_dot=-3*x1+5*x2-4*x3-x4-2*x5, \
                      x5_dot=4*x2-2*x3+x4, \
                      t_dot = 1 & t < 10> \
                      invariant [x1 + x3 + x4 > 0] {dbx};",
                  post="!(x1 < -5 & x3 == -x4)")

    # TODO: Nonlinear problem 113. Definitions of constants value and no tactic.

    # TODO: Nonlinear problem 114, 115. No tactic and even inv->post is too slow to verify.

    def testNonlinear116_0(self):
        # {x > 10}<x_dot = 1 & x < 5>{x > 8}
        runVerify(self, pre="x > 10",
                  hp="<x_dot = 1 & x < 5> \
                       invariant [false];",
                  post="x > 8")
    # TODO: 
    # When not sure that ODE is executed or not, set invariant as true, 
    # because both cases should hold: 
    # Boundary of D -> Q and (P & !D) -> Q
    def testNonlinear116(self):
        # Nonlinear benchmark, problem 116
        # {x5 > -5 & x5 < x1 & x2 > x1 + 8 & x1 >= -1}
        #    <x1_dot=x1-2*x2+x3-2*x6,
        #     x2_dot=3*x2-x3-x5+2*x6,
        #     x3_dot=-x1+x3+2*x4+2*x5,
        #     x4_dot=-x1+x4+x5+x6,
        #     x5_dot=x1+x2+x5,
        #     x6_dot=x1-x2+x3-x4-x6 &
        #     x5 < 0>@invariant(x1+x2+x5 >= 0)
        # {!(x2 < 0 & x1 < x2 & x5 < x2)} //{x2 >= 0 | x1 >= x2 | x5 >= x2}
        runVerify(self, pre="x5 > -5 & x5 < x1 & x2 > x1 + 8 & x1 >= -1",
                  hp="<x1_dot=x1-2*x2+x3-2*x6, \
                       x2_dot=3*x2-x3-x5+2*x6, \
                       x3_dot=-x1+x3+2*x4+2*x5, \
                       x4_dot=-x1+x4+x5+x6, \
                       x5_dot=x1+x2+x5, \
                       x6_dot=x1-x2+x3-x4-x6 & \
                       x5 < 0> \
                       invariant [true];",
                  post="!(x2 < 0 & x1 < x2 & x5 < x2)")
                # #   diff_cuts={((), ()): ["x1+x2+x5 >= 0", "!(x2 < 0 & x1 < x2 & x5 < x2)"]},
                # #   darboux_rule={((), (0,)): "true"},
                #   diff_weakening_rule={((), ()): "true"})
        # I think this problem is different in hhl.

    # TODO: Nonlinear problem 117. No invariants offered.

# I took out this test because it was too slow -- Alex
    # def testNonlinear118(self):
    #     # Nonlinear benchmark, problem 118
    #     # It takes a very long time to prove.
    #     #  {0.99 <= x1 & x1 <= 1.01 &
    #     #   0.99 <= x2 & x2 <= 1.01 &
    #     #   0.99 <= x3 & x3 <= 1.01 &
    #     #   0.99 <= x4 & x4 <= 1.01 &
    #     #   0.99 <= x5 & x5 <= 1.01 &
    #     #   0.99 <= x6 & x6 <= 1.01 &
    #     #   0.99 <= x7 & x7 <= 1.01}
    #     #     <
    #     #       x1_dot = -0.4*x1 + 5*x3*x4,
    #     #       x2_dot = 0.4*x1 - x2,
    #     #       x3_dot = x2 - 5*x3*x4,
    #     #       x4_dot = 5*x5*x6 - 5*x3*x4,
    #     #       x5_dot = -5*x5*x6 + 5*x3*x4,
    #     #       x6_dot = 0.5*x7 - 5*x5*x6,
    #     #       x7_dot = -0.5*x7 + 5*x5*x6 &
    #     #       -2 <= x1 & x1 <= 2 &
    #     #       -2 <= x2 & x2 <= 2 &
    #     #       -2 <= x3 & x3 <= 2 &
    #     #       -2 <= x4 & x4 <= 2 &
    #     #       -2 <= x5 & x5 <= 2 &
    #     #       -2 <= x6 & x6 <= 2 &
    #     #       -2 <= x7 & x7 <= 2
    #     #     >@invariant(x1+x2+x3<=706/233)
    #     #   {!(
    #     #     1.8 <= x1 & x1 <= 2 &
    #     #     1.8 <= x2 & x2 <= 2 &
    #     #     1.8 <= x3 & x3 <= 2 &
    #     #     1.8 <= x4 & x4 <= 2 &
    #     #     1.8 <= x5 & x5 <= 2 &
    #     #     1.8 <= x6 & x6 <= 2 &
    #     #     1.8 <= x7 & x7 <= 2
    #     #   )}
    #     runVerify(self, pre="0.99 <= x1 & x1 <= 1.01 & \
    #                          0.99 <= x2 & x2 <= 1.01 & \
    #                          0.99 <= x3 & x3 <= 1.01 & \
    #                          0.99 <= x4 & x4 <= 1.01 & \
    #                          0.99 <= x5 & x5 <= 1.01 & \
    #                          0.99 <= x6 & x6 <= 1.01 & \
    #                          0.99 <= x7 & x7 <= 1.01",
    #               hp="<x1_dot = -0.4*x1 + 5*x3*x4, \
    #                    x2_dot = 0.4*x1 - x2, \
    #                    x3_dot = x2 - 5*x3*x4, \
    #                    x4_dot = 5*x5*x6 - 5*x3*x4, \
    #                    x5_dot = -5*x5*x6 + 5*x3*x4, \
    #                    x6_dot = 0.5*x7 - 5*x5*x6, \
    #                    x7_dot = -0.5*x7 + 5*x5*x6 & \
    #                    -2 < x1 & x1 < 2 & \
    #                    -2 < x2 & x2 < 2 & \
    #                    -2 < x3 & x3 < 2 & \
    #                    -2 < x4 & x4 < 2 & \
    #                    -2 < x5 & x5 < 2 & \
    #                    -2 < x6 & x6 < 2 & \
    #                    -2 < x7 & x7 < 2> \
    #                   invariant [x1+x2+x3<=706/233]",
    #               post="!( \
    #                         1.8 <= x1 & x1 <= 2 & \
    #                         1.8 <= x2 & x2 <= 2 & \
    #                         1.8 <= x3 & x3 <= 2 & \
    #                         1.8 <= x4 & x4 <= 2 & \
    #                         1.8 <= x5 & x5 <= 2 & \
    #                         1.8 <= x6 & x6 <= 2 & \
    #                         1.8 <= x7 & x7 <= 2 \
    #                     )",
    #               wolfram_engine=True)

    def testNonlinear119(self):
        # Nonlinear benchmark, problem 119
        #  {x1==r1 & y1==r1
        #   & x2==r2 & y2==r2
        #   & d1==a
        #   & d2==0
        #   & e1==0
        #   & e2==b}
        #      t := 0;
        #     <x1_dot=d1, x2_dot=d2, d1_dot=-w*d2, d2_dot=w*d1, 
        #     y1_dot=e1, y2_dot=e2, e1_dot=-theta*e2, e2_dot=theta*e1, t_dot = 1 & t < 10>
        #     @invariant(e1^2+e2^2-b^2==0, d1^2+d2^2-a^2==0, e1-r2*theta+theta*y2==0, -a+d1-r2*w+w*x2==0) 
        #   {(e1 - r2*theta + theta * y2) != e2^2 + 1}
        runVerify(self, pre="x1==r1 & y1==r1 \
                            & x2==r2 & y2==r2 \
                            & d1==a \
                            & d2==0 \
                            & e1==0 \
                            & e2==b",
                  hp="t := 0; \
                     <x1_dot=d1, x2_dot=d2, \
                      d1_dot=-w*d2, d2_dot=w*d1, \
                      y1_dot=e1, y2_dot=e2, \
                      e1_dot=-theta*e2, e2_dot=theta*e1, t_dot = 1 & t < 10> \
                      invariant [e1^2+e2^2-b^2==0] [d1^2+d2^2-a^2==0] [e1-r2*theta+theta*y2==0] [-a+d1-r2*w+w*x2==0];",
                  post="(e1 - r2*theta + theta * y2) != e2^2 + 1",
                  constants={'a', 'b', 'r1', 'r2', 'w', 'theta'})

    # TODO: Nonlinear problem 120. Definitions.
    def testNonlinear120(self):
        # Nonlinear benchmark, problem 120
        # {(x1-y1)^2 + (x2-y2)^2 >= p^2
        #   & d1 =-om*(x2-c2) & d2=om*(x1-c1)
        #   & e1 =-om*(y2-c2) & e2=om*(y1-c1)}
        #     t := 0;
        #    <x1_dot=d1, x2_dot=d2, d1_dot=-om*d2, d2_dot=om*d1,
        #     y1_dot=e1, y2_dot=e2, e1_dot=-om*e2, e2_dot=om*e1,
        #     t_dot = 1 & t < 10>
        #     @invariant(d1-e1=-om*(x2-y2)&d2-e2=om*(x1-y1))
        # {(x1-y1)^2 + (x2-y2)^2 >= p^2}
        runVerify(self, pre="(x1-y1)^2 + (x2-y2)^2 >= p^2 \
                           & d1 ==-om*(x2-c2) & d2==om*(x1-c1) \
                           & e1 ==-om*(y2-c2) & e2==om*(y1-c1)",
                  hp="t := 0; \
                     <x1_dot=d1, x2_dot=d2, d1_dot=-om*d2, d2_dot=om*d1, \
                      y1_dot=e1, y2_dot=e2, e1_dot=-om*e2, e2_dot=om*e1, \
                      t_dot = 1 & t < 10> \
                      invariant [d1-e1 == -om*(x2-y2) & d2-e2 == om*(x1-y1)] \
                                [(x1-y1)^2 + (x2-y2)^2 >= p^2];",
                  post="(x1-y1)^2 + (x2-y2)^2 >= p^2",
                  constants={'p', 'om', 'omy', 'c1', 'c2'})
    
    def testNonlinear121(self):
        # Nonlinear benchmark, problem 121
        #  {x1 == xi1 &
        #   x2 == xi2 &
        #   d1 == di1 &
        #   d2 == di2 &
        #   y1 == yi1 &
        #   y2 == yi2 &
        #   e1 == ei1 &
        #   e2 == ei2}
        #      t := 0;
        #     <x1_dot=d1, x2_dot=d2, 
        #      d1_dot=-w1*d2, d2_dot=w1*d1, 
        #      y1_dot=e1, y2_dot=e2, 
        #      e1_dot=-w2*e2, e2_dot=w2*e1,
        #      t_dot = 1 & t < 10>
        #     @invariant(w1*x2 + d1 - w1*xi2 - di1 == 0, -w1*x1 + d2 + w1*xi1 - di2 == 0, -w1*x1 + w1*x2 + d1 + d2 + w1*xi1 - w1*xi2 - di1 - di2 == 0, d1^2 + d2^2 - di1^2 - di2^2 == 0)
        # {-w1*x1 + 3*w1*x2 + 3*d1 + d2 + w1*xi1 - 3*w1*xi2 - 3*di1 - di2 >= -d1^2} 
        runVerify(self, pre="x1 == xi1 & \
                             x2 == xi2 & \
                             d1 == di1 & \
                             d2 == di2 & \
                             y1 == yi1 & \
                             y2 == yi2 & \
                             e1 == ei1 & \
                             e2 == ei2",
                  hp="t := 0; \
                     <x1_dot=d1, x2_dot=d2, \
                      d1_dot=-w1*d2, d2_dot=w1*d1, \
                      y1_dot=e1, y2_dot=e2, \
                      e1_dot=-w2*e2, e2_dot=w2*e1, \
                      t_dot = 1 & t < 10> \
                      invariant \
                          [w1*x2 + d1 - w1*xi2 - di1 == 0] \
                          [-w1*x1 + d2 + w1*xi1 - di2 == 0] \
                          [-w1*x1 + w1*x2 + d1 + d2 + w1*xi1 - w1*xi2 - di1 - di2 == 0] \
                          [d1^2 + d2^2 - di1^2 - di2^2 == 0];",
                  post="-w1*x1 + 3*w1*x2 + 3*d1 + d2 + w1*xi1 - 3*w1*xi2 - 3*di1 - di2 >= -d1^2")

    # TODO: Nonlinear problem 122, 123, 124. No invariants.

# I took out this test because it was too slow -- Alex
    # def testNonlinear125(self):
    #     # Nonlinear benchmark, problem 125
    #     #  {0.99 <= x1 & x1 <= 1.01 & 
    #     #   0.99 <= x2 & x2 <= 1.01 & 
    #     #   0.99 <= x3 & x3 <= 1.01 &
    #     #   0.99 <= x4 & x4 <= 1.01 &
    #     #   0.99 <= x5 & x5 <= 1.01 &
    #     #   0.99 <= x6 & x6 <= 1.01 &
    #     #   0.99 <= x6 & x6 <= 1.01 &
    #     #   0.99 <= x7 & x7 <= 1.01 &
    #     #   0.99 <= x8 & x8 <= 1.01 &
    #     #   0.99 <= x9 & x9 <= 1.01}
    #     #     <
    #     #       x1_dot = 3*x3 - x1*x6,
    #     #       x2_dot = x4 - x2*x6,
    #     #       x3_dot = x1*x6 - 3*x3,
    #     #       x4_dot = x2*x6 - x4,
    #     #       x5_dot = 3*x3 + 5*x1 - x5,
    #     #       x6_dot = 5*x5 + 3*x3 + x4 - x6*(x1 + x2 + 2*x8 + 1),
    #     #       x7_dot = 5*x4 + x2 - 0.5*x7,
    #     #       x8_dot = 5*x7 - 2*x6*x8 + x9 - 0.2*x8,
    #     #       x9_dot = 2*x6*x8 - x9 &
    #     #       -2 <= x1 & x1 <= 2 &
    #     #       -2 <= x2 & x2 <= 2 &
    #     #       -2 <= x3 & x3 <= 2 &
    #     #       -2 <= x4 & x4 <= 2 &
    #     #       -2 <= x5 & x5 <= 2 &
    #     #       -2 <= x6 & x6 <= 2 &
    #     #       -2 <= x7 & x7 <= 2 &
    #     #       -2 <= x8 & x8 <= 2 &
    #     #       -2 <= x9 & x9 <= 2>
    #     #     @invariant(x2+x4<=101/50)
    #     #  {!(
    #     #     1.8 <= x1 & x1 <= 2 &
    #     #     1.8 <= x2 & x2 <= 2 &
    #     #     1.8 <= x3 & x3 <= 2 &
    #     #     1.8 <= x4 & x4 <= 2 &
    #     #     1.8 <= x5 & x5 <= 2 &
    #     #     1.8 <= x6 & x6 <= 2 &
    #     #     1.8 <= x7 & x7 <= 2 &
    #     #     1.8 <= x8 & x8 <= 2 &
    #     #     1.8 <= x9 & x9 <= 2
    #     #   )}
    #     runVerify(self, pre="0.99 <= x1 & x1 <= 1.01 & \
    #                          0.99 <= x2 & x2 <= 1.01 & \
    #                          0.99 <= x3 & x3 <= 1.01 & \
    #                          0.99 <= x4 & x4 <= 1.01 & \
    #                          0.99 <= x5 & x5 <= 1.01 & \
    #                          0.99 <= x6 & x6 <= 1.01 & \
    #                          0.99 <= x6 & x6 <= 1.01 & \
    #                          0.99 <= x7 & x7 <= 1.01 & \
    #                          0.99 <= x8 & x8 <= 1.01 & \
    #                          0.99 <= x9 & x9 <= 1.01",
    #               hp="< \
    #                     x1_dot = 3*x3 - x1*x6, \
    #                     x2_dot = x4 - x2*x6, \
    #                     x3_dot = x1*x6 - 3*x3, \
    #                     x4_dot = x2*x6 - x4, \
    #                     x5_dot = 3*x3 + 5*x1 - x5, \
    #                     x6_dot = 5*x5 + 3*x3 + x4 - x6*(x1 + x2 + 2*x8 + 1), \
    #                     x7_dot = 5*x4 + x2 - 0.5*x7, \
    #                     x8_dot = 5*x7 - 2*x6*x8 + x9 - 0.2*x8, \
    #                     x9_dot = 2*x6*x8 - x9 & \
    #                     -2 < x1 & x1 < 2 & \
    #                     -2 < x2 & x2 < 2 & \
    #                     -2 < x3 & x3 < 2 & \
    #                     -2 < x4 & x4 < 2 & \
    #                     -2 < x5 & x5 < 2 & \
    #                     -2 < x6 & x6 < 2 & \
    #                     -2 < x7 & x7 < 2 & \
    #                     -2 < x8 & x8 < 2 & \
    #                     -2 < x9 & x9 < 2> \
    #                   invariant [x2+x4<=101/50]",
    #               post="!( \
    #                         1.8 <= x1 & x1 <= 2 & \
    #                         1.8 <= x2 & x2 <= 2 & \
    #                         1.8 <= x3 & x3 <= 2 & \
    #                         1.8 <= x4 & x4 <= 2 & \
    #                         1.8 <= x5 & x5 <= 2 & \
    #                         1.8 <= x6 & x6 <= 2 & \
    #                         1.8 <= x7 & x7 <= 2 & \
    #                         1.8 <= x8 & x8 <= 2 & \
    #                         1.8 <= x9 & x9 <= 2 \
    #                     )")

    # TODO: Nonlinear 126, 127. Definitions.

    # TODO: Nonlinear 128, 129, 130, 131, 132. No invariants.
    # 128: Automation in keymaera doesn't work.

    def testNonlinear133(self):
        # Nonlinear benchmark, problem 133
        # {xleft^2+(-2+yleft)^2 < 1/24&
        # -3/2<=x1right & x1right<=-1/2&
        # -3/2<=x2right & x2right<=-1/2}
        # <xleft_dot = -xleft+2*xleft^2*yleft,
        #  yleft_dot = -yleft,
        #  x1right_dot = -x1right+x1right*x2right,
        #  x2right_dot = -x2right & 
        #  -2<=x1right & x1right<=2 & -2<=x2right & x2right<=2>
        # {!(xleft<=-2|yleft<=-1) & 
        # !(-1/2<=x1right & x1right<=1/2 & 1/2<=x2right & x2right<=3/2)}
        runVerify(self, pre="xleft^2+(-2+yleft)^2 < 1/24 & \
                            -3/2<=x1right & x1right<=-1/2 & \
                            -3/2<=x2right & x2right<=-1/2",
                  hp="<xleft_dot = -xleft+2*xleft^2*yleft, \
                       yleft_dot = -yleft, \
                       x1right_dot = -x1right+x1right*x2right, \
                       x2right_dot = -x2right &  \
                       -2< x1right & x1right< 2 & -2< x2right & x2right< 2> \
                      invariant \
                          [x2right+yleft>0] {dbx} \
                          [x2right^2+x2right*yleft+yleft^2>0] {dbx} \
                          [x1right < 0] {dbx} \
                          [x2right < 0] {dbx} \
                          [xleft*yleft < 1] {dbx} \
                          [xleft > -2] {dbx} \
                          [yleft > -1] {dbx};",
                  post="!(xleft<=-2|yleft<=-1) & \
                        !(-1/2<=x1right & x1right<=1/2 & 1/2<=x2right & x2right<=3/2)")

    # TODO: Nonlinear 134. No tactic.

    def testNonlinear135(self):
        # Nonlinear benchmark, problem 135
        # {xleft^2+yleft^2<=1/4 & 
        # 4<=x1right & x1right<=4.5 & 
        # 1<=x2right & x2right<=2}
        #   <xleft_dot=-yleft+2*xleft^2*yleft,
        #    yleft_dot=yleft+2*xleft*yleft^2,
        #    x1right_dot=-11/2*x2right+x2right^2,
        #    x2right_dot=6*x1right-x1right^2 & 
        #   1<=x1right & x1right<=5 & 1<=x2right & x2right<=5>
        #    @invariant(349+4*((-9)+x1right)*x1right^2+x2right^2*((-33)+4*x2right)<=0, 2*xleft^2 < 1)
        # {!xleft>3 & !(1<=x1right & x1right<=2 & 2<=x2right & x2right<=3)}
        runVerify(self, pre="xleft^2+yleft^2<=1/4 & \
                             4<=x1right & x1right<=4.5 & \
                             1<=x2right & x2right<=2",
                  hp="<xleft_dot=-yleft+2*xleft^2*yleft, \
                      yleft_dot=yleft+2*xleft*yleft^2, \
                      x1right_dot=-11/2*x2right+x2right^2, \
                      x2right_dot=6*x1right-x1right^2 & \
                        1<x1right & x1right<5 & \
                        1<x2right & x2right<5> \
                      invariant \
                        [349+4*((-9)+x1right)*x1right^2+ \
                          x2right^2*((-33)+4*x2right)<=0] \
                        [2*xleft^2 < 1] {dbx};",
                  post="!xleft>3 & !(1<=x1right & x1right<=2 & 2<=x2right & x2right<=3)")

    # TODO: Nonlinear 136, 137, 138, 139, 140, 141. No tactics.

if __name__ == "__main__":
    unittest.main()

