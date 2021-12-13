"""Unit test for hhlpy."""

from operator import pos
import unittest

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.parser import aexpr_parser, bexpr_parser, hp_parser
from hhlpy.hhlpy2 import CmdVerifier


def runVerify(self, *, pre, hp, post, constants=set(), loop_invariants=None, ode_invariants=None, 
              diff_weakening=None, diff_invariants=None, assume_invariants=None, 
              diff_cuts=None, ghost_equations=None, ghost_invariants=None, darboux_equality = None,
              print_vcs=False, expected_vcs=None):
    # Parse pre-condition, HCSP program, and post-condition
    pre = bexpr_parser.parse(pre)
    hp = hp_parser.parse(hp)
    post = bexpr_parser.parse(post)

    # Initialize the verifier
    verifier = CmdVerifier(pre=pre, hp=hp, post=post, constants=constants)

    # Place loop invariants
    if loop_invariants:
        for pos, loop_inv in loop_invariants.items():
            if isinstance(loop_inv, str):
                loop_inv = bexpr_parser.parse(loop_inv)
            verifier.add_loop_invariant(pos, loop_inv)

    # Place ode invariants
    if ode_invariants:
        for pos, ode_inv in ode_invariants.items():
            if isinstance(ode_inv, str):
                ode_inv = bexpr_parser.parse(ode_inv)
            verifier.add_ode_invariant(pos, ode_inv)

    # Set differential weakening proof rule as true
    if diff_weakening:
        for pos, dw in diff_weakening.items():
            if isinstance(dw, str):
                dw = bexpr_parser.parse(dw)
            verifier.set_diff_weakening(pos, dw)
            
    # Place differential invariants
    if diff_invariants:
        for pos, diff_inv in diff_invariants.items():
            if isinstance(diff_inv, str):
                diff_inv = bexpr_parser.parse(diff_inv)
            verifier.add_diff_invariant(pos, diff_inv)
    
    # Place assume invariants
    if assume_invariants:
        for pos, assume_inv in assume_invariants.items():
            if isinstance(assume_inv, str):
                assume_inv = bexpr_parser.parse(assume_inv)
            verifier.add_assume_invariant(pos, assume_inv)
    
    # Place differential cuts
    if diff_cuts:
        for pos, sub_diffcuts_str in diff_cuts.items():
            sub_diffcuts = []
            for diff_cut in sub_diffcuts_str:
                if isinstance(diff_cut, str):
                    diff_cut = bexpr_parser.parse(diff_cut)
                    sub_diffcuts.append(diff_cut)
            verifier.add_diff_cuts(pos, sub_diffcuts)

    # Place ghost invariants
    if ghost_invariants:
        for pos, ghost_inv in ghost_invariants.items():
            if isinstance(ghost_inv, str):
                ghost_inv = bexpr_parser.parse(ghost_inv)
            verifier.add_ghost_invariant(pos, ghost_inv)

    # Place ghost equations：
    if ghost_equations:
        for pos, ghost_eqs in ghost_equations.items():
            if isinstance(ghost_eqs, str):
                ghost_eqs = hp_parser.parse(ghost_eqs)
                ghost_eqs_dict = dict()
                for name, e in ghost_eqs.eqs:
                    ghost_eqs_dict[name] = e
            verifier.add_ghost_equation(pos, ghost_eqs_dict)

    if darboux_equality:
        for pos, dbx_equal in darboux_equality.items():
            if isinstance(dbx_equal, str):
                dbx_equal = bexpr_parser.parse(dbx_equal)
            verifier.use_darboux_equality(pos, dbx_equal)

    # Compute wp and verify
    verifier.compute_wp()

    # Optional: Print verification conditions
    if print_vcs:
        for pos, vcs in verifier.get_all_vcs().items():
            print("%s:" % str(pos))
            for vc in vcs:
                print(vc)

    # Use SMT to verify all verification conditions
    self.assertTrue(verifier.verify())

    # Optional: check the verification conditions are expected
    def is_trivial(vc):
        if isinstance(vc, expr.LogicExpr) and vc.op == "-->" and vc.exprs[0] == vc.exprs[1]:
            return True
        else:
            return False

    if expected_vcs:
        for pos, vcs in expected_vcs.items():
            vcs = [bexpr_parser.parse(vc) for vc in vcs]
            actual_vcs = [vc for vc in verifier.infos[pos].vcs if not is_trivial(vc)]
            self.assertEqual(set(vcs), set(actual_vcs))


class HHLPyTest(unittest.TestCase):
    def testVerify1(self):
        # Baisc benchmark, problem 1 
        # {x >= 0} x := x + 1 {x >= 1}
        runVerify(self, pre="x >= 0", hp="x := x+1", post="x >= 1",
                  expected_vcs={((), ()): ["x >= 0 --> x + 1 >= 1"]})

    def testVerify2(self):
        # {x >= 0} x := x+1 ++ x := x+2 {x >= 1}
        runVerify(self, pre="x >= 0", hp="x := x+1 ++ x := x+2", post="x >= 1",
                  expected_vcs={((), ()): ["x >= 0 --> x + 1 >= 1 && x + 2 >= 1"]})

    def testVerify3(self):
        # {x >= 0} x := x+1; y := x+2 {x >= 1 && y >= 3}
        runVerify(self, pre="x >= 0", hp="x := x+1; y := x+2", post="x >= 1 && y >= 3",
                  expected_vcs={((), ()): ["x >= 0 --> x + 1 >= 1 && x + 1 + 2 >= 3"]})

    def testVerify4(self):
        # Basic benchmark, problem 2
        # {x >= 0} x := x+1; x := x+1 ++ y := x+1 {x >= 1}
        runVerify(self, pre="x >= 0", hp="x := x+1; x := x+1 ++ y := x+1", post="x >= 1",
                  expected_vcs={((), ()): ["x >= 0 --> x + 1 + 1 >= 1 && x + 1 >= 1"]})

    def testVerify5(self):
        # {x >= 0} (x := x+1)** {x >= 0}
        runVerify(self, pre="x >= 0", hp="(x := x+1)**", post="x >= 0",
                  loop_invariants={((), ()): "x >= 0"},
                  expected_vcs={((), ()): ["x >= 0 --> x + 1 >= 0"]})

    def testVerify6(self):
        # Basic benchmark, problem 3
        # {x >= 0} x := x+1; (x := x+1)** {x >= 1}
        # Invariant for loop is x >= 1.
        runVerify(self, pre="x >= 0", hp="x := x+1; (x := x+1)**", post="x >= 1", 
                  loop_invariants={((1,), ()): "x >= 1"},
                  expected_vcs={((), ()): ["x >= 0 --> x + 1 >= 1"],
                                ((1,), ()): ["x >= 1 --> x + 1 >= 1"]})

    def testVerify7(self):
        # {x >= 0} <x_dot=2 & x < 10> {x >= 0}
        # Invariant for ODE is x >= 0.
        runVerify(self, pre="x >= 0", hp="<x_dot=2 & x < 10>", post="x >= 0",
                  diff_invariants={((), ()): "x >= 0"})

    def testVerify8(self):
        # {x * x + y * y == 1} <x_dot=y, y_dot=-x & x > 0> {x * x + y * y = 1}
        # Invariant for ODE is x * x + y * y == 1
        runVerify(self, pre="x * x + y * y == 1", 
                  hp="<x_dot=y, y_dot=-x & x > 0>",
                  post="x * x + y * y == 1",
                  diff_invariants={((), ()): "x * x + y * y == 1"})

    def testVerify9(self):
        # Basic benchmark, problem 4
        # {x >= 0} x := x+1; <x_dot=2 & x < 10> {x >= 1}
        runVerify(self, pre="x >= 0", hp="x := x+1; <x_dot=2 & x < 10>", post="x >= 1",            
                  diff_invariants={((1,), ()): "x >= 1"})

    def testVerify10(self):
        # Basic Benchmark, problem5
        # {x >= 0} x := x+1; x := {x >= 1} {x >= 1}
        runVerify(self, pre="x >= 0", hp="x := x+1; x := {x >= 1}", post="x >= 1",
                  expected_vcs={((), ()): ["x >= 0 --> x0 >= 1 --> x0 >= 1"]})

    def testVerify11(self):
        # {x0 >= 0} x := x+1; x := {x >= 1} {x >= 1}
        runVerify(self, pre="x0 >= 0", hp="x := x+1; x := {x >= 1}", post="x >= 1",
                  expected_vcs={((), ()): ["x0 >= 0 --> x1 >= 1 --> x1 >= 1"]})

    def testVerify12(self):
        # {x >= 0} x := x+1; y := {y >= x} {y >= 1}
        runVerify(self, pre="x >= 0", hp="x := x+1; y := {y >= x}", post="y >= 1",
                  expected_vcs={((), ()): ["x >= 0 --> y0 >= x + 1 --> y0 >= 1"]})

    def testVerify13(self):
        # {x >= 0} x := x+1; y := {y >= x}; y := {y >= x + 1} {y >= 2}
        runVerify(self, pre="x >= 0", hp="x := x+1; y := {y >= x}; y := {y >= x+1}", post="y >= 2",
                  expected_vcs={((), ()): ["x >= 0 --> y1 >= x + 1 -->y0 >= x + 1 + 1 --> y0 >= 2"]})

    def testVerify14(self):
        # Basic Benchmark, problem7
        # confusion about the inv of loop
        # {x >= 0 && y >= 1} 

        # x := x + 1; 
        # (x := x + 1)**@invariant(x >= 1) ++ y:= x + 1; 
        # <y_dot = 2>@invariant(y >= 1);
        #  x := y

        # {x >= 1}
        runVerify(self, pre="x >= 0 && y >= 1", 
                  hp="x := x + 1; (x := x + 1)** ++ y:= x + 1; <y_dot = 2 & y < 10>; x := y", 
                  post="x >= 1",
                  loop_invariants={((1,0,), ()): "x >= 1 && y >= 1"}, 
                  diff_invariants={((2,), ()): "y >= 1"},
                  expected_vcs={((), ()): ["x >= 0 && y >= 1 --> (x + 1 >= 1 && y >= 1) && x + 1 + 1 >= 1"],
                                ((1,0,), ()): ["x >= 1 && y >= 1 --> x + 1 >= 1 && y >= 1", 
                                        "x >= 1 && y >= 1 --> y >= 1"],
                                ((2,), ()): ["y == 10 --> 2 >= 0"]}) 

    def testVerify15(self):
        # Basic benchmark, problem8
        # {x > 0 && y > 0} 

        # <x_dot = 5 & x < 10>@invariant(x > 0); 
        # (x := x + 3)**@invariant(x > 0) ++ y := x

        # {x > 0 && y > 0}
        runVerify(self, pre="x > 0 && y > 0", hp="<x_dot = 5 & x < 10>; (x := x + 3)** ++ y := x", 
                  post="x > 0 && y > 0", 
                  loop_invariants={((1,0), ()): "x > 0 && y > 0"}, 
                  diff_invariants={((0,), ()): "x > 0 && y > 0"},
                  expected_vcs={((0,), ()): ["x == 10 --> 5 >= 0 && 0 >= 0", 
                                        "x > 0 && y > 0 --> (x > 0 && y > 0) && x > 0 && x > 0"],
                                ((1,0), ()): ["x > 0 && y > 0 --> x + 3 > 0 && y > 0"]})

    def testVerify16(self):
        # Test case containing ghost variables
        # Basic benchmark, problem15
        # dG Rule
        # {x > 0} <x_dot = -x> {x > 0}
        runVerify(self, pre="x > 0", hp="t := 0; <x_dot = -x, t_dot=1 & t < 1>", post="x > 0",
                ode_invariants={((1,), ()): "x > 0"},
                ghost_invariants={((1,), ()): "x * y * y == 1"},
                expected_vcs={((1,), ()): ["x > 0 --> (EX y. x * y * y == 1)",
                                           "x * y * y == 1 --> x > 0",
                                           "2 != 0"]})

    def testVerify17(self):
        # Basic benchmark, problem9
        # dG Rule
        # {x>0 && y>0} 
        # t := 0; 
        # <x_dot = -x, t_dot = 1 & t < 1>;
        # (x := x+3)**@invariant(x > 0) ++ y := x 
        # {x>0 && y>0}
        runVerify(self, pre="x > 0 && y > 0", 
                  hp="t := 0; <x_dot = -x, t_dot = 1 & t < 1>; (x := x+3)** ++ y := x",
                  post="x > 0 && y > 0",
                  loop_invariants={((2,0), ()): "x > 0 && y > 0"},
                  ode_invariants={((1,), ()): "x > 0 && y > 0"},
                  ghost_invariants={((1,), (0,)): "x * z * z == 1"},
                  diff_invariants={((1,), (1,)): "y > 0"},
                  expected_vcs={((1,), (0,)): ["x > 0 --> (EX z. x * z * z == 1)",
                                               "x * z * z == 1 --> x > 0",
                                               "2 != 0"],
                                ((1,), (1,)): ["t == 1 --> 0 >= 0"]})

    def testVerify18(self):
        # Basic bencmark, problem10
        # dG Rule
        # {x > 0} <x_dot = 5>; <x_dot = 2>; <x_dot = x> {x > 0}
        runVerify(self, pre="x > 0",
                  hp="<x_dot = 5 & x < 1>; <x_dot = 2 & x < 2>; <x_dot = x & x < 5>",
                  post="x > 0",
                  diff_invariants={((0,), ()): "x > 0", ((1,), ()): "x > 0"},
                  ghost_invariants={((2,), ()): "x * y * y == 1"},
                  ode_invariants={((2,), ()): "x > 0"})

    def testVerify19(self):
        # Basic benchmark, problem11
        # {x = 0} <x_dot = 1 & x < 10> {x >= 0}
        runVerify(self, pre="x == 0", hp="<x_dot = 1 & x < 10>", post="x >= 0", 
                  diff_invariants={((), ()): "x >= 0"})

    def testVerify20(self):
        # Basic benchmark, problem12
        # dC Rule
        # {x >= 0 && y >= 0} <x_dot = y> {x >= 0}
        runVerify(self, pre="x >= 0 && y >= 0", hp="<x_dot = y & x < 10>", post="x >= 0",
                  diff_cuts={((), ()): ["y >= 0"]})

    def testVerify21(self):
        # Basic benchmark, problem13
        # dC Rule
        # {x >= 0 && y >= 0 && z >= 0} <x_dot = y, y_dot = z & x < 10> {x >= 0}
        runVerify(self, pre="x >= 0 && y >= 0 && z >= 0", 
                  hp="<x_dot = y, y_dot = z & x < 10>", post="x >= 0",
                  diff_cuts={((), ()):["z >= 0", "y >= 0"]})

    def testVerify22(self):
        # Basic benchmark, problem14
        # dC Rule
        # {x >= 0 && y >= 0 && z >= 0 && j >= 0} 
        # <x_dot = y, y_dot = z, z_dot = j, j_dot = j * j & x < 10>
        # {x >= 0}
        runVerify(self, pre="x >= 0 && y >= 0 && z >= 0 && j >= 0",
                  hp="<x_dot = y, y_dot = z, z_dot = j, j_dot = j * j & x < 10>", post="x >= 0",
                  diff_cuts={((), ()): ["j >= 0", "z >= 0", "y >= 0"]})

    # Basic benchmark problem15 is verified in testVerify16

    # def testVerify23(self):
    #     # Basic benchmark, problem16
    #     # dG Rule
    #     # {x > 0} t := 0; <x_dot = -x + 1, t_dot = 1 & t < 10> {x > 0}
    #     runVerify(self, pre="x > 0", hp="t := 0; <x_dot = -x + 1, t_dot = 1 & t < 10>", post="x > 0",
    #               ode_invariants={((1,), ()): "x > 0"},
    #               ghost_invariants={((1,), ()): "x * y * y == 1"},
    #               print_vcs=True)

    def testVerify24(self):
        # Basic benchmark, problem17
        # {x > 0 && y > 0} t := 0; <x_dot = -y * x, t_dot = 1 & t < 10> {x > 0}
        runVerify(self, pre="x > 0 && y > 0", hp="t := 0; <x_dot = -y * x, t_dot = 1 & t < 10>", 
                  post="x > 0",
                  ode_invariants={((1,), ()): "x > 0"},
                  ghost_invariants={((1,), ()): "x * z * z == 1"},
                  expected_vcs={((), ()): ["x > 0 && y > 0 --> x > 0"],
                                ((1,), ()): ["x > 0 --> (EX z. x * z * z == 1)",
                                             "x * z * z == 1 --> x > 0",
                                             "2 != 0"]})

    def testVerify25(self):
        # Basic benchmark, problem 18
        # {x >= 0} <x_dot = x & x < 10> {x >= 0}
        # dG and Conjunction Rule
        # Question remained: the form of ghost_equations.
        runVerify(self, pre="x >= 0", hp="<x_dot = x & x < 10>", post="x >= 0",
                  ode_invariants={((), ()): "x >= 0"},
                  diff_invariants={((), (0,1)): "x * y >= 0"},
                  ghost_equations = {((), ()): "<y_dot = - y & y < 10>"},
                  ghost_invariants={((), ()): "y > 0 && x * y >= 0",
                                    ((), (0,0)): "y * z * z == 1"})

    def testVerify26(self):
        # Basic benchmark, problem 19
        # dC Rule
        # {x >= 0 && y >= 0} <x_dot = y, y_dot = y * y & x < 10> {x >= 0}
        runVerify(self, pre="x >= 0 && y >= 0",
                  hp="<x_dot = y, y_dot = y * y & x < 10>", post="x >= 0", 
                  diff_cuts={((), ()): ["y >= 0"]})

    # Basic benchmark, problem 20

    def testVerify28(self):
        # Basic benchmark, problem 21
        # dI Rule
        # {x >= 1} <x_dot = x ^ 2 + 2 * x ^ 4 & x < 10> {x ^ 3 >= x ^ 2}
        runVerify(self, pre="x >= 1", hp="<x_dot = x ^ 2 + 2 * x ^ 4 & x < 10>",
                  post="x ^ 3 >= x ^ 2",
                  diff_invariants={((), ()): "x >= 1"})

    def testVerify29(self):
        # Basic benchmark, problem 22
        # dI Rule
        # {x * x + y * y == 1} t := 0; <x_dot = -y, y_dot = x, t_dot = 1 & t < 10> {x * x + y * y == 1}
        runVerify(self, pre="x * x + y * y == 1", 
                  hp="t := 0; <x_dot = -y, y_dot = x, t_dot = 1 & t < 10>",
                  post="x * x + y * y == 1",
                  diff_invariants={((1,), ()): "x * x + y * y == 1"})

    def testVerify30(self):
        # Basic benchmark, problem 23
        # dC and dI rule
        # {x^2 + y^2 == 1 && e == x} 
        # t:=0; <x_dot = -y, y_dot = e, e_dot = -y, t_dot = 1 & t < 10>
        # {x^2 + y^2 == 1 && e == x}
        runVerify(self, pre="x^2 + y^2 == 1 && e == x",
                  hp="t:=0; <x_dot = -y, y_dot = e, e_dot = -y, t_dot = 1 & t < 10>",
                  post="x^2 + y^2 == 1 && e == x",
                  ode_invariants={((1,), ()): "x^2 + y^2 == 1 && e == x"},
                  diff_cuts={((1,), (0,)): ["e == x"]})

    def testVerify31(self):
        # Basic benchmark, problem 24
        # Conjunction rule and dI rule
        # {d1^2 + d2^2 == w^2 * p^2 && d1 == -w * x2 && d2 == w * x1}
        # t := 0; <x1_dot = d1, x2_dot = d2, d1_dot = -w * d2, d2_dot = w * d1, t_dot = 1 & t < 10>
        # {d1^2 + d2^2 == w^2 * p^2 && d1 == -w * x2 && d2 == w * x1}
        runVerify(self, pre="d1^2 + d2^2 == w^2 * p^2 && d1 == -w * x2 && d2 == w * x1",
                  hp="t := 0; <x1_dot = d1, x2_dot = d2, d1_dot = -w * d2, d2_dot = w * d1, t_dot = 1 & t < 10>",
                  post="d1^2 + d2^2 == w^2 * p^2 && d1 == -w * x2 && d2 == w * x1",
                  ode_invariants={((1,), ()): \
                      "d1^2 + d2^2 == w^2 * p^2 && d1 == -w * x2 && d2 == w * x1"})

    def testVerify32(self):
        # Benchmark, problem 25
        # dC rule? and dI rule
        # {w >= 0 && x == 0 && y == 3} 
        # t := 0; <x_dot = y, y_dot = -w^2 * x - 2 * w * y, t_dot = 1 & t < 10>
        # {w^2 * x^2 + y^2 <= 9}
        runVerify(self, pre="w >= 0 && x == 0 && y == 3",
                  hp="t := 0; <x_dot = y, y_dot = -w^2 * x - 2 * w * y, t_dot = 1 & t < 10>",
                  post="w^2 * x^2 + y^2 <= 9",
                  diff_cuts={((1,), ()): ["w >= 0"]})

    def testVerify33(self):
    # Benchmark, problem 26
    # {x^3 > 5 && y > 2} 
    # t := 0; <x_dot = x^3 + x^4, y_dot = 5 * y + y^2, t_dot = 1 & t < 10>
    # {x^3 > 5 && y > 2}
        runVerify(self, pre="x^3 > 5 && y > 2",
                  hp="t := 0; <x_dot = x^3 + x^4, y_dot = 5 * y + y^2, t_dot = 1 & t < 10>",
                  post="x^3 > 5 && y > 2",
                  ode_invariants={((1,), ()): "x^3 > 5 && y > 2"},
                  assume_invariants={((1,),(0,)): "x^3 > 5", ((1,), (1,)): "y > 2"})

    def testVerify34(self):
        # Benchmark, problem 27
        # dW rule
        # {x >= 1 && y == 10 && z == -2} 
        # <x_dot = y, y_dot = z + y^2 - y & y > 0>
        # {x >= 1 && y >= 0}
        runVerify(self, pre="x >= 1 && y == 10 && z == -2", 
                  hp="<x_dot = y, y_dot = z + y^2 - y & y > 0>",
                  post="x >= 1 && y >= 0",
                  ode_invariants={((), ()): "x >= 1 && y >= 0"},
                  diff_weakening={((), (1,)): "true", ((),(0,0)): "true"},
                  diff_cuts={((), (0,)): ["y >= 0"]})

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
                   t_dot = 1 & t < 10>",
                  post="x1^4 * x2^2 + x1^2 * x2^4 - 3 * x1^2 * x2^2 + 1 <= c")

    def testVerify36(self):
        # Benchmark, problem 29
        # constants: {"B()"}
        # {x + z == 0} 
        # t := 0; <x_dot = (A * x^2 + B() * x), z_dot = A * z * x + B() * z, t_dot = 1 & t < 10> 
        # {0 == -x - z}
        runVerify(self, pre="x + z == 0", 
                  hp="t := 0; <x_dot = (A * x^2 + B() * x), z_dot = A * z * x + B() * z, t_dot = 1 & t < 10>",
                  post="0 == -x - z",
                  constants={"B()"},
                  ode_invariants={((1,), ()): "x + z == 0"},
                  darboux_equality={((1,), ()): "true"})

    # Benchmark, problem 30-32

    def testVerify40(self):
        # Condition rule
        # {x >= 0} x >= -2 -> (x := x+1 ++ x := x+2; x := x+1) {x >= 2}
        runVerify(self, pre="x >= 0", hp="x >= -2 -> (x := x+1 ++ x := x+2; x := x+1)", post="x >= 2")

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
                  pre="w >= 0 && d >= 0 && -2 <= a && a <= 2 && b^2 >= 1/3 && w^2 * x^2 + y^2 <= c",
                  hp="t := 0; \
                      <x_dot = y, y_dot = -w^2 * x - 2 * d * w * y, t_dot = 1 & t < 10>; \
                      (x == y * a -> (w := 2 * w; d := d/2; c := c * ((2 * w)^2 + 1^2) / (w^2 + 1^2))\
                      ++ x == y * b -> (w := w/2; d := 2 * d; c := c * (w^2 + 1^2) / ((2 * w^2) + 1^2)) \
                      ++ skip)**",
                  post="w^2 * x^2 + y^2 <= c",
                  loop_invariants={((2,), ()): "w^2 * x^2 + y^2 <= c && d >= 0 && w >= 0 && -2 <= a && a <= 2 && b^2 >= 1/3"},
                  diff_cuts={((1,), (0,)): ["w >= 0 && d >= 0"]},
                  ode_invariants={((1,), ()): "w^2 * x^2 + y^2 <= c && d >= 0 && w >= 0 && -2 <= a && a <= 2 && b^2 >= 1/3"})

    def testVerify42(self):
        runVerify(self,
                  pre="w >= 0 && d >= 0 && -2 <= a && a <= 2 && b^2 >= 1/3 && w^2 * x^2 + y^2 <= c",
                  hp=
                   "(x == y * a -> (w := 2 * w; d := d/2; c := c * ((2 * w)^2 + 1^2) / (w^2 + 1^2))\
                  ++ x == y * b -> (w := w/2; d := 2*d; c := c * (w^2+1^2) / ((2*w^2)+1^2)))**",
                  post="w^2 * x^2 + y^2 <= c",
                  loop_invariants={((), ()): "w^2 * x^2 + y^2 <= c && d >= 0 && w >= 0 && -2 <= a && a <= 2 && b^2 >= 1/3"})


    def testVerify43(self):
        # Basic benchmark, problem 34
        # {x^3 >= -1} <x_dot = (x-3)^4 + a & a > 0> x^3 >= -1
        runVerify(self, pre="x^3 >= -1", hp="<x_dot = (x-3)^4 + a & a > 0>", post="x^3 >= -1",
                  diff_invariants={((), ()): "x^3 >= -1"})

    def testVerify44(self):
        # Basic benchmark, problem 35
        # {x1 + x2^2 / 2 == a} 
        # t := 0; <x1_dot = x1 * x2 , x2_dot = -x1, t_dot = 1 & t < 10> 
        # {x1 + x2^2 / 2 == a}
        runVerify(self, pre="x1 + x2^2 / 2 == a",
                  hp="t := 0; <x1_dot = x1 * x2 , x2_dot = -x1, t_dot = 1 & t < 10>",
                  post="x1 + x2^2 / 2 == a")

    def testVerify45(self):
        # Basic benchmark, problem 36
        # {x1^2 / 2 - x2^2 / 2 >= a}
        # <x1_dot = x2 + x1 * x2^2, x2_dot = -x1 + x1^2 * x2 & x1 > 0 && x2 > 0>
        # {x1^2 / 2 - x2^2 / 2 >= a}
        runVerify(self, pre="x1^2 / 2 - x2^2 / 2 >= a", 
                  hp="<x1_dot = x2 + x1 * x2^2, x2_dot = -x1 + x1^2 * x2 & x1 > 0 && x2 > 0>",
                  post="x1^2 / 2 - x2^2 / 2 >= a")

    def testVerify46(self):
        # Basic benchmark, problem 37
        # {-x1 * x2 >= a}
        # t := 0; <x1_dot = x1 - x2 + x1 * x2, x2_dot = -x2 - x2^2, t_dot = 1 & t < 10>
        # {-x1 * x2 >= a}
        runVerify(self, pre="-x1 * x2 >= a", 
                  hp="t := 0; <x1_dot = x1 - x2 + x1 * x2, x2_dot = -x2 - x2^2, t_dot = 1 & t < 10>",
                  post="-x1 * x2 >= a")

    def testVerify47(self):
        # Basic benchmark, problem 38
        # {2 * x^3 >= 1/4} t := 0; <x_dot = x^2 + x^4, t_dot = 1 & t < 10> {2 * x^3 >= 1/4}
        runVerify(self, pre="2 * x^3 >= 1/4", hp="t := 0; <x_dot = x^2 + x^4, t_dot = 1 & t < 10>",
                  post="2 * x^3 >= 1/4")

    def testVerify48(self):
        # Basic benchmark, problem 39
        # {x^3 >= -1 && y^5 >= 0} 
        # t := 0; <x_dot = (x - 3)^4 + y^5, y_dot = y^2, t_dot = 1 & t < 10> 
        # {x^3 >= -1 && y^5 >= 0}
        runVerify(self, pre="x^3 >= -1 && y^5 >= 0",
                  hp="t := 0; <x_dot = (x - 3)^4 + y^5, y_dot = y^2, t_dot = 1 & t < 10>",
                  post="x^3 >= -1 && y^5 >= 0",
                  ode_invariants={((1,), ()): "x^3 >= -1 && y^5 >= 0"},
                  diff_cuts={((1,), (0,)): ["y^5 >= 0"]})

    def testVerify49(self):
        # Basic benchmark, problem 40
        # A is a constant.
        # {v >= 0 && A > 0} <x_dot = v, v_dot = A & x < 10> {v >= 0}
        runVerify(self, pre="v >= 0 && A > 0", hp="<x_dot = v, v_dot = A & x < 10>",
                  post="v >= 0", constants={'A'})

    def testVerify50(self):
        # Basic bencnmark, problem 41
        # A, B are constants.
        # {v >= 0 && A > 0 && B > 0}
        # (
        #  a := A ++ a := 0 ++ a := -B; 
        #  <x_dot = v, v_dot = a & v > 0>
        # )**
        # {v >= 0}
        runVerify(self, pre="v >= 0 && A > 0 && B > 0",
                  hp="(a := A ++ a := 0 ++ a := -B; <x_dot = v, v_dot = a & v > 0>)**",
                  post="v >= 0",
                  constants={'A', 'B'},
                  loop_invariants={((), ()): "v >= 0"},
                  diff_weakening={((0,1,), ()): "true"})

    def testVerify51(self):
        # ITE
        # {x >= 0} if x < 5 then x := x + 1 else x := x endif {x > 0}
        runVerify(self, pre="x >= 0", hp="if x < 5 then x := x + 1 else x := x endif",
                  post="x > 0")

    def testVerify52(self):
        # Basic benchmark, problem 42 
        # constants = {'A', 'B', 'S'}
        # {v >= 0 && A > 0 && B > 0 && x + v^2 / (2*B) < S}
        #
        # (   if x + v^2 / (2*B) < S then a := A else a := -B endif
        #  ++ if v == 0 then a := 0 else a := -B endif
        #  ++ a := -B;
        #     <x_dot = v, v_dot = a & v >= 0 && x + v^2 / (2*B) < S>
        #  ++ <x_dot = v, v_dot = a & v >= 0 && x + v^2 / (2*B) > S>
        # )**@invariant(v >= 0 && x+v^2/(2*B) <= S)
        #
        # {x <= S}
        runVerify(self, pre="v >= 0 && A > 0 && B > 0 && x + v^2 / (2*B) < S",
                  hp="(   if x + v^2 / (2*B) < S then a := A else a := -B endif \
                       ++ if v == 0 then a := 0 else a := -B endif \
                       ++ a := -B; \
                          <x_dot = v, v_dot = a & v > 0 && x + v^2 / (2*B) < S> \
                       ++ <x_dot = v, v_dot = a & v > 0 && x + v^2 / (2*B) > S> \
                      )**",
                  post="x <= S",
                  constants={'A', 'B', 'S'},
                  loop_invariants={((), ()): "v >= 0 && x+v^2/(2*B) <= S"},
                  diff_weakening={((0, 1, 0), ()): "true", ((0, 1, 1), ()): "true"}
        )

    def testVerify53(self):
        # Basic benchmark, problem 43
        # contants = {'A', 'V'}
        # {v <= V && A > 0}
        #
        # (   if v == V then a := 0 else a := A endif
        #  ++ if v != V then a := A else a := 0 endif;

        #     <x_dot = v, v_dot = a & v <= V>
        # )**@invariant(v <= V)
        #
        # {v <= V}
        runVerify(self, pre="v <= V && A > 0", 
                  hp="(   if v == V then a := 0 else a := A endif \
                       ++ if v != V then a := A else a := 0 endif; \
                          <x_dot = v, v_dot = a & v < V> \
                      )**",
                  post="v <= V",
                  constants={'A', 'V'},
                  loop_invariants={((), ()): "v <= V"},
                  diff_weakening={((0,1), ()): "v <= V"})


if __name__ == "__main__":
    unittest.main()
