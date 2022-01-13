"""Unit test for hhlpy."""

from operator import pos
import unittest

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.parser import aexpr_parser, bexpr_parser, hp_parser
from hhlpy.hhlpy2 import CmdVerifier


def runVerify(self, *, pre, hp, post, 
              constants=set(), strengthened_posts=None,
              loop_invariants=None, ode_invariants=None, 
              solution_rule=None,
              diff_invariant_rule=None, diff_weakening_rule=None, diff_cuts=None, 
              ghost_equations=None, ghost_invariants=None, 
              darboux_rule=None, darboux_cofactors=None,
              barrier_certificate_rule = None, assume_invariants=None, 
              wolfram_engine = False, z3 = True,
              print_vcs=False, expected_vcs=None):
    # Parse pre-condition, HCSP program, and post-condition
    pre = bexpr_parser.parse(pre)

    hp = hp_parser.parse(hp)
    post = bexpr_parser.parse(post)

    # Initialize the verifier
    verifier = CmdVerifier(pre=pre, hp=hp, post=post, constants=constants, 
                           wolfram_engine=wolfram_engine, z3=z3)

    if strengthened_posts:
        for pos, stren_post in strengthened_posts.items():
            if isinstance(stren_post, str):
                stren_post = bexpr_parser.parse(stren_post)
            verifier.add_strengthened_post(pos, stren_post)

    # Place loop invariants
    if loop_invariants:
        for pos, loop_inv in loop_invariants.items():
            if isinstance(loop_inv, str):
                loop_inv = bexpr_parser.parse(loop_inv)
            verifier.add_loop_invariant(pos, loop_inv)
    # Use solution rule
    if solution_rule:
        for pos, sln_rule in solution_rule.items():
            if isinstance(sln_rule, str):
                sln_rule = bexpr_parser.parse(sln_rule)
            verifier.use_solution_rule(pos, sln_rule)

    # Place ode invariants
    if ode_invariants:
        for pos, ode_inv in ode_invariants.items():
            if isinstance(ode_inv, str):
                ode_inv = bexpr_parser.parse(ode_inv)
            verifier.add_ode_invariant(pos, ode_inv)

    # Set differential weakening proof rule as true
    if diff_weakening_rule:
        for pos, dw in diff_weakening_rule.items():
            if isinstance(dw, str):
                dw = bexpr_parser.parse(dw)
            verifier.set_diff_weakening(pos, dw)
            
    # Use differential invariant rule
    if diff_invariant_rule:
        for pos, diff_inv_rule in diff_invariant_rule.items():
            if isinstance(diff_inv_rule, str):
                diff_inv_rule = bexpr_parser.parse(diff_inv_rule)
            verifier.use_diff_invariant_rule(pos, diff_inv_rule)
    
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
                # Remove the blank space.
                ghost_eqs = "".join(ghost_eqs.split())
                if ghost_eqs.count("_dot=") == 1:
                    index = ghost_eqs.index('_dot')
                    ghost_var = ghost_eqs[:index]
                    ghost_diff = ghost_eqs[index + 5:]
                    ghost_diff = aexpr_parser.parse(ghost_diff)
                    
                    ghost_eqs_dict = dict()
                    ghost_eqs_dict[ghost_var] = ghost_diff
                else:
                    raise AssertionError("Wrong Form of Ghost Equations!")
            verifier.add_ghost_equation(pos, ghost_eqs_dict)

    if darboux_rule:
        for pos, dbx_rule in darboux_rule.items():
            if isinstance(dbx_rule, str):
                dbx_rule = bexpr_parser.parse(dbx_rule)
            verifier.use_darboux_rule(pos, dbx_rule)

    if darboux_cofactors:
        for pos, dbx_cofactor in darboux_cofactors.items():
            if isinstance(dbx_cofactor, str):
                dbx_cofactor = aexpr_parser.parse(dbx_cofactor)
            verifier.add_darboux_cofactor(pos, dbx_cofactor)

    if barrier_certificate_rule:
        for pos, barrier_rule in barrier_certificate_rule.items():
            if isinstance(barrier_rule, str):
                barrier_rule = bexpr_parser.parse(barrier_rule)
            verifier.use_barrier_certificate_rule(pos, barrier_rule)

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
        runVerify(self, pre="x >= 0.12345", hp="x := x+1.23456", post="x >= 1")
                  #expected_vcs={((), ()): ["x >= 0 --> x + 1 >= 1"]})

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
                  diff_invariant_rule={((), ()): "true"},
                  ode_invariants={((), ()): "x >= 0"})

    def testVerify8(self):
        # {x * x + y * y == 1} <x_dot=y, y_dot=-x & x > 0> {x * x + y * y = 1}
        # Invariant for ODE is x * x + y * y == 1
        runVerify(self, pre="x * x + y * y == 1", 
                  hp="<x_dot=y, y_dot=-x & x > 0>",
                  post="x * x + y * y == 1",
                  diff_invariant_rule={((), ()): "true"},
                  ode_invariants={((), ()): "x * x + y * y == 1"})

    def testVerify9(self):
        # Basic benchmark, problem 4
        # {x >= 0} x := x+1; <x_dot=2 & x < 10> {x >= 1}
        runVerify(self, pre="x >= 0", hp="x := x+1; <x_dot=2 & x < 10>", post="x >= 1",            
                  ode_invariants={((1,), ()): "x >= 1"})

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

    # Basic benchmark problem 6 is hard to translate into HCSP program.

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
                  ode_invariants={((2,), ()): "y >= 1"},
                  expected_vcs={((), ()): ["x >= 0 && y >= 1 --> (x + 1 >= 1 && y >= 1) && x + 1 + 1 >= 1"],
                                ((1,0,), ()): ["x >= 1 && y >= 1 --> x + 1 >= 1 && y >= 1", 
                                        "x >= 1 && y >= 1 --> y >= 1"],
                                ((2,), ()): ["y < 10 --> 2 >= 0"]}) 

    def testVerify15(self):
        # Basic benchmark, problem8
        # {x > 0 && y > 0} 

        # <x_dot = 5 & x < 10>@invariant(x > 0); 
        # (x := x + 3)**@invariant(x > 0) ++ y := x

        # {x > 0 && y > 0}
        runVerify(self, pre="x > 0 && y > 0", hp="<x_dot = 5 & x < 10>; (x := x + 3)** ++ y := x", 
                  post="x > 0 && y > 0", 
                  loop_invariants={((1,0), ()): "x > 0 && y > 0"}, 
                  ode_invariants={((0,), ()): "x > 0 && y > 0"})

    def testVerify16(self):
        # Test case containing ghost variables
        # Basic benchmark, problem15
        # dG Rule
        # {x > 0} <x_dot = -x> {x > 0}
        runVerify(self, pre="x > 0", hp="t := 0; <x_dot = -x, t_dot=1 & t < 1>", post="x > 0",
                ode_invariants={((1,), ()): "x > 0"},
                ghost_invariants={((1,), ()): "x * y * y == 1"},
                expected_vcs={((1,), ()): ["x > 0 --> (EX y. x * y * y == 1)",
                                           "x * y * y == 1 --> x > 0"]})

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
                  expected_vcs={((1,), (0,)): ["x > 0 --> (EX z. x * z * z == 1)",
                                               "x * z * z == 1 --> x > 0"],
                                ((1,), (1,)): ["t < 1 --> 0 >= 0"]})

    def testVerify18(self):
        # Basic bencmark, problem10
        # dG Rule
        # {x > 0} <x_dot = 5>; <x_dot = 2>; <x_dot = x> {x > 0}
        runVerify(self, pre="x > 0",
                  hp="<x_dot = 5 & x < 1>; <x_dot = 2 & x < 2>; <x_dot = x & x < 5>",
                  post="x > 0",
                  ode_invariants={((0,), ()): "x > 0", ((1,), ()): "x > 0", ((2,), ()): "x > 0"},
                  ghost_invariants={((2,), ()): "x * y * y == 1"})

    def testVerify19(self):
        # Basic benchmark, problem11
        # {x = 0} <x_dot = 1 & x < 10> {x >= 0}
        runVerify(self, pre="x == 0", hp="<x_dot = 1 & x < 10>", post="x >= 0", 
                  ode_invariants={((), ()): "x >= 0"})

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

    def testVerify23(self):
        # Basic benchmark, problem16
        # dbx inequality Rule
        # {x > 0} t := 0; <x_dot = -x + 1, t_dot = 1 & t < 10> {x > 0}
        runVerify(self, pre="x > 0", hp="t := 0; <x_dot = -x + 1, t_dot = 1 & t < 10>", post="x > 0",
                  darboux_rule={((1,), ()): 'true'},
                  darboux_cofactors={((1,),()): "-1"})

    def testVerify24(self):
        # Basic benchmark, problem17
        # {x > 0 && y > 0} t := 0; <x_dot = -y * x, t_dot = 1 & t < 10> {x > 0}
        runVerify(self, pre="x > 0 && y > 0", hp="t := 0; <x_dot = -y * x, t_dot = 1 & t < 10>", 
                  post="x > 0",
                  ode_invariants={((1,), ()): "x > 0"},
                  ghost_invariants={((1,), ()): "x * z * z == 1"},
                  expected_vcs={((), ()): ["x > 0 && y > 0 --> x > 0"],
                                ((1,), ()): ["x > 0 --> (EX z. x * z * z == 1)",
                                             "x * z * z == 1 --> x > 0"]})

    def testVerify25(self):
        # Basic benchmark, problem 18
        # {x >= 0} <x_dot = x & x < 10> {x >= 0}
        # dG and Conjunction Rule
        # Question remained: the form of ghost_equations.
        runVerify(self, pre="x >= 0", hp="<x_dot = x & x < 10>", post="x >= 0",
                  ode_invariants={((), ()): "x >= 0", ((), (0,1)): "x * y >= 0"},
                  ghost_equations = {((), ()): "y_dot = - y"},
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
                  ode_invariants={((), ()): "x >= 1"})

    def testVerify29(self):
        # Basic benchmark, problem 22
        # dI Rule
        # {x * x + y * y == 1} t := 0; <x_dot = -y, y_dot = x, t_dot = 1 & t < 10> {x * x + y * y == 1}
        runVerify(self, pre="x * x + y * y == 1", 
                  hp="t := 0; <x_dot = -y, y_dot = x, t_dot = 1 & t < 10>",
                  post="x * x + y * y == 1",
                  ode_invariants={((1,), ()): "x * x + y * y == 1"})

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
                  diff_weakening_rule={((), (1,)): "true", ((),(0,0)): "true"},
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
                  darboux_rule={((1,), ()): "true"})

    # Benchmark, problem 30, 32 are hard to translate into hcsp programs.

    def testVerify38(self):
        # Basic benchmark, problem 31
        # {x + z >= 0} 
        # <x_dot = x^2, z_dot = z * x + y & y > x^2>
        # {x + z >= 0}
        runVerify(self, pre="x + z >= 0",
                  hp="<x_dot = x^2, z_dot = z * x + y & y > x^2>",
                  post="x + z >= 0",
                  darboux_cofactors={((), ()): "x"})

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
                  ode_invariants={((), ()): "x^3 >= -1"})

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
                  post="v >= 0", constants={'A'}, 
                  diff_cuts={((), ()): ["A > 0"]})

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
                  diff_weakening_rule={((0,1,), ()): "true"})

    def testVerify51(self):
        # ITE
        # {x >= 0} if x < 5 then x := x + 1 else x := x endif {x > 0}
        runVerify(self, pre="x >= 0", hp="if x < 5 then x := x + 1 else x := x endif",
                  post="x > 0")

    def testVerify52(self):
        # Basic benchmark, problem 42 
        # constants = {'A', 'B', 'S'}

        # another version
        # {v >= 0 && A > 0 && B > 0 && x + v^2 / (2*B) < S}
        # 
        # (if x + v^2 / (2*B) < S 
        #     then a := A; <x_dot = v, v_dot = a & v > 0 && x + v^2 / (2*B) < S>
        #  elif v == 0
        #     then a := 0
        #  else a := -B; <x_dot = v, v_dot = a & v > 0>
        #  endif
        # )**
        #
        # {x <= S}
        runVerify(self, pre="v >= 0 && A > 0 && B > 0 && x + v^2 / (2*B) < S",
                  hp="(if x + v^2 / (2*B) < S \
                          then (a := A; <x_dot = v, v_dot = a & v > 0 && x + v^2 / (2*B) < S>) \
                       elif v == 0 \
                          then a := 0 \
                       else (a := -B; <x_dot = v, v_dot = a & v > 0>) \
                       endif \
                      )**",
                  post="x <= S",
                  constants={'A', 'B', 'S'},
                  loop_invariants={((), ()): "v >= 0 && x+v^2/(2*B) <= S"},
                  diff_weakening_rule={((0, 2, 1), (0,)): "true",
                                       ((0, 0, 1), (0,)): "true",
                                       ((0, 0, 1), (1,)): "true"},
                  ode_invariants={((0, 2, 1), (1,)): "x+v^2/(2*B) <= S"},
                  diff_cuts={((0, 2, 1), (1,)): ["a == -B"]},
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
                  diff_weakening_rule={((0,1), ()): "v <= V"})

    def testVerify54(self):
        # Basic benchmark, problem 44
        # constants = {'A', 'V'}
        # {v <= V && A > 0}
        #
        # (a := A;
        #  <x_dot = v, v_dot = a & v < V>
        # )**
        #
        # {v <= V}
        runVerify(self, pre="v <= V && A > 0", 
                  hp="(a := A;\
                      <x_dot = v, v_dot = a & v < V>\
                       )**",
                  post="v <= V",
                  constants={'A', 'V'},
                  loop_invariants={((), ()): "v <= V"},
                  diff_weakening_rule={((0,1), ()): "true"},
        )

    # Basic benchmark, problem 46-48
    def testVerify55(self):
        # Basic benchmark, problem 45
        # constants = {'A', 'V'}
        # {v <= V && A > 0}
        #     (
        #         if v == V then a := 0; t := 0; <x_dot = v, v_dot = a & t < 10>
        #         else a := A; <x_dot = v, v_dot = a & v < V>
        #         endif        
        #     )**@invariant(v <= V)
        # {v <= V}
        runVerify(self, pre="v <= V && A > 0",
                  hp="(if v == V then a := 0; t := 0; <x_dot = v, v_dot = a & t < 10> \
                       else a := A; <x_dot = v, v_dot = a & v < V> \
                       endif \
                       )**",
                  post="v <= V",
                  constants={'A', 'V'},
                  loop_invariants={((), ()): "v <= V"},
                  diff_cuts={((0, 0, 2), ()): ["a == 0"]},
                  diff_weakening_rule={((0, 1, 1), ()): "true"},
                )       

    # def testVerify56(self):
    #     # Basic benchcmark, problem 46
    #     # constants = {'A', 'B', 'S', 'ep'}
    #     # {v >= 0 && A > 0 && B > 0 && x + v^2 / (2*B) <= S && ep > 0}
    #     #     (      if x+v^2/(2*B) + (A/B+1)*(A/2*ep^2+ep*v) <= S then a := A else a := -B endif
    #     #         ++ if v == 0 then a := 0 else a := -B endif
    #     #         ++ a := -B
    #     #         ;

    #     #         c := 0;
    #     #         < x_dot = v, v_dot = a, c_dot = 1 & v > 0 && c < ep >
    #     #     )**@invariant(v >= 0 && x+v^2/(2*B) <= S)
    #     # {x <= S}
    #     runVerify(self,  pre="v >= 0 && A > 0 && B > 0 && x + v^2 / (2*B) <= S && ep > 0",
    #               hp="(   if x+v^2/(2*B) + (A/B+1)*(A/2*ep^2+ep*v) <= S then a := A else a := -B endif \
    #                    ++ if v == 0 then a := 0 else a := -B endif \
    #                    ++ a := -B; \
    #                     c := 0; \
    #                     < x_dot = v, v_dot = a, c_dot = 1 & v > 0 && c < ep > \
    #                  )**",
    #               post="x <= S",
    #               constants={'A', 'B', 'S', 'ep'},
    #               loop_invariants={((), ()): "v >= 0 && x+v^2/(2*B) <= S"},
    #               diff_weakening_rule={((0, 2), (0,)): "true"},
    #               solution_rule={((0, 2), (1,)): "true"},
    #               print_vcs=True)

    def testVerify59(self):
        # Basic benchmark, problem 49
        # Constants = {'Kp()', 'Kd()', 'xr()', 'c()'}
        # {v >= 0 && c() > 0 && Kp() == 2 && Kd() == 3 && 5/4*(x1-xr())^2 + (x1-xr())*v/2 + v^2/4 < c()}
        # t := 0; 
        # <x1_dot = v, v_dot = -Kp()*(x1-xr()) - Kd()*v, t_dot = 1 & t < 10>
        # {5/4*(x1-xr())^2 + (x1-xr())*v/2 + v^2/4 < c()}
        runVerify(self, \
                  pre="v >= 0 && c() > 0 && Kp() == 2 && Kd() == 3 \
                      && 5/4*(x1-xr())^2 + (x1-xr())*v/2 + v^2/4 < c()",
                  hp="t := 0; <x1_dot = v, v_dot = -Kp()*(x1-xr()) - Kd()*v, t_dot = 1 & t < 10>",
                  post="5/4*(x1-xr())^2 + (x1-xr())*v/2 + v^2/4 < c()",
                  ode_invariants={((1,), ()): "5/4*(x1-xr())^2 + (x1-xr())*v/2 + v^2/4 < c()"},
                  constants={'Kp()', 'Kd()', 'xr()', 'c()'}
                  )

    # def testVerify60(self):
    #     # Basic benchmark, problem 50
    #     #         v >= 0 & xm <= x2 & x2 <= S & xr = (xm + S)/2 & Kp = 2 & Kd = 3
    #     #            & 5/4*(x2-xr)^2 + (x2-xr)*v/2 + v^2/4 < ((S - xm)/2)^2
    #     #  -> [ { {  xm := x2;
    #     #            xr := (xm + S)/2;
    #     #            ?5/4*(x2-xr)^2 + (x2-xr)*v/2 + v^2/4 < ((S - xm)/2)^2;
    #     #         ++ ?true;
    #     #         };
    #     #         {{ x2' = v, v' = -Kp*(x2-xr) - Kd*v & v >= 0 }
    #     #           @invariant(
    #     #             xm<=x2,
    #     #             5/4*(x2-(xm+S())/2)^2 + (x2-(xm+S())/2)*v/2 + v^2/4 < ((S()-xm)/2)^2
    #     #          )
    #     #         }
    #     #       }*@invariant(v >= 0 & xm <= x2 & xr = (xm + S)/2 & 5/4*(x2-xr)^2 + (x2-xr)*v/2 + v^2/4 < ((S - xm)/2)^2)
    #     #     ] x2 <= S
    #     runVerify(self, \
    #               pre="v >= 0 && xm <= x2 && x2 <= S && xr == (xm + S)/2 && Kp == 2 && Kd == 3 \
    #                 && 5/4*(x2-xr)^2 + (x2-xr)*v/2 + v^2/4 < ((S - xm)/2)^2",\
    #               hp="( \
    #                     xm := x2; \
    #                     xr := (xm + S)/2; \
    #                     <x2_dot = v, v_dot = -Kp * (x2 - xr) - Kd * v & v > 0> \
    #                   )**",
    #               post="x2 <= S",
    #               constants={'Kp', 'Kd', 'S'},
    #               loop_invariants={((), ()): "v >= 0 && xm <= x2 && xr == (xm + S)/2 && \
    #                                           5/4*(x2-xr)^2 + (x2-xr)*v/2 + v^2/4 < ((S - xm)/2)^2"},
    #               diff_weakening_rule={((0,3), (0,)): "true"},
    #               diff_cuts={((0, 3), (3,)): ["xm <= x2", 
    #                  "5/4*(x2-(xm+S)/2)^2 + (x2-(xm+S)/2)*v/2 + v^2/4 < ((S-xm)/2)^2"]})

    # Basic benchmark, problem 50-51

    def testVerify62(self):
        # Basic benchmark, problem 52
        # {v >= 0 && a >= 0}
        # <x_dot = v, v_dot = a & v > 0>
        # {v >= 0}
        runVerify(self, pre="v >= 0 && a >= 0",
                  hp="<x_dot = v, v_dot = a & v > 0>",
                  post="v >= 0",
                  diff_weakening_rule={((), ()): "true"})

    # Basic benchmark, problem 53, A() or A?

    def testVerify64(self):
        # Basic benchmark, problem 54
        # {v >= 0 && A >= 0 && b > 0}
        # (
        #    {  ?(m-x>=2); a := A;
        #   ++ a := -b;
        #   };
        #   {x' = v, v' = a & v >= 0}
        #  )**@invariant(v >= 0)
        # {v >= 0}
        runVerify(self, pre="v >= 0 && A >= 0 && b > 0",
                  hp="( \
                      if m-x >= 2 \
                        then a := A; t := 0; <x_dot = v, v_dot = a & t < 10> \
                      else a := -b; <x_dot = v, v_dot = a & v > 0> \
                      endif \
                      )**",
                  post="v >= 0",
                  loop_invariants={((), ()): "v >= 0 && A >= 0"},
                  diff_weakening_rule={((0, 1, 1), (0,)): "true"},
                  diff_cuts={((0, 0, 2), ()): ["a >= 0"]})

    def testVerify65(self):
        # Solution Axiom
        # {v >= 0}
        # <v_dot = 1 & v < 10>
        # {v >= 0}
        runVerify(self, pre="v >= 0",
                  hp="<v_dot = 1 & v < 10>",
                  post="v >= 0",
                  solution_rule = {((), ()): "true"})

    def testVerify66(self):
        # Solution Axiom
        # {x >= 0 && v >= 0 && a >= 0}
        # <x_dot = v, v_dot = a & x < 10>
        # {x >= 0}
        runVerify(self, pre="x >= 0 && v >= 0 && a >= 0",
                  hp="<x_dot = v, v_dot = a & x < 10>",
                  post="x >= 0",
                  solution_rule={((), ()): "true"})

    def testVerify67(self):
        # Solution Axiom
        # {x >= 0 && v >= 0 && a >= 0 && c == 0}
        # <x_dot = v, v_dot = a, c_dot = 1 & c < 10>
        # {x >= 0}
        runVerify(self, pre="x >= 0 && v >= 0 && a >= 0 && c == 0",
                  hp="<x_dot = v, v_dot = a, c_dot = 1 & c < 10>",
                  post="x >= 0",
                  solution_rule={((), ()): "true"})

    def testVerify68(self):
        # Strengthened post
        # {x == 0}
        # t := 0; <x_dot = 2, t_dot = 1 & t < 1>
        # stren_post: {x == 2*t && t == 1}
        # {x == 2}
        runVerify(self, pre="x == 0",
                  hp="t := 0; <x_dot = 2, t_dot = 1 & t < 1>",
                  post="x == 2",
                  strengthened_posts={((), ()): "x == 2 * t && t == 1"},
                  diff_weakening_rule={((1,), (1,)): "true"})

    # def testVerify69(self):
    #     # Basic benchmark, problem 55
    #     # {v^2 <= 2*b*(m-x) && v >= 0  && A >= 0 && b > 0}
    #     #     (
    #     #         if 2*b*(m-x) >= v^2 + (A+b)*(A*ep^2+2*ep*v) then a := A else a := -b endif 
    #     #      ++ a := -b; 
    #     #         t := 0;
    #     #         <x_dot = v, v_dot = a, t_dot = 1 & v > 0 && t < ep>
    #     #     )**@invariant(v^2 <= 2*b*(m-x))
    #     # {x <= m}
    #     runVerify(self, pre="v^2 <= 2*b*(m-x) && v >= 0  && A >= 0 && b > 0",
    #               hp="( \
    #                     if 2*b*(m-x) >= v^2 + (A+b)*(A*ep^2+2*ep*v) then a := A else a := -b endif \
    #                 ++ a := -b; \
    #                     t := 0; \
    #                     <x_dot = v, v_dot = a, t_dot = 1 & v > 0 && t < ep> \
    #                 )**",
    #               post="x <= m",
    #               constants={'b', 'A', 'ep'},
    #               loop_invariants={((), ()): "v^2 <= 2*b*(m-x)"},
    #               solution_rule={((0, 2), ()): "true"},
    #               )
    
    # Basic benchmark, problem 56 - 60, cannot be written into hcsp program.

    def nonlinearTestVerify1(self):
        # Nonlinear benchmark, problem 1
        #  {0.5 <= x && x <= 0.7 && 0 <= y && y <= 0.3}
        #  t := 0; <x_dot = -x + x * y , y_dot = -y, t_dot = 1 & t < 10>
        #  {~(-0.8 >= x && x >= -1 && -0.7 >= y && y >= -1)}
        runVerify(self,pre="0.5 <= x && x <= 0.7 && 0 <= y && y <= 0.3",
                  hp="t := 0; <x_dot = -x + x * y , y_dot = -y, t_dot = 1 & t < 10>",
                  post="~(-0.8 >= x && x >= -1 && -0.7 >= y && y >= -1)",
                  ode_invariants={((1,),()): "x >= 0 && y >= 0"},
                  darboux_rule={((1,),(0,)): "true", ((1,), (1,)): "true"})
    
    def nonlinearTestVerify2(self):
        # Nonlinear benchmark, problem 2
        # {x == 1 && y == 1/8}
        # t := 0; <x_dot = x - y^2, y_dot = y * (x - y^2) & t < 10>@invariant(y^2 < x)
        # {~(x < 0)}
        runVerify(self, pre="x == 1 && y == 1/8",
                  hp="t := 0; <x_dot = x - y^2, y_dot = y * (x - y^2) & t < 10>",
                  post="~(x < 0)",
                  ode_invariants={((1,), ()): "y^2 < x"},
                  darboux_rule={((1,), ()): "true"})

    def nonlinearTestVerify3(self):
        # Nonlinear benchmark, problem 3
        # {x == 1 && y == -1}
        #     t := 0;
        #     <x_dot = x^2 + (x+y)/2, y_dot = (-x + 3*y)/2 & t < 10>@invariant(y-x+1<=0 & y<=0)
        # {~(y>0)}
        runVerify(self, pre="x == 1 && y == -1",
                  hp="t := 0; <x_dot = x^2 + (x+y)/2, y_dot = (-x + 3*y)/2 & t < 10>",
                  post="~(y>0)",
                  diff_cuts={((1,), ()): ["y-x+1 <= 0"]},
                  ode_invariants={((1,), ()): "y <= 0"},
                  darboux_cofactors={((1,), (0,)): "1",
                                     ((1,), (1,)): "1"},
                  print_vcs=True)

    # def nonlinearTestVerify4(self):
    #     # Nonlinear benchmark, problem 4
    #     # {-1/5000 + (1/20+x)^2 + (3/200 + y)^2 <= 0}
    #     #     t := 0;
    #     #     <x_dot = (-3 * x^2) / 2 - x^3 / 2 - y, y_dot = 3 * x - y & t < 10>@invariant(0.073036*x^6-0.014461*x^5*y+0.059693*x^4*y^2-0.0063143*x^3*y^3+0.029392*x^2*y^4+0.0036316*y^6+0.064262*x^5+0.24065*x^4*y-0.082711*x^3*y^2+0.28107*x^2*y^3-0.015542*x*y^4+0.036437*y^5+0.47415*x^4-0.56542*x^3*y+1.1849*x^2*y^2-0.22203*x*y^3+0.19053*y^4-0.59897*x^3+1.8838*x^2*y-0.59653*x*y^2+0.47413*y^3+1.0534*x^2-0.51581*x*y+0.43393*y^2-0.35572*x-0.11888*y-0.25586<=0)
    #     # {~(49/100 + x + x^2 + y + y^2 <= 0)}
    #     runVerify(self, pre="-1/5000 + (1/20+x)^2 + (3/200 + y)^2 <= 0",
    #               hp="t := 0; \
    #                  <x_dot = (-3 * x^2) / 2 - x^3 / 2 - y, y_dot = 3 * x - y & t < 10>",
    #               post="~(49/100 + x + x^2 + y + y^2 <= 0)",
    #               ode_invariants={((1,), ()): "0.073036*x^6-0.014461*x^5*y+0.059693*x^4*y^2-0.0063143*x^3*y^3+0.029392*x^2*y^4+0.0036316*y^6+0.064262*x^5+0.24065*x^4*y-0.082711*x^3*y^2+0.28107*x^2*y^3-0.015542*x*y^4+0.036437*y^5+0.47415*x^4-0.56542*x^3*y+1.1849*x^2*y^2-0.22203*x*y^3+0.19053*y^4-0.59897*x^3+1.8838*x^2*y-0.59653*x*y^2+0.47413*y^3+1.0534*x^2-0.51581*x*y+0.43393*y^2-0.35572*x-0.11888*y-0.25586<=0"})

    def nonlinearTestVerify5(self):
        # Nonlinear benchmark, problem 5
        # {-1/20 + (5/4+x)^2 + (-5/4+y)^2 <= 0}
        #     t := 0;
        #     <x_dot = 7/8 + x - x^3/3 - y, y_dot = (2 * (7/10 + x - (4*y)/5)) / 25, t_dot = 1 & t < 10>
        #           @invariant(x * ((-73) + 23*x) < 157 + y * (134 + 81*y))
        # {~(36/5 + 5*x + x^2 + 2*y + y^2 <= 0)}
        runVerify(self, pre="-1/20 + (5/4+x)^2 + (-5/4+y)^2 <= 0",
                  hp="t := 0; \
                      <x_dot = 7/8 + x - x^3/3 - y, y_dot = (2 * (7/10 + x - (4*y)/5)) / 25, t_dot = 1 & t < 10>",
                  post="~(36/5 + 5*x + x^2 + 2*y + y^2 <= 0)",
                  ode_invariants={((1,), ()): "x * ((-73) + 23*x) < 157 + y * (134 + 81*y)"},
                  barrier_certificate_rule={((1,), ()): "true"})

    def nonlinearTestVerify6(self):
        # Nonlinear benchmark, problem 6
        # {x^2 + (-1/2 + y)^2 < 1/24}
        #     <x_dot = -x + 2*x^3*y^2, y_dot = -y & x^2*y^2 < 1>
        # @invariant(4*x*(1821+5601250*x)+4827750*x*y+125*(76794+(-45619)*x^3)*y^2 < 1375*(4891+3332*y))
        # {~(x <= -2 || y <= -1)}
        runVerify(self, pre="x^2 + (-1/2 + y)^2 < 1/24",
                  hp="<x_dot = -x + 2*x^3*y^2, y_dot = -y & x^2*y^2 < 1>",
                  post="~(x <= -2 || y <= -1)",
                  strengthened_posts={((), ()): "4*x*(1821+5601250*x)+4827750*x*y+125*(76794+(-45619)*x^3)*y^2 < 1375*(4891+3332*y) && x^2*y^2 == 1"},
                  barrier_certificate_rule={((), (0,)): "true"},
                  diff_weakening_rule={((), (1,)): "true"},
                  wolfram_engine=True,
                  print_vcs=True)

    def nonlinearTestVerify7(self):
    #   {(2+x)^2 + (-1+y)^2 <= 1/4}
    #     t := 0;
    #     <x_dot = x^2 + 2*x*y + 3*y^2, y_dot = 2*y*(2*x+y), t_dot = 1 & t < 10>@invariant(x<y, x+y<0)
    #   {~(x > 0)}
        runVerify(self, pre="(2+x)^2 + (-1+y)^2 <= 1/4", 
                  hp="t := 0; \
                      <x_dot = x^2 + 2*x*y + 3*y^2, y_dot = 2*y*(2*x + y), t_dot = 1 & t < 10>",
                  post="~(x > 0)",
                  ode_invariants={((1,), ()): "x < y && x + y < 0"},
                  diff_cuts={((1,), (1,)): ["x < y"]},
                  darboux_rule={((1,), (0,)): "true",
                                ((1,), (1, 0)): "true",
                                ((1,), (1, 1)): "true"})


if __name__ == "__main__":
    unittest.main()
