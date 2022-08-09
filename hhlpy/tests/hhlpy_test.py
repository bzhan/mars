"""Unit test for hhlpy."""

import unittest
import os
from wolframclient.evaluation import WolframLanguageSession

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.hcsp import HCSP, Function
from ss2hcsp.hcsp.parser import parse_expr_with_meta, parse_expr_with_meta, parse_hp_with_meta, \
    parse_hoare_triple_with_meta
from hhlpy.hhlpy_without_dG import CmdVerifier
from hhlpy.wolframengine_wrapper import found_wolfram, session

def runFile(self, file, 
              andR_rule=None,
              print_vcs=False, expected_vcs=None):
    # Read the file
    file = os.path.join(os.path.dirname(__file__), "../examples", file)
    file = open(file,mode='r', encoding='utf-8')
    file_contents = file.read()
    file.close()

    # Parse pre-condition, HCSP program, and post-condition
    hoare_triple = parse_hoare_triple_with_meta(file_contents)

    # Initialize the verifier
    verifier = CmdVerifier(
        pre=hoare_triple.pre, 
        hp=hoare_triple.hp,
        post=hoare_triple.post,
        functions=hoare_triple.functions)
    
    if andR_rule:
        for pos, andR in andR_rule.items():
            if isinstance(andR, str):
                andR = parse_expr_with_meta(andR)
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
                "annot_pos:", vc.annot_pos,
                "categ:", vc.categ,
                "blabel:", str(vc.blabel),
                "comp_label:", str(vc.comp_label),
                "vc:", vc.vc,
                "pc:", vc.pc)

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
            vcs = [parse_expr_with_meta(vc) for vc in vcs]
            actual_vcs = [vc.expr for vc in verifier.infos[pos].vcs if not is_trivial(vc.expr)]
            self.assertEqual(set(vcs), set(actual_vcs), 
            "\nExpect: {}\nActual: {}".format([str(vc) for vc in vcs],[str(vc) for vc in actual_vcs]))

class HHLPyTest(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        if found_wolfram:
            session.start()

    @classmethod
    def tearDownClass(cls):
        if found_wolfram:
            session.terminate()

    def testParseHoareTriple(self):
        res = parse_hoare_triple_with_meta("""
            pre [x >= 0];
            x := x + 1;
            post [x >= 1];
        """)
        self.assertEqual(str(res.pre[0]), "x >= 0")
        self.assertEqual(str(res.post[0].expr), "x >= 1")
        self.assertEqual(str(res.hp), "x := x + 1;")

    def testParseHoareTriple2(self):
        res = parse_hoare_triple_with_meta("""
            function bar(x, y) = 2 * x + y;
            pre [x >= 0];
            x := x + 1;
            post [x >= 1];
        """)
        self.assertEqual(str(res.functions["bar"]), "bar(x,y) = 2 * x + y")

    def testParseHoareTriple3(self):
        res = parse_hoare_triple_with_meta("""
            function bar(x, y) = 2 * x == y;
            pre [x >= 0];
            x := x + 1;
            post [x >= 1];
        """)
        self.assertEqual(str(res.functions["bar"]), "bar(x,y) = 2 * x == y")

    def testReplaceFunction1(self):
        res = parse_expr_with_meta("bar(y)")
        funcs = {'bar': Function('bar', ['x'], 'x + 1')}

        self.assertEqual(str(expr.replace_function(res, funcs)), 'y + 1')

    def testReplaceFunction2(self):
        res = parse_expr_with_meta("bar(a, b)")
        
        funcs = {'bar': Function('bar', ['x', 'y'], '2 * x == y')}

        self.assertEqual(str(expr.replace_function(res, funcs)), '2 * a == b')

    def testReplaceFunction3(self):
        res = parse_expr_with_meta("am(x)")
        
        funcs = {'bar': Function('bar', ['x'], 'x + 1'), 'am': Function('am', ['x'], '2 * bar(x)')}

        self.assertEqual(str(expr.replace_function(res, funcs)), '2 * bar(x)')

    def testVerify1(self):
        runFile(self, file="test1.hhl")

    def testVerify1_1(self):
        runFile(self, file="test1_1.hhl")

    def testVerify2(self):
        runFile(self, file="test2.hhl",
                  expected_vcs={((), ()): ["x >= 0 -> x + 1 >= 1", "x >= 0 -> x + 2 >= 1"]},
                  print_vcs=False)

    def testVerify2_1(self):
        runFile(self, file="test2_1.hhl",
        print_vcs=False)

    def testVerify2_2(self):
        runFile(self, file="test2_2.hhl",
                print_vcs=False)

    def testVerify2_3(self):
        runFile(self, file="test2_3.hhl",
                print_vcs=False)

    def testVerify3(self):
        runFile(self, file="test3.hhl",
                  expected_vcs={((), ()): ["x >= 0 -> x + 1 >= 1", "x >= 0 -> x + 1 + 2 >= 3"]})

    def testVerify4_1(self):
        runFile(self, file="test4_1.hhl",
                  print_vcs=False)

    def testVerify4_2(self):
        runFile(self, file="test4_2.hhl",
                  print_vcs=False)

    def testVerify5(self):
        runFile(self, file="test5.hhl", print_vcs=False,
                  expected_vcs={((), (0,)): ["x >= 0 -> x + 1 >= 0"]})

    def testVerify5_1(self):
        runFile(self, file="test5_1.hhl",
                  print_vcs=False)

    def testVerify5_2(self):
        runFile(self, file="test5_2.hhl",
                  print_vcs=False)

    def testVerify5_3(self):
         runFile(self, file="test5_3.hhl",
                  print_vcs=False)

    def testVerify7(self):
        runFile(self, file="test7.hhl", print_vcs=False)

    # TODO: 
    # def testVerify7_1(self):
    #     # {true} <x_dot = 2 & x < 10> {true}
    #     runVerify(self, pre="true", hp="<x_dot = 2 & x < 10>", post="true", print_vcs=True)

    def testVerify7_2(self):
        runFile(self, file="test7_2.hhl",
                  print_vcs=False)

    def testVerify8(self):
        runFile(self, file="test8.hhl",
                  print_vcs=False)

    def testVerify11(self):
        runFile(self, file="test11.hhl",
                  expected_vcs={((), ()): ["x0 >= 0 -> x0 >= 0 -> x1 >= 1 -> x1 >= 1"]})

    def testVerify12(self):
        runFile(self, file="test12.hhl",
                  expected_vcs={((), ()): ["x >= 0 -> y0 >= x + 1 -> y0 >= 1"]})

    def testVerify13(self):
        runFile(self, file="test13.hhl",
                  expected_vcs={((), ()): ["x >= 0 -> y1 >= x + 1 ->y0 >= x + 1 + 1 -> y0 >= 2"]})

    def testVerify9(self):
        runFile(self, file="test9.hhl", print_vcs=False)

    def testVerify14_1(self):
        runFile(self, file="test14_1.hhl",
                  print_vcs=False) 

    def testVerify18(self):
        runFile(self, file="test18.hhl",
                  print_vcs=False)

    def testVerify36_1(self):
        runFile(self, file="test36_1.hhl",)

    def testVerify40(self):
        runFile(self, file="test40.hhl",)

    def testVerify42(self):
        runFile(self,file="test42.hhl",)

    def testVerify51(self):
        runFile(self, file="test51.hhl",)

    def testVerify52_1(self):
            runFile(self, file="test52_1.hhl",)

    def testVerify56_1(self):
        runFile(self, file="test56_1.hhl",)

    def testVerify65(self):
        runFile(self, file="test65.hhl",)

    def testVerify66(self):
        runFile(self, file="test66.hhl",)

    def testVerify67(self):
        runFile(self, file="test67.hhl",)

    def testVerify68(self):
        runFile(self, file="test68.hhl",)

class BasicHHLPyTest(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        if found_wolfram:
            session.start()

    @classmethod
    def tearDownClass(cls):
        if found_wolfram:
            session.terminate()

    def testBasic1(self):
        runFile(self, file="basic1.hhl")
                  #expected_vcs={((), ()): ["x >= 0 -> x + 1 >= 1"]})

    def testBasic2(self):
        runFile(self, file="basic2.hhl",
                  expected_vcs={((), ()): ["x >= 0 -> x + 1 + 1 >= 1", "x >= 0 -> x + 1 >= 1"]})

    def testBasic3(self):
        runFile(self, file="basic3.hhl",
                  expected_vcs={((), ()): ["x >= 0 -> x + 1 >= 1"],
                                ((1,), (0,)): ["x >= 1 -> x + 1 >= 1"]})

    def testBasic4(self):
        runFile(self, file="basic4.hhl",
                  print_vcs=False)

    def testBasic5(self):
        runFile(self, file="basic5.hhl",
                  expected_vcs={((), ()): ["x >= 0 -> x0 >= 1 -> x0 >= 1"]})

    # TODO: Basic benchmark problem 6 is hard to translate into HCSP program.

    def testBasic7(self):
        runFile(self, file="basic7.hhl") 

    def testBasic8(self):
        runFile(self, file="basic8.hhl")

    def testBasic9(self):
        runFile(self, file="basic9.hhl")
    
    def testBasic10(self):
        runFile(self, file="basic10.hhl",
                  print_vcs=False)

    def testBasic11(self):
        runFile(self, file="basic11.hhl",)

    def testBasic12(self):
        runFile(self, file="basic12.hhl",
                  expected_vcs={((), ()): ["y >= 0 -> x >= 0 && y >= 0 -> t0 >= 0 -> t0 > 0 -> y >= 0",
                                           "y >= 0 -> x >= 0 && y >= 0 -> t0 >= 0 -> t0 > 0 -> x >= 0",
                                           "y >= 0 -> x >= 0 && y >= 0 -> t0 >= 0 -> t0 <= 0 -> x >= 0"]})

    def testBasic13(self):
        runFile(self, file="basic13.hhl",)


    def testBasic14(self):
        runFile(self, file="basic14.hhl",)

    def testBasic15(self):
        runFile(self, file="basic15.hhl")
                # expected_vcs={((), ()): ["x > 0 -> 0 < 1 -> (\exists y. x * y * y == 1)", \
                #                          "x > 0 -> 0 >= 1 -> x > 0"],
                #               ((1,), ()): ["(\exists y. x * y * y == 1) && t == 1 -> x > 0"]})

    def testBasic16(self):
        runFile(self, file="basic16.hhl",)

    def testBasic17(self):
        runFile(self, file="basic17.hhl",)
                #   expected_vcs={((), ()): ["y > 0 -> x > 0 && y > 0 -> t0 >= 0 -> t0 > 0 -> (\exists z. x * z * z == 1)",
                #                            "y > 0 -> x > 0 && y > 0 -> t0 >= 0 -> t0 <= 0 -> x > 0"],
                #                 ((1,), ()): ["y > 0 -> (\\exists z. x * z * z == 1) && t == 0 -> x > 0"]})

    def testBasic18(self):
        runFile(self, file="basic18.hhl", print_vcs=False)

    def testBasic19(self):
        runFile(self, file="basic19.hhl",)

    # TODO: Basic benchmark, problem 20. The expression is not a polynomial.

    def testBasic21(self):
        runFile(self, file="basic21.hhl",)

    def testBasic22(self):
        runFile(self, file="basic22.hhl",)

    def testBasic23(self):
        runFile(self, file="basic23.hhl",)

    def testBasic24(self):
        runFile(self, file="basic24.hhl",)

    def testBasic25(self):
        runFile(self, file="basic25.hhl",)

    def testBasic26(self):
        runFile(self, file="basic26.hhl",)

    def testBasic27(self):
        runFile(self, file="basic27.hhl",
                  expected_vcs={((),()): ["z == -2 -> x >= 1 && y == 0 -> x >= 1",
                                          "z == -2 -> x >= 1 && y == 0 -> y >= 0", 
                                          # `y == 0` comes from implicit dW
                                          "z == -2 -> x >= 1 && y == 10 && z == -2 ->\
                                          (y > 0 -> x >= 1)", 
                                          "z == -2 -> x >= 1 && y == 10 && z == -2 -> \
                                           y <= 0 -> x >= 1",
                                           "z == -2 -> x >= 1 && y == 10 && z == -2 -> \
                                           y <= 0 -> y >= 0"],
                                ((), (0,)): ["z == -2 -> y > 0 -> y >= 0"] 
                                          # This is from dI (condition implies differential of invariant)
                                }) 
                                          # `y <= 0 -> x >= 1 && y >= 0` is the dW precondition

    def testBasic28(self):
        runFile(self, file="basic28.hhl",)

    def testBasic29(self):
        runFile(self, file="basic29.hhl",)

    # TODO: Benchmark, problem 30, 32 are hard to translate into hcsp programs.

    def testBasic31(self):
        runFile(self, file="basic31.hhl",)

    def testBasic33(self):
        runFile(self, file="basic33.hhl",)

    def testBasic34(self):
        runFile(self, file="basic34.hhl",)

    def testBasic35(self):
        runFile(self, file="basic35.hhl",)

    def testBasic36(self):
        runFile(self, file="basic36.hhl",)

    def testBasic37(self):
        runFile(self, file="basic37.hhl",)

    def testBasic38(self):
        runFile(self, file="basic38.hhl",)

    def testBasic39(self):
        runFile(self, file="basic39.hhl",)

    def testBasic40(self):
        runFile(self, file="basic40.hhl",)
                #   constants={'A'})

    def testBasic41(self):
        runFile(self, file="basic41.hhl",)
                #   constants={'A', 'B'})

    def testBasic42(self):
        runFile(self, file="basic42.hhl",)
                #   constants={'A', 'B', 'S'})

    def testBasic43(self):
        runFile(self, file="basic43.hhl",)
                #   constants={'A', 'V'})

    def testBasic44(self):
        runFile(self, file="basic44.hhl",)
                #   constants={'A', 'V'})

    def testBasic45(self):
        runFile(self, file="basic45.hhl",
                #  constants={'A', 'V'}
                ) 

    def testBasic46(self):
        runFile(self, file="basic46.hhl",)

    def testBasic47(self):
        runFile(self, file="basic47.hhl",)

    def testBasic48(self):
        runFile(self, file="basic48.hhl",)

    def testBasic49(self):
        runFile(self, file="basic49.hhl",)

    def testBasic50(self):
        runFile(self, \
                  file="basic50.hhl",
                  )

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

    def testBasic52(self):
        runFile(self, file="basic52.hhl",)

    def testBasic53(self):
        runFile(self, file="basic53.hhl",)

    def testBasic54(self):
        runFile(self, file="basic54.hhl",)

    def testBasic55(self):
        runFile(self, file="basic55.hhl",)
    
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
        runFile(self, file="nonlinear1.hhl")
    
    def testNonlinear2(self):
        runFile(self, file="nonlinear2.hhl")

    def testNonlinear3(self):
        runFile(self, file="nonlinear3.hhl")

    def testNonlinear4(self):
        runFile(self, file="nonlinear4.hhl",)

    def testNonlinear5(self):
        runFile(self, file="nonlinear5.hhl")

    def testNonlinear6(self):
        runFile(self, file="nonlinear6.hhl",)

    def testNonlinear7(self):
        runFile(self, file="nonlinear7.hhl")
    
    def testNonlinear8(self):
        runFile(self, file="nonlinear8.hhl",)

    def testNonlinear9(self):
        runFile(self, file="nonlinear9.hhl",)

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
        runFile(self, file="nonlinear11.hhl",)

    def testNonlinear12(self):
        runFile(self, file="nonlinear12.hhl")

    def testNonlinear13(self):
        runFile(self, file="nonlinear13.hhl")

    def testNonlinear14(self):
        runFile(self, file="nonlinear14.hhl")

    def testNonlinear15(self):
        runFile(self, file="nonlinear15.hhl")

    def testNonlinear16(self):
        runFile(self, file="nonlinear16.hhl")

    def testNonlinear17(self):
        runFile(self, file="nonlinear17.hhl")

    def testNonlinear18(self):
        runFile(self, file="nonlinear18.hhl")

    # TODO: Nonlinear benchmark, problem 19, 20. The ODE rule is not clear.

    def testNonlinear21(self):
        runFile(self, file="nonlinear21.hhl",)

    def testNonlinear22(self):
        runFile(self, file="nonlinear22.hhl")

    def testNonlinear23(self):
        runFile(self, file="nonlinear23.hhl")
                  
    # TODO: Nonlinear benchmark, problem 24. ODE rule not clear.

    def testNonlinear25(self):
        runFile(self, file="nonlinear25.hhl")

    def testNonlinear26(self):
        runFile(self, file="nonlinear26.hhl")

    def testNonlinear27(self):
        runFile(self, file="nonlinear27.hhl")

    def testNonlinear28(self):
        runFile(self, file="nonlinear28.hhl")

    def testNonlinear29(self):
        runFile(self, file="nonlinear29.hhl")

    def testNonlinear30(self):
        runFile(self, file="nonlinear30.hhl")

    def testNonlinear31(self):
        runFile(self, file="nonlinear31.hhl")

    def testNonlinear32(self):
        runFile(self, file="nonlinear32.hhl")

    def testNonlinear33(self):
        runFile(self, file="nonlinear33.hhl")

    def testNonlinear34(self):
        runFile(self, file="nonlinear34.hhl")

    def testNonlinear35(self):
        runFile(self, file="nonlinear35.hhl")

    def testNonlinear36(self):
        runFile(self, file="nonlinear36.hhl")

    def testNonlinear37(self):
        runFile(self, file="nonlinear37.hhl")

    def testNonlinear38(self):
        runFile(self, file="nonlinear38.hhl")

    def testNonlinear39(self):
        runFile(self, file="nonlinear39.hhl")

    def testNonlinear40(self):
        runFile(self, file="nonlinear40.hhl")

    def testNonlinear41(self):
        runFile(self, file="nonlinear41.hhl")

    def testNonlinear42(self):
        runFile(self, file="nonlinear42.hhl")

    def testNonlinear43(self):
        runFile(self, file="nonlinear43.hhl")

    def testNonlinear44(self):
        runFile(self, file="nonlinear44.hhl")

    def testNonlinear45(self):
        runFile(self, file="nonlinear45.hhl")

    def testNonlinear46(self):
        runFile(self, file="nonlinear46.hhl")

    def testNonlinear47(self):
        runFile(self, file="nonlinear47.hhl")

    def testNonlinear48(self):
        runFile(self, file="nonlinear48.hhl")

    def testNonlinear49(self):
        runFile(self, file="nonlinear49.hhl")

    def testNonlinear50(self):
        runFile(self, file="nonlinear50.hhl")

    def testNonlinear51(self):
        runFile(self, file="nonlinear51.hhl")

    def testNonlinear52(self):
        runFile(self, file="nonlinear52.hhl")

    def testNonlinear53(self):
        runFile(self, file="nonlinear53.hhl")

    # TODO: Problem 54, invariant unknown

    def testNonlinear55(self):
        runFile(self, file="nonlinear55.hhl")

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
        runFile(self, file="nonlinear58.hhl")

    def testNonlinear59(self):
        runFile(self, file="nonlinear59.hhl")

    def testNonlinear60(self):
        runFile(self, file="nonlinear60.hhl")

    # TODO: Nonlinear problem 61. Invariants unknown.

    def testNonlinear62(self):
        runFile(self, file="nonlinear62.hhl")

    def testNonlinear63(self):
        runFile(self, file="nonlinear63.hhl")

    def testNonlinear64(self):
        runFile(self, file="nonlinear64.hhl")

    # TODO: Nonlinear 65, 66, 67. Invariants unknown.

    def testNonlinear68(self):
        runFile(self, file="nonlinear68.hhl")

    def testNonlinear69(self):
        runFile(self, file="nonlinear69.hhl")

    # TODO: Nonlinear 70. Invariants unknown.

    def testNonlinear71(self):
        runFile(self, file="nonlinear71.hhl")

    def testNonlinear72(self):
        runFile(self, file="nonlinear72.hhl")

    def testNonlinear73(self):
        runFile(self, file="nonlinear73.hhl")

    def testNonlinear74(self):
        runFile(self, file="nonlinear74.hhl")

    def testNonlinear75(self):
        runFile(self, file="nonlinear75.hhl")

    def testNonlinear76(self):
        runFile(self, file="nonlinear76.hhl")

    def testNonlinear77(self):
        runFile(self, file="nonlinear77.hhl")

    # TODO: Nonlinear problem 78 is the same with problem 77.
    def testNonlinear78(self):
        runFile(self, file="nonlinear78.hhl")

    def testNonlinear79(self):
        runFile(self, file="nonlinear79.hhl")

    def testNonlinear80(self):
        runFile(self, file="nonlinear80.hhl")

    def testNonlinear81(self):
        runFile(self, file="nonlinear81.hhl")

    # TODO: Nonlinear problem 82, Proving invariant stuck.

    def testNonlinear83(self):
        runFile(self, file="nonlinear83.hhl")

    # TODO: Nonlinear problem 84, invariant not implied by precondition

    def testNonlinear85(self):
        runFile(self, file="nonlinear85.hhl")

    # TODO: Program 86 should also be proved by dbx automatically. 
    # But now it can only proved by dI or by offering the parameter g.
    def testNonlinear86(self):
        runFile(self, file="nonlinear86.hhl")

    def testNonlinear87(self):
        runFile(self, file="nonlinear87.hhl")

    def testNonlinear88(self):
        runFile(self, file="nonlinear88.hhl")
    
    def testNonlinear89(self):
        runFile(self, file="nonlinear89.hhl")

    def testNonlinear90(self):
        runFile(self, file="nonlinear90.hhl")

    # TODO: Nonlinear benchmark, problem 91. Invariants unknown.

    # TODO: Nonlinear benchmark, problem 92, 93, 94, 95. ODE rule unknown.

    def testNonlinear96(self):
        runFile(self, file="nonlinear96.hhl")

    def testNonlinear97(self):
        runFile(self, file="nonlinear97.hhl")

    # TODO:Nonlinear problem 98. How to define a function.
    def testNonlinear98(self):
        runFile(self, file="nonlinear98.hhl")

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
        runFile(self, file="nonlinear102.hhl")

    def testNonlinear103(self):
        runFile(self, file="nonlinear103.hhl")

    def testNonlinear104(self):
        runFile(self, file="nonlinear104.hhl")

    # TODO: Nonlinear problem 105, 106, 107. No tactic offered.

    # TODO: Nonlinear problem 108. Auto rule unknown. Too slow to give a result.

    def testNonlinear109(self):
        runFile(self, file="nonlinear109.hhl")

    # TODO: Nonlinear problem 110, 111. Definitions and no tactic.

    def testNonlinear112(self):
        runFile(self, file="nonlinear112.hhl")

    # TODO: Nonlinear problem 113. Definitions of constants value and no tactic.

    # TODO: Nonlinear problem 114, 115. No tactic and even inv->post is too slow to verify.

    # TODO: 
    # When not sure that ODE is executed or not, set invariant as true, 
    # because both cases should hold: 
    # Boundary of D -> Q and (P & !D) -> Q
    def testNonlinear116(self):
        runFile(self, file="nonlinear116.hhl")
                # #   diff_cuts={((), ()): ["x1+x2+x5 >= 0", "!(x2 < 0 & x1 < x2 & x5 < x2)"]},
                # #   darboux_rule={((), (0,)): "true"},
                #   diff_weakening_rule={((), ()): "true"})
        # I think this problem is different in hhl.

    # TODO: Nonlinear problem 117. No invariants offered.

    # I took out this test because it was too slow -- Alex
    # def testNonlinear118(self):
    #     runFile(self, file="nonlinear118.hhl",
    #               wolfram_engine=True)

    def testNonlinear119(self):
        runFile(self, file="nonlinear119.hhl")

    def testNonlinear120(self):
        runFile(self, file="nonlinear120.hhl")
    
    def testNonlinear121(self):
        runFile(self, file="nonlinear121.hhl")

    # TODO: Nonlinear problem 122, 123, 124. No invariants.

    # I took out this test because it was too slow -- Alex
    # def testNonlinear125(self):
    #     runFile(self, file="nonlinear125.hhl")

    def testNonlinear126(self):
        runFile(self, file="nonlinear126.hhl")

    def testNonlinear127(self):
        runFile(self, file="nonlinear127.hhl")

    # TODO: Nonlinear 128, 129, 130, 131, 132. No invariants.
    # 128: Automation in keymaera doesn't work.

    def testNonlinear133(self):
        runFile(self, file="nonlinear133.hhl")

    # TODO: Nonlinear 134. No tactic.

    def testNonlinear135(self):
        runFile(self, file="nonlinear135.hhl")

    # TODO: Nonlinear 136, 137, 138, 139, 140, 141. No tactics.

class SSHHLPyTest(unittest.TestCase):

    def testBouncing(self):
        runFile(self, file="simulink/sf_bouncing.hhl")

    def testSawtooth1(self):
        runFile(self, file="simulink/sf_sawtooth1.hhl")

    def testSawtooth2(self):
        runFile(self, file="simulink/sf_sawtooth2.hhl")

    def testDelay(self):
        runFile(self, file="simulink/sl_delay.hhl")


if __name__ == "__main__":
    unittest.main()

