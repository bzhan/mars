"""Unit test for hhlpy."""

import unittest
import os
from wolframclient.evaluation import WolframLanguageSession

from ss2hcsp.hcsp import expr
from ss2hcsp.hcsp.hcsp import HCSP, Function
from ss2hcsp.hcsp.parser import parse_expr_with_meta, parse_expr_with_meta, parse_hp_with_meta, \
    parse_hoare_triple_with_meta
from hhlpy.hhlpy import CmdVerifier
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
                "categ:", vc.categ,
                "blabel:", str(vc.blabel),
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
            vcs = [parse_expr_with_meta(vc) for vc in vcs]
            assert pos in verifier.infos, "pos {} is not in infos.".format(pos)
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
        self.assertEqual(str(res.pre[0].expr), "x >= 0")
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
                  expected_vcs={((0,), ()): ["x >= 0 -> x + 1 >= 0"]})

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
    #     runVerify(self, pre="true", hp="<x_dot = 2 & x < 10>", post="true", print_vcs=False)

    def testVerify7_2(self):
        runFile(self, file="test7_2.hhl",
                  print_vcs=False)

    def testVerify8(self):
        runFile(self, file="test8.hhl",
                  print_vcs=False)

    def testVerify11(self):
        runFile(self, file="test11.hhl",
                  expected_vcs={((), ()): ["x1 >= 0 -> x1 >= 0 -> x2 >= 1 -> x2 >= 1"]})

    def testVerify12(self):
        runFile(self, file="test12.hhl",
                  expected_vcs={((), ()): ["x >= 0 -> y1 >= x + 1 -> y1 >= 1"]})

    def testVerify13(self):
        runFile(self, file="test13.hhl",
                  expected_vcs={((), ()): ["x >= 0 -> y2 >= x + 1 ->y1 >= x + 1 + 1 -> y1 >= 2"]})

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

    def testVerify65_1(self):
        runFile(self, file="test65_1.hhl",)

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
                                ((1, 0), ()): ["x >= 1 -> x + 1 >= 1"]})

    def testBasic4(self):
        runFile(self, file="basic4.hhl",)

    def testBasic5(self):
        runFile(self, file="basic5.hhl",
                  expected_vcs={((), ()): ["x >= 0 -> x1 >= 1 -> x1 >= 1"]})

    # TODO: Basic benchmark problem 6 is hard to translate into HCSP program.

    def testBasic7(self):
        runFile(self, file="basic7.hhl") 

    def testBasic8(self):
        runFile(self, file="basic8.hhl")

    def testBasic9(self):
        runFile(self, file="basic9.hhl", print_vcs=False)
    
    def testBasic10(self):
        runFile(self, file="basic10.hhl",
                  print_vcs=False)

    def testBasic11(self):
        runFile(self, file="basic11.hhl",)

    def testBasic12(self):
        runFile(self, file="basic12.hhl",
                  expected_vcs={((), ()): ["y >= 0 -> x >= 0 && y >= 0 -> t1 >= 0 -> t1 > 0 -> y >= 0",
                                           "y >= 0 -> x >= 0 && y >= 0 -> t1 >= 0 -> t1 > 0 -> x >= 0",
                                           "y >= 0 -> x >= 0 && y >= 0 -> t1 >= 0 -> t1 <= 0 -> x >= 0"]})

    def testBasic13(self):
        runFile(self, file="basic13.hhl",)


    def testBasic14(self):
        runFile(self, file="basic14.hhl",)

    def testBasic15(self):
        runFile(self, file="basic15.hhl", 
                expected_vcs={((), ()): ["x > 0 -> t1 >= 0 -> t1 > 0 -> (\exists y. x * y * y == 1)", \
                                         "x > 0 -> t1 >= 0 -> t1 <= 0 -> x > 0"],
                              ((1,), ()): ["x * y * y == 1 && t == 0 -> x > 0"],
                              ((1,), (0,)): ["t >= 0 -> x * y * (y / 2) + (x * (y / 2) + -x * y) * y == 0"]})

    def testBasic16(self):
        runFile(self, file="basic16.hhl",)

    def testBasic17(self):
        runFile(self, file="basic17.hhl", print_vcs=False,
                expected_vcs={((), ()): ["y > 0 -> x > 0 && y > 0 -> t1 >= 0 -> t1 > 0 -> (\exists z. x * z * z == 1)",
                                         "y > 0 -> x > 0 && y > 0 -> t1 >= 0 -> t1 <= 0 -> x > 0"],
                              ((1,), ()): ["y > 0 -> x * z * z == 1 && t == 0 -> x > 0"],
                              ((1,), (0,)): ["y > 0 -> t >= 0 -> x * z * (y * z / 2) + (x * (y * z / 2) + -y * x * z) * z == 0"]})

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
                                ((), (0,)): ["z == -2 -> y >= 0 -> y >= 0"] 
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
    
    # TODO: 48 is very slow.(But fast on interface)
    def testBasic48(self):
        runFile(self, file="basic48.hhl")

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
    
    # TODO: Does this example correspond to problem 57 in basic benchmark?
    def testBasic57(self):
        runFile(self, file="basic57.hhl")

    # TODO: Does this example correspond to problem 60 in basic benchmark?
    def testBasic60(self):
        runFile(self, file="basic60.hhl")
    
    # TODO: Basic benchmark, problem 56, 58 - 60, cannot be written into hcsp program.

    # TODO: Proofs or invariants Unknown
    # def testOscillator(self):
    #     runFile(self, file="oscillator.hhl",)


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

    def testNonlinear10(self):
        runFile(self, file="nonlinear10.hhl",)
    
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

    # TODO: Nonlinear benchmark, problem 19. The ODE rule is not clear.

    def testNonlinear20(self):
        runFile(self, file="nonlinear20.hhl")

    def testNonlinear21(self):
        runFile(self, file="nonlinear21.hhl",)

    def testNonlinear22(self):
        runFile(self, file="nonlinear22.hhl")

    def testNonlinear23(self):
        runFile(self, file="nonlinear23.hhl")

    def testNonlinear24(self):
        runFile(self, file="nonlinear24.hhl")

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

    # TODO: ODE rule is not clear
    # def testNonlinear56(self):
    #     runFile(self, file="nonlinear56.hhl")
    # pre [-3 <= x][x <= -2][-3 <= y][y <= -2];

    # t := *(t >= 0);
    # {x_dot = 4 + 21*x - 7*y + 42*x^2 - 24*x*y + 4*y^2 + 27*x^3 - 9*x^2*y + 6*x^4,
    # y_dot = 12 + 71*x -21*y + 150*x^2 -80*x*y + 12*y^2 + 99*x^3 - 39*x^2*y + 2*x*y^2 + 18*x^4,
    # t_dot = -1 & t > 0}
    #     invariant
    #     [3+x>=0] {dbx}
    #     [3+y>=0] {dbx}
    #     [4+3*x*(1+x)*(7+x*(7+2*x))+4*y^2>(7+3*x*(8+3*x))*y]{?}
    #     [1+x*(3+x)>y] {dbx}
    #     [1+3*x*(2+x)>2*y] {dbx}
    #     [2+3*x < y] {dbx}
    #     [x < 0]{bc}
    #     [y < 0]{bc};

    # post [!(x >= 0 || y >= 0)];

    # TODO: Problem 57. Invariant not known.

    def testNonlinear58(self):
        runFile(self, file="nonlinear58.hhl")

    def testNonlinear59(self):
        runFile(self, file="nonlinear59.hhl")

    def testNonlinear60(self):
        runFile(self, file="nonlinear60.hhl")

     # TODO: Nonlinear problem 61. Invariants unknown.
    # def testNonlinear61(self):
    #     runFile(self, file="nonlinear61.hhl")
    # pre [y >= 2.5 || x >= 0];
    #     {x_dot = 6*x^2 - 6*x*y + 4*y^2 + 3*x^3 - 9*x^2*y + 6*x^4,
    #     y_dot = -6*x*y + 10*y^2 + 27*x^3 - 39*x^2 + 2*x*y^2 + 18*x^4,
    #     t_dot = 1 & t < 5}
    # post [(x + 3)^2 + (y + 2)^2 > 3];

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

    def testNonlinear92(self):
        runFile(self, file="nonlinear92.hhl")

    def testNonlinear93(self):
        runFile(self, file="nonlinear93.hhl")

    def testNonlinear94(self):
        runFile(self, file="nonlinear94.hhl")

    def testNonlinear95(self):
        runFile(self, file="nonlinear95.hhl")

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
    #     runFile(self, file="nonlinear100.hhl")
    #     # Nonlinear benchmark, problem 100
    #     pre [x1 == 1/20] [x2 == 1/32] [sint==0] [cost==1]; /* t==0 initially */
        #     t := 0;
        #     {x1_dot=x2, x2_dot=-x2-(2+sint)*x1, sint_dot=cost, cost_dot=-sint,
        #     t_dot = 1 & t < 10}
        #     invariant [cost^2+sint^2>=1]
        #             [cost^2+sint^2<=100000/99999]
        #             [98*x1^2 + 24*x1*x2 + 24*x2*x1 + 55*x2^2 < 1]{dbx};
        # post [98*x1^2 + 24*x1*x2 + 24*x2*x1 + 55*x2^2 < 1];

    # TODO: Nonlinear problem 101. No tactic. Post not implied by inv.

    def testNonlinear102(self):
        runFile(self, file="nonlinear102.hhl")

    def testNonlinear103(self):
        runFile(self, file="nonlinear103.hhl")

    def testNonlinear104(self):
        runFile(self, file="nonlinear104.hhl")

    # TODO: Nonlinear problem 105, 106, 107. No tactic offered.

    # TODO: Nonlinear problem 108. Auto rule unknown. Too slow to give a result.
    # def testNonlinear108(self):
    #     runFile(self, file="nonlinear108.hhl")
    # pre [-1.6<=x1][x1<=1.6][-1.6<=x2][x2<=1.6][-1.6<=x3][x3<=1.6][-1.6<=x4][x4<=1.6]
    # [u1==0.9][u2==0.7][u3==1.5][u4==1][u5==1][u6==1.5][u7==1][u8==1.1];

    # {x1_dot=u1*x2-x3-x4+(u2-x1^2-x2^2-x3^2-x4^2)*x1,
    #     x2_dot=-x1+u3*x3-x4+(u4-x1^2-x2^2-x3^2-x4^2)*x2,
    #     x3_dot=x1-x2+u5*x4+(u6-x1^2-x2^2-x3^2-x4^2)*x3,
    #     x4_dot=x1+u7*x2-x3+(u8-x1^2-x2^2-x3^2-x4^2)*x4 &
    #     -2<x1 && x1<2 && -2<x2 && x2<2 && -2<x3 && x3<2 && -2<x4 && x4<2}
    #     invariant [8.2997-0.18912*x1-0.19551*x2-0.19371*x3-0.18707*x4-0.37075*x1^2
    #     -0.37215*x2^2-0.37283*x3^2-0.37155*x4^2-0.14238*x1*x2-0.14189*x1*x3
    #     -0.14254*x2*x3-0.14137*x1*x4-0.14203*x2*x4-0.14327*x3*x4>=0]{bc}{{init:wolfram, maintain: wolfram}};

    # post [!(1.8<=x1&&x1<=2 && 1.8<=x2&&x2<=2 && 1.8<=x3&&x3<=2 && 1.8<=x4&&x4<=2)]{{exec: wolfram}};

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
    # 132: our tool cannot find g by auto, but keymaerax can. We don't know what g is.
    # ArchiveEntry "Benchmarks/Nonlinear/Product of Dumortier Llibre Artes Ex. 1_11a and ZYLZCL Example C4"

    # pre [xleft > -1/2][xleft < -1/3][yleft < 0][yleft >= -1/2][-1 <= x1right][x1right <= 0][-1 <= x2right][x2right <= 0];

    # {xleft_dot=2*xleft-xleft^5-xleft*yleft^4,
    # yleft_dot=yleft-xleft^2*yleft-yleft^3,
    # x1right_dot=-1+x1right^2+x2right^2,
    # x2right_dot=5*(-1+x1right*x2right) &-2 < x1right && x1right<2 && -2<x2right && x2right<2}
    # invariant [xleft < 0]{dbx}
    #         [yleft < 0]{dbx}
    #         [22667*x1right^2+x2right*(257910+6221*x2right)+x1right*(141840+15973*x2right) < 42786]{dbx};

    # post [!xleft+yleft > 0][!(1 <= x1right && x1right<=2 && 1<=x2right && x2right<=2)];

    def testNonlinear133(self):
        runFile(self, file="nonlinear133.hhl")

    # TODO: Nonlinear 134. No tactic.

    def testNonlinear135(self):
        runFile(self, file="nonlinear135.hhl")

    # TODO: Nonlinear 136, 137, 138, 139, 140. No tactics.

    def testNonlinear141(self):
        runFile(self, file="nonlinear141.hhl")

class SSHHLPyTest(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        try:
            session.start()
        except Exception as e:
            session.start()

    @classmethod
    def tearDownClass(cls):
        session.terminate()

    def testBouncing(self):
        runFile(self, file="simulink/sf_bouncing.hhl")

    def testSawtooth1(self):
        runFile(self, file="simulink/sf_sawtooth1.hhl")

    def testSawtooth2(self):
        runFile(self, file="simulink/sf_sawtooth2.hhl")

    def testSawtooth3(self):
        runFile(self, file="simulink/sf_sawtooth3.hhl")

    def testDelay(self):
        runFile(self, file="simulink/sl_delay.hhl")

    def testPIcontrol(self):
        runFile(self, file="simulink/PIcontrol.hhl")


class AdvancedHHLPyTest(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        try:
            session.start()
        except Exception as e:
            session.start()

    @classmethod
    def tearDownClass(cls):
        session.terminate()

    def testAdvanced1(self):
        runFile(self, file="advanced1.hhl",)


if __name__ == "__main__":
    unittest.main()

