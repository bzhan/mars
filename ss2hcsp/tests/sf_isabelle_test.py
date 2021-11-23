"""Unit test for sf_isabelle"""

import unittest

from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.sf.sf_state import Junction, OR_State, AND_State
from ss2hcsp.sf.sf_isabelle import translate_expr, translate_action, translate_actions, \
    translate_event, translate_trans, translate_state
from ss2hcsp.matlab import function
from ss2hcsp.matlab.parser import expr_parser, cond_parser, cmd_parser, event_parser


class SFIsabelleTest(unittest.TestCase):
    def testTranslateExpr(self):
        test_data = [
            ("0", "N 0"),
            ("x + 1", "Plus (V ''x'') (N 1)"),
        ]

        for e, res in test_data:
            e = expr_parser.parse(e)
            self.assertEqual(translate_expr(e), res)

    def testTranslateCond(self):
        test_data = [
            ("true", "Bc True"),
            ("false", "Bc False"),
            ("x > 10", "(V ''x'') [>] (N 10)"),
        ]

        for e, res in test_data:
            e = cond_parser.parse(e)
            self.assertEqual(translate_expr(e), res)

    def testTranslateHp(self):
        test_data = [
            ("x := 0", "x ::= N 0"),
            ("x := -1", "x ::= N -1"),
            ("x := x + 1", "x ::= Plus (V ''x'') (N 1)"),
        ]

        for c, res in test_data:
            c = cmd_parser.parse(c)
            self.assertEqual(translate_action(c), res)

    def testTranslateEvent(self):
        test_data = [
            ("e", "E e"),
        ]

        for event, res in test_data:
            event = event_parser.parse(event)
            self.assertEqual(translate_event(event), res)

    def testTranslate1(self):
        diagram = SL_Diagram(location="./Examples/Stateflow/translate/example1.xml")
        diagram.parse_xml()
        diagram.add_line_name()
        _, _, charts, _, _, _, _, _, _ = diagram.seperate_diagram()
        chart = charts[0]
        print(chart)

        for ssid, state in chart.all_states.items():
            if isinstance(state, OR_State):
                print(translate_state(ssid, chart))
            elif isinstance(state, AND_State):
                print("AND_State", state.name)
            elif isinstance(state, Junction):
                print("Junction", state.name)
                if state.out_trans:
                    for tran in state.out_trans:
                        print(tran)
                        print(translate_trans(tran, chart))


if __name__ == "__main__":
    unittest.main()
