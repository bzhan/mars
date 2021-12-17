"""Unit test for sf_isabelle"""

import unittest

from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.sf.sf_state import Junction, OR_State, AND_State
from ss2hcsp.sf.sf_isabelle import translate_composition, translate_expr, translate_action, translate_actions, \
    translate_event, translate_trans, translate_state, translate_junction_function, dfs_search_chart, \
    translate_chart_info
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
            ("x = 0", "\'\'x\'\' ::= N 0"),
            ("x = -1", "\'\'x\'\' ::= N (-1)"),
            ("x = x + 1", "\'\'x\'\' ::= Plus (V ''x'') (N 1)"),
        ]

        for c, res in test_data:
            c = cmd_parser.parse(c)
            self.assertEqual(translate_action(c), res)

    def testTranslateEvent(self):
        test_data = [
            ("e", "S [\'\'e\'\']"),
        ]

        for event, res in test_data:
            event = event_parser.parse(event)
            self.assertEqual(translate_event(event), res)

    #unittest.skip("skip")
    def testTranslate1(self):
        filename = "./Examples/Stateflow/translate/Trans_State2State.xml"
        diagram = SL_Diagram(location=filename)
        diagram.parse_xml()
        diagram.add_line_name()
        _, _, charts, _, _, _, _, _, _ = diagram.seperate_diagram()
        chart = charts[0]
        print(chart)
        print('\n')
        save_name  = filename.split('/')[-1].split('.')[0]
        str = 'theory %s\n  imports Send_Total_ML \nbegin\n\n' %save_name
        chart_str, def_list = dfs_search_chart(chart.diagram.ssid, chart, '', [])
        str += chart_str
        #print(chart_str)

        junc_str = translate_junction_function(chart)
        str += junc_str + '\n\n'
        def_list.append('g_def')

        v_str = 'definition v :: vals where \" v = Vals (λstr. 0) (λp str. 0) (λp. 0) ([],[]) \"\n'
        str += v_str + '\n'
        def_list.append('v_def')
        
        chart_str = translate_chart_info(chart)

        str += chart_str + '\n'
        #print(str)
        def_list.append('Chart_def')

        str += 'text‹EXECUTION PROOF›\n'

        str += 'schematic_goal \"root_execution_for_times Root \'\'\'\' (%s::int) Chart v g ?Chart2 ?v2\"\n' %'2'

        str += '  unfolding '
        cnt = len('  unfolding ')
        for mydef in def_list:
            str += mydef + ' '
            cnt += len(mydef) + 1
            if(cnt > 80):
                str += '\n'
                cnt = 0
        str += '\n  apply simp\n'
        str += '  by stateflow_execution2\n\n'
        str += 'end'
        str = str.replace("-", "_")
        str = str.replace("(_", "(-")
        print(str)
        save_name += '.thy'
        f = open(save_name, 'w')
        f.write(str)
        f.close()

if __name__ == "__main__":
    suite = unittest.TestSuite()
    suite.addTest(SFIsabelleTest('testTranslateHp'))

    #suite =  unittest.TestLoader().loadTestsFromTestCase(SFIsabelleTest)
    unittest.TextTestRunner(verbosity=1).run(suite)
