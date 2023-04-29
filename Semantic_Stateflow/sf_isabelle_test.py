"""Unit test for sf_isabelle"""

import unittest
import json

from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.sf.sf_state import Junction, OR_State, AND_State
from ss2hcsp.sf.sf_isabelle import translate_composition, translate_expr, translate_action, translate_actions, \
    translate_event, translate_trans, translate_state, translate_junction_function, dfs_search_chart, \
    translate_chart_info, translate_fe_info, translate_ge_info
from ss2hcsp.matlab import function
from ss2hcsp.matlab.parser import expr_parser, cond_parser, cmd_parser, event_parser


class SFIsabelleTest(unittest.TestCase):
    def testTranslate1(self):
        #Inputs: Stateflow XML file
        filename = "Semantic_Stateflow/test3.xml"
        n = 2
        input_enent = "[\'\'\'\', \'\'\'\']"
        output_str = ""
        try:
            #Inputs: Stateflow Json file
            jsonname  = "./Semantic_Stateflow/test3.json"
            with open(jsonname,'r',encoding='utf8')as fp:
                json_data = json.load(fp)
                for key in json_data.keys():
                    if key == "output1":
                        output_str = json_data['output1']
                    elif key == 'n':
                        n = json_data['n']
                    elif key == 'Event Sequence':
                        input_enent = json_data['Event Sequence']
        except:
            pass
        
        diagram = SL_Diagram(location=filename)
        diagram.parse_xml()
        diagram.add_line_name()
        charts = [block for block in diagram.blocks_dict.values() if block.type == "stateflow"]
        chart = charts[0]
        print(chart)
        print('\n')
        save_name  = filename.split('/')[-1].split('.')[0]
        str = 'theory %s\n  imports Final_ML \nbegin\n\n' %save_name
        chart_str, def_list = dfs_search_chart(chart.diagram.ssid, chart, '', [])
        str += chart_str
        #print(chart_str)

        junc_str = translate_junction_function(chart)
        str += junc_str + '\n\n'
        def_list.append('g_def')

        v_str = 'definition v :: vals where \" v = Vals (λstr. 0) (λp str. 0) (λp. 0) (λx. []) ([],[]) \"\n'
        str += v_str + '\n'
        def_list.append('v_def')
        
        #chart_str = translate_chart_info(chart)
        chart_str = 'definition I :: ctxt where \n\"I str = (Info False [] [])\"'
        str += chart_str + '\n'

        def_list.append('I_def')

        #fe and ge
        fe_str = 'definition fe::fenv where \" ' + '\n'
        fe_str += translate_fe_info(chart)

        str += fe_str + '\n'
        def_list.append('fe_def')

        ge_str = 'definition ge::genv where \" ' + '\n'
        ge_str += translate_ge_info(chart)

        print(ge_str)
        str += ge_str + '\n'
        def_list.append('ge_def')

        env_str = 'definition env::env where \"env = Env Root fe ge g\" ' + '\n'
        str += env_str
        def_list.append('env_def')

        status_str = 'definition s::status where \" s = Status v I\" ' + '\n'
        str += status_str
        def_list.append('s_def')

        str += 'text\<open>EXECUTION PROOF\<close>\n'


        str += 'schematic_goal \"Root_Exec_for_times env %s (%s::int) s' %(input_enent, n)
        if output_str == "":
            str += ' ?s\"\n'
        else:
            str += '\n (Status (Vals ?v1 ?v2 ?v3 ?v4 (%s, ?o2)) (?I))\"\n' %output_str
        str += '  unfolding '
        cnt = len('  unfolding ')
        for mydef in def_list:
            str += mydef + ' '
            cnt += len(mydef) + 1
            if(cnt > 80):
                str += '\n'
                cnt = 0
        #str += '\n  apply simp'
        str += '\n  by stateflow_execution2\n\n'
        str += 'end'
        str = str.replace("-", "_")
        str = str.replace("(_", "(-")
        print(str)
        save_name = "Semantic_Stateflow/" + save_name + '.thy'
        f = open(save_name, 'w')
        f.write(str)
        f.close()

if __name__ == "__main__":
    suite = unittest.TestSuite()
    suite.addTest(SFIsabelleTest('testTranslateHp'))

    #suite =  unittest.TestLoader().loadTestsFromTestCase(SFIsabelleTest)
    unittest.TextTestRunner(verbosity=1).run(suite)
