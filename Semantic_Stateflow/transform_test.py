#coding:utf-8
import json
import os
import traceback
import unittest

from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.sf.sf_isabelle import translate_junction_function, dfs_search_chart, \
    translate_fe_info, translate_ge_info


file = []
dir = []
dir_res = []
give_path = 'Semantic_Stateflow/example_xml'

def list_dir(start_dir):
    dir_res = os.listdir(start_dir)
    for path in dir_res:
        temp_path = start_dir + '/' + path
        if os.path.isfile(temp_path):
            file.append(temp_path)
        if os.path.isdir(temp_path):
            dir.append(temp_path)
            list_dir(temp_path)
'''
class TransformAllExamples(unittest.TestCase):

    def TransformExamples(self):
        print("here")
        try:
            list_dir(give_path)
            print("file：", file)
            print("dir：", dir)
        except Exception as e:
            print(traceback.format_exc(), flush=True)

if __name__ == "__main__":
    suite = unittest.TestSuite()
    suite.addTest(TransformAllExamples('TransformExamples'))
    suite =  unittest.TestLoader().loadTestsFromTestCase(TransformAllExamples)
    unittest.TextTestRunner(verbosity=1).run(suite)
'''
class TransformAllExamples(unittest.TestCase):
    def testTransformExamples1(self):
        print("here")
        try:
            list_dir(give_path)
            #print("file：", file)
            #print("dir：", dir)
            for f in file:
                filename = str(f)
                #print(filename)
                if filename.endswith('.xml'):
                    if (filename == "Semantic_Stateflow/example_xml/WashMachine/WashMachine.xml" or
                       filename == "Semantic_Stateflow/example_xml/Transitions/InnerTransitiontoHistoryJunction.xml" or
                       filename == "Semantic_Stateflow/example_xml/Transitions/LabeledDefaultTransition.xml"):
                        continue    #These three example has a feature that cannot be tranformed so that we transformed it manually
                    
                    n = 2
                    input_enent = "[\'\'\'\', \'\'\'\']"
                    output_str = ""
                    try:
                        jsonname = filename.split('.')[0] + '.json'
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
                        print(jsonname)
                    diagram = SL_Diagram(location=filename)
                    diagram.parse_xml()
                    diagram.add_line_name()
                    charts = [block for block in diagram.blocks_dict.values() if block.type == "stateflow"]
                    chart = charts[0]
                    #print(chart)
                    #print('\n')
                    save_name  = filename.split('/')[-1].split('.')[0]
                    content = 'theory %s\n  imports "../Final_ML" \nbegin\n\n' %save_name
                    chart_str, def_list = dfs_search_chart(chart.diagram.ssid, chart, '', [])
                    content += chart_str
                    #print(chart_str)

                    junc_str = translate_junction_function(chart)
                    #print(junc_str)
                    content += junc_str + '\n\n'
                    def_list.append('g_def')

                    v_str = 'definition v :: vals where \" v = Vals (λstr. 0) (λp str. 0) (λp. 0) (λx. []) ([],[]) \"\n'
                    content += v_str + '\n'
                    def_list.append('v_def')
                    
                    #chart_str = translate_chart_info(chart)
                    chart_str = 'definition I :: ctxt where \n\"I str = (Info False [] [])\"'
                    content += chart_str + '\n'
                    #print(content)
                    def_list.append('I_def')

                    #fe and ge
                    fe_str = 'definition fe::fenv where \" ' + '\n'
                    fe_str += translate_fe_info(chart)

                    #print(fe_str)
                    content += fe_str + '\n'
                    def_list.append('fe_def')

                    ge_str = 'definition ge::genv where \" ' + '\n'
                    ge_str += translate_ge_info(chart)

                    #print(ge_str)
                    content += ge_str + '\n'
                    def_list.append('ge_def')

                    env_str = 'definition env::env where \"env = Env Root fe ge g\" ' + '\n'
                    content += env_str
                    def_list.append('env_def')

                    status_str = 'definition s::status where \" s = Status v I\" ' + '\n'
                    content += status_str
                    def_list.append('s_def')

                    content += 'text\<open>EXECUTION PROOF\<close>\n'

                    #note that the default n is 2
                    #content += 'schematic_goal \"Root_Exec_for_times env \'\'\'\' (%s::int) s ?s\"\n' %'2'
                    content += 'schematic_goal \"Root_Exec_for_times env %s (%s::int) s' %(input_enent, n)
                    if output_str == "":
                        content += ' ?s\"\n'
                    else:
                        content += '\n (Status (Vals ?v1 ?v2 ?v3 ?v4 (%s, ?o2)) (?I))\"\n' %output_str

                    content += '  unfolding '
                    cnt = len('  unfolding ')
                    for mydef in def_list:
                        content += mydef + ' '
                        cnt += len(mydef) + 1
                        if(cnt > 80):
                            content += '\n'
                            cnt = 0
                    content += '\n  by stateflow_execution2\n\n'
                    content += 'end'
                    content = content.replace("-", "_")
                    content = content.replace("(_", "(-")
                    #print(content)
                    save_name = "Semantic_Stateflow/all_examples/" + save_name + '.thy'
                    if os.path.exists("Semantic_Stateflow/all_examples/") == False:
                        os.makedirs("Semantic_Stateflow/all_examples/")
                    f = open(save_name, 'w')
                    f.write(content)
                    f.close()

        except Exception as e:
            print(traceback.format_exc(), flush=True)

if __name__ == "__main__":
    suite = unittest.TestSuite()
    test_cases = [TransformAllExamples('testTransformExamples1')]
    suite.addTests(test_cases)
    #suite.addTest(TransformAllExamples('TransformExamplesHp'))
    unittest.TextTestRunner(verbosity=1).run(suite)

