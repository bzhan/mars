import unittest
import os, json

from aadl2hcsp.xmlparser import Parser

class XMLParserTest(unittest.TestCase):
    def testXMLParser(self):
        #path = './Examples/AADL/air_conditioner/instances'
        #out_file = './Examples/AADL/air_conditioner/out.json'
        #ref_file = './Examples/AADL/air_conditioner/out_ref.json'

        path = './Examples/AADL/scheduler'
        xmlfile = 'scheduler_s_i_Instance.xml'
        aadl_file = 'scheduler.aadl'
        # sim_file = './Examples/isolette/babybox.xml'
        sim_file = './Examples/AADL/CCS/Simulink/emerg_imp.xml'

        out_file = os.path.join(path, 'out.json')
        ref_file = os.path.join(path, 'out_ref.json')

        dic = Parser().parser(os.path.join(path, xmlfile), os.path.join(path, aadl_file), sim_file)


       # with open(ref_file, 'r', encoding='utf-8') as ref:
       #     dic_ref = json.load(ref)

        with open(out_file, "w+", encoding='utf-8') as f_obj:
            json.dump(dic, f_obj, indent=4, sort_keys=True)

        #self.assertEqual(dic, dic_ref)


if __name__ == "__main__":
    unittest.main()
