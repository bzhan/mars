import unittest
import os, json

from aadl2hcsp.xmlparser import Parser

class XMLParserTest(unittest.TestCase):
    def testXMLParser(self):
        #path = './Examples/AADL/air_conditioner/instances'
        #out_file = './Examples/AADL/air_conditioner/out.json'
        #ref_file = './Examples/AADL/air_conditioner/out_ref.json'

        path = './Examples/AADL/isolette'
        xmlfile = 'asd_isollete_impl_Instance.xml'
        aadl_file = 'asd.aadl'
        sim_file = './Examples/isolette/babybox.xml'

        out_file = './Examples/AADL/isolette/out2.json'
        ref_file = './Examples/AADL/isolette/out_ref.json'

        dic = Parser().parser(os.path.join(path, xmlfile), os.path.join(path, aadl_file), sim_file)


        with open(ref_file, 'r', encoding='utf-8') as ref:
            dic_ref = json.load(ref)

        with open(out_file, "w+", encoding='utf-8') as f_obj:
            json.dump(dic, f_obj, indent=4, sort_keys=True)

        self.assertEqual(dic, dic_ref)


if __name__ == "__main__":
    unittest.main()
