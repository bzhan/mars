import unittest
import os, json

from aadl2hcsp.xmlparser import parser, aadlparser

class XMLParserTest(unittest.TestCase):
    def testXMLParser(self):
        #path = './Examples/AADL/air_conditioner/instances'
        #out_file = './Examples/AADL/air_conditioner/out.json'
        #ref_file = './Examples/AADL/air_conditioner/out_ref.json'

        path = './Examples/AADL/isolette/instances'
        aadl_file = './Examples/AADL/isolette/asd.aadl'
        out_file = './Examples/AADL/isolette/out.json'
        ref_file = './Examples/AADL/isolette/out_ref.json'

        dic = {}
        for xmlfile in os.listdir(path):
            parser(os.path.join(path, xmlfile), dic, protocol="Periodic")

        aadlparser(aadl_file, dic)

        with open(ref_file, 'r', encoding='utf-8') as ref:
            dic_ref = json.load(ref)

        with open(out_file, "w+", encoding='utf-8') as f_obj:
            json.dump(dic, f_obj, indent=4, sort_keys=True)

        self.assertEqual(dic, dic_ref)


if __name__ == "__main__":
    unittest.main()
