# Unit test for json2hcsp

import unittest
import json

from aadl2hcsp.json2hcsp import translate_aadl_from_json

class Json2HCSPTest(unittest.TestCase):
    def testJson2HCSP(self):
        json_file = "./Examples/AADL/CCS/AADL/joint_model.json"
        with open(json_file, 'r') as f:
            jsoninfo = json.load(f)

        translate_aadl_from_json(jsoninfo, './Examples/AADL/CCS/TCS/generatedcode')


if __name__ == "__main__":
    unittest.main()
