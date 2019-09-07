import unittest
import json

from aadl2hcsp import json2hcsp
from ss2hcsp.hcsp import parser
from ss2hcsp.hcsp.hcsp import HCSPProcess

class Json2HCSPTest(unittest.TestCase):
    def testJson2HCSP(self):
        json_file = './Examples/AADL/air_conditioner/out_ref.json'
        annex_file = './Examples/AADL/air_conditioner/air_conditioner.aadl'
        out_file = './Examples/AADL/air_conditioner/hcsp.txt'
        ref_file = './Examples/AADL/air_conditioner/hcsp_ref.txt'

        out = json2hcsp.convert_AADL(json_file, annex_file)

        for _, hp in out.hps:
            hp_str = str(hp)
            hp2 = parser.hp_parser.parse(hp_str)
            self.assertEqual(hp, hp2)

        with open(out_file, 'w', encoding='utf-8') as f:
            f.write(str(out))

        with open(ref_file, 'r', encoding='utf-8') as f:
            ref = f.read()

        self.assertEqual(str(out), ref)


if __name__ == "__main__":
    unittest.main()
