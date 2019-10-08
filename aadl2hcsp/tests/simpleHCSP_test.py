import unittest
import json

from aadl2hcsp import simple_hcsp
from ss2hcsp.hcsp import parser

class Json2simHCSPTest(unittest.TestCase):
    def testJson2simHCSP(self):
        #json_file = './Examples/AADL/air_conditioner/out_ref.json'
        #annex_file = './Examples/AADL/air_conditioner/air_conditioner.aadl'
        #out_file = './Examples/AADL/air_conditioner/hcsp.txt'
        #ref_file = './Examples/AADL/air_conditioner/hcsp_ref.txt'

        json_file = './Examples/AADL/isolette/out_ref.json'
        annex_file = './Examples/AADL/isolette/asd.aadl'
        out_file = './Examples/AADL/isolette/hcsp2.txt'

        out = simple_hcsp.convert_AADL(json_file, annex_file)

        for _, hp in out.hps:
            hp_str = str(hp)
            hp2 = parser.hp_parser.parse(hp_str)
            self.assertEqual(hp, hp2)

        with open(out_file, 'w', encoding='utf-8') as f:
            f.write(str(out))


if __name__ == "__main__":
    unittest.main()