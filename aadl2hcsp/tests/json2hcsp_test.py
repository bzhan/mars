import unittest
import json

from aadl2hcsp.parserAnnex import AnnexParser
from aadl2hcsp import json2hcsp
from ss2hcsp.hcsp import parser
from ss2hcsp.hcsp.hcsp import HCSPProcess

class Json2HCSPTest(unittest.TestCase):
    def testJson2HCSP(self):
        json_file = './Examples/AADL/air_conditioner/out_ref.json'
        annex_file = './Examples/AADL/air_conditioner/air_conditioner.aadl'
        out_file = './Examples/AADL/air_conditioner/hcsp.txt'
        ref_file = './Examples/AADL/air_conditioner/hcsp_ref.txt'

        out = HCSPProcess()

        AP = AnnexParser()
        Annexs = AP.getAnnex(annex_file)
        Annex_HP = {}
        for th in Annexs.keys():
            Annex_HP[th] = AP.createHCSP(Annexs[th][1:-1])


        with open(json_file, 'r') as f:
            dic = json.load(f)

        out.extend(json2hcsp.createStructure(dic))
        out.extend(json2hcsp.createConnections(dic))

        for category in dic.values():
            if category['category'] == 'process' and len(category['components']) > 0:
                threadlines = []
                for com in category['components']:
                    if com['category'] == 'thread':
                        threadlines.append(com['name'])
                out.extend(json2hcsp.Process(category,threadlines).lines)

            elif category['category'] == 'thread':
                if category['name'] in Annex_HP.keys():
                    out.extend(json2hcsp.Thread(category, Annex_HP[category['name']]).lines)
                else:
                    out.extend(json2hcsp.Thread(category).lines)

        for _, hp in out.hps:
            hp_str = str(hp)
            print(hp_str)
            hp2 = parser.hp_parser.parse(hp_str)
            print(repr(hp))
            print(repr(hp2))
            self.assertEqual(hp, hp2)

        with open(out_file, 'w', encoding='utf-8') as f:
            f.write(str(out))

        with open(ref_file, 'r', encoding='utf-8') as f:
            ref = f.read()

        self.assertEqual(str(out), ref)


if __name__ == "__main__":
    unittest.main()
