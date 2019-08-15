import unittest
import json

from aadl2hcsp.parserAnnex import *
from aadl2hcsp.json2hcsp import *

class Json2HCSPTest(unittest.TestCase):
    def testJson2HCSP(self):
        file = 'aadl2hcsp/tests/out.json'
        annex_file = 'air_conditioner/air_conditioner.aadl'
        out = ""

        AP = AnnexParser()
        Annexs = AP.getAnnex(annex_file)
        Annex_HP = {}
        for th in Annexs.keys():
            Annex_HP[th] = AP.createHCSP(Annexs[th][1:-1])


        with open(file, 'r') as f:
            dic = json.load(f)
        out += "\n".join(str(line) for line in createStructure(dic)) + '\n'
        out += "\n".join(str(line) for line in createConnections(dic)) + '\n'

        for category in dic.values():
            if category['category'] == 'process' and len(category['components']) > 0:
                threadlines = []
                for com in category['components']:
                    if com['category'] == 'thread':
                        threadlines.append(com['name'])
                out += "\n".join(str(line) for line in Process(category,threadlines).lines) + '\n'

            elif category['category'] == 'thread':
                if category['name'] in Annex_HP.keys():
                    out += "\n".join(str(line) for line in Thread(category, Annex_HP[category['name']]).lines) + '\n'
                else:
                    out += "\n".join(str(line) for line in Thread(category).lines) + '\n'

        print(out)


if __name__ == "__main__":
    unittest.main()
