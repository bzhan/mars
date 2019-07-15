import unittest
import json

from aadl2hcsp.json2hcsp import *

class Json2HCSPTest(unittest.TestCase):
    def testJson2HCSP(self):
        file = 'aadl2hcsp/tests/out.json'
        out = ""
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
                out += "\n".join(str(line) for line in Thread(category).lines) + '\n'

        print(out)


if __name__ == "__main__":
    unittest.main()
