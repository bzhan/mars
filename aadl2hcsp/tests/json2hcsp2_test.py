# Unit test for json2hcsp2

import unittest
import json

from aadl2hcsp import json2hcsp2
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import pprint

class Json2HCSP2Test(unittest.TestCase):
    def testJson2HCSP2(self):
        json_file = "./Examples/AADL/CCS/out.json"
        with open(json_file, 'r') as f:
            dic = json.load(f)

        mods = []
        for name, content in dic.items():
            if content['category'] == 'thread':
                mod = json2hcsp2.translate_thread(name, content)
                mods.append(mod)
            elif content['category'] == 'device':
                mod = json2hcsp2.translate_device(name, content)
                mods.append(mod)
            elif content['category'] == 'abstract':
                mod = json2hcsp2.translate_abstract(name, content)
                mods.append(mod)
            else:
                raise NotImplementedError

        for mod in mods:
            print(mod.export())
            print()

        json2hcsp2.translate_model(dic)


if __name__ == "__main__":
    unittest.main()
