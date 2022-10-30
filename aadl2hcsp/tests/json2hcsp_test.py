# Unit test for json2hcsp

import unittest
import json

from aadl2hcsp.json2hcsp import translate_aadl_from_json
from ss2hcsp.hcsp.hcsp import convert_infos_to_concrete_chs, has_all_concrete_chs
from ss2hcsp.hcsp import parser
from ss2hcsp.hcsp.pprint import pprint
from ss2hcsp.hcsp.module import HCSPDeclarations, HCSPModule, HCSPModuleInst, HCSPSystem

class Json2HCSPTest(unittest.TestCase):
    def testJson2HCSP(self):
        json_file = "./Examples/AADL/CCS/AADL/joint_model.json"
        with open(json_file, 'r') as f:
            jsoninfo = json.load(f)

        translate_aadl_from_json(jsoninfo, './Examples/AADL/CCS/TCS/generatedcode')

    def testConvertToConcreteChs(self):
        with open("./Examples/AADL/CCS/TCS/generatedcode/system.txt", 'r') as f:
            text = f.read()

        infos = parser.parse_module_file(text)
        infos2 = convert_infos_to_concrete_chs(infos)
        assert has_all_concrete_chs(infos2)

        modules = []
        module_insts = []
        for info in infos2:
            modules.append(HCSPModule(info.name, info.hp, outputs=info.outputs, procedures=info.procedures))
            module_insts.append(HCSPModuleInst(info.name, info.name))

        decls = HCSPDeclarations(modules + [HCSPSystem(module_insts)])
        with open("./Examples/AADL/CCS/TCS/generatedcode/systemv2.txt", 'w') as f:
            f.write(decls.export())

if __name__ == "__main__":
    unittest.main()
