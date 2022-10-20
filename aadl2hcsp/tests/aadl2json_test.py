
# Unit test for aadl2json

import unittest
import json

from aadl2hcsp.aadl2json import convert_AADL, CompactJSONEncoder


class AADL2JsonTest(unittest.TestCase):
    def testCCS(self):
        directory = "Examples\AADL\CCS\AADL"
        startfile = "joint_model.aadl"
        configfile = "config.json"
        info = convert_AADL(directory, startfile, configfile)

        with open("Examples\AADL\CCS\AADL\joint_model_ref.json", "r") as f:
            infos_ref = json.load(f)
        
        self.assertEqual(info, infos_ref)
        output_path = "Examples\AADL\CCS\AADL\joint_model.json"
        f = open(output_path, "w")
        f.write(json.dumps(info, separators=(',', ': '), indent=4, cls=CompactJSONEncoder))
        f.close()


if __name__ == "__main__":
    unittest.main()
