import unittest
import json

from ss2hcsp.hcsp import parser

class HCSPTest(unittest.TestCase):
    def testCCS(self):
        with open("Examples\AADL\CCS\TCS\generatedcode\system.txt", "r") as f:
            text = f.read()
        try:
            if text.startswith('%type: module'):
                infos = parser.parse_module_file(text)
            else:
                infos = parser.parse_file(text)
        except parser.ParseFileException as e:
            print(e.error_msg)


if __name__ == "__main__":
    unittest.main()



