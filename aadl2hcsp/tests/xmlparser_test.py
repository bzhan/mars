import unittest

from aadl2hcsp.xmlparser import *

class XMLParserTest(unittest.TestCase):
    def testXMLParser(self):
        path = 'aadl2hcsp/instances/'
        outfile = 'out.json'
        dic = {}
        for xmlfile in os.listdir(path):
            parser(os.path.join(path, xmlfile), dic)
        print(dic)
        with open(outfile, "w") as f_obj:
            json.dump(dic, f_obj)


if __name__ == "__main__":
    unittest.main()
