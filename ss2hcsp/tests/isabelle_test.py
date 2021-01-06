"""Unit test for translation to Isabelle."""

import unittest

from ss2hcsp.hcsp import isabelle
from ss2hcsp.hcsp import parser
from ss2hcsp.hcsp import pprint


class IsabelleTest(unittest.TestCase):
    def testTranslate(self):
        with open('CaseStudies/lander/lander_simple.txt', 'r', encoding='utf-8') as f:
            text = f.read()
        process = parser.parse_file(text)
        output = isabelle.translate_isabelle(process, "Lander1")
        with open('lunarlander_sl/Lander1.thy', 'w', encoding='utf-8') as f:
            f.write(output)


if __name__ == "__main__":
    unittest.main()
