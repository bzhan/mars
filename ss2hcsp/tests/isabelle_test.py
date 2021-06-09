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
        with open('CaseStudies/lander/Lander1.thy', 'w', encoding='utf-8') as f:
            f.write(output)

    def testTranslate2(self):
        with open('CaseStudies/lander/lander_simple2.txt', 'r', encoding='utf-8') as f:
            text = f.read()
        process = parser.parse_file(text)
        output = isabelle.translate_isabelle(process, "Lander2")
        with open('CaseStudies/lander/Lander2.thy', 'w', encoding='utf-8') as f:
            f.write(output)

    def testTranslate3(self):
        with open('CaseStudies/lander/lander_simple3.txt', 'r', encoding='utf-8') as f:
            text = f.read()
        process = parser.parse_file(text)
        output = isabelle.translate_isabelle(process, "Lander3")
        with open('CaseStudies/lander/Lander3.thy', 'w', encoding='utf-8') as f:
            f.write(output)

    def testTranslate4(self):
        with open('CaseStudies/lander/lander_simple4.txt', 'r', encoding='utf-8') as f:
            text = f.read()
        process = parser.parse_file(text)
        output = isabelle.translate_isabelle(process, "Lander4")
        with open('CaseStudies/lander/Lander4.thy', 'w', encoding='utf-8') as f:
            f.write(output)


if __name__ == "__main__":
    unittest.main()
