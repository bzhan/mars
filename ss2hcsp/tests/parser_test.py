"""Unit test for parsing files."""

import unittest

from ss2hcsp.hcsp.parser import hp_parser, parse_file


class ParserTest(unittest.TestCase):
    def testParseFile(self):
        infos = parse_file("""
            P0 ::= x := 0; (<x_dot = 1 & true> |> [](p2c!x --> skip); c2p?x)**
            P1 ::= (wait(2); p2c?x; c2p!x-1)**
        """)

        self.assertEqual(infos, [
            ("P0", hp_parser.parse("x := 0; (<x_dot = 1 & true> |> [](p2c!x --> skip); c2p?x)**")),
            ("P1", hp_parser.parse("(wait(2); p2c?x; c2p!x-1)**"))
        ])


if __name__ == "__main__":
    unittest.main()
