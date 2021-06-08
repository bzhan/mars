"""Unit test for sf_convert."""

import unittest
from ss2hcsp.sf import sf_convert
from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.hcsp.pprint import pprint
from ss2hcsp.hcsp import module
from ss2hcsp.tests.simulator_test import run_test


class SFConvertTest(unittest.TestCase):
    def testNoEventTrig(self):
        location = "./Examples/Stateflow/tests/no_event_trig.xml"
        diagram = SL_Diagram(location=location)
        model_name = diagram.parse_xml()
        diagram.add_line_name()
        _, _, charts, _, _, _, _, _ = diagram.seperate_diagram()
        chart = charts[0]

        converter = sf_convert.SFConvert(chart)
        procs = converter.get_procs()
        hp = converter.get_toplevel_process()

        run_test(self, [
            (procs, hp)
        ], 1, ['log en_A2', 'log b', 'log en_A3', 'log tb', 'log en_B2', 'delay 0.1'])


if __name__ == "__main__":
    unittest.main()
