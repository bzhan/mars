"""Unit test for sf_convert."""

import unittest
from ss2hcsp.sf import sf_convert
from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.hcsp.pprint import pprint
from ss2hcsp.hcsp import module
from ss2hcsp.hcsp import hcsp
from ss2hcsp.tests.simulator_test import run_test as run_simulator_test
from ss2hcsp.hcsp.pprint import pprint


def run_test(self, filename, num_cycle, res, *,
             print_chart=False, print_before_simp=False, print_after_simp=False):
    """Test function for Stateflow diagrams.

    filename : str - name of the XML file.
    num_cycle : int - number of cycles of Stateflow diagram to simulate.
    res : List[str] - expected output events.
    print_chart : bool - print parsed chart.
    print_before_simp : bool - print HCSP program before simplification.
    print_after_simp : bool - print HCSP program after simplification.
 
    """
    diagram = SL_Diagram(location=filename)
    model_name = diagram.parse_xml()
    diagram.add_line_name()
    _, _, charts, _, _, _, _, _ = diagram.seperate_diagram()
    chart = charts[0]

    # Optional: print chart
    if print_chart:
        print(chart)

    converter = sf_convert.SFConvert(chart)
    procs = converter.get_procs()
    hp = converter.get_toplevel_process()

    # Optional: print HCSP program before simplification
    if print_before_simp:
        print(pprint(hp))
        for name, proc in procs.items():
            print('\n' + name + " ::=\n" + pprint(proc))

    # Reduce procedures
    hp = hcsp.reduce_procedures(hp, procs)

    # Reduce skip
    hp = hcsp.simplify(hp)
    for name in procs:
        procs[name] = hcsp.simplify(procs[name])

    # Optional: print HCSP program after simplification
    if print_after_simp:
        print(pprint(hp))
        for name, proc in procs.items():
            print('\n' + name + " ::=\n" + pprint(proc))

    # Test result using simulator
    run_simulator_test(self, [(procs, hp)], num_cycle, res)


class SFConvertTest(unittest.TestCase):
    def testNoEventTrig(self):
        run_test(self, "./Examples/Stateflow/tests/no_event_trig.xml", 1,
            ['log en_A2', 'log b', 'log en_A3', 'log tb', 'log en_B2', 'delay 0.1'], print_after_simp=True)

    def testAggregatedJunctions(self):
        run_test(self, "./Examples/Stateflow/tests/aggregated_junctions.xml", 2,
            ['log enA', 'log exA', 'log enB', 'delay 0.1', 'log conBJun', 'log conJunC',
             'log exB', 'log tranBJun', 'log tranJunC', 'delay 0.1'])

    def testFakeEarlyReturn(self):
        run_test(self, "./Examples/Stateflow/tests/fake_early_return.xml", 1,
            ['log a', 'log c', 'log du_A1', 'log b', 'log a', 'log c', 'log ex_A1',
             'log en_A2', 'log en_C2', 'log tb', 'log en_B2', 'log en_C3', 'delay 0.1'])

    def testJunctionLoop(self):
        run_test(self, "./Examples/Stateflow/tests/junction_loop.xml", 1,
            ['log t1', 'log t2', 'log t1', 'log t2', 'log t1', 'log t2', 'log t1',
             'log t4', 'delay 0.1'])

    def testEarlyExit(self):
        run_test(self, "./Examples/Stateflow/tests/early_exit.xml", 1,
            ['log en_A1', 'log ex_A1', 'log en_B', 'delay 0.1'], print_before_simp=True)


if __name__ == "__main__":
    unittest.main()
