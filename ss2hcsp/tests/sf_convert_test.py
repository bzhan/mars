"""Unit test for sf_convert."""

import unittest
import random
from pstats import Stats
import cProfile

from ss2hcsp.sf import sf_convert
from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.hcsp.pprint import pprint
from ss2hcsp.hcsp import module
from ss2hcsp.hcsp import hcsp
from ss2hcsp.tests.simulator_test import run_test as run_simulator_test
from ss2hcsp.hcsp.pprint import pprint


def run_test(self, filename, num_cycle, res, *, io_filter=None,
             print_chart=False, print_before_simp=False, print_final=False,
             print_res=False, profile=False, output_to_file=None):
    """Test function for Stateflow diagrams.

    filename : str - name of the XML file.
    num_cycle : int - number of cycles of Stateflow diagram to simulate.
    res : List[str] - expected output events.
    io_filter : str -> bool - (optional) filter for IO events to display.
    print_chart : bool - print parsed chart.
    print_before_simp : bool - print HCSP program before simplification.
    print_final : bool - print HCSP program after optimization.
    output_to_file : str - (optional) name of file to output HCSP.

    """
    if profile:
        pr = cProfile.Profile()
        pr.enable()

    diagram = SL_Diagram(location=filename)
    proc_map = sf_convert.convert_diagram(
        diagram, print_chart=print_chart, print_before_simp=print_before_simp, print_final=print_final)

    if profile:
        p = Stats(pr)
        p.strip_dirs()
        p.sort_stats('cumtime')
        p.print_stats()

    # Optional: output converted HCSP to file
    if output_to_file is not None:
        modules = []
        module_insts = []
        for name, (procs, hp) in proc_map.items():
            procs_lst = [hcsp.Procedure(proc_name, hp) for proc_name, hp in procs.items()]
            modules.append(module.HCSPModule(name, code=hp, procedures=procs_lst))
            module_insts.append(module.HCSPModuleInst(name, name, []))
        system = module.HCSPSystem(module_insts)
        declarations = module.HCSPDeclarations(modules + [system])

        with open(output_to_file, "w") as f:
            f.write(declarations.export())

    # Test result using simulator
    run_simulator_test(self, proc_map, num_cycle, res, io_filter=io_filter,
                       print_res=print_res)


class SFConvertTest(unittest.TestCase):
    def testStates1(self):
        run_test(self, "./Examples/Stateflow/tests/States/States1.xml", 3,
            ['log enA', 'log enA1', 'log duA', 'log exA1', 'log enA2', 'delay 0.1',
             'log duA', 'log duA2', 'delay 0.1', 'log duA', 'log duA2', 'delay 0.1'])

    def testStates2(self):
        run_test(self, "./Examples/Stateflow/tests/States/States2.xml", 3,
            ['log enA', 'log enA1', 'log exA1', 'log exA', 'log enB', 'log enB1', 'delay 0.1',
             'log duB', 'log duB1', 'delay 0.1', 'log duB', 'log duB1', 'delay 0.1'])

    def testStates3(self):
        run_test(self, "./Examples/Stateflow/tests/States/States3.xml", 2,
            ['log enA', 'log enA1', 'log enA2', 'log exA2', 'log exA1',
             'log exA', 'log enB', 'log enB1', 'log enB2', 'delay 0.1',
             'log duB', 'log duB1', 'log duB2', 'delay 0.1'])

    def testStates4(self):
        run_test(self, "./Examples/Stateflow/tests/States/States4.xml", 3,
            ['log enA', 'log enA1', 'log enB', 'log enB1', 'delay 0.1',
             'log enA', 'log enA1', 'delay 0.1', 'log enB', 'log enB1', 'delay 0.1'])

    def testStates5(self):
        run_test(self, "./Examples/Stateflow/tests/States/States5.xml", 10,
            ['log enA1', 'log enA2', 'delay 0.1', 'log enB1', 'delay 0.1', 'log enB2', 'delay 0.1',
             'log enA2', 'delay 0.1', 'log enA1', 'delay 0.1',
             'log enB1', 'delay 0.1', 'log enB2', 'delay 0.1',
             'log enA1', 'delay 0.1', 'log enA2', 'delay 0.1', 'log enB1', 'delay 0.1'])

    def testStates6(self):
        run_test(self, "./Examples/Stateflow/tests/States/States6.xml", 1,
            ['log enA', 'log enA1', 'log enA2', 'log enB', 'log enB1', 'log enB2', 'delay 0.1'])

    def testStates7(self):
        run_test(self, "./Examples/Stateflow/tests/States/States7.xml", 2,
            ['log enA', 'log enA1', 'log exA1', 'log exA', 'log enA', 'log enA1', 'delay 0.1',
             'log exA1', 'log exA', 'log enA', 'log enA1', 'delay 0.1'])

    def testStates8(self):
        run_test(self, "./Examples/Stateflow/tests/States/States8.xml", 6,
            ['log loop', 'delay 0.1', 'log loop', 'delay 0.1', 'log loop', 'delay 0.1',
             'log loop', 'delay 0.1', 'log loop', 'delay 0.1',
             'log 100,200,300,400,500', 'delay 0.1'])

    def testTransitions1(self):
        run_test(self, "./Examples/Stateflow/tests/Transitions/Transitions1.xml", 1,
            ['log enS', 'log enA', 'log ca', 'log exA', 'log exS', 'log ta',
             'log enT', 'log enB', 'delay 0.1'])

    def testTransitions2(self):
        run_test(self, "./Examples/Stateflow/tests/Transitions/Transitions2.xml", 2,
            ['log enS', 'log enA', 'log exA', 'log enB', 'delay 0.1',
             'log ca', 'log exB', 'log exS', 'log ta', 'log enT', 'log enB', 'delay 0.1'])

    def testTransitions3(self):
        run_test(self, "./Examples/Stateflow/tests/Transitions/Transitions3.xml", 5,
            ['log b', 'log c1', 'delay 0.1', 'log c2', 'delay 0.1', 'log B',
             'delay 0.1', 'log c2', 'delay 0.1', 'log B', 'delay 0.1'])

    def testTransitions4(self):
        run_test(self, "./Examples/Stateflow/tests/Transitions/Transitions4.xml", 2,
            ['log enS', 'log condDefault', 'log tranDefault', 'log enA',
             'log duS', 'log condInner', 'log exA', 'log tranInner', 'log enA', 'delay 0.1',
             'log duS', 'log condInner', 'log exA', 'log tranInner', 'log enA', 'delay 0.1'])

    def testTransitions5(self):
        run_test(self, "./Examples/Stateflow/tests/Transitions/Transitions5.xml", 1,
            ['log enS', 'log enA', 'log duS', 'log condInner', 'log exA',
             'log tranInner', 'log enA', 'delay 0.1'])

    def testTransitions6(self):
        run_test(self, "./Examples/Stateflow/tests/Transitions/Transitions6.xml", 2,
            ['log enS', 'log enA', 'log duS', 'log exA', 'log enB', 'delay 0.1',
             'log duS', 'log innerCond', 'log exB', 'log innerTran', 'log enA', 'delay 0.1'])

    def testTransitions7(self):
        run_test(self, "./Examples/Stateflow/tests/Transitions/Transitions7.xml", 1,
            ['log enS', 'log enT', 'delay 0.1'])

    def testTransitions8(self):
        run_test(self, "./Examples/Stateflow/tests/Transitions/Transitions8.xml", 5,
            ['log enS', 'log duS', 'log ca1', 'delay 0.1', 'log duS', 'log ca1', 'delay 0.1',
             'log duS', 'log ca2', 'delay 0.1', 'log duS', 'log ca2', 'delay 0.1',
             'log enT', 'delay 0.1'])

    def testJunctions1(self):
        run_test(self, "./Examples/Stateflow/tests/Junctions/Junctions1.xml", 1,
            ['log enA', 'log enD', 'delay 0.1'])

    def testJunctions2(self):
        run_test(self, "./Examples/Stateflow/tests/Junctions/Junctions2.xml", 2,
            ['log enA', 'log exA', 'log enB', 'delay 0.1', 'log conBJun', 'log conJunC',
             'log exB', 'log tranBJun', 'log tranJunC', 'log enC', 'delay 0.1'])

    def testJunctions3(self):
        run_test(self, "./Examples/Stateflow/tests/Junctions/Junctions3.xml", 1,
            ['log t1', 'log t2', 'log t1', 'log t2', 'log t1', 'log t2', 'log t1',
             'log t4', 'delay 0.1'])

    def testJunctions4(self):
        run_test(self, "./Examples/Stateflow/tests/Junctions/Junctions4.xml", 1,
            ['log enA', 'log enA1', 'log duA', 'log c1', 'log c2', 'log exA1', 'log exA',
             'log t1', 'log t2', 'log enC', 'log enC2', 'delay 0.1'])

    def testJunctions5(self):
        run_test(self, "./Examples/Stateflow/tests/Junctions/Junctions5.xml", 1,
            ['log enA', 'log enA1', 'log duA', 'log ca', 'log exA1', 'log enA2', 'delay 0.1'])

    def testJunctions6(self):
        run_test(self, "./Examples/Stateflow/tests/Junctions/Junctions6.xml", 1,
            ['log enA', 'log ca', 'log ca', 'log exA', 'log ta2', 'log ta4',
             'log enC', 'delay 0.1'])

    def testJunctions7(self):
        run_test(self, "./Examples/Stateflow/tests/Junctions/Junctions7.xml", 1,
            ['log enA', 'log exA', 'log xle2', 'log yeq2', 'log zge2', 'log enC', 'delay 0.1'])

    def testJunctions8(self):
        run_test(self, "./Examples/Stateflow/tests/Junctions/Junctions8.xml", 3,
            ['log enA', 'log ca1', 'log exA', 'log enC', 'delay 0.1',
             'log exC', 'log enA', 'delay 0.1',
             'log duA', 'log ca2', 'log exA', 'log enC', 'delay 0.1'])

    def testEvent1(self):
        run_test(self, "./Examples/Stateflow/tests/Events/Event1.xml", 1,
            ['log b', 'log a', 'log en_A2', 'log tb', 'log en_B2', 'delay 0.1'])

    def testEvent2(self):
        run_test(self, "./Examples/Stateflow/tests/Events/Event2.xml", 1,
            ['log b', 'log a', 'log en_A2', 'log c', 'log en_C2', 'log tb',
             'log en_B2', 'delay 0.1'])

    def testEvent3(self):
        run_test(self, "./Examples/Stateflow/tests/Events/Event3.xml", 1,
            ['log b', 'log a1', 'log a2', 'log en_A2', 'log tb', 'log en_B2', 'delay 0.1'])

    def testEvent4(self):
        run_test(self, "./Examples/Stateflow/tests/Events/Event4.xml", 1,
            ['log b', 'log a1', 'log c', 'log en_C2', 'log a2', 'log en_A2',
             'log tb', 'log en_B2', 'delay 0.1'])

    def testEvent5(self):
        run_test(self, "./Examples/Stateflow/tests/Events/Event5.xml", 1,
            ['log en_A2', 'log b', 'log en_A3', 'log tb', 'log en_B2', 'delay 0.1'])

    def testEvent6(self):
        run_test(self, "./Examples/Stateflow/tests/Events/Event6.xml", 1,
            ['log a 5', 'log a 4', 'log a 3', 'log a 2', 'log a 1', 'log a 0',
             'log en_A2 0', 'delay 0.1'])

    def testDirectedEvent1(self):
        run_test(self, "./Examples/Stateflow/tests/Events/DirectedEvent1.xml", 1,
            ['log en_A1', 'log en_B1', 'log en_C1',
             'log ex_C1', 'log en_C2', 'log ex_B1', 'log en_B2', 'log ex_A1', 'log en_A2',
             'log ex_A2', 'log en_A1', 'log ex_B2', 'log en_B1', 'log ex_C2', 'log en_C1',
             'delay 0.1'])

    def testDirectedEvent2(self):
        run_test(self, "./Examples/Stateflow/tests/Events/DirectedEvent2.xml", 1,
            ['log en_A1', 'log en_B1_A1', 'log en_C1_A1', 'log ex_C1_A1', 'log en_C2_A2',
             'log ex_B1_A1', 'log en_B2_A2', 'log ex_A1', 'log en_A2', 'log ex_A2',
             'log en_A1', 'log ex_B2_A2', 'log en_B1_A1', 'log ex_C2_A2', 'log en_C1_A1',
             'delay 0.1'])
        
    def testDirectedEvent3(self):
        run_test(self, "./Examples/Stateflow/tests/Events/DirectedEvent3.xml", 1,
            ['log en_A1', 'log en_B1', 'log ex_B1',
             'log en_B2', 'log ex_A1', 'log en_A2', 'delay 0.1'])

    def testDirectedEvent4(self):
        run_test(self, "./Examples/Stateflow/tests/Events/DirectedEvent4.xml", 1,
            ['log en_A1', 'log en_B2', 'log en_B21',
             'log ex_B21', 'log ex_B2', 'log en_B4', 'log ex_A1', 'log en_A2', 'delay 0.1'])

    def testDirectedEvent5(self):
        run_test(self, "./Examples/Stateflow/tests/Events/DirectedEvent5.xml", 1,
            ['log en_A1', 'log en_B2', 'log en_B21',
             'log ex_B21', 'log en_B22', 'log ex_A1', 'log en_A2', 'delay 0.1'])

    def testDirectedEvent6(self):
        run_test(self, "./Examples/Stateflow/tests/Events/DirectedEvent6.xml", 1,
            ['log a', 'log c', 'delay 0.1'])

    def testGraphicalFunction1(self):
        run_test(self, "./Examples/Stateflow/tests/Functions/GraphicalFunction1.xml", 1,
            ['log en_A', 'log en_B', 'delay 0.1'])
        
    def testGraphicalFunction2(self):
        run_test(self, "./Examples/Stateflow/tests/Functions/GraphicalFunction2.xml", 1,
            ['log en_A', 'log set', 'log set', 'log set', 'log en_B',
             'log 100 200 300 0 0', 'delay 0.1'])

    def testGraphicalFunction3(self):
        run_test(self, "./Examples/Stateflow/tests/Functions/GraphicalFunction3.xml", 1,
            ['log en_A', 'log en_B', 'log 4', 'log 9', 'delay 0.1'])

    def testGraphicalFunction4(self):
        run_test(self, "./Examples/Stateflow/tests/Functions/GraphicalFunction4.xml", 1,
            ['log en_A', 'log ack', 'log ack', 'log ack', 'log ack', 'log ack',
             'log en_B', 'delay 0.1'])

    def testTemporal1(self):
        run_test(self, "./Examples/Stateflow/tests/Temporal/Temporal1.xml", 10,
            ['log en_A', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1',
             'log en_B', 'delay 0.1', 'log du_B', 'delay 0.1', 'log du_B', 'delay 0.1',
             'log en_A', 'delay 0.1', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1',
             'log en_B', 'delay 0.1', 'log du_B', 'delay 0.1'])

    def testTemporal2(self):
        random.seed(0)  # for repeatability
        run_test(self, "./Examples/Stateflow/tests/Temporal/Temporal2.xml", 10,
            ['log en_A', 'log Picked 4', 'delay 1', 'delay 1', 'delay 1', 'delay 1',
             'log en_B', 'log Picked 4', 'delay 1', 'delay 1', 'delay 1', 'delay 1',
             'log en_A', 'log Picked 1', 'delay 1',
             'log en_B', 'log Picked 3', 'delay 1'])

    def testTemporal3(self):
        run_test(self, "./Examples/Stateflow/tests/Temporal/Temporal3.xml", 10,
            ['log en_A', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1',
             'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1',
             'log en_B', 'delay 0.1', 'log du_B', 'delay 0.1', 'log du_B', 'delay 0.1',
             'log en_A', 'delay 0.1', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1'])

    def testTemporal4(self):
        run_test(self, "./Examples/Stateflow/tests/Temporal/Temporal4.xml", 10,
            ['log en_A', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1',
             'log en_B', 'delay 0.1', 'log du_B', 'delay 0.1', 'log du_B', 'delay 0.1',
             'log du_B', 'delay 0.1', 'log du_B', 'delay 0.1', 'log du_B', 'delay 0.1',
             'log du_B', 'delay 0.1', 'log du_B', 'delay 0.1'])

    def testTemporal5(self):
        run_test(self, "./Examples/Stateflow/tests/Temporal/Temporal5.xml", 10,
            ['log en_A', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1',
             'log en_B', 'delay 0.1', 'log en_A', 'delay 0.1',
             'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1',
             'log en_B', 'delay 0.1', 'log en_A', 'delay 0.1'])

    def testTemporal6(self):
        run_test(self, "./Examples/Stateflow/tests/Temporal/Temporal6.xml", 5,
            ['log en_A', 'log en_A', 'delay 0.1', 'log en_A', 'delay 0.1', 'log en_A',
             'delay 0.1', 'log en_A', 'delay 0.1', 'log en_A', 'delay 0.1'])
    
    def testTemporal7(self):
        run_test(self, "./Examples/Stateflow/tests/Temporal/Temporal7.xml", 5,
            ['log en_A', 'log en_B', 'delay 0.1', 'log en_A', 'delay 0.1', 'log en_B',
             'delay 0.1', 'log en_A', 'delay 0.1', 'log en_B', 'delay 0.1'])

    def testTemporal8(self):
        run_test(self, "./Examples/Stateflow/tests/Temporal/Temporal8.xml", 10,
            ['log en_A', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1',
             'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1',
             'log en_B', 'delay 0.1', 'log du_B', 'delay 0.1', 'log du_B', 'delay 0.1',
             'log en_A', 'delay 0.1', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1'])

    def testEarlyReturn1(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn1.xml", 1,
            ['log en_A', 'log en_A1', 'log ex_A1', 'log ex_A', 'log en_B', 'delay 0.1'])

    def testEarlyReturn2(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn2.xml", 1,
            ['log en_A', 'log en_A1', 'log E', 'log ex_A1', 'log ex_A', 'log en_B', 'delay 0.1'])

    def testEarlyReturn3(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn3.xml", 1,
            ['log en_A 1', 'log ex_A 2', 'log en_C 2', 'delay 0.1'])

    def testEarlyReturn4(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn4.xml", 1,
            ['log ca', 'log ta', 'log en_A2', 'delay 0.1'])

    def testEarlyReturn5(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn5.xml", 1,
            ['log en_A', 'log en_A1', 'log ex_A1', 'log ex_A', 'log en_B', 'delay 0.1'])

    def testEarlyReturn6(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn6.xml", 1,
            ['log en_A', 'log en_A1', 'log ex_A1', 'log loop', 'log ex_A', 'log en_A',
             'log en_A1', 'delay 0.1'])

    def testEarlyReturn7(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn7.xml", 2,
            ['log en_A', 'log en_A1', 'log ex_A1', 'log en_A2', 'delay 0.1',
             'log ex_A2', 'log loop', 'log ex_A', 'log en_A', 'log en_A1', 'delay 0.1'])

    def testEarlyReturn8(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn8.xml", 1,
            ['log a', 'log c', 'log du_A1', 'log b', 'log a', 'log c', 'log ex_A1',
             'log en_A2', 'log en_C2', 'log tb', 'log en_B2', 'log en_C3', 'delay 0.1'])

    def testEarlyReturn9(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn9.xml", 1,
            ['log en_A', 'log en_A1', 'log pre', 'log ex_A1', 'log ex_A', 'log en_B', 'delay 0.1'])

    def testEarlyReturn10(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn10.xml", 1,
            ['log en_A', 'log en_A1', 'log pre', 'log ex_A1', 'log ex_A', 'log en_B', 'delay 0.1'])

    def testEarlyReturn11(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn11.xml", 2,
            ['log en_A', 'log en_A1', 'log ex_A1', 'log en_A2', 'log en_A2a', 'delay 0.1',
             'log ex_A2a', 'log ex_A2', 'log loop', 'log ex_A', 'log en_A', 'log en_A1', 'delay 0.1'])

    def testEarlyReturn12(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn12.xml", 1,
            ['log enB', 'log enC', 'delay 0.1'])

    def testEarlyReturn13(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn13.xml", 1,
            ['log F', 'log exA1', 'log exA1', 'log exA1', 'log exA1', 'log exA1',
             'log exA1_done', 'log enA3', 'delay 0.1'])

    def testEarlyReturn14(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn14.xml", 1,
            ['log en_A', 'log en_A1', 'log loop', 'log ex_A1', 'log ex_A', 'log en_A',
             'log en_A1', 'log ca', 'log ex_A1', 'log ta', 'log en_A2', 'delay 0.1'])

    def testEarlyReturn15(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn15.xml", 1,
            ['log enS', 'log enA1', 'log enA1a', 'log enA2', 'log ca', 'log enB', 'delay 0.1'])

    def testEarlyReturn16(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn16.xml", 1,
            ['log en_A', 'log en_A1', 'log outA1', 'log ex_A1', 'log en_A3', 'delay 0.1'])

    def testEarlyReturn17(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn17.xml", 2,
            ['log en_A', 'log en_A1', 'log ex_A1', 'log en_A2', 'delay 0.1',
             'log outA2', 'log ex_A2', 'log en_A3', 'delay 0.1'])

    def testEarlyReturn18(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn18.xml", 1,
            ['log enS', 'log duS', 'log ca1', 'log exS', 'log enT', 'delay 0.1'])

    def testEarlyReturn19(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn19.xml", 1,
            ['log enS', 'log duS', 'log ca1', 'log ca2', 'log exS', 'log enT', 'delay 0.1'])

    def testEarlyReturn20(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn20.xml", 1,
            ['log enS', 'log duS', 'log ca1', 'log ca2', 'log exS', 'log enT', 'delay 0.1'])

    def testDSM1(self):
        io_filter = lambda s: False
        run_test(self, "./Examples/Stateflow/tests/Data/DSM1.xml", 20,
            ['log 2', 'delay 0.1', 'log 4', 'delay 0.1', 'log 5', 'delay 0.1',
             'log 7', 'delay 0.1', 'log 8', 'delay 0.1', 'log 10', 'delay 0.1'], io_filter=io_filter)

    def testDSM2(self):
        io_filter = lambda s: False
        run_test(self, "./Examples/Stateflow/tests/Data/DSM2.xml", 20,
            ['log 1', 'delay 0.1', 'log 3', 'delay 0.1', 'log 4', 'delay 0.1',
             'log 6', 'delay 0.1', 'log 7', 'delay 0.1', 'log 9', 'delay 0.1'], io_filter=io_filter)

    def testDSM3(self):
        io_filter = lambda s: False
        run_test(self, "./Examples/Stateflow/tests/Data/DSM3.xml", 20,
            ['log 3 2', 'delay 0.1', 'log 3 5', 'delay 0.1', 'log 8 5', 'delay 0.1',
             'log 8 13', 'delay 0.1', 'log 21 13', 'delay 0.1', 'log 21 34', 'delay 0.1'], io_filter=io_filter)

    def testDSM4(self):
        io_filter = lambda s: False
        run_test(self, "./Examples/Stateflow/tests/Data/DSM4.xml", 19,
            ['log A1', 'log C1', 'log B2', 'log D4', 'delay 0.1',
             'log A4', 'log C4', 'delay 0.1', 'log B5', 'log D7', 'delay 0.1'], io_filter=io_filter)

    def testDSM5(self):
        io_filter = lambda s: False
        run_test(self, "./Examples/Stateflow/tests/Data/DSM5.xml", 34,
            ['log 4 2', 'delay 0.1', 'log 4 4', 'delay 0.1', 'log 5 4', 'delay 0.1',
             'log 5 6', 'delay 0.1', 'log 6 6', 'delay 0.1', 'log 6 8', 'delay 0.1'], io_filter=io_filter)

    def testDSM6(self):
        io_filter = lambda s: False
        run_test(self, "./Examples/Stateflow/tests/Data/DSM6.xml", 20,
            ['log en_A 0 0', 'log en_A1 3 0', 'log en_B 4 4', 'log du_A1 4 0', 'delay 0.1',
             'log en_A 4 -1', 'log du_A1 3 -1', 'delay 0.1',
             'log en_B 4 -1', 'log du_A1 4 0', 'delay 0.1'], io_filter=io_filter)

    def testCommunication1(self):
        io_filter = lambda s: False
        run_test(self, "./Examples/Stateflow/tests/Data/Communication1.xml", 20,
            ['log en_A', 'log en_A1', 'log en_B', 'log 1 1', 'delay 0.1',
             'log en_A', 'log 2 1', 'delay 0.1', 'log en_B', 'log 2 2', 'delay 0.1',
             'log en_A', 'log 3 2', 'delay 0.1', 'log en_B', 'log 3 3', 'delay 0.1',
             'log en_A', 'log 4 3', 'delay 0.1'], io_filter=io_filter)
        
    def testCommunication2(self):
        io_filter = lambda s: False
        run_test(self, "./Examples/Stateflow/tests/Data/Communication2.xml", 34,
            ['log en_A', 'log en_A1', 'log en_B', 'log 1 2 1 1', 'delay 0.1',
             'log en_A', 'log 1 2 2 1', 'delay 0.1', 'log en_B', 'log 1 2 2 2', 'delay 0.1',
             'log en_A', 'log 1 2 3 2', 'delay 0.1', 'log en_B', 'log 1 2 3 3', 'delay 0.1',
             'log en_A', 'log 1 2 4 3', 'delay 0.1'], io_filter=io_filter)

    def testSFNew(self):
        random.seed(0)  # for repeatability
        pat = [
            'IO read_Chart_WHC [0,0,0,0,0]', 'IO read_Chart_RHC [0,0,0,0,0]',
            'IO read_Chart_RHC2 [0,0,0,0,0]', 'IO write_Chart_WHC [0,0,0,0,0]',
            'IO write_Chart_RHC [0,0,0,0,0]', 'IO write_Chart_RHC2 [0,0,0,0,0]',
            'IO read_DDS_Writer_WHC [0,0,0,0,0]', 'IO read_DDS_Writer_RHC [0,0,0,0,0]',
            'IO read_DDS_Writer_RHC2 [0,0,0,0,0]', 'IO write_DDS_Writer_WHC [0,0,0,0,0]',
            'IO write_DDS_Writer_RHC [0,0,0,0,0]', 'IO write_DDS_Writer_RHC2 [0,0,0,0,0]',
            'IO ch_x0_0 1', 'IO ch_x1_0 1', 'IO ch_x2_0 1', 'IO ch_x3_0 0'
        ]
        res = pat * 2 + ['delay 0.1'] + pat + ['delay 0.1']
        run_test(self, "./Examples/Stateflow/sf_new/sf_new.xml", 50,
            res, output_to_file="./Examples/Stateflow/sf_new/sf_new.txt")

    def testMessages1(self):
        run_test(self, "./Examples/Stateflow/tests/Messages/Messages1.xml", 2,
            ['log en_A', 'log en_B', 'delay 0.1', 'delay 0.1'])

    def testMessages2(self):
        run_test(self, "./Examples/Stateflow/tests/Messages/Messages2.xml", 3,
            ['log en_A', 'log en_B', 'delay 0.1', 'log en_C',
             'delay 0.1', 'log en_D', 'delay 0.1'])

    def testMessages3(self):
        run_test(self, "./Examples/Stateflow/tests/Messages/Messages3.xml", 7,
           ['log en_A', 'IO ch_x0_0 {name:M,data:0,scope:OUTPUT_DATA}', 'log en_A0',
            'delay 1', 'delay 1', 'delay 1','log en_A1', 'delay 1', 'log en_A2',
             'delay 1', 'delay 1'])
    
    def testMessage4(self):
        run_test(self, "./Examples/Stateflow/tests/Messages/Messages4.xml", 3,
            ['log en_A', 'log en_B', 'delay 0.1', 'log en_C', 'delay 0.1', 'log en_D', 'delay 0.1'])

    def testMessages5(self):
        run_test(self, "./Examples/Stateflow/tests/Messages/Messages3_2018a.xml",7,
           ['log en_A','IO ch_x0_0 {name:M,data:2,scope:OUTPUT_DATA}', 'log en_A0',
            'delay 1', 'delay 1', 'delay 1','log en_A1', 'delay 1', 'log en_A2',
             'delay 1', 'delay 1'])

    def testMessage6(self):
        run_test(self, "./Examples/Stateflow/tests/Messages/Messages5.xml",3,
            ['log en_A', 'log en_B', 'delay 0.1', 'log en_C', 'delay 0.1', 'delay 0.1'])

    def testMessage7(self):
        run_test(self, "./Examples/Stateflow/tests/Messages/Messages6.xml",4,
            ['log en_A', 'log en_B', 'delay 0.1', 'log en_C', 'delay 0.1',
             'log en_D', 'delay 0.1', 'log en_E', 'delay 0.1'])

    def testMessage8(self):
        run_test(self, "./Examples/Stateflow/tests/Messages/Messages7.xml",3,
            ['log en_A', 'log en_B', 'delay 0.1', 'delay 0.1', 'delay 0.1'])



if __name__ == "__main__":
    unittest.main()
