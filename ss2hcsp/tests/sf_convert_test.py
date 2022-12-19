"""Unit test for sf_convert."""

import unittest
import random
from pstats import Stats
import cProfile

from ss2hcsp.sf import sf_convert
from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.hcsp import module
from ss2hcsp.hcsp import hcsp
from ss2hcsp.tests.simulator_test import run_test as run_simulator_test
from ss2hcsp.tests.sim_test import run_test as run_sim_test
from ss2hcsp.hcsp.pprint import pprint


def run_test(self, filename, num_cycle, res, *, io_filter=None,
             print_chart=False, print_before_simp=False, print_final=False,
             debug_name=False, print_res=False, profile=False, output_to_file=None):
    """Test function for Stateflow diagrams.

    filename : str - name of the XML file.
    num_cycle : int - number of cycles of Stateflow diagram to simulate.
    res : List[str] - expected output events.
    io_filter : str -> bool - (optional) filter for IO events to display.
    print_chart : bool - print parsed chart.
    print_before_simp : bool - print HCSP program before simplification.
    print_final : bool - print HCSP program after optimization.
    debug_name : bool - print size of HCSP program before and after optimization.
    output_to_file : str - (optional) name of file to output HCSP.

    """
    if profile:
        pr = cProfile.Profile()
        pr.enable()

    diagram = SL_Diagram(location=filename)
    proc_map = sf_convert.convert_diagram(
        diagram, print_chart=print_chart, print_before_simp=print_before_simp,
        print_final=print_final, debug_name=debug_name)

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

# Path to all test cases
prefix = "./Examples/Stateflow/tests/"

class SFConvertTest(unittest.TestCase):
    def testStates1(self):
        run_test(self, prefix+"States/States1.xml", 3,
            ['log enA', 'log enA1', 'log duA', 'log exA1', 'log enA2', 'delay 0.1',
             'log duA', 'log duA2', 'delay 0.1', 'log duA', 'log duA2', 'delay 0.1'],
            output_to_file=prefix+"States/States1.txt")

    def testStates2(self):
        run_test(self, prefix+"States/States2.xml", 3,
            ['log enA', 'log enA1', 'log exA1', 'log exA', 'log enB', 'log enB1', 'delay 0.1',
             'log duB', 'log duB1', 'delay 0.1', 'log duB', 'log duB1', 'delay 0.1'],
            output_to_file=prefix+"States/States2.txt")

    def testStates3(self):
        run_test(self, prefix+"States/States3.xml", 2,
            ['log enA', 'log enA1', 'log enA2', 'log exA2', 'log exA1',
             'log exA', 'log enB', 'log enB1', 'log enB2', 'delay 0.1',
             'log duB', 'log duB1', 'log duB2', 'delay 0.1'],
            output_to_file=prefix+"States/States3.txt")

    def testStates4(self):
        run_test(self, prefix+"States/States4.xml", 3,
            ['log enA', 'log enA1', 'log enB', 'log enB1', 'delay 0.1',
             'log enA', 'log enA1', 'delay 0.1', 'log enB', 'log enB1', 'delay 0.1'],
            output_to_file=prefix+"States/States4.txt")

    def testStates5(self):
        run_test(self, prefix+"States/States5.xml", 10,
            ['log enA1', 'log enA2', 'delay 0.1', 'log enB1', 'delay 0.1', 'log enB2', 'delay 0.1',
             'log enA2', 'delay 0.1', 'log enA1', 'delay 0.1',
             'log enB1', 'delay 0.1', 'log enB2', 'delay 0.1',
             'log enA1', 'delay 0.1', 'log enA2', 'delay 0.1', 'log enB1', 'delay 0.1'],
            output_to_file=prefix+"States/States5.txt")

    def testStates6(self):
        run_test(self, prefix+"States/States6.xml", 1,
            ['log enA', 'log enA1', 'log enA2', 'log enB', 'log enB1', 'log enB2', 'delay 0.1'],
            output_to_file=prefix+"States/States6.txt")

    def testStates7(self):
        run_test(self, prefix+"States/States7.xml", 2,
            ['log enA', 'log enA1', 'log exA1', 'log exA', 'log enA', 'log enA1', 'delay 0.1',
             'log exA1', 'log exA', 'log enA', 'log enA1', 'delay 0.1'],
            output_to_file=prefix+"States/States7.txt")

    def testStates8(self):
        run_test(self, prefix+"States/States8.xml", 6,
            ['log loop', 'delay 0.1', 'log loop', 'delay 0.1', 'log loop', 'delay 0.1',
             'log loop', 'delay 0.1', 'log loop', 'delay 0.1',
             'log 100,200,300,400,500', 'delay 0.1'],
            output_to_file=prefix+"States/States8.txt")

    def testTransitions1(self):
        run_test(self, prefix+"Transitions/Transitions1.xml", 1,
            ['log enS', 'log enA', 'log ca', 'log exA', 'log exS', 'log ta',
             'log enT', 'log enB', 'delay 0.1'],
            output_to_file=prefix+"Transitions/Transitions1.txt")

    def testTransitions2(self):
        run_test(self, prefix+"Transitions/Transitions2.xml", 2,
            ['log enS', 'log enA', 'log exA', 'log enB', 'delay 0.1',
             'log ca', 'log exB', 'log exS', 'log ta', 'log enT', 'log enB', 'delay 0.1'],
            output_to_file=prefix+"Transitions/Transitions2.txt")

    def testTransitions3(self):
        run_test(self, prefix+"Transitions/Transitions3.xml", 5,
            ['log b', 'log c1', 'delay 0.1', 'log c2', 'delay 0.1', 'log B',
             'delay 0.1', 'log c2', 'delay 0.1', 'log B', 'delay 0.1'],
            output_to_file=prefix+"Transitions/Transitions3.txt")

    def testTransitions4(self):
        run_test(self, prefix+"Transitions/Transitions4.xml", 2,
            ['log enS', 'log condDefault', 'log tranDefault', 'log enA',
             'log duS', 'log condInner', 'log exA', 'log tranInner', 'log enA', 'delay 0.1',
             'log duS', 'log condInner', 'log exA', 'log tranInner', 'log enA', 'delay 0.1'],
            output_to_file=prefix+"Transitions/Transitions4.txt")

    def testTransitions5(self):
        run_test(self, prefix+"Transitions/Transitions5.xml", 1,
            ['log enS', 'log enA', 'log duS', 'log condInner', 'log exA',
             'log tranInner', 'log enA', 'delay 0.1'],
            output_to_file=prefix+"Transitions/Transitions5.txt")

    def testTransitions6(self):
        run_test(self, prefix+"Transitions/Transitions6.xml", 2,
            ['log enS', 'log enA', 'log duS', 'log exA', 'log enB', 'delay 0.1',
             'log duS', 'log innerCond', 'log exB', 'log innerTran', 'log enA', 'delay 0.1'],
            output_to_file=prefix+"Transitions/Transitions6.txt")

    def testTransitions7(self):
        run_test(self, prefix+"Transitions/Transitions7.xml", 1,
            ['log enS', 'log enT', 'delay 0.1'],
            output_to_file=prefix+"Transitions/Transitions7.txt")

    def testTransitions8(self):
        run_test(self, prefix+"Transitions/Transitions8.xml", 5,
            ['log enS', 'log duS', 'log ca1', 'delay 0.1', 'log duS', 'log ca1', 'delay 0.1',
             'log duS', 'log ca2', 'delay 0.1', 'log duS', 'log ca2', 'delay 0.1',
             'log enT', 'delay 0.1'],
            output_to_file=prefix+"Transitions/Transitions8.txt")

    def testJunctions1(self):
        run_test(self, prefix+"Junctions/Junctions1.xml", 1,
            ['log enA', 'log enD', 'delay 0.1'],
            output_to_file=prefix+"Junctions/Junctions1.txt")

    def testJunctions2(self):
        run_test(self, prefix+"Junctions/Junctions2.xml", 2,
            ['log enA', 'log exA', 'log enB', 'delay 0.1', 'log conBJun', 'log conJunC',
             'log exB', 'log tranBJun', 'log tranJunC', 'log enC', 'delay 0.1'],
            output_to_file=prefix+"Junctions/Junctions2.txt")

    def testJunctions3(self):
        run_test(self, prefix+"Junctions/Junctions3.xml", 1,
            ['log t1', 'log t2', 'log t1', 'log t2', 'log t1', 'log t2', 'log t1',
             'log t4', 'delay 0.1'],
            output_to_file=prefix+"Junctions/Junctions3.txt")

    def testJunctions4(self):
        run_test(self, prefix+"Junctions/Junctions4.xml", 1,
            ['log enA', 'log enA1', 'log duA', 'log c1', 'log c2', 'log exA1', 'log exA',
             'log t1', 'log t2', 'log enC', 'log enC2', 'delay 0.1'],
            output_to_file=prefix+"Junctions/Junctions4.txt")

    def testJunctions5(self):
        run_test(self, prefix+"Junctions/Junctions5.xml", 1,
            ['log enA', 'log enA1', 'log duA', 'log ca', 'log exA1', 'log enA2', 'delay 0.1'],
            output_to_file=prefix+"Junctions/Junctions5.txt")

    def testJunctions6(self):
        run_test(self, prefix+"Junctions/Junctions6.xml", 1,
            ['log enA', 'log ca', 'log ca', 'log exA', 'log ta2', 'log ta4',
             'log enC', 'delay 0.1'],
            output_to_file=prefix+"Junctions/Junctions6.txt")

    def testJunctions7(self):
        run_test(self, prefix+"Junctions/Junctions7.xml", 1,
            ['log enA', 'log exA', 'log xle2', 'log yeq2', 'log zge2', 'log enC', 'delay 0.1'],
            output_to_file=prefix+"Junctions/Junctions7.txt")

    def testJunctions8(self):
        run_test(self, prefix+"Junctions/Junctions8.xml", 3,
            ['log enA', 'log ca1', 'log exA', 'log enC', 'delay 0.1',
             'log exC', 'log enA', 'delay 0.1',
             'log duA', 'log ca2', 'log exA', 'log enC', 'delay 0.1'],
            output_to_file=prefix+"Junctions/Junctions8.txt")

    def testEvent1(self):
        run_test(self, prefix+"Events/Event1.xml", 1,
            ['log b', 'log a', 'log en_A2', 'log tb', 'log en_B2', 'delay 0.1'],
            output_to_file=prefix+"Events/Events1.txt")

    def testEvent2(self):
        run_test(self, prefix+"Events/Event2.xml", 1,
            ['log b', 'log a', 'log en_A2', 'log c', 'log en_C2', 'log tb',
             'log en_B2', 'delay 0.1'],
            output_to_file=prefix+"Events/Events2.txt")

    def testEvent3(self):
        run_test(self, prefix+"Events/Event3.xml", 1,
            ['log b', 'log a1', 'log a2', 'log en_A2', 'log tb', 'log en_B2', 'delay 0.1'],
            output_to_file=prefix+"Events/Events3.txt")

    def testEvent4(self):
        run_test(self, prefix+"Events/Event4.xml", 1,
            ['log b', 'log a1', 'log c', 'log en_C2', 'log a2', 'log en_A2',
             'log tb', 'log en_B2', 'delay 0.1'],
            output_to_file=prefix+"Events/Events4.txt")

    def testEvent5(self):
        run_test(self, prefix+"Events/Event5.xml", 1,
            ['log en_A2', 'log b', 'log en_A3', 'log tb', 'log en_B2', 'delay 0.1'],
            output_to_file=prefix+"Events/Events5.txt")

    def testEvent6(self):
        run_test(self, prefix+"Events/Event6.xml", 1,
            ['log a 5', 'log a 4', 'log a 3', 'log a 2', 'log a 1', 'log a 0',
             'log en_A2 0', 'delay 0.1'],
            output_to_file=prefix+"Events/Events6.txt")

    def testDirectedEvent1(self):
        run_test(self, prefix+"Events/DirectedEvent1.xml", 1,
            ['log en_A1', 'log en_B1', 'log en_C1',
             'log ex_C1', 'log en_C2', 'log ex_B1', 'log en_B2', 'log ex_A1', 'log en_A2',
             'log ex_A2', 'log en_A1', 'log ex_B2', 'log en_B1', 'log ex_C2', 'log en_C1',
             'delay 0.1'],
            output_to_file=prefix+"Events/DirectedEvent1.txt")

    def testDirectedEvent2(self):
        run_test(self, prefix+"Events/DirectedEvent2.xml", 1,
            ['log en_A1', 'log en_B1_A1', 'log en_C1_A1', 'log ex_C1_A1', 'log en_C2_A2',
             'log ex_B1_A1', 'log en_B2_A2', 'log ex_A1', 'log en_A2', 'log ex_A2',
             'log en_A1', 'log ex_B2_A2', 'log en_B1_A1', 'log ex_C2_A2', 'log en_C1_A1',
             'delay 0.1'],
            output_to_file=prefix+"Events/DirectedEvent2.txt")
        
    def testDirectedEvent3(self):
        run_test(self, prefix+"Events/DirectedEvent3.xml", 1,
            ['log en_A1', 'log en_B1', 'log ex_B1',
             'log en_B2', 'log ex_A1', 'log en_A2', 'delay 0.1'],
            output_to_file=prefix+"Events/DirectedEvent3.txt")

    def testDirectedEvent4(self):
        run_test(self, prefix+"Events/DirectedEvent4.xml", 1,
            ['log en_A1', 'log en_B2', 'log en_B21',
             'log ex_B21', 'log ex_B2', 'log en_B4', 'log ex_A1', 'log en_A2', 'delay 0.1'],
            output_to_file=prefix+"Events/DirectedEvent4.txt")

    def testDirectedEvent5(self):
        run_test(self, prefix+"Events/DirectedEvent5.xml", 1,
            ['log en_A1', 'log en_B2', 'log en_B21',
             'log ex_B21', 'log en_B22', 'log ex_A1', 'log en_A2', 'delay 0.1'],
            output_to_file=prefix+"Events/DirectedEvent5.txt")

    def testDirectedEvent6(self):
        run_test(self, prefix+"Events/DirectedEvent6.xml", 1,
            ['log a', 'log c', 'delay 0.1'],
            output_to_file=prefix+"Events/DirectedEvent6.txt")

    def testFunction1(self):
        run_test(self, prefix+"Functions/Function1.xml", 1,
            ['log en_A', 'log en_B', 'delay 0.1'],
            output_to_file=prefix+"Functions/Function1.txt")

    def testFunction2(self):
        run_test(self, prefix+"Functions/Function2.xml", 1,
            ['log en_A', 'log en_B', 'delay 0.1'],
            output_to_file=prefix+"Functions/Function2.txt")

    def testFunction3(self):
        run_test(self, prefix+"Functions/Function3.xml", 1,
            ['log en_A', 'log en_B', 'delay 0.1'],
            output_to_file=prefix+"Functions/Function3.txt")

    def testFunction4(self):
        run_test(self, prefix+"Functions/Function4.xml", 1,
            ['log en_A', 'log en_B', 'delay 0.1'],
            output_to_file=prefix+"Functions/Function4.txt")

    def testFunction5(self):
        run_test(self, prefix+"Functions/Function5.xml", 1,
            ['log en_A', 'log en_B', 'delay 0.1'],
            output_to_file=prefix+"Functions/Function5.txt")

    def testFunction6(self):
        run_test(self, prefix+"Functions/Function6.xml", 1,
            ['log en_A', 'log en_B', 'delay 0.1'],
            output_to_file=prefix+"Functions/Function6.txt")

    def testGraphicalFunction1(self):
        run_test(self, prefix+"Functions/GraphicalFunction1.xml", 1,
            ['log en_A', 'log en_B', 'delay 0.1'],
            output_to_file=prefix+"Functions/GraphicalFunction1.txt")
        
    def testGraphicalFunction2(self):
        run_test(self, prefix+"Functions/GraphicalFunction2.xml", 1,
            ['log en_A', 'log set', 'log set', 'log set', 'log en_B',
             'log 100 200 300 0 0', 'delay 0.1'],
            output_to_file=prefix+"Functions/GraphicalFunction2.txt")

    def testGraphicalFunction3(self):
        run_test(self, prefix+"Functions/GraphicalFunction3.xml", 1,
            ['log en_A', 'log en_B', 'log 4', 'log 9', 'delay 0.1'],
            output_to_file=prefix+"Functions/GraphicalFunction3.txt")

    def testGraphicalFunction4(self):
        run_test(self, prefix+"Functions/GraphicalFunction4.xml", 1,
            ['log en_A', 'log ack', 'log ack', 'log ack', 'log ack', 'log ack',
             'log en_B', 'delay 0.1'],
            output_to_file=prefix+"Functions/GraphicalFunction4.txt")

    def testTemporal1(self):
        run_test(self, prefix+"Temporal/Temporal1.xml", 10,
            ['log en_A', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1',
             'log en_B', 'delay 0.1', 'log du_B', 'delay 0.1', 'log du_B', 'delay 0.1',
             'log en_A', 'delay 0.1', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1',
             'log en_B', 'delay 0.1', 'log du_B', 'delay 0.1'],
            output_to_file=prefix+"Temporal/Temporal1.txt")

    def testTemporal2(self):
        random.seed(0)  # for repeatability
        run_test(self, prefix+"Temporal/Temporal2.xml", 10,
            ['log en_A', 'log Picked 4', 'delay 1', 'delay 1', 'delay 1', 'delay 1',
             'log en_B', 'log Picked 4', 'delay 1', 'delay 1', 'delay 1', 'delay 1',
             'log en_A', 'log Picked 1', 'delay 1',
             'log en_B', 'log Picked 3', 'delay 1'],
            output_to_file=prefix+"Temporal/Temporal2.txt")

    def testTemporal3(self):
        run_test(self, prefix+"Temporal/Temporal3.xml", 10,
            ['log en_A', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1',
             'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1',
             'log en_B', 'delay 0.1', 'log du_B', 'delay 0.1', 'log du_B', 'delay 0.1',
             'log en_A', 'delay 0.1', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1'],
            output_to_file=prefix+"Temporal/Temporal3.txt")

    def testTemporal4(self):
        run_test(self, prefix+"Temporal/Temporal4.xml", 10,
            ['log en_A', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1',
             'log en_B', 'delay 0.1', 'log du_B', 'delay 0.1', 'log du_B', 'delay 0.1',
             'log du_B', 'delay 0.1', 'log du_B', 'delay 0.1', 'log du_B', 'delay 0.1',
             'log du_B', 'delay 0.1', 'log du_B', 'delay 0.1'],
            output_to_file=prefix+"Temporal/Temporal4.txt")

    def testTemporal5(self):
        run_test(self, prefix+"Temporal/Temporal5.xml", 10,
            ['log en_A', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1',
             'log en_B', 'delay 0.1', 'log en_A', 'delay 0.1',
             'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1',
             'log en_B', 'delay 0.1', 'log en_A', 'delay 0.1'],
            output_to_file=prefix+"Temporal/Temporal5.txt")

    def testTemporal6(self):
        run_test(self, prefix+"Temporal/Temporal6.xml", 5,
            ['log en_A', 'log en_A', 'delay 0.1', 'log en_A', 'delay 0.1', 'log en_A',
             'delay 0.1', 'log en_A', 'delay 0.1', 'log en_A', 'delay 0.1'],
            output_to_file=prefix+"Temporal/Temporal6.txt")
    
    def testTemporal7(self):
        run_test(self, prefix+"Temporal/Temporal7.xml", 5,
            ['log en_A', 'log en_B', 'delay 0.1', 'log en_A', 'delay 0.1', 'log en_B',
             'delay 0.1', 'log en_A', 'delay 0.1', 'log en_B', 'delay 0.1'],
            output_to_file=prefix+"Temporal/Temporal7.txt")

    def testTemporal8(self):
        run_test(self, prefix+"Temporal/Temporal8.xml", 10,
            ['log en_A', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1',
             'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1',
             'log en_B', 'delay 0.1', 'log du_B', 'delay 0.1', 'log du_B', 'delay 0.1',
             'log en_A', 'delay 0.1', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1'],
            output_to_file=prefix+"Temporal/Temporal8.txt")

    def testEarlyReturn1(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn1.xml", 1,
            ['log en_A', 'log en_A1', 'log ex_A1', 'log ex_A', 'log en_B', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn1.txt")

    def testEarlyReturn2(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn2.xml", 1,
            ['log en_A', 'log en_A1', 'log E', 'log ex_A1', 'log ex_A', 'log en_B', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn2.txt")

    def testEarlyReturn3(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn3.xml", 1,
            ['log en_A 1', 'log ex_A 2', 'log en_C 2', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn3.txt")

    def testEarlyReturn4(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn4.xml", 1,
            ['log ca', 'log ta', 'log en_A2', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn4.txt")

    def testEarlyReturn5(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn5.xml", 1,
            ['log en_A', 'log en_A1', 'log ex_A1', 'log ex_A', 'log en_B', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn5.txt")

    def testEarlyReturn6(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn6.xml", 1,
            ['log en_A', 'log en_A1', 'log ex_A1', 'log loop', 'log ex_A', 'log en_A',
             'log en_A1', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn6.txt")

    def testEarlyReturn7(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn7.xml", 2,
            ['log en_A', 'log en_A1', 'log ex_A1', 'log en_A2', 'delay 0.1',
             'log ex_A2', 'log loop', 'log ex_A', 'log en_A', 'log en_A1', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn7.txt")

    def testEarlyReturn8(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn8.xml", 1,
            ['log a', 'log c', 'log du_A1', 'log b', 'log a', 'log c', 'log ex_A1',
             'log en_A2', 'log en_C2', 'log tb', 'log en_B2', 'log en_C3', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn8.txt")

    def testEarlyReturn9(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn9.xml", 1,
            ['log en_A', 'log en_A1', 'log pre', 'log ex_A1', 'log ex_A', 'log en_B', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn9.txt")

    def testEarlyReturn10(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn10.xml", 1,
            ['log en_A', 'log en_A1', 'log pre', 'log ex_A1', 'log ex_A', 'log en_B', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn10.txt")

    def testEarlyReturn11(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn11.xml", 2,
            ['log en_A', 'log en_A1', 'log ex_A1', 'log en_A2', 'log en_A2a', 'delay 0.1',
             'log ex_A2a', 'log ex_A2', 'log loop', 'log ex_A', 'log en_A', 'log en_A1', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn11.txt")

    def testEarlyReturn12(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn12.xml", 1,
            ['log enB', 'log enC', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn12.txt")

    def testEarlyReturn13(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn13.xml", 1,
            ['log F', 'log exA1', 'log exA1', 'log exA1', 'log exA1', 'log exA1',
             'log exA1_done', 'log enA3', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn13.txt")

    def testEarlyReturn14(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn14.xml", 1,
            ['log en_A', 'log en_A1', 'log loop', 'log ex_A1', 'log ex_A', 'log en_A',
             'log en_A1', 'log ca', 'log ex_A1', 'log ta', 'log en_A2', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn14.txt")

    def testEarlyReturn15(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn15.xml", 1,
            ['log enS', 'log enA1', 'log enA1a', 'log enA2', 'log ca', 'log enB', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn15.txt")

    def testEarlyReturn16(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn16.xml", 1,
            ['log en_A', 'log en_A1', 'log outA1', 'log ex_A1', 'log en_A3', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn16.txt")

    def testEarlyReturn17(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn17.xml", 2,
            ['log en_A', 'log en_A1', 'log ex_A1', 'log en_A2', 'delay 0.1',
             'log outA2', 'log ex_A2', 'log en_A3', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn17.txt")

    def testEarlyReturn18(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn18.xml", 1,
            ['log enS', 'log duS', 'log ca1', 'log exS', 'log enT', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn18.txt")

    def testEarlyReturn19(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn19.xml", 1,
            ['log enS', 'log duS', 'log ca1', 'log ca2', 'log exS', 'log enT', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn19.txt")

    def testEarlyReturn20(self):
        run_test(self, prefix+"EarlyReturn/EarlyReturn20.xml", 1,
            ['log enS', 'log duS', 'log ca1', 'log ca2', 'log exS', 'log enT', 'delay 0.1'],
            output_to_file=prefix+"EarlyReturn/EarlyReturn20.txt")

    def testDSM1(self):
        io_filter = lambda s: False
        run_test(self, prefix+"Data/DSM1.xml", 20,
            ['log 2', 'delay 0.1', 'log 4', 'delay 0.1', 'log 5', 'delay 0.1',
             'log 7', 'delay 0.1', 'log 8', 'delay 0.1', 'log 10', 'delay 0.1'], io_filter=io_filter,
            output_to_file=prefix+"Data/DSM1.txt")

    def testDSM2(self):
        io_filter = lambda s: False
        run_test(self, prefix+"Data/DSM2.xml", 20,
            ['log 1', 'delay 0.1', 'log 3', 'delay 0.1', 'log 4', 'delay 0.1',
             'log 6', 'delay 0.1', 'log 7', 'delay 0.1', 'log 9', 'delay 0.1'], io_filter=io_filter,
            output_to_file=prefix+"Data/DSM2.txt")

    def testDSM3(self):
        io_filter = lambda s: False
        run_test(self, prefix+"Data/DSM3.xml", 20,
            ['log 3 2', 'delay 0.1', 'log 3 5', 'delay 0.1', 'log 8 5', 'delay 0.1',
             'log 8 13', 'delay 0.1', 'log 21 13', 'delay 0.1', 'log 21 34', 'delay 0.1'], io_filter=io_filter,
            output_to_file=prefix+"Data/DSM3.txt")

    def testDSM4(self):
        io_filter = lambda s: False
        run_test(self, prefix+"Data/DSM4.xml", 35,
            ['log A1', 'log C1', 'log B2', 'log D4', 'delay 0.1',
             'log A4', 'log C4', 'delay 0.1', 'log B5', 'log D7', 'delay 0.1'], io_filter=io_filter,
            output_to_file=prefix+"Data/DSM4.txt")

    def testDSM5(self):
        io_filter = lambda s: False
        run_test(self, prefix+"Data/DSM5.xml", 34,
            ['log 4 2', 'delay 0.1', 'log 4 4', 'delay 0.1', 'log 5 4', 'delay 0.1',
             'log 5 6', 'delay 0.1', 'log 6 6', 'delay 0.1', 'log 6 8', 'delay 0.1'], io_filter=io_filter,
            output_to_file=prefix+"Data/DSM5.txt")

    def testDSM6(self):
        io_filter = lambda s: False
        run_test(self, prefix+"Data/DSM6.xml", 36,
            ['log en_A 0 0', 'log en_A1 3 0', 'log en_B 4 4', 'log du_A1 4 0', 'delay 0.1',
             'log en_A 4 -1', 'log du_A1 3 -1', 'delay 0.1',
             'log en_B 4 -1', 'log du_A1 4 0', 'delay 0.1'], io_filter=io_filter,
            output_to_file=prefix+"Data/DSM6.txt")

    def testCommunication1(self):
        io_filter = lambda s: False
        run_test(self, prefix+"Data/Communication1.xml", 62,
            ['log en_A', 'log en_A1', 'log en_B', 'log 2 1', 'delay 0.1',
             'log en_A', 'log 2 2', 'delay 0.1', 'log en_B', 'log 3 2', 'delay 0.1',
             'log en_A', 'log 3 3', 'delay 0.1', 'log en_B', 'log 4 3', 'delay 0.1',
             'log en_A', 'log 4 4', 'delay 0.1'], io_filter=io_filter,
            output_to_file=prefix+"Data/Communication1.txt")
        
    def testCommunication2(self):
        io_filter = lambda s: False
        run_test(self, prefix+"Data/Communication2.xml", 65,
            ['log en_A', 'log en_A1', 'log en_B', 'log 1 2 2 1', 'delay 0.1',
             'log en_A', 'log 1 2 2 2', 'delay 0.1',
             'log en_B', 'log 1 2 3 2', 'delay 0.1',
             'log en_A', 'log 1 2 3 3', 'delay 0.1',
             'log en_B', 'log 1 2 4 3', 'delay 0.1'], io_filter=io_filter,
            output_to_file=prefix+"Data/Communication2.txt")

    def testCommunication3(self):
        io_filter = lambda s: False
        run_test(self, prefix+"Data/Communication3.xml", 62,
            ['log en_A', 'log en_A1', 'log en_B', 'log 2 1', 'delay 0.1',
             'log en_A', 'log 2 2', 'delay 0.1', 'log en_B', 'log 3 2', 'delay 0.1',
             'log en_A', 'log 3 3', 'delay 0.1', 'log en_B', 'log 4 3', 'delay 0.1',
             'log en_A', 'log 4 4', 'delay 0.1'], io_filter=io_filter,
            output_to_file=prefix+"Data/Communication3.txt")

    def testCommunication4(self):
        io_filter = lambda s: False
        run_test(self, prefix+"Data/Communication4.xml", 105,
            ['log en_A', 'log en_A1', 'log en_B', 'log 2 2', 'delay 0.1',
             'log en_A', 'log 2 4', 'delay 0.1', 'log en_B', 'log 3 4', 'delay 0.1',
             'log en_A', 'log 3 6', 'delay 0.1', 'log en_B', 'log 4 6', 'delay 0.1',
             'log en_A', 'log 4 8', 'delay 0.1'], io_filter=io_filter,
            output_to_file=prefix+"Data/Communication4.txt")

    def testCommunication5(self):
        io_filter = lambda s: False
        run_test(self, prefix+"Data/Communication5.xml", 147,
           ['log en_A', 'log en_C', 'log en_A1', 'log en_B', 'log 2 2 2', 'delay 0.1',
            'log en_A', 'log 2 4 4', 'delay 0.1', 'log en_B', 'log 3 4 10', 'delay 0.1',
            'log en_A', 'log 3 6 20', 'delay 0.1', 'log en_B', 'log 4 6 42', 'delay 0.1',
            'log en_A', 'log 4 8 84', 'delay 0.1'], io_filter=io_filter,
           output_to_file=prefix+"Data/Communication5.txt")

    def testCommunication6(self):
        io_filter = lambda s: False
        run_test(self, prefix+"Data/Communication6.xml", 120,
            ['log en_A', 'log en_A1', 'log en_C', 'log en_B', 'log 2 1', 'log 1', 'delay 0.1',
             'log en_A', 'log 2 2', 'log 1', 'delay 0.1',
             'log en_B', 'log 3 2', 'log 2', 'delay 0.1',
             'log en_A', 'log 3 3', 'log 2', 'delay 0.1',
             'log en_B', 'log 4 3', 'log 3', 'delay 0.1',
             'log en_A', 'log 4 4', 'log 3', 'delay 0.1'], io_filter=io_filter,
            output_to_file=prefix+"Data/Communication6.txt")

    def testMessages1(self):
        run_test(self, prefix+"Messages/Messages1.xml", 2,
            ['log en_A', 'log en_B', 'delay 0.1', 'delay 0.1'],
            output_to_file=prefix+"Messages/Messages1.txt")

    def testMessages2(self):
        run_test(self, prefix+"Messages/Messages2.xml", 3,
            ['log en_A', 'log en_B', 'delay 0.1', 'log en_C',
             'delay 0.1', 'log en_D', 'delay 0.1'],
            output_to_file=prefix+"Messages/Messages2.txt")

    def testMessages3(self):
        io_filter = lambda s: False
        run_test(self, prefix+"Messages/Messages3.xml", 40,
            ['log en_A', 'log en_A0', 'delay 1', 'delay 1', 'delay 1',
             'log en_A1', 'delay 1', 'log en_A2', 'delay 1', 'delay 1'], io_filter=io_filter,
            output_to_file=prefix+"Messages/Messages3.txt")
    
    def testMessages4(self):
        run_test(self, prefix+"Messages/Messages4.xml", 3,
            ['log en_A', 'log en_B', 'delay 0.1', 'log en_C', 'delay 0.1', 'delay 0.1'],
            output_to_file=prefix+"Messages/Messages4.txt")

    def testMessages5(self):
        run_test(self, prefix+"Messages/Messages5.xml", 4,
            ['log en_A', 'log en_B', 'delay 0.1', 'delay 0.1', 'log en_C', 'delay 0.1', 'delay 0.1'],
            output_to_file=prefix+"Messages/Messages5.txt")

    def testMessages6(self):
        run_test(self, prefix+"Messages/Messages6.xml", 5,
            ['log en_A', 'log en_B', 'delay 0.1', 'delay 0.1', 'log en_C', 'delay 0.1',
             'log en_D', 'delay 0.1', 'log en_E', 'delay 0.1'],
            output_to_file=prefix+"Messages/Messages6.txt")

    def testMessages7(self):
        run_test(self, prefix+"Messages/Messages7.xml", 4,
            ['log en_A', 'log en_B', 'delay 0.1', 'log en_C', 'delay 0.1',
             'log en_D', 'delay 0.1', 'delay 0.1'],
            output_to_file=prefix+"Messages/Messages7.txt")

    def testMessages8(self):
        io_filter = lambda s: False
        run_test(self, prefix+"Messages/Messages8.xml", 40,
            ['log en_A', 'log en_A0', 'delay 1', 'delay 1', 'delay 1', 'log en_A1',
             'delay 1', 'log en_A2', 'delay 1', 'log en_A3', 'delay 1'], io_filter=io_filter,
            output_to_file=prefix+"Messages/Messages8.txt")

    def testMessages9(self):
        io_filter = lambda s: False
        run_test(self, prefix+"Messages/Messages9.xml", 40,
            ['log en_A', 'log en_A0', 'log en_B', 'delay 1', 'delay 1', 'delay 1', 'log en_A1',
             'delay 1', 'log en_A2', 'delay 1', 'log en_A3', 'delay 1'], io_filter=io_filter,
            output_to_file=prefix+"Messages/Messages9.txt")

    def testMessages10(self):
        io_filter = lambda s: False
        run_test(self, prefix+"Messages/Messages10.xml", 4,
            ['log A', 'log B', 'delay 0.1', 'log B', 'delay 0.1', 'log C',
             'delay 0.1', 'log D', 'delay 0.1'], io_filter=io_filter,
            output_to_file=prefix+"Messages/Messages10.txt")

    def testContinuous1(self):
        run_test(self, prefix+"Continuous/Continuous1.xml", 2,
            ['log enA 0.000 0.000', 'delay 0.5',
             'log conAB1 1.000 0.500', 'log exA 1.000 0.500', 'log tranAB1 1.000 0.500',
             'log enB 1.000 0.500', 'log enB1 0.000 0.500', 'delay 1.0'],
            output_to_file=prefix+"Continuous/Continuous1.txt")

    def testContinuous2(self):
        run_test(self, prefix+"Continuous/Continuous2.xml", 3,
            ['log enA 0.000 1.000', 'delay 0.524', 'delay 0.0',
             'log conAB1 0.500 0.866', 'log exA 0.500 0.866', 'log tranAB1 0.500 0.866',
             'log enB 0.500 0.866', 'log enB1 0.000 0.866', 'delay 1.0'],
            output_to_file=prefix+"Continuous/Continuous2.txt")

    def testContinuous3(self):
        run_test(self, prefix+"Continuous/Continuous3.xml", 2,
            ['log enA 0.000 0.000', 'delay 1.414',
             'log conAB1 1.414 1.000', 'log exA 1.414 1.000', 'log tranAB1 1.414 1.000',
             'log enB 1.414 1.000', 'log enB1 0.000 1.000', 'delay 1.0'],
            output_to_file=prefix+"Continuous/Continuous3.txt")

    def testContinuous4(self):
        run_test(self, prefix+"Continuous/Continuous4.xml", 2,
            ['log enA 0.000 0.000', 'delay 1.0',
             'log conAB 1.000 0.500', 'log exA 1.000 0.500', 'log tranAB 1.000 0.500',
             'log enB 1.000 0.500', 'log enB1 0.000 0.500', 'delay 1.0'],
            output_to_file=prefix+"Continuous/Continuous4.txt")

    def testContinuous5(self):
        run_test(self, prefix+"Continuous/Continuous5.xml", 3,
            ['log enA', 'log enA1', 'delay 1.0', 'log enA2', 'delay 1.0',
             'log exA', 'log enB', 'delay 1.0'],
            output_to_file=prefix+"Continuous/Continuous5.txt")

    def testContinuous6(self):
        run_test(self, prefix+"Continuous/Continuous6.xml", 3,
            ['log enA', 'log enA1', 'delay 1.0', 'log enA2', 'delay 0.5',
             'log condA2B', 'log exA', 'log enB', 'delay 1.0'],
            output_to_file=prefix+"Continuous/Continuous6.txt")

    def testTriggerEdge1(self):
        run_sim_test(self, prefix+"Triggered/TriggerEdge1.xml", 200, {
            0: {'y': 0, 'signal': 0.0},
            0.5: {'y': 1, 'signal': 1.0},
            1.0: {'y': 1, 'signal': 0.0},
            1.5: {'y': 2, 'signal': 1.0},
            2.0: {'y': 2, 'signal': 0.0},
            2.5: {'y': 3, 'signal': 1.0},
            3.0: {'y': 3, 'signal': 0.0},
            3.5: {'y': 4, 'signal': 1.0},
            4.0: {'y': 4, 'signal': 0.0},
            4.5: {'y': 5, 'signal': 1.0}
        }, output_to_file=prefix+"Triggered/TriggerEdge1.txt")

    def testTriggerEdge2(self):
        run_sim_test(self, prefix+"Triggered/TriggerEdge2.xml", 200, {
            0: {'y': 0, 'signal': 1.0},
            0.5: {'y': 1, 'signal': 0.0},
            1.0: {'y': 1, 'signal': 1.0},
            1.5: {'y': 2, 'signal': 0.0},
            2.0: {'y': 2, 'signal': 1.0},
            2.5: {'y': 3, 'signal': 0.0},
            3.0: {'y': 3, 'signal': 1.0},
            3.5: {'y': 4, 'signal': 0.0},
            4.0: {'y': 4, 'signal': 1.0},
            4.5: {'y': 5, 'signal': 0.0}
        }, output_to_file=prefix+"Triggered/TriggerEdge2.txt")

    def testTriggerEdge3(self):
        run_sim_test(self, prefix+"Triggered/TriggerEdge3.xml", 300, {
            0: {'y': 0, 'signal': 0.0},
            0.3: {'y': 1, 'signal': 1.0},
            0.8: {'y': 2, 'signal': 0.0},
            1.3: {'y': 3, 'signal': 1.0},
            1.8: {'y': 4, 'signal': 0.0},
            2.3: {'y': 5, 'signal': 1.0}
        }, output_to_file=prefix+"Triggered/TriggerEdge3.txt")

    def testTriggerEdge4(self):
        run_sim_test(self, prefix+"Triggered/TriggerEdge4.xml", 1000, {
            0: {'a': 0.0},
            0.2: {'a': 0.0},
            0.4: {'a': 2.0},
            0.6: {'a': 3.0},
            0.9: {'a': 1.0},
            1.2: {'a': 0.0},
            1.4: {'a': 2.0},
            1.6: {'a': 3.0},
            1.9: {'a': 1.0}
        }, output_to_file=prefix+"Triggered/TriggerEdge4.txt")

    def testTriggerEdge5(self):
        run_sim_test(self, prefix+"Triggered/TriggerEdge5.xml", 60, {
            0.1: {'y': 0.0, 'signal': 0.0},
            3.9: {'y': 0.0, 'signal': 0.0},
            4.1: {'y': 1.0, 'signal': 1.0},
            5.9: {'y': 1.0, 'signal': 1.0},
            6.1: {'y': 2.0, 'signal': 0.0}
        }, output_to_file=prefix+"Triggered/TriggerEdge5.txt")

    def testTriggerEdge6(self):
        run_sim_test(self, prefix+"Triggered/TriggerEdge6.xml", 60, {
            0.1: {'y': 0.0, 'signal': 0.0},
            3.9: {'y': 0.0, 'signal': 0.0},
            4.1: {'y': 1.0, 'signal': 1.0},
            5.9: {'y': 1.0, 'signal': 1.0},
            6.1: {'y': 1.0, 'signal': 0.0}
        }, output_to_file=prefix+"Triggered/TriggerEdge6.txt")

    def testTriggerEdge7(self):
        run_sim_test(self, prefix+"Triggered/TriggerEdge7.xml", 60, {
            0.1: {'y': 0.0, 'signal': 0.0},
            3.9: {'y': 0.0, 'signal': 0.0},
            4.1: {'y': 0.0, 'signal': 1.0},
            5.9: {'y': 0.0, 'signal': 1.0},
            6.1: {'y': 1.0, 'signal': 0.0}
        }, output_to_file=prefix+"Triggered/TriggerEdge7.txt")

    def testTriggerEdge8(self):
        run_sim_test(self, prefix+"Triggered/TriggerEdge8.xml", 100, {
            0.1: {'y': 0.0},
            0.9: {'y': 0.0},
            1.1: {'y': 1.0},
            3.9: {'y': 1.0},
            4.1: {'y': 2.0}
        }, output_to_file=prefix+"Triggered/TriggerEdge8.txt")

    def testTriggerFun1(self):
        run_sim_test(self, prefix+"Triggered/TriggerFun1.xml", 400, {
            0: {'y': 1},
            0.1: {'y': 2},
            0.2: {'y': 3},
            0.3: {'y': 4},
            0.9: {'y': 4},
            1.0: {'y': 5},
            1.1: {'y': 6},
            1.2: {'y': 7},
            1.3: {'y': 8},
            1.9: {'y': 8},
            2.0: {'y': 9}
        }, output_to_file=prefix+"Triggered/TriggerFun1.txt")

    def testTriggerFun2(self):
        run_sim_test(self, prefix+"Triggered/TriggerFun2.xml", 100, {
            0.0: {'y': 4},
            0.1: {'y': 4},
            0.2: {'y': 4},
            0.3: {'y': 4},
            0.4: {'y': 4}
        }, output_to_file=prefix+"Triggered/TriggerFun2.txt")

    def testSettaDemo(self):
        run_test(self, prefix+"settaDemo.xml", 2,
            ['log B', 'log D', 'log A', 'log D', 'delay 0.1',
             'log B', 'log D', 'log A', 'log D', 'delay 0.1'],
            output_to_file=prefix+"settaDemo.txt")

    def testRTPS(self):
        random.seed(0)  # for repeatability
        io_filter = lambda s: s == 'WHC_out'
        run_test(self, prefix+"RTPS.xml", 500,
            ['IO WHC_out [0,0,0,0,0]', 'IO WHC_out [0,0,0,0,0]',
             'IO WHC_out [0,0,0,0,0]', 'IO WHC_out [0,0,0,0,0]', 'delay 0.1',
             'IO WHC_out [0,0,0,0,0]', 'IO WHC_out [0,0,0,0,0]', 'delay 0.1',
             'IO WHC_out [0,0,0,0,0]', 'IO WHC_out [0,0,0,0,0]', 'delay 0.1',
             'IO WHC_out [0,0,0,0,0]', 'IO WHC_out [0,0,0,0,0]', 'delay 0.1',
             'IO WHC_out [0,0,0,0,0]', 'IO WHC_out [0,0,0,0,0]', 'delay 0.1',
             'IO WHC_out [0,0,0,0,0]', 'IO WHC_out [0,0,0,0,0]', 'delay 0.1',
             'IO WHC_out [0,0,0,0,0]', 'IO WHC_out [0,0,0,0,0]', 'delay 0.1',
             'IO WHC_out [0,0,0,0,0]', 'IO WHC_out [0,0,0,0,0]', 'delay 0.1',
             'IO WHC_out [0,0,0,0,0]', 'IO WHC_out [0,0,0,0,0]', 'delay 0.1',
             'IO WHC_out [100,0,0,0,0]', 'IO WHC_out [100,0,0,0,0]', 'delay 0.1',
             'IO WHC_out [100,0,0,0,0]', 'IO WHC_out [100,0,0,0,0]', 'delay 0.1',
             'IO WHC_out [100,0,0,0,0]', 'IO WHC_out [100,0,0,0,0]', 'delay 0.1',
             'IO WHC_out [100,0,0,0,0]', 'IO WHC_out [100,0,0,0,0]', 'delay 0.1',
             'IO WHC_out [100,0,0,0,0]', 'IO WHC_out [100,0,0,0,0]', 'delay 0.1',
             'IO WHC_out [100,0,0,0,0]'], io_filter=io_filter,
            output_to_file=prefix+"RTPS.txt")

    def testStopWatch1(self):
        run_sim_test(self, prefix+"StopWatch1.xml", 6000, {
            0:   {'disp_cent': 0, 'start': 0.0, 'lap': 0.0},
            0.1: {'disp_cent': 6, 'start': 1.0, 'lap': 0.0},
            0.2: {'disp_cent': 15, 'start': 1.0, 'lap': 1.0},
            0.3: {'disp_cent': 15, 'start': 1.0, 'lap': 0.0},
            0.4: {'disp_cent': 36, 'start': 1.0, 'lap': 1.0},
            0.5: {'disp_cent': 46, 'start': 1.0, 'lap': 1.0},
            0.6: {'disp_cent': 56, 'start': 0.0, 'lap': 0.0},
            0.7: {'disp_cent': 66, 'start': 0.0, 'lap': 0.0},
            0.8: {'disp_cent': 76, 'start': 0.0, 'lap': 0.0},
            0.9: {'disp_cent': 86, 'start': 0.0, 'lap': 0.0},
            1.0: {'disp_cent': 96, 'start': 0.0, 'lap': 0.0},
            1.1: {'disp_cent': 6, 'start': 0.0, 'lap': 0.0},
        }, output_to_file=prefix+"StopWatch1.txt")

    def testStopWatch2(self):
        run_sim_test(self, prefix+"StopWatch2.xml", 6000, {
            0:   {'disp_cent': 0, 'start': 0.0, 'lap': 0.0},
            0.1: {'disp_cent': 2, 'start': 1.0, 'lap': 0.0},
            0.2: {'disp_cent': 18, 'start': 0.0, 'lap': 0.0},
            0.3: {'disp_cent': 22, 'start': 0.0, 'lap': 0.0},
            0.4: {'disp_cent': 22, 'start': 1.0, 'lap': 0.0},
            0.5: {'disp_cent': 0, 'start': 0.0, 'lap': 0.0},
            0.6: {'disp_cent': 0, 'start': 0.0, 'lap': 0.0},
            0.7: {'disp_cent': 2, 'start': 1.0, 'lap': 0.0},
            0.8: {'disp_cent': 18, 'start': 0.0, 'lap': 0.0},
            0.9: {'disp_cent': 22, 'start': 0.0, 'lap': 0.0},
            1.0: {'disp_cent': 22, 'start': 1.0, 'lap': 0.0},
        }, output_to_file=prefix+"StopWatch2.txt")

    def testStopWatch3(self):
        run_sim_test(self, prefix+"StopWatch3.xml", 6000, {
            0:   {'disp_cent': 0, 'start': 0.0, 'lap': 0.0},
            0.1: {'disp_cent': 5, 'start': 1.0, 'lap': 1.0},
            0.2: {'disp_cent': 5, 'start': 1.0, 'lap': 0.0},
            0.3: {'disp_cent': 26, 'start': 0.0, 'lap': 1.0},
            0.4: {'disp_cent': 35, 'start': 1.0, 'lap': 0.0},
            0.5: {'disp_cent': 35, 'start': 1.0, 'lap': 0.0},
            0.6: {'disp_cent': 35, 'start': 0.0, 'lap': 0.0},
            0.7: {'disp_cent': 36, 'start': 1.0, 'lap': 0.0},
            0.8: {'disp_cent': 46, 'start': 1.0, 'lap': 0.0},
            0.9: {'disp_cent': 56, 'start': 0.0, 'lap': 0.0},
            1.0: {'disp_cent': 66, 'start': 0.0, 'lap': 0.0},
            1.1: {'disp_cent': 76, 'start': 0.0, 'lap': 0.0},
        }, output_to_file=prefix+"StopWatch3.txt")

    def testStopWatch4(self):
        run_sim_test(self, prefix+"StopWatch4.xml", 6000, {
            0:   {'disp_cent': 0, 'start': 0.0, 'lap': 0.0},
            0.1: {'disp_cent': 6, 'start': 1.0, 'lap': 0.0},
            0.2: {'disp_cent': 16, 'start': 1.0, 'lap': 0.0},
            0.3: {'disp_cent': 26, 'start': 0.0, 'lap': 0.0},
            0.4: {'disp_cent': 35, 'start': 1.0, 'lap': 0.0},
            0.5: {'disp_cent': 0, 'start': 1.0, 'lap': 1.0},
            0.6: {'disp_cent': 0, 'start': 0.0, 'lap': 1.0},
            0.7: {'disp_cent': 1, 'start': 1.0, 'lap': 0.0},
            0.8: {'disp_cent': 11, 'start': 1.0, 'lap': 0.0},
            0.9: {'disp_cent': 21, 'start': 0.0, 'lap': 0.0},
            1.0: {'disp_cent': 31, 'start': 0.0, 'lap': 0.0},
            1.1: {'disp_cent': 41, 'start': 0.0, 'lap': 0.0},
        }, output_to_file=prefix+"StopWatch4.txt")

    def testStopWatch5(self):
        run_sim_test(self, prefix+"StopWatch5.xml", 6000, {
            0:   {'disp_cent': 0, 'start': 0.0, 'lap': 0.0},
            0.1: {'disp_cent': 6, 'start': 1.0, 'lap': 0.0},
            0.2: {'disp_cent': 15, 'start': 1.0, 'lap': 1.0},
            0.3: {'disp_cent': 15, 'start': 0.0, 'lap': 0.0},
            0.4: {'disp_cent': 15, 'start': 1.0, 'lap': 0.0},
            0.5: {'disp_cent': 15, 'start': 1.0, 'lap': 0.0},
            0.6: {'disp_cent': 15, 'start': 0.0, 'lap': 0.0},
            0.7: {'disp_cent': 15, 'start': 1.0, 'lap': 0.0},
            0.8: {'disp_cent': 46, 'start': 1.0, 'lap': 1.0},
            0.9: {'disp_cent': 56, 'start': 0.0, 'lap': 0.0},
            1.0: {'disp_cent': 66, 'start': 0.0, 'lap': 0.0},
            1.1: {'disp_cent': 76, 'start': 0.0, 'lap': 0.0},
        }, output_to_file=prefix+"StopWatch5.txt")

    def testStopWatch6(self):
        run_sim_test(self, prefix+"StopWatch6.xml", 6000, {
            0:   {'disp_cent': 0, 'start': 0.0, 'lap': 0.0},
            0.1: {'disp_cent': 6, 'start': 1.0, 'lap': 0.0},
            0.2: {'disp_cent': 15, 'start': 1.0, 'lap': 1.0},
            0.3: {'disp_cent': 15, 'start': 0.0, 'lap': 0.0},
            0.4: {'disp_cent': 15, 'start': 1.0, 'lap': 0.0},
            0.5: {'disp_cent': 15, 'start': 1.0, 'lap': 1.0},
            0.6: {'disp_cent': 15, 'start': 0.0, 'lap': 0.0},
            0.7: {'disp_cent': 36, 'start': 1.0, 'lap': 0.0},
            0.8: {'disp_cent': 46, 'start': 1.0, 'lap': 0.0},
            0.9: {'disp_cent': 56, 'start': 0.0, 'lap': 0.0},
            1.0: {'disp_cent': 66, 'start': 0.0, 'lap': 0.0},
            1.1: {'disp_cent': 76, 'start': 0.0, 'lap': 0.0},
        }, output_to_file=prefix+"StopWatch6.txt")

    def testSFSawtooth1(self):
        run_test(self, "./hhlpy/examples/simulink/sf_sawtooth1.xml", 3,
            ['delay 1.0', 'delay 1.0', 'delay 1.0'],
            output_to_file="./hhlpy/examples/simulink/sf_sawtooth1.txt")

    def testSFSawtooth2(self):
        run_test(self, "./hhlpy/examples/simulink/sf_sawtooth2.xml", 3,
            ['delay 1.0', 'delay 1.0', 'delay 1.0'],
            output_to_file="./hhlpy/examples/simulink/sf_sawtooth2.txt")

    def testSFBouncing(self):
        run_test(self, "./hhlpy/examples/simulink/sf_bouncing.xml", 3,
            ['delay 1.01', 'delay 0.909', 'delay 0.909'],
            output_to_file="./hhlpy/examples/simulink/sf_bouncing.txt")

    def testSFSawtooth3(self):
        run_test(self, "./hhlpy/examples/simulink/sf_sawtooth3.xml", 3,
            ['delay 1.0', 'delay 1.0', 'delay 1.0'],
            output_to_file="./hhlpy/examples/simulink/sf_sawtooth3.txt")

    def testCruiseControl(self):
        run_test(self, "./Examples/Simulink/CruiseControl.xml", 3,
            ['delay 100', 'delay 100', 'delay 100'],
            output_to_file="./Examples/Simulink/CruiseControl.txt")


if __name__ == "__main__":
    unittest.main()
