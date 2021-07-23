"""Unit test for sf_convert."""

import unittest
import random

from ss2hcsp.sf import sf_convert
from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.hcsp.pprint import pprint
from ss2hcsp.hcsp import module
from ss2hcsp.hcsp import hcsp
from ss2hcsp.tests.simulator_test import run_test as run_simulator_test
from ss2hcsp.hcsp.pprint import pprint


def run_test(self, filename, num_cycle, res, *, io_filter=None,
             print_chart=False, print_before_simp=False, print_after_simp=False,
             print_final=False, output_to_file=None):
    """Test function for Stateflow diagrams.

    filename : str - name of the XML file.
    num_cycle : int - number of cycles of Stateflow diagram to simulate.
    res : List[str] - expected output events.
    io_filter : str -> bool - (optional) filter for IO events to display.
    print_chart : bool - print parsed chart.
    print_before_simp : bool - print HCSP program before simplification.
    print_after_simp : bool - print HCSP program after simplification.
    print_final : bool - print HCSP program after optimization.
    output_to_file : str - (optional) name of file to output HCSP.

    """
    diagram = SL_Diagram(location=filename)
    procs_list = sf_convert.convert_diagram(
        diagram, print_chart=print_chart, print_before_simp=print_before_simp,
        print_after_simp=print_after_simp, print_final=print_final)

    # Optional: output converted HCSP to file
    if output_to_file is not None:
        modules = []
        module_insts = []
        for i, (procs, hp) in enumerate(procs_list):
            procs_lst = [hcsp.Procedure(name, hp) for name, hp in procs.items()]
            modules.append(module.HCSPModule("P" + str(i), code=hp, procedures=procs_lst))
            module_insts.append(module.HCSPModuleInst("P" + str(i), "P" + str(i), []))
        system = module.HCSPSystem(module_insts)
        declarations = module.HCSPDeclarations(modules + [system])

        with open(output_to_file, "w") as f:
            f.write(declarations.export())

    # Test result using simulator
    run_simulator_test(self, procs_list, num_cycle, res, io_filter=io_filter)


class SFConvertTest(unittest.TestCase):
    def testJunctionPriority(self):
        run_test(self, "./Examples/Stateflow/tests/junction_priority.xml", 1,
            ['log enA', 'log enD', 'delay 0.1'])

    def testNestedState(self):
        run_test(self, "./Examples/Stateflow/tests/nested_state.xml", 3,
            ['log enA', 'log enA1', 'log enB', 'log enB1', 'delay 0.1',
             'log enA', 'log enA1', 'delay 0.1', 'log enB', 'log enB1', 'delay 0.1'])

    def testNoEventTrig(self):
        run_test(self, "./Examples/Stateflow/tests/no_event_trig.xml", 1,
            ['log en_A2', 'log b', 'log en_A3', 'log tb', 'log en_B2', 'delay 0.1'])

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
            ['log en_A1', 'log ex_A1', 'log en_B', 'delay 0.1'])

    def testEarlyExitSameLevel(self):
        run_test(self, "./Examples/Stateflow/tests/early_exit_same_level.xml", 1,
            ['log en_A', 'log ex_A', 'log en_C', 'delay 0.1'])

    def testHistoryJunction(self):
        run_test(self, "./Examples/Stateflow/tests/history_junction.xml", 5,
            ['log b', 'log c1', 'delay 0.1', 'log c2', 'delay 0.1', 'log B',
             'delay 0.1', 'log c2', 'delay 0.1', 'log B', 'delay 0.1'])

    def testDirectedEvent(self):
        run_test(self, "./Examples/Stateflow/tests/directed_event.xml", 1,
            ['log en_A1', 'log en_B1', 'log en_C1',
             'log ex_C1', 'log en_C2', 'log ex_B1', 'log en_B2', 'log ex_A1', 'log en_A2',
             'log ex_A2', 'log en_A1', 'log ex_B2', 'log en_B1', 'log ex_C2', 'log en_C1',
             'delay 0.1'])

    def testDirectedEvent2(self):
        run_test(self, "./Examples/Stateflow/tests/directed_event2_2018a.xml", 1,
            ['log en_A1', 'log en_B1_A1', 'log en_C1_A1', 'log ex_C1_A1', 'log en_C2_A2',
             'log ex_B1_A1', 'log en_B2_A2', 'log ex_A1', 'log en_A2', 'log ex_A2',
             'log en_A1', 'log ex_B2_A2', 'log en_B1_A1', 'log ex_C2_A2', 'log en_C1_A1',
             'delay 0.1'])
        
    def testDirectedEventSend(self):
        run_test(self, "./Examples/Stateflow/tests/direct_event_send_2018a.xml", 1,
            ['log en_A1', 'log en_B1', 'log cond_act_B', 'log ex_B1',
             'log en_B2', 'log ex_A1', 'log en_A2','delay 0.1'])

    def testDirectedEventSend2(self):
        run_test(self, "./Examples/Stateflow/tests/direct_event_send2_2018a.xml", 1,
            ['log en_A1', 'log en_B2', 'log en_B21',
             'log ex_B21', 'log ex_B2', 'log en_B4', 'log ex_A1', 'log en_A2', 'delay 0.1'])
        
    def testCopyofDirectedEvent(self):
        run_test(self, "./Examples/Stateflow/tests/Copy_of_directed_event_2018a.xml", 1,
            ['log en_A1', 'log en_B1', 'log en_C1',
             'log ex_C1', 'log en_C2', 'log ex_B1', 'log en_B2', 'log ex_A1', 'log en_A2',
             'log ex_A2', 'log en_A1', 'log ex_B2', 'log en_B1', 'log ex_C2', 'log en_C1',
             'delay 0.1'])
        
    def testInnerTrans(self):
        run_test(self, "./Examples/Stateflow/tests/inner_trans.xml", 2,
            ['log enS', 'log condDefault', 'log tranDefault', 'log enA',
             'log duS', 'log condInner', 'log exA', 'log tranInner', 'log enA', 'delay 0.1',
             'log duS', 'log condInner', 'log exA', 'log tranInner', 'log enA', 'delay 0.1'])

    def testWriter(self):
        run_test(self, "./Examples/Stateflow/tests/writer.xml", 6,
            ['log 1,1', 'delay 0.1', 'log 1,2', 'delay 0.1', 'log 1,3', 'delay 0.1',
             'log 1,4', 'delay 0.1', 'log 1,5', 'delay 0.1',
             'log 100,200,300,400,500', 'delay 0.1'])

    def testGraphicalFunction(self):
        run_test(self, "./Examples/Stateflow/tests/graphical_function.xml", 1,
            ['log en_A', 'log en_B', 'delay 0.1'])
        
    def testGraphicalFunction2(self):
        run_test(self, "./Examples/Stateflow/tests/graphical_function2_2018a.xml", 1,
            ['log en_A', 'log set_mesg', 'log set_mesg', 'log en_B', 'delay 0.1'])

    def testGraphicalFunction3(self):
        run_test(self, "./Examples/Stateflow/tests/graphical_function3_2018a.xml", 1,
            ['log en_A', 'log en_B', 'delay 0.1'])

    def testGraphicalFunction4(self):
        run_test(self, "./Examples/Stateflow/tests/graphical_function4_2018a.xml", 1,
            ['log en_A', 'log en_B', 'delay 0.1'])

    def testCommunityCharts(self):
        run_test(self, "./Examples/Stateflow/tests/community_charts.xml",20,
           ['log en_add', 'log en_A1', 'log en_A1_1', 'IO ch_x0_0 0', 'IO ch_x1_0 0', 'log con_actB', 'log en_B', 'log con_act_chart1', 'log en_B1',
            'log en_B1_1', 'IO ch_x0_0 1', 'IO ch_x1_0 1', 'delay 0.1', 'log con_actAdd', 'log en_add', 'log du_b1', 'IO ch_x0_0 2',
            'IO ch_x1_0 1', 'delay 0.1', 'log con_actB', 'log en_B', 'log du_b1', 'IO ch_x0_0 1', 'IO ch_x1_0 2', 'delay 0.1', 'log con_actAdd',
            'log en_add', 'log du_b1', 'IO ch_x0_0 2', 'IO ch_x1_0 2', 'delay 0.1', 'log con_actB', 'log en_B', 'log du_b1', 'IO ch_x0_0 1',
            'IO ch_x1_0 3', 'delay 0.1', 'log con_actAdd', 'log en_add', 'log du_b1', 'IO ch_x0_0 2', 'IO ch_x1_0 3', 'delay 0.1'])
        
    def testCommunityCharts1(self):
        run_test(self, "./Examples/Stateflow/tests/community_charts1.xml",31,
          ['log en_add', 'log en_A1', 'log en_A1_1', 'IO ch_x2_0 1', 'IO ch_x3_0 1', 'IO ch_x0_0 0',
           'IO ch_x1_0 0', 'log con_actB', 'log en_B', 'log con_act_chart1', 'log en_B1', 'log en_B1_1',
           'IO ch_x2_0 1', 'IO ch_x3_0 1', 'IO ch_x0_0 1', 'IO ch_x1_0 1', 'delay 0.1', 'log con_actAdd',
           'log en_add', 'log du_b1', 'IO ch_x2_0 1', 'IO ch_x3_0 1', 'IO ch_x0_0 2', 'IO ch_x1_0 1', 'delay 0.1',
           'log con_actB', 'log en_B', 'log du_b1', 'IO ch_x2_0 1', 'IO ch_x3_0 1', 'IO ch_x0_0 1', 'IO ch_x1_0 2',
           'delay 0.1', 'log con_actAdd', 'log en_add', 'log du_b1', 'IO ch_x2_0 1', 'IO ch_x3_0 1', 'IO ch_x0_0 2',
           'IO ch_x1_0 2', 'delay 0.1', 'log con_actB', 'log en_B', 'log du_b1', 'IO ch_x2_0 1', 'IO ch_x3_0 1', 'IO ch_x0_0 1',
           'IO ch_x1_0 3', 'delay 0.1', 'log con_actAdd', 'log en_add', 'log du_b1', 'IO ch_x2_0 1', 'IO ch_x3_0 1'])

    def testDsmExample(self):
        io_filter = lambda s: not (s.startswith("read") or s.startswith("write"))
        run_test(self, "./Examples/Stateflow/tests/DSM_example.xml", 20,
            ['log en_A', 'log en_A1', 'log du_A', 'log du_A1', 'delay 0.1',
             'log du_A', 'log du_A1', 'delay 0.1',
             'log du_A', 'log du_A1', 'delay 0.1'], io_filter=io_filter)

    def testAfterRandom(self):
        random.seed(0)  # for repeatability
        run_test(self, "./Examples/Stateflow/tests/after_random.xml", 10,
            ['log en_A', 'log Picked 4', 'delay 1', 'delay 1', 'delay 1', 'delay 1',
             'log en_B', 'log Picked 4', 'delay 1', 'delay 1', 'delay 1', 'delay 1',
             'log en_A', 'log Picked 1', 'delay 1',
             'log en_B', 'log Picked 3', 'delay 1'])

    def testAfterTick(self):
        run_test(self, "./Examples/Stateflow/tests/after_tick_eg_2018a.xml", 20,
            ['log en_A', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1',
             'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1', 'log du_A',
             'delay 0.1', 'log du_A', 'delay 0.1', 'log du_A', 'delay 0.1', 'log en_B', 'delay 0.1', 
             'log du_B', 'delay 0.1', 'log du_B', 'delay 0.1', 'log du_B', 'delay 0.1', 'log du_B', 
             'delay 0.1', 'log du_B', 'delay 0.1', 'log du_B', 'delay 0.1', 'log du_B', 'delay 0.1', 
             'log du_B', 'delay 0.1', 'log du_B', 'delay 0.1', 'log en_A', 'delay 0.1'])

    def testSFNew(self):
        random.seed(0)  # for repeatability
        run_test(self, "./Examples/Stateflow/sf_new/sf_new.xml", 10,
            [], print_final=True, output_to_file="./Examples/Stateflow/sf_new/sf_new.txt")

    def testMessage1(self):
        run_test(self, "./Examples/Stateflow/tests/Message_eg_2018a.xml", 2,
            ['log en_A', 'log en_B', 'delay 0.1', 'delay 0.1'])
    def testMessage2(self):
        run_test(self, "./Examples/Stateflow/tests/Message_eg2_2018a.xml", 2,
            ['log en_A', 'log en_B', 'delay 0.1', 'log en_C', 'delay 0.1'])
    def testMessage3(self):
        run_test(self, "./Examples/Stateflow/tests/msgex1_msg.xml",100,
           ['log en_A', 'IO ch_x0_0 "M"', 'log en_A0', 'delay 0.1', 'delay 0.1', 'delay 0.1', 'delay 0.1', 'delay 0.1', 'delay 0.1', 'delay 0.1',
            'delay 0.1', 'delay 0.1', 'delay 0.1', 'delay 0.1', 'delay 0.1', 'delay 0.1', 'delay 0.1', 'delay 0.1', 'delay 0.1', 'delay 0.1',
            'delay 0.1', 'delay 0.1', 'delay 0.1', 'delay 0.1', 'delay 0.1', 'delay 0.1', 'delay 0.1', 'delay 0.1', 'delay 0.1', 'delay 0.1',
            'delay 0.1', 'delay 0.1', 'delay 0.1', 'log en_A1', 'delay 0.1', 'log en_A2', 'delay 0.1'],print_before_simp=True)


if __name__ == "__main__":
    unittest.main()
