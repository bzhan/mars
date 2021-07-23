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

    def testJunctionLoop(self):
        run_test(self, "./Examples/Stateflow/tests/junction_loop.xml", 1,
            ['log t1', 'log t2', 'log t1', 'log t2', 'log t1', 'log t2', 'log t1',
             'log t4', 'delay 0.1'])

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

    def testJunInState(self):
        run_test(self, "./Examples/Stateflow/tests/jun_in_state.xml", 1,
            ['log enA', 'log enA1', 'log duA', 'log c1', 'log c2', 'log exA1', 'log exA',
             'log t1', 'log t2', 'log enC', 'log enC2', 'delay 0.1'])

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
            ['log en_A', 'log en_A1', 'log ex_A1', 'log en_A2', 'log ex_A2',
             'log loop', 'log ex_A', 'log en_A', 'log en_A1', 'delay 0.1'])

    def testEarlyReturn8(self):
        run_test(self, "./Examples/Stateflow/tests/EarlyReturn/EarlyReturn8.xml", 1,
            ['log a', 'log c', 'log du_A1', 'log b', 'log a', 'log c', 'log ex_A1',
             'log en_A2', 'log en_C2', 'log tb', 'log en_B2', 'log en_C3', 'delay 0.1'])

    def testDSM1(self):
        io_filter = lambda s: False
        run_test(self, "./Examples/Stateflow/tests/DataStore/DSM1.xml", 20,
            ['log 2', 'delay 0.1', 'log 4', 'delay 0.1', 'log 5', 'delay 0.1',
             'log 7', 'delay 0.1', 'log 8', 'delay 0.1', 'log 10', 'delay 0.1'], io_filter=io_filter)

    def testDSM2(self):
        io_filter = lambda s: False
        run_test(self, "./Examples/Stateflow/tests/DataStore/DSM2.xml", 20,
            ['log 1', 'delay 0.1', 'log 3', 'delay 0.1', 'log 4', 'delay 0.1',
             'log 6', 'delay 0.1', 'log 7', 'delay 0.1', 'log 9', 'delay 0.1'], io_filter=io_filter)

    def testDSM3(self):
        io_filter = lambda s: False
        run_test(self, "./Examples/Stateflow/tests/DataStore/DSM3.xml", 20,
            ['log 3 2', 'delay 0.1', 'log 3 5', 'delay 0.1', 'log 8 5', 'delay 0.1',
             'log 8 13', 'delay 0.1', 'log 21 13', 'delay 0.1', 'log 21 34', 'delay 0.1'], io_filter=io_filter)

    def testDSM4(self):
        io_filter = lambda s: False
        run_test(self, "./Examples/Stateflow/tests/DataStore/DSM4.xml", 19,
            ['log A1', 'log C1', 'log B2', 'log D4', 'delay 0.1',
             'log A4', 'log C4', 'delay 0.1', 'log B5', 'log D7', 'delay 0.1'], io_filter=io_filter)

    def testDSM5(self):
        io_filter = lambda s: False
        run_test(self, "./Examples/Stateflow/tests/DataStore/DSM5.xml", 34,
            ['log 4 2', 'delay 0.1', 'log 4 4', 'delay 0.1', 'log 5 4', 'delay 0.1',
             'log 5 6', 'delay 0.1', 'log 6 6', 'delay 0.1', 'log 6 8', 'delay 0.1'], io_filter=io_filter)

    def testDSM6(self):
        io_filter = lambda s: False
        run_test(self, "./Examples/Stateflow/tests/DataStore/DSM6.xml", 20,
            ['log en_A 0 0', 'log en_A1 3 0', 'log en_B 4 4', 'log du_A1 4 0', 'delay 0.1',
             'log en_A 4 -1', 'log du_A1 3 -1', 'delay 0.1',
             'log en_B 4 -1', 'log du_A1 4 0', 'delay 0.1'], io_filter=io_filter)

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


if __name__ == "__main__":
    unittest.main()
