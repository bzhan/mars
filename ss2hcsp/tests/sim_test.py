# Unit test for translation of Simulink diagrams

import unittest

from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.sl.get_hcsp import get_hcsp, new_get_hcsp
from ss2hcsp.hcsp.simulator import SimInfo, exec_parallel
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import optimize


def printTofile(path, content, module=False):
    with open(path, "w") as f:
        if module:
            f.write("%type: module\n")
        f.write(content)

def print_module(path, m):
    with open(path, "w") as f:
        f.write("%type: module\n\n")
        f.write(m.export() + '\n')
        f.write("system\n  %s=%s()\nendsystem" % (m.name, m.name))

def run_test(self, location, num_steps, expected_series, *,
             print_diagrams=False, print_hcsp=False, print_time_series=False,
             print_module_path=None):
    # First, parse and process diagram
    diagram = SL_Diagram(location=location)
    diagram.parse_xml()
    diagram.delete_subsystems()
    diagram.add_line_name()
    diagram.comp_inher_st()
    diagram.inherit_to_continuous()
    diagram.separate_diagram()

    # Optional: print diagram
    if print_diagrams:
        print("Discrete blocks:")
        for block in diagram.discrete_blocks:
            print(block)
        print("Continuous blocks:")
        for block in diagram.continuous_blocks:
            print(block)
        print("Outputs:")
        print(diagram.outputs)

    # Convert to HCSP
    result_hp = new_get_hcsp(
        diagram.discrete_blocks, diagram.continuous_blocks,
        diagram.chart_parameters, diagram.outputs)

    # Optimize module
    hp = result_hp.code
    procs = dict((proc.name, proc.hp) for proc in result_hp.procedures)
    procs, hp = optimize.full_optimize_module(procs, hp)
    result_hp.procedures = [hcsp.Procedure(name, hp) for name, hp in procs.items()]
    result_hp.code = hp

    # Optional: print HCSP
    if print_hcsp:
        print(result_hp.export())

    # Optional: export HCSP to file
    if print_module_path:
        assert isinstance(print_module_path, str)
        print_module(print_module_path, result_hp)

    # Perform simulation
    proc_dict = dict()
    for proc in result_hp.procedures:
        proc_dict[proc.name] = proc
    info = SimInfo(result_hp.name, result_hp.code, procedures=proc_dict, outputs=result_hp.outputs)
    res = exec_parallel([info], num_steps=num_steps, verbose=False)

    # Optional: print time series
    if print_time_series:
        series = res['time_series']['P']
        for i, pt in enumerate(series):
            if i != len(series)-1 and pt['time'] == series[i+1]['time']:
                continue
            print("%.2f: %s" % (pt['time'], pt['state']))

    if expected_series:
        series = dict()
        for pt in res['time_series']['P']:
            for time in expected_series:
                if abs(pt['time'] - time) < 1e-10:
                    series[time] = pt['state']
        for time in expected_series:
            self.assertTrue(time in series, "Time %s not found in result" % time)
            self.assertTrue(len(expected_series[time]) == len(series[time]), "Unequal length at time %s" % time)
            for var in expected_series[time]:
                self.assertTrue(var in series[time])
                self.assertAlmostEqual(
                    series[time][var], expected_series[time][var],
                    msg="Disagreement at time %s, variable %s" % (time, var), places=3)

class SimTest(unittest.TestCase):
    def testLunarLander(self):
        run_test(self, "./Examples/Simulink/LunarLander.xml", 1600, {
            0: {'m': 1250, 'v': -2, 'Fc': 2437.055},
            2.020: {'m': 1248.185, 'v': -1.644, 'Fc': 2122.533},
            3.968: {'m': 1246.569, 'v': -1.564, 'Fc': 2044.469},
            6.016: {'m': 1244.903, 'v': -1.543, 'Fc': 2025.467},
            8.036: {'m': 1243.269, 'v': -1.536, 'Fc': 2019.523},
            9.984: {'m': 1241.697, 'v': -1.532, 'Fc': 2016.002}
        })

    def testMarsLander(self):
        run_test(self, "./Examples/Simulink/MarsLander.xml", 1600, {
            0.000: {'m': 759.5, 'v': -1.5, 'Fc': 2834.449},
            2.020: {'m': 757.118, 'v': -1.500, 'Fc': 2825.807},
            3.968: {'m': 754.828, 'v': -1.499, 'Fc': 2816.761},
            6.016: {'m': 752.428, 'v': -1.499, 'Fc': 2807.788},
            8.036: {'m': 750.068, 'v': -1.499, 'Fc': 2799.413},
            9.984: {'m': 747.800, 'v': -1.499, 'Fc': 2790.511}
        })

    def testVanderPol(self):
        # This test case contains blocks with different sample times
        run_test(self, "./Examples/Simulink/Van_der_Pol.xml", 50, {
            0: {'z': 1},
            1: {'z': 1.382},
            2: {'z': 0.493},
            3: {'z': -0.849},
            4: {'z': -1.410},
            5: {'z': -0.675},
            6: {'z': 0.681},
            7: {'z': 1.411},
            8: {'z': 0.844},
            9: {'z': -0.532}
        })

    def testThreeTank(self):
        run_test(self, "./Examples/Simulink/ThreeTank.xml", 600, {
            0: {'x': 0, 'y': 0, 'z': 0},
            10: {'x': 0.672, 'y': 0.028, 'z': 0.004},
            20: {'x': 1.316, 'y': 0.076, 'z': 0.014},
            30: {'x': 1.941, 'y': 0.135, 'z': 0.027},
            40: {'x': 2.552, 'y': 0.202, 'z': 0.043},
            50: {'x': 3.150, 'y': 0.277, 'z': 0.062},
            60: {'x': 3.736, 'y': 0.356, 'z': 0.083},
            70: {'x': 4.313, 'y': 0.441, 'z': 0.106},
            80: {'x': 4.880, 'y': 0.530, 'z': 0.132},
            90: {'x': 5.439, 'y': 0.623, 'z': 0.159},
            100: {'x': 5.989, 'y': 0.720, 'z': 0.188}
        })

    # def testIsolette(self):
    #     run_test(self, "./Examples/Simulink/Isolette.xml", 1200, {
    #         0.0: {'q': 75, 'c': 75},
    #         40.0: {'q': 115.0, 'c': 90.133},
    #         80.0: {'q': 103.054, 'c': 107.166},
    #         120.0: {'q': 98.645, 'c': 96.473},
    #         160.0: {'q': 89.899, 'c': 100.370},
    #         200.0: {'q': 92.852, 'c': 99.874}
    #     })

    # def testSignalBuilder(self):
    #     directory = "./Examples/signalBuilder/"
    #     xml_file = "testSignalBuilder.xml"
    #     diagram = SL_Diagram(location=directory + xml_file)
    #     model_name = diagram.parse_xml()
    #     diagram.add_line_name()
    #     diagram.comp_inher_st()
    #     diagram.inherit_to_continuous()
    #     real_hp = get_hcsp(*diagram.seperate_diagram(), model_name)
    #     printTofile(path=directory+xml_file[:-3]+"txt", content=real_hp)

    # def testVelocityControl(self):
    #     directory = "./Examples/signalBuilder/"
    #     xml_file = "velocity_control.xml"
    #     diagram = SL_Diagram(location=directory + xml_file)
    #     model_name = diagram.parse_xml()
    #     diagram.delete_subsystems()
    #     diagram.comp_inher_st()
    #     # diagram.add_buffers()
    #     diagram.add_line_name()
    #     # print(diagram)
    #     real_hp = get_hcsp(*diagram.seperate_diagram(), model_name)
    #     # print(real_hp)
    #     printTofile(path=directory+xml_file[:-3]+"txt", content=real_hp)

    def testSource1(self):
        # Value should be y = sin(t)
        run_test(self, "./Examples/Simulink/Source1.xml", 30, {
            0: {'y': 0},
            1: {'y': 0.841},
            2: {'y': 0.909},
            3: {'y': 0.141},
            4: {'y': -0.757},
            5: {'y': -0.959}
        })

    def testDelay1(self):
        run_test(self, "./Examples/Simulink/Delay1.xml", 60, {
            0: {'x': 0},
            1: {'x': 1},
            2: {'x': 2},
            3: {'x': 3},
            4: {'x': 4},
            5: {'x': 5}
        })

    def testDelay2(self):
        run_test(self, "./Examples/Simulink/Delay2.xml", 80, {
            0: {'x': 0},
            1: {'x': 0},
            2: {'x': 1},
            3: {'x': 1},
            4: {'x': 2},
            5: {'x': 2}
        })

    def testDelay3(self):
        run_test(self, "./Examples/Simulink/Delay3.xml", 60, {
            0: {'y': 1, 'x': 0},
            1: {'y': 1, 'x': 1},
            2: {'y': 2, 'x': 1},
            3: {'y': 3, 'x': 2},
            4: {'y': 5, 'x': 3},
            5: {'y': 8, 'x': 5}
        })

    # def testEnabled1(self):
    #     run_test(self, "./Examples/Simulink/Enabled1.xml", 70, {
    #
    #     })

    def testTriggered1(self):
        # Continuous triggered subsystem
        run_test(self, "./Examples/Simulink/Triggered1.xml", 70, {
            0: {'a': 0, 'y': -1},
            1: {'a': 1, 'y': 0},
            2: {'a': 1, 'y': 2},
            3: {'a': 1, 'y': 4},
            4: {'a': 1, 'y': 6},
            5: {'a': 1, 'y': 8}
        })

    def testTriggered2(self):
        # Discrete triggered subsystem
        # NOTE: the result here agrees with simulation in Matlab only if the
        # simulation time is set to 3 seconds. For longer simulation time,
        # the result from Matlab is different (and inconsistent with itself).
        run_test(self, "./Examples/Simulink/Triggered2.xml", 70, {
            0: {'z': -1, 'a': 0, 'y': -1},
            1: {'z': 0, 'a': 1, 'y': 0},
            1.5: {'z': 0, 'a': 1, 'y': 1},
            2: {'z': 2, 'a': 3, 'y': 2},
            2.5: {'z': 2, 'a': 3, 'y': 4},
            3: {'z': 6, 'a': 3, 'y': 6}
        })

    # def testTemporalLogic(self):
    #     run_test(self, "./Examples/Simulink/Temporal_Logic.xml", 80, {
    #
    #     })

    def testInputEvent(self):
        run_test(self, "./Examples/Simulink/Input_Event_2018a.xml", 80, {

        })

    def testStopWatch1(self):
        run_test(self, "./Examples/Stateflow/tests/StopWatch1.xml", 6000, {
            0: {'t': 0.0, 'cent': 0, 'disp_cent': 0},
            0.1: {'t': 0.1, 'cent': 6, 'disp_cent': 6},
            0.2: {'t': 0.2, 'cent': 16, 'disp_cent': 15},
            0.3: {'t': 0.3, 'cent': 26, 'disp_cent': 15},
            0.4: {'t': 0.4, 'cent': 36, 'disp_cent': 36},
            0.5: {'t': 0.5, 'cent': 46, 'disp_cent': 46},
            0.6: {'t': 0.6, 'cent': 56, 'disp_cent': 56},
            0.7: {'t': 0.7, 'cent': 66, 'disp_cent': 66},
            0.8: {'t': 0.8, 'cent': 76, 'disp_cent': 76},
            0.9: {'t': 0.9, 'cent': 86, 'disp_cent': 86},
            1.0: {'t': 1.0, 'cent': 96, 'disp_cent': 96},
            1.1: {'t': 1.1, 'cent': 6, 'disp_cent': 6},
        })

    def testStopWatch2(self):
        run_test(self, "./Examples/Stateflow/tests/StopWatch2.xml", 6000, {
            0: {'t': 0.0, 'cent': 0, 'disp_cent': 0, 'start': 0.0, 'lap': 0.0},
            0.1: {'t': 0.1, 'cent': 8, 'disp_cent': 2, 'start': 1.0, 'lap': 0.0},
            0.2: {'t': 0.2, 'cent': 18, 'disp_cent': 18, 'start': 0.0, 'lap': 0.0},
            0.3: {'t': 0.3, 'cent': 28, 'disp_cent': 22, 'start': 0.0, 'lap': 0.0},
            0.4: {'t': 0.4, 'cent': 30, 'disp_cent': 22, 'start': 1.0, 'lap': 0.0},
            0.5: {'t': 0.5, 'cent': 0, 'disp_cent': 0, 'start': 0.0, 'lap': 0.0},
            0.6: {'t': 0.6, 'cent': 0, 'disp_cent': 0, 'start': 0.0, 'lap': 0.0},
            0.7: {'t': 0.7, 'cent': 8, 'disp_cent': 2, 'start': 1.0, 'lap': 0.0},
            0.8: {'t': 0.8, 'cent': 18, 'disp_cent': 18, 'start': 0.0, 'lap': 0.0},
            0.9: {'t': 0.9, 'cent': 28, 'disp_cent': 22, 'start': 0.0, 'lap': 0.0},
            1.0: {'t': 1.0, 'cent': 30, 'disp_cent': 22, 'start': 1.0, 'lap': 0.0},
        })

    def testStopWatch3(self):
        run_test(self, "./Examples/Stateflow/tests/StopWatch3.xml", 6000, {
            0: {'t': 0.0, 'cent': 0, 'disp_cent': 0},
            0.1: {'t': 0.1, 'cent': 6, 'disp_cent': 5},
            0.2: {'t': 0.2, 'cent': 16, 'disp_cent': 5},
            0.3: {'t': 0.3, 'cent': 26, 'disp_cent': 26},
            0.4: {'t': 0.4, 'cent': 35, 'disp_cent': 35},
            0.5: {'t': 0.5, 'cent': 35, 'disp_cent': 35},
            0.6: {'t': 0.6, 'cent': 35, 'disp_cent': 35},
            0.7: {'t': 0.7, 'cent': 36, 'disp_cent': 36},
            0.8: {'t': 0.8, 'cent': 46, 'disp_cent': 46},
            0.9: {'t': 0.9, 'cent': 56, 'disp_cent': 56},
            1.0: {'t': 1.0, 'cent': 66, 'disp_cent': 66},
            1.1: {'t': 1.1, 'cent': 76, 'disp_cent': 76},
        }, print_time_series=True)


if __name__ == "__main__":
    unittest.main()
