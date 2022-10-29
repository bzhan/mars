# Unit test for translation of Simulink diagrams

import unittest

from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.sl.get_hcsp import get_hcsp
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
             print_diagram=False, print_hcsp_raw=False, print_hcsp=False,
             print_time_series=False, output_to_file=None, debug_name=False):
    # First, parse and process diagram
    diagram = SL_Diagram(location=location)
    diagram.parse_xml()
    diagram.delete_subsystems()
    diagram.add_line_name()
    diagram.comp_inher_st()
    diagram.inherit_to_continuous()
    diagram.connect_goto()
    diagram.separate_diagram()

    # Optional: print diagram
    if print_diagram:
        if diagram.constants:
            print("Constants:")
            for k, v in diagram.constants.items():
                print("%s = %s" % (k, v))
        print("Discrete blocks:")
        for block in diagram.discrete_blocks:
            print(block)
        print("Continuous blocks:")
        for block in diagram.continuous_blocks:
            print(block)
        print("Scopes:")
        for block in diagram.scopes:
            print(block)

    # Convert to HCSP
    result_hp = get_hcsp(diagram)

    if debug_name:
        before_size = 0
        before_size += result_hp.code.size()
        for proc in result_hp.procedures:
            before_size += proc.hp.size()

    # Optional: print HCSP before optimization
    if print_hcsp_raw:
        print(result_hp.export())

    # Optimize module
    hp = result_hp.code
    procs = dict((proc.name, proc.hp) for proc in result_hp.procedures)
    procs, hp = optimize.full_optimize_module(procs, hp)
    result_hp.procedures = [hcsp.Procedure(name, hp) for name, hp in procs.items()]
    result_hp.code = hp

    if debug_name:
        after_size = 0
        after_size += result_hp.code.size()
        for proc in result_hp.procedures:
            after_size += proc.hp.size()
        print(diagram.name, before_size, after_size)

    # Optional: print HCSP
    if print_hcsp:
        print(result_hp.export())

    # Optional: export HCSP to file
    if output_to_file:
        assert isinstance(output_to_file, str)
        print_module(output_to_file, result_hp)

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
        }, output_to_file="./Examples/Simulink/LunarLander.txt")

    def testMarsLander(self):
        run_test(self, "./Examples/Simulink/MarsLander.xml", 1600, {
            0.000: {'r': 20.0, 'm': 759.5, 'v': -1.5, 'Fc': 2834.449},
            2.020: {'r': 16.971, 'm': 757.118, 'v': -1.500, 'Fc': 2825.807},
            3.968: {'r': 14.049, 'm': 754.828, 'v': -1.499, 'Fc': 2816.761},
            6.016: {'r': 10.979, 'm': 752.428, 'v': -1.499, 'Fc': 2807.788},
            8.036: {'r': 7.950, 'm': 750.068, 'v': -1.499, 'Fc': 2799.413},
            9.984: {'r': 5.029, 'm': 747.800, 'v': -1.499, 'Fc': 2790.511}
        }, output_to_file="./Examples/Simulink/MarsLander.txt")

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

    def testSLIsolette(self):
        run_test(self, "./hhlpy/examples/simulink/sl_isolette.xml", 80, {

        }, output_to_file="./hhlpy/examples/simulink/sl_isolette.txt")

    def testSLDelay(self):
        run_test(self, "./hhlpy/examples/simulink/sl_delay.xml", 80, {

        }, output_to_file="./hhlpy/examples/simulink/sl_delay.txt")

    def testPIcontrol(self):
        run_test(self, "./hhlpy/examples/simulink/PIcontrol.xml", 80, {

        }, output_to_file="./hhlpy/examples/simulink/PIcontrol.txt")

    def testCanonicalMax(self):
        run_test(self, "./Examples/Simulink/CanonicalMax.xml", 80, {

        }, output_to_file="./Examples/Simulink/CanonicalMax.txt")

    def testCanonicalMax2(self):
        run_test(self, "./Examples/Simulink/CanonicalMax2.xml", 80, {

        }, output_to_file="./Examples/Simulink/CanonicalMax2.txt")

    def testTransferFcn1(self):
        run_test(self, "./Examples/Simulink/TransferFcn1.xml", 10, {
            0.00: {'y': 0, 'u': 1.0},
            0.10: {'y': 0.28346924831934156, 'u': 1.0},
            0.20: {'y': 0.48658392408107254, 'u': 1.0},
            0.30: {'y': 0.6321214212850567, 'u': 1.0},
            0.40: {'y': 0.7364023884971252, 'u': 1.0},
            0.50: {'y': 0.8111235425573193, 'u': 1.0},
            0.60: {'y': 0.8646657542925558, 'u': 1.0},
            0.70: {'y': 0.9030281701522963, 'u': 1.0},
            0.80: {'y': 0.9305151699725418, 'u': 1.0},
            0.90: {'y': 0.9502140562735414, 'u': 1.0},
            1.00: {'y': 0.9643238807540565, 'u': 1.0},
        }, output_to_file="./Examples/Simulink/TransferFcn1.txt")

    def testAbstractFuelControlM2(self):
        run_test(self, "./Examples/Simulink/AbstractFuelControl_M2.xml", 120, {
            0.00: {'AF': 14.7, 'TA': 8.8, 'ES': 1000},
            0.05: {'AF': 14.652951328662022, 'TA': 8.8, 'ES': 1000},
            0.10: {'AF': 14.597133383303678, 'TA': 8.8, 'ES': 1000},
            0.15: {'AF': 14.54673387221721, 'TA': 8.8, 'ES': 1000},
            0.20: {'AF': 14.508231577066661, 'TA': 8.8, 'ES': 1000},
            0.25: {'AF': 14.483227478549416, 'TA': 8.8, 'ES': 1000},
            0.30: {'AF': 14.470757070356782, 'TA': 8.8, 'ES': 1000},
            0.35: {'AF': 14.468769394147365, 'TA': 8.8, 'ES': 1000},
            0.40: {'AF': 14.47494692818884, 'TA': 8.8, 'ES': 1000},
            0.45: {'AF': 14.487107544502074, 'TA': 8.8, 'ES': 1000},
            0.50: {'AF': 14.503370055844176, 'TA': 8.8, 'ES': 1000},
        }, output_to_file="./Examples/Simulink/AbstractFuelControl_M2.txt")


if __name__ == "__main__":
    unittest.main()
