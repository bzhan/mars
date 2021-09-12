# Unit test for translation of Simulink diagrams

import unittest

from ss2hcsp.sl.port import Port
from ss2hcsp.sl.Continuous.integrator import Integrator
from ss2hcsp.sl.MathOperations.gain import Gain
from ss2hcsp.sl.LogicOperations.logic import And, Or, Not
from ss2hcsp.sl.LogicOperations.relation import Relation
from ss2hcsp.sl.SignalRouting.switch import Switch
from ss2hcsp.sl.SubSystems.subsystem import Subsystem
from ss2hcsp.sl.sl_diagram import SL_Diagram
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp import pprint
from ss2hcsp.sl.get_hcsp import get_hcsp, new_get_hcsp
from ss2hcsp.hcsp.parser import hp_parser
from ss2hcsp.hcsp.simulator import SimInfo, exec_parallel


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
    discrete_diagram, continuous_diagram, outputs = diagram.new_seperate_diagram()

    # Optional: print diagram
    if print_diagrams:
        print("Discrete diagram:")
        for block in discrete_diagram:
            print(block)
        print("Continuous diagram:")
        for block in continuous_diagram:
            print(block)
        print("Outputs:")
        print(outputs)

    # Convert to HCSP
    result_hp = new_get_hcsp(discrete_diagram, continuous_diagram, outputs)

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
    res = exec_parallel([info], num_steps=num_steps)

    # Optional: print time series
    if print_time_series:
        series = res['time_series']['P']
        for i, pt in enumerate(series):
            if i != len(series)-1 and pt['time'] == series[i+1]['time']:
                continue
            print("%.1f: %s" % (pt['time'], pt['state']))

    series = dict()
    for pt in res['time_series']['P']:
        for time in expected_series:
            if abs(pt['time'] - time) < 1e-10:
                series[time] = pt['state']
    for time in expected_series:
        self.assertTrue(time in series, "Time %s not found in result" % time)
        self.assertTrue(len(expected_series[time]) == len(series[time]))
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

    # def testIsollete(self):
    #     location = "./ss2hcsp/server/portParser/simulinkModel/simulink_isollete.xml"
    #     diagram = SL_Diagram(location=location)
    #     diagram.parse_xml()
    #     get_hp.delete_subsystems(diagram.blocks_dict)
    #     diagram.add_line_name()
    #     diagram.comp_inher_st()
    #     dis_subdiag_with_chs, con_subdiag_with_chs = get_hp.seperate_diagram(diagram.blocks_dict)
    #     real_hp = get_hp.get_processes(dis_subdiag_with_chs, con_subdiag_with_chs)
    #     # print(real_hp)

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

    def testIsolette(self):
        location = "./Examples/isolette/babybox.xml"
        diagram = SL_Diagram(location)
        model_name = diagram.parse_xml()
        diagram.add_line_name()
        diagram.comp_inher_st()
        diagram.inherit_to_continuous()
        real_hp = get_hcsp(*diagram.seperate_diagram(), model_name)
        # print(real_hp)

        expected_hp = hcsp.HCSPProcess()
        # expected_hp.add(model_name, hcsp.Var("PC0"))
        con_init = hp_parser.parse("q := 97; c := 100; x0 := 1")
        con_hp = hp_parser.parse("<q_dot = -1, c_dot = (-q+c)*(-0.026) & x0 <= 0> |> [] "
                                 "(babybox_heatCommand?x0 --> skip, babybox_boxTemp!c --> skip); "
                                 "<q_dot = 1, c_dot = (-q+c)*(-0.026) & x0 > 0> |> [] "
                                 "(babybox_heatCommand?x0 --> skip, babybox_boxTemp!c --> skip)")
        continuous_hp = hcsp.Sequence(con_init, hcsp.Loop(con_hp))
        expected_hp.add(model_name, continuous_hp)
        # print(expected_hp)

        # self.assertEqual(real_hp, expected_hp)

    def testLander(self):
        directory = "./CaseStudies/lander/"
        xml_file = "lander_2018a.xml"
        diagram = SL_Diagram(location=directory+xml_file)
        model_name = diagram.parse_xml()
        diagram.delete_subsystems()
        diagram.comp_inher_st()
        diagram.add_buffers()
        diagram.add_line_name()
        # print(diagram)
        real_hp = get_hcsp(*diagram.seperate_diagram(), model_name)
        printTofile(path=directory+xml_file[:-3]+"txt", content=real_hp)

        # expected_hp = hcsp.HCSPProcess()
        # expected_hp.add(model_name, hcsp.Var("PC0"))
        # con_init = hp_parser.parse("q := 97; c := 100; x0 := 1")
        # con_hp = hp_parser.parse("<q_dot = -1, c_dot = (-q+c)*(-0.026) & x0 <= 0> |> [] "
        #                          "(babybox_heatCommand?x0 --> skip, babybox_boxTemp!c --> skip); "
        #                          "<q_dot = 1, c_dot = (-q+c)*(-0.026) & x0 > 0> |> [] "
        #                          "(babybox_heatCommand?x0 --> skip, babybox_boxTemp!c --> skip)")
        # continuous_hp = hcsp.Sequence(con_init, hcsp.Loop(con_hp))
        # expected_hp.add(model_name, continuous_hp)
        # print(expected_hp)

        # self.assertEqual(real_hp, expected_hp)

    def testSignalBuilder(self):
        directory = "./Examples/signalBuilder/"
        xml_file = "testSignalBuilder.xml"
        diagram = SL_Diagram(location=directory + xml_file)
        model_name = diagram.parse_xml()
        diagram.add_line_name()
        diagram.comp_inher_st()
        diagram.inherit_to_continuous()
        real_hp = get_hcsp(*diagram.seperate_diagram(), model_name)
        printTofile(path=directory+xml_file[:-3]+"txt", content=real_hp)

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

    def testEnabled1(self):
        run_test(self, "./Examples/Simulink/Enabled1.xml", 70, {

        })

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
            2: {'z': 2, 'a': 1, 'y': 2},
            2.5: {'z': 2, 'a': 1, 'y': 3},
            3: {'z': 4, 'a': 1, 'y': 4}
        })


if __name__ == "__main__":
    unittest.main()
