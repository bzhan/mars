import unittest
from ss2hcsp.aadl.get_modules import get_thread_module, get_bus_module,\
    get_databuffer_module, get_continuous_module
from ss2hcsp.sl.sl_diagram import SL_Diagram


class SimTest(unittest.TestCase):
    def testTranslateThread(self):
        directory = "./Examples/AADL/CCS/Simulink/"
        # xml_file = "comp_obs_pos_imp.xml"
        xml_file = "velo_voter_imp.xml"
        # xml_file = "PI_ctr_imp.xml"
        # xml_file = "img_acq_imp.xml"
        diagram = SL_Diagram(location=directory + xml_file)
        _ = diagram.parse_xml()
        diagram.add_line_name()
        thread_hp = get_thread_module(name=xml_file[:-4],
                                      ports={"wheel_v": "in data", "wheel_valid": "in data",
                                             "laser_v": "in data", "laser_valid": "in data",
                                             "veh_v": "out data"},
                                      discrete_diagram=list(diagram.blocks_dict.values()),
                                      deadline=0.01, max_et=0.045, prior=1
                                      )  # reqResources="bus")
        # print(thread_hp.export())


    def testBus(self):
        bus_module = get_bus_module(name="bus",
                                    thread_ports={"th0": {"d00": "out data", "d01": "out data",
                                                          "e00": "out event", "e01": "out event"},
                                                  "th1": {"d10": "out data", "d11": "out data",
                                                          "e10": "out event", "e11": "out event"}
                                                  },
                                    device_ports={"dv2": {"d20": "out data", "d21": "out data",
                                                          "e20": "out event", "e21": "out event"},
                                                  "dv3": {"d30": "out data", "d31": "out data",
                                                          "e30": "out event", "e31": "out event"}
                                                  },
                                    latency=2
                                    )
        # print(bus_module.export())


    def testDataBuffer(self):
        dataBuffer = get_databuffer_module(2)
        # print(dataBuffer.export())

    def testContinuousModule(self):
        directory = "./Examples/AADL/CCS/Simulink/"
        xml_file = "vehicle_imp.xml"
        diagram = SL_Diagram(location=directory + xml_file)
        _ = diagram.parse_xml()
        diagram.add_line_name()
        continuous_diagram = [block for block in diagram.blocks_dict.values() if block.type == "integrator"]
        continuous_module = get_continuous_module(name=xml_file[:-4],
                                                  ports={"actuator": ("veh_a", "in data"),
                                                         "GPS": ("veh_s", "out data"),
                                                         "wheel": ("veh_v", "out data"),
                                                         "laser": ("veh_v", "out data")},
                                                  continuous_diagram=continuous_diagram)
        print(continuous_module.export())


if __name__ == "__main__":
    unittest.main()
