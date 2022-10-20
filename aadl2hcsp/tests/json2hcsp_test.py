# Unit test for json2hcsp

import unittest
import json

from aadl2hcsp import json2hcsp
from aadl2hcsp.get_modules import get_databuffer_module
from ss2hcsp.hcsp import module

class Json2HCSPTest(unittest.TestCase):
    def testJson2HCSP3(self):
        json_file = "./Examples/AADL/CCS/AADL/joint_model.json"
        with open(json_file, 'r') as f:
            dic = json.load(f)

        mods = list()
        dataBuffers = dict()  # {recv_num: databuffer}
        buses = list()
        for name, content in dic.items():
            if content['category'] == 'thread':
                mod = json2hcsp.translate_thread(name, content)
                for _content in dic.values():
                    if _content['category'] == "connection" and _content['source'] == name and ('bus' in _content.keys()):
                        mod = json2hcsp.translate_thread(name, content, _content['bus'])
                        break
                mods.append(mod)
            elif content['category'] == 'device':
                mod = json2hcsp.translate_device(name, content)
                mods.append(mod)
            elif content['category'] == 'abstract':
                mod = json2hcsp.translate_abstract(name, content)
                mods.append(mod)
            elif content['category'] == "connection":
                if content['type'] == 'data':
                    recv_num = len(content['target'])
                    if recv_num not in dataBuffers:
                        dataBuffers[recv_num] = get_databuffer_module(recv_num)
            elif content['category'] == "bus":
                bus = json2hcsp.translate_bus(name, content, dic)
                buses.append(bus)
            elif content['category'] == "processor":
                # processor use for change protocal, remain tobe done
                continue
            else:
                raise NotImplementedError

        with open('./Examples/AADL/CCS/TCS/generatedcode/other_modules.txt', 'w') as f:
            f.write("%type: module\n\n")
            for mod in mods:
                f.write(mod.export())
                f.write('\n\n')

        with open('./Examples/AADL/CCS/TCS/generatedcode/DataBuffer.txt', 'w') as f:
            f.write("%type: module\n\n")
            for dataBuffer in dataBuffers.values():
                f.write(dataBuffer.export())
                f.write('\n\n')

        with open('./Examples/AADL/CCS/TCS/generatedcode/Bus.txt', 'w') as f:
            f.write("%type: module\n\n")
            for bus in buses:
                f.write(bus.export())
                f.write('\n\n')

        with open('./Examples/AADL/CCS/TCS/generatedcode/system.txt', 'w') as f:
            f.write("%type: module\n")
            f.write("import other_modules\n")
            f.write("import SCHEDULLER_HPF\n")
            f.write("import ACT_periodic\n")
            f.write("import ACT_aperiodic\n")
            f.write("import DataBuffer\n")
            f.write("import EventBuffer\n")
            f.write("import Bus\n")
            f.write("import BusEventBuffer\n\n")
            f.write("system\n\n")
            f.write(str(module.HCSPSystem(json2hcsp.translate_model(dic))))
            f.write("\n\nendsystem")


if __name__ == "__main__":
    unittest.main()
