import unittest
from ss2hcsp.hcsp import hcsp
from ss2hcsp.hcsp.parser import hp_parser
import re


class SystemCTest(unittest.TestCase):
    def testSystemC(self):
        def systemCform(_hp, _name=""):
            if isinstance(_hp, hcsp.ITE):
                head_cond, head_hp = _hp.if_hps[0]

                if isinstance(head_hp, hcsp.Var):
                    new_name_0 = head_hp.name
                else:
                    new_name_0 = "SC" + str(len(indices))
                    indices.append(new_name_0)
                    _ = systemCform(head_hp, new_name_0)

                if len(_hp.if_hps) >= 2:
                    new_name_1 = "SC" + str(len(indices))
                    indices.append(new_name_1)
                    _ = systemCform(hcsp.ITE(_hp.if_hps[1:], _hp.else_hp), new_name_1)
                else:
                    assert len(_hp.if_hps) == 1
                    if isinstance(_hp.else_hp, hcsp.Var):
                        new_name_1 = _hp.else_hp.name
                    elif _hp.else_hp is not None:
                        new_name_1 = "SC" + str(len(indices))
                        indices.append(new_name_1)
                        _ = systemCform(_hp.else_hp, new_name_1)

                _hp.if_hps = ((head_cond, hcsp.Var(new_name_0)),)
                if _hp.else_hp is not None:
                    _hp.else_hp = hcsp.Var(new_name_1)

            elif isinstance(_hp, hcsp.ODE_Comm):
                io_comms = list()
                for ch, sub_hp in _hp.io_comms:
                    if isinstance(sub_hp, hcsp.Var):
                        io_comms.append((ch, sub_hp))
                    else:
                        new_name = "SC" + str(len(indices))
                        indices.append(new_name)
                        _ = systemCform(sub_hp, new_name)
                        io_comms.append((ch, hcsp.Var(new_name)))

                _hp.io_comms = io_comms

            elif isinstance(_hp, hcsp.Sequence):
                hps = list()
                for sub_hp in _hp.hps:
                    hps.append(systemCform(sub_hp))
                _hp.hps = hps

            elif isinstance(_hp, hcsp.Loop):
                if not isinstance(_hp.hp, hcsp.Var):
                    new_name = "SC" + str(len(indices))
                    indices.append(new_name)
                    _ = systemCform(_hp.hp, new_name)
                    _hp.hp = hcsp.Var(new_name)

            elif isinstance(_hp, hcsp.SelectComm):
                io_comms = list()
                for ch, sub_hp in _hp.io_comms:
                    if isinstance(sub_hp, (hcsp.Var, hcsp.Skip)):
                        io_comms.append((ch, sub_hp))
                    else:
                        io_comms.append((ch, systemCform(sub_hp)))
                _hp.io_comms = io_comms

            sc_process.add(_name, _hp)
            return _hp

        expected_process = hcsp.HCSPProcess()
        f = open("./Examples/AADL/isolette/new_hcsp4.txt", "r")
        for line in f.readlines():
            start, end = re.search(pattern="::=", string=line).span()
            name = line[:start].strip()
            process = line[end:].strip()
            expected_process.add(name, hp_parser.parse(process))
        f.close()

        sc_process = hcsp.HCSPProcess()
        indices = []
        for name, process in expected_process.hps:
            _ = systemCform(process, name)
        new_hps = [(name, process) for name, process in sc_process.hps if name]
        sc_process.hps = new_hps
        print(sc_process.sc_str())

        f = open("./Examples/AADL/isolette/isolette.hcsp", "w")
        f.write(sc_process.sc_str())
        f.close()


if __name__ == "__main__":
    unittest.main()