
# Unit test for json2hcsp2

import unittest
import json
from aadl2hcsp.aadl2json import convert_AADL 

path = "Examples\AADL\CCS\AADL\joint_model.aadl"
infos = convert_AADL(path)

path = "output.json"
f = open(path, "w")
f.write(infos)
f.close()

