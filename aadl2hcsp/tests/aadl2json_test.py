
# Unit test for json2hcsp2

import unittest
import json
from aadl2hcsp.aadl2json import convert_AADL 

path1 = "Examples\AADL\CCS\AADL\joint_model.aadl"
path2 = "Examples\AADL\CCS\AADL\config.json"
infos = convert_AADL(path1,path2)

path = "output.json"
f = open(path, "w")
f.write(infos)
f.close()

