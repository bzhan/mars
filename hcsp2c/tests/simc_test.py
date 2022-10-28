import unittest
import subprocess

from hcsp2c import transfer2c
from ss2hcsp.hcsp.parser import parse_module_file

class SimcTest(unittest.TestCase):
    def testLunarLander(self):
        file = "./Examples/Simulink/LunarLander.txt"
        filename = "LunarLander"

        with open(file, "r") as f:
            s = f.read()
            infos = parse_module_file(s)

        res = transfer2c.convertHps(infos, step_size=1e-3)

        with open('hcsp2c/target/%s.c' % filename, 'w') as f:
            f.write(res)
        res = subprocess.run(
            "sudo gcc hcsp2c/target/%s.c -lpthread -o hcsp2c/output/%s.out" % (filename, filename),
            stderr=subprocess.PIPE,
            text=True,
            shell=True
        )

        # Handle exception resulting from conversion step
        if res.stderr != '':
            err = res.stderr
            raise Exception(err)

        res = subprocess.run(
            "./hcsp2c/output/%s.out" % filename,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            shell=True
        )

        print(res.stdout)


if __name__ == "__main__":
    unittest.main()
