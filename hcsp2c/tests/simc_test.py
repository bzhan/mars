import unittest
import subprocess

from hcsp2c import transfer2c
from ss2hcsp.hcsp.parser import parse_module_file

class SimcTest(unittest.TestCase):
    def run_test(self, file, outputfile, *, step_size=1e-3, output_step_size=1.0, max_time=10.0, expected_output=None):
        with open(file, "r") as f:
            s = f.read()
            infos = parse_module_file(s)

        res = transfer2c.convertHps(infos, step_size=1e-3, output_step_size=2.0, maxTime=10.0)

        with open('hcsp2c/target/%s.c' % outputfile, 'w') as f:
            f.write(res)
        res = subprocess.run(
            "sudo gcc hcsp2c/target/%s.c -lpthread -o hcsp2c/output/%s.out" % (outputfile, outputfile),
            stderr=subprocess.PIPE,
            text=True,
            shell=True
        )

        # Handle exception resulting from conversion step
        if res.stderr != '':
            err = res.stderr
            raise Exception(err)

        res = subprocess.run(
            "./hcsp2c/output/%s.out" % outputfile,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            shell=True
        )

        if expected_output:
            self.assertEqual(res.stdout, '\n'.join(expected_output) + '\n')
        else:
            print(res.stdout)

    def testLunarLander(self):
        self.run_test(
            "./Examples/Simulink/LunarLander.txt", "LunarLander",
            step_size=1e-3,
            output_step_size=2.0,
            max_time=10.0,
            expected_output=[
                "0.000: {m = 1250.000 v = -2.000 Fc = 2437.055}",
                "2.000: {m = 1248.202 v = -1.645 Fc = 2122.533}",
                "4.000: {m = 1246.543 v = -1.563 Fc = 2044.469}",
                "6.000: {m = 1244.916 v = -1.543 Fc = 2026.087}",
                "8.000: {m = 1243.298 v = -1.536 Fc = 2019.523}",
                "10.000: {m = 1241.684 v = -1.532 Fc = 2016.002}"
            ])

    def testMarsLander(self):
        self.run_test(
            "./Examples/Simulink/MarsLander.txt", "MarsLander",
            step_size=1e-3,
            output_step_size=2.0,
            max_time=10.0,
            expected_output=[
                "0.000: {m = 759.500 v = -1.500 Fc = 2834.449 r = 20.000}",
                "2.000: {m = 757.141 v = -1.500 Fc = 2825.807 r = 17.001}",
                "4.000: {m = 754.790 v = -1.499 Fc = 2816.761 r = 14.002}",
                "6.000: {m = 752.447 v = -1.499 Fc = 2808.348 r = 11.003}",
                "8.000: {m = 750.110 v = -1.499 Fc = 2799.413 r = 8.004}",
                "10.000: {m = 747.781 v = -1.499 Fc = 2790.511 r = 5.005}"
            ]
        )

if __name__ == "__main__":
    unittest.main()
