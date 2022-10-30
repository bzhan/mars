import unittest
import subprocess

from hcsp2c import transfer2c
from ss2hcsp.hcsp.parser import parse_module_file

class SysTest(unittest.TestCase):
    def run_test(self, file, outputfile, *, step_size=1e-3, output_step_size=1.0, max_time=10.0, expected_output=None):
        with open(file, "r") as f:
            s = f.read()
            infos = parse_module_file(s)

        (res, head_res, threads_res) = transfer2c.convertHps(outputfile, infos, step_size=step_size, output_step_size=output_step_size,
                                    max_time=max_time)

        run_str = "sudo gcc"
        with open('hcsp2c/target/%s.c' % outputfile, 'w') as f:
            f.write(res)
            run_str += ' hcsp2c/target/%s.c' % outputfile
        with open('hcsp2c/target/%s.h' % outputfile, 'w') as f:
            f.write(head_res)
        for (thread_name, thread_body) in threads_res:
            with open('hcsp2c/target/%s__%s.c' % (outputfile, thread_name), 'w') as f:
                f.write(thread_body)
                run_str += ' hcsp2c/target/%s__%s.c' % (outputfile, thread_name)
        
        run_str += " hcsp2c/target/hcsp2c.c -lpthread -lm -o hcsp2c/output/%s.out" % outputfile

        res = subprocess.run(
            run_str,
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

    def testSystemv2(self):
        self.run_test(
            "./Examples/AADL/CCS/TCS/generatedcode/systemv2.txt", "systemv2",
            step_size=1e-3,
            output_step_size=2.0,
            max_time=10.0,
            expected_output=[
            ])

    def testMarsLander(self):
        self.run_test(
            "./Examples/Simulink/MarsLander.txt", "MarsLander",
            step_size=1e-3,
            output_step_size=2.0,
            max_time=10.0,
            expected_output=[
                "0.000: m = 759.500, v = -1.500, Fc = 2834.449, r = 20.000",
                "2.000: m = 757.141, v = -1.500, Fc = 2825.807, r = 17.001",
                "4.000: m = 754.790, v = -1.499, Fc = 2816.761, r = 14.002",
                "6.000: m = 752.447, v = -1.499, Fc = 2808.348, r = 11.003",
                "8.000: m = 750.110, v = -1.499, Fc = 2799.413, r = 8.004",
                "10.000: m = 747.781, v = -1.499, Fc = 2790.511, r = 5.005"
            ]
        )

    def testAbstractFuelControlM2(self):
        self.run_test(
            "./Examples/Simulink/AbstractFuelControl_M2.txt", "AbstractFuelControl_M2",
            step_size=1e-3,
            output_step_size=5.0,
            max_time=31.0,
            expected_output=[
                "0.000: AF = 14.700, TA = 8.800, ES = 1000.000",
                "5.000: AF = 14.746, TA = 84.100, ES = 1000.000",
                "10.000: AF = 14.700, TA = 84.100, ES = 1000.000",
                "15.000: AF = 14.690, TA = 8.800, ES = 1000.000",
                "20.000: AF = 14.731, TA = 84.100, ES = 1000.000",
                "25.000: AF = 14.701, TA = 84.100, ES = 1000.000",
                "30.000: AF = 14.679, TA = 8.800, ES = 1000.000"
            ]
        )


if __name__ == "__main__":
    unittest.main()
