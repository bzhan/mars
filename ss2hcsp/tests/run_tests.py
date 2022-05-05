import os

def run_cmds():
    cmds = [
        'python -m unittest ss2hcsp.tests.expr_test',
        'python -m unittest ss2hcsp.tests.isabelle_test',
        'python -m unittest ss2hcsp.tests.matlab_test',
        'python -m unittest ss2hcsp.tests.module_test',
        'python -m unittest ss2hcsp.tests.optimize_test',
        'python -m unittest ss2hcsp.tests.parser_test',
        'python -m unittest ss2hcsp.tests.pprint_test',
        'python -m unittest ss2hcsp.tests.sf_convert_test',
        'python -m unittest ss2hcsp.tests.sf_isabelle_test',
        'python -m unittest ss2hcsp.tests.sim_test',
        'python -m unittest ss2hcsp.tests.simulator_test',
        'python -m unittest ss2hcsp.tests.systemC_test',
        'python -m unittest ss2hcsp.tests.topsort_test',
        'python -m unittest ss2hcsp.tests.transition_test',
    ]

    for cmd in cmds:
        os.system(cmd)

if __name__ == '__main__':
    run_cmds()