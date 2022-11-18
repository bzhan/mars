from os import listdir
from os.path import isfile, join, dirname
import time
import re

from hhlpy.wolframengine_wrapper import session
from ss2hcsp.hcsp.parser import parse_hoare_triple_with_meta
from hhlpy.hhlpy import CmdVerifier
from ss2hcsp.hcsp import expr

def natural_sort(l): 
    convert = lambda text: int(text) if text.isdigit() else text.lower() 
    alphanum_key = lambda key: [convert(c) for c in re.split('([0-9]+)', key)] 
    return sorted(l, key=alphanum_key)

def eval(name, filenames):
    if name == "basic":
        title = "Basic Benchmarks"
    elif name == "nonlinear":
        title = "Nonlinear Benchmarks"

    print(f"=== {title} ===")
    start = time.perf_counter()
    failures = 0
    completed = 0
    for file in filenames:

        print("Running {}. ".format(file), end ="")

        tic = time.perf_counter()
        file = join(path, file)
        file = open(file, mode='r', encoding='utf-8')
        file_contents = file.read()
        file.close()

        # Parse pre-condition, HCSP program, and post-condition
        hoare_triple = parse_hoare_triple_with_meta(file_contents)

        # Initialize the verifier
        verifier = CmdVerifier(
                    pre=hoare_triple.pre, 
                    hp=hoare_triple.hp,
                    post=hoare_triple.post,
                    constants=hoare_triple.constants,
                    functions=hoare_triple.functions)

        # Compute wp and verify
        verifier.compute_wp()
        res = verifier.verify()
        toc = time.perf_counter()

        if res:
            print(f"Completed in {toc - tic:0.4f} seconds.")
            completed += 1
        else:
            print(f"Failed after {toc - tic:0.4f} seconds.")
            failures += 1
    stop = time.perf_counter()
    print(f"Completed {completed} {name} examples in {stop - start:0.4f} seconds.")
    if failures > 0:
        print(f"{failures} failure(s).")
    print("")

if __name__ == "__main__":
    print("Starting Wolfram Engine.")

    with session:
        example_categs = ["basic", "nonlinear"]
        for categ in example_categs:
            path = join(dirname(__file__), "examples", categ)
            file_names = natural_sort([f for f in listdir(path) if isfile(join(path, f))])
            eval(categ, file_names)
