from os import listdir
from os.path import isfile, join, dirname
import time

from ss2hcsp.hcsp.parser import parse_hoare_triple_with_meta
from hhlpy.hhlpy import CmdVerifier
from ss2hcsp.hcsp import expr

if __name__ == "__main__":
    start = time.perf_counter()
    path = join(dirname(__file__), "examples")
    filenames = [f for f in listdir(path) if isfile(join(path, f))]
    for file in filenames:

        if not (file.startsWith("basic") or file.startsWith("nonlinear")):
            print("Skipping {}".format(file))
            continue

        print("Running {}".format(file))
        tic = time.perf_counter()
        file = join(dirname(__file__), "examples", file)
        file = open(file,mode='r')
        file_contents = file.read()
        file.close()

        # Parse pre-condition, HCSP program, and post-condition
        hoare_triple = parse_hoare_triple_with_meta(file_contents)

        # Initialize the verifier
        verifier = CmdVerifier(
            pre=expr.list_conj(*hoare_triple.pre), 
            hp=hoare_triple.hp,
            post=expr.list_conj(*hoare_triple.post))

        # Compute wp and verify
        verifier.compute_wp()
        verifier.verify()
        toc = time.perf_counter()
        print(f"Completed in {toc - tic:0.4f} seconds")
    stop = time.perf_counter()
    print(f"All benchmarks completed in {stop - start:0.4f} seconds")
