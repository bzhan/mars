"""test for parsing files."""

import unittest

import sys
sys.path.append(r"/Users/jizekun/Desktop/形式语言/hcsp-c/mars-git")


from hcsp2c.parse2c import parse_file

# from ss2hcsp.hcsp.parser import parse_file

with open('/Users/jizekun/Desktop/形式语言/hcsp-c/mars-git/hcsp2c/example/hcsp2c_test.txt', 'r') as f:
    test = f.read()
    infos = parse_file(test)
    f.close()
print(infos)