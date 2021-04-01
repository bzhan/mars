'''
Command:
python plot.py file0, file1, ...
'''

import sys
import matplotlib.pyplot as plt

for file_name in sys.argv[1:]:
    f = open(file_name+".txt", 'r')
    lines = f.readlines()
    f.close()
    assert len(lines) == 1
    data = [float(e.strip()) for e in lines[0].split(',') if e]
    plt.plot(data)
plt.show()

