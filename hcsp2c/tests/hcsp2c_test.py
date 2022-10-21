import unittest

from ss2hcsp.hcsp import parser
from hcsp2c import transfer2c


header = \
"""
#include "hcsp2c.h"

double step_size = 1e7;
double min_step_size = 1e10;
"""

main_header = \
"""
int main() {
    printf("The program starts.\\n");
    fflush(stdout);
    const int threadNumber = %d;
    const int channelNumber = %d;
    void* (*threadFuns[threadNumber])(void*);
"""

main_footer = \
"""
    init(threadNumber, channelNumber, threadFuns);
    printf(\"The program is completed.\\n\");
    fflush(stdout);
    destroy(threadNumber, channelNumber);
    return 0;
}
"""

class HCSP2CTest(unittest.TestCase):
    def test1(self):
        progs = [
            "x := 0; { {x_dot = 1 & true} |> [](p2c!x --> skip;) c2p?x; }*",
            "{ wait(2); p2c?x; c2p!x-1; }*"
        ]

        hps = [parser.hp_parser.parse(prog) for prog in progs]

        channels = set()
        threads = []
        for hp in hps:
            channels.update(hp.get_chs())

        res = ""
        res += header
        count = 0
        for channel in channels:
            res += "const int %s = %d;\n" % (channel, count)
            count += 1

        for i, hp in enumerate(hps):
            name = "P" + str(i+1)
            threads.append(name)
            code = transfer2c.transferToCProcess(name, hp)
            res += code

        res += main_header % (len(threads), count)
        count = 0
        for thread in threads:
            res += "\tthreadFuns[%d] = &%s;\n" %(count, thread)
            count += 1

        res += main_footer

        with open('hcsp2c/target/test1.c', 'w') as f:
            f.write(res)


if __name__ == "__main__":
    unittest.main()
