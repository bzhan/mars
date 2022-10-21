from collections import OrderedDict
import sys
from tkinter import N
# sys.path.append(r"/Users/jizekun/Desktop/形式语言/hcsp-c/mars-master")

from ss2hcsp.hcsp import hcsp, parser
from hcsp2c import c
from ss2hcsp.hcsp.expr import AExpr, AVar, AConst, BExpr, true_expr, false_expr, RelExpr, LogicExpr
from ss2hcsp.matlab import function
from ss2hcsp.util.topsort import topological_sort
import re

def parse_file(text):
    """Parsing regular HCSP files.

    Input is the string of the file. Output is a list of pairs (name, hp).

    """
    text_lines = text.strip().split('\n')
    hcsp_info = []

    c_thread_number = 0

    # First, read lines from file, each line containing ::= means the
    # start of a new program.
    lines = []
    for line in text_lines:
        comment_pos = line.find('#')
        if comment_pos != -1:
            line = line[:comment_pos]
        if line.find('::=') != -1:
            lines.append(line)
        else:
            if line != "":
                if len(lines) == 0:
                    raise parser.ParseFileException('Unexpected line: ' + line)
                lines[-1] += line + '\n'

    infos = []
    channels = set()
    threads = []

    # Now each entry in lines represent the definition of a program.
    for line in lines:
        index = line.index('::=')
        name = line[:index].strip()
        hp_text = line[index+3:].strip()

        try:
            hp = parser.hp_parser.parse(hp_text)
            c_thread_number = c_thread_number + 1
        except (parser.exceptions.UnexpectedToken, parser.exceptions.UnexpectedCharacters) as e:
            error_str = "Unable to parse\n"
            for i, line in enumerate(hp_text.split('\n')):
                error_str += line + '\n'
                if i == e.line - 1:
                    error_str += " " * (e.column-1) + "^" + '\n'
            raise parser.ParseFileException(error_str)

        cp = c.CInfo(name, c.transferToC(hp, 0, c_thread_number))
        infos.append(str(cp))
        channels.update(cp.get_chs())
        threads.append(name)
    
    res = "#include \"hcsp2c.h\"\n"
    res += "double step_size = 1e7; double min_step_size = 1e10;\n"
    count = 0
    for channel in channels:
        res += "const int %s = %d;" % (channel, count)
        count += 1
    for info in infos:
        res += "\n"
        res += info
    res += "\n int main() { printf(\"The program starts.\\n\"); fflush(stdout); const int threadNumber = %d; const int channelNumber = %d; void* (*threadFuns[threadNumber])(void*);" %(len(threads), count)
    count = 0
    for thread in threads:
        res += "threadFuns[%d] = &%s;" %(count, thread)
        count += 1

    res += "init(threadNumber, channelNumber, threadFuns); printf(\"The program is completed.\\n\"); fflush(stdout); destroy(threadNumber, channelNumber); return 0; }"

    return res