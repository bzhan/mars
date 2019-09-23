import json
import json2hcsp
from ss2hcsp.hcsp.expr import AVar, AConst, PlusExpr, RelExpr
from ss2hcsp.hcsp.hcsp import *
from aadl2hcsp.parserAnnex import *
from aadl2hcsp.json2hcsp import *

class code:
    def __init__(self):
        self.line=""
        self.delname=[]

    def generator(self, code):
        self.line='\n'.join(str(hp) for _, hp in code)

        for name, hp in code:
            temp_line=self.line
            self.line=self.line.replace('@'+str(name), str(hp))
            if self.line != temp_line:
                self.delname.append(name)

        for name in self.delname:
            for hpname, hp in code:
                if str(name)==str(hpname):
                    self.line=self.line.replace(str(hp)+'\n','')

        self.line = self.line.replace(' || ','\n')

        return self.line


c=code()
json_file = '../Examples/AADL/air_conditioner/out_ref.json'
annex_file = '../Examples/AADL/air_conditioner/air_conditioner.aadl'
out_file = '../Examples/AADL/air_conditioner/hcsp.txt'
ref_file = '../Examples/AADL/air_conditioner/hcsp_ref.txt'

out = json2hcsp.convert_AADL(json_file, annex_file)
print(c.generator(out.hps))
