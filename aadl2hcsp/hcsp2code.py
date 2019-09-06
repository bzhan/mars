import json
from ss2hcsp.hcsp.expr import AVar, AConst, PlusExpr, RelExpr
from ss2hcsp.hcsp.hcsp import *
from aadl2hcsp.parserAnnex import *
from aadl2hcsp.json2hcsp import *

class code:
    def __init__(self):
        self.code_dic={}
        self.para_process={}
        self.rename={}
    def process_split(self, code):
        #code=code.strip().split('\n')
        for line in code:
            if not isinstance(line, Definition):
                print('Error' + str(line))
                continue
            if isinstance(line.hp2, Parallel):
                self.para_process[line.hp1] = []
                for seq in line.hp2.hps:
                    if seq.type=='name':
                        self.para_process[line.hp1].append(seq)
                    elif isinstance(seq, Sequence):
                        new_process=[]
                        for sub_seq in seq.hps:
                            if sub_seq.type=='name':
                                process_name=str(sub_seq)
                                print(process_name)
                            else:
                                new_process.append(sub_seq)

            elif isinstance(line.hp2, HCSP) and line.hp2.type=='name':
                self.rename[line.hp1]=str(line.hp2)
            else:
                self.code_dic[str(line.hp1)]={}
                self.code_dic[str(line.hp1)]['code']= str(line.hp2)
                self.code_dic[str(line.hp1)]['state'] = {}

c=code()
file = 'tests/out.json'
annex_file = 'air_conditioner/air_conditioner.aadl'
hcsp=[]
AP = AnnexParser()
Annexs = AP.getAnnex(annex_file)
Annex_HP = {}
for th in Annexs.keys():
    Annex_HP[th] = AP.createHCSP(Annexs[th][1:-1])

with open(file, 'r') as f:
    dic = json.load(f)

for line in createStructure(dic):
    hcsp.append(line)
for line in createConnections(dic):
    hcsp.append(line)

for category in dic.values():
    if category['category'] == 'process' and len(category['components']) > 0:
        threadlines = []
        for com in category['components']:
            if com['category'] == 'thread':
                threadlines.append(com['name'])
        for line in Process(category, threadlines).lines:
            hcsp.append(line)

    elif category['category'] == 'thread':
        if category['name'] in Annex_HP.keys():
            for line in Thread(category, Annex_HP[category['name']]).lines:
                hcsp.append(line)
        else:
            for line in Thread(category).lines:
                hcsp.append(line)

c.process_split(hcsp)
code=json.dumps(c.code_dic)
print(code)




    #def generator(self):
    #    if