
import re
import numpy
import pandas
import codecs

basicfile=""

class THREAD:
    def __init__(self,name):
        self.name=name

    def setPriority(self,priority):
        self.priority = priority

    def setDispatch_protocal(self,dispatch_protocol):
        self.dispatch_protocol = dispatch_protocol

    def setDeadline(self,deadline):
        self.deadline = deadline

    def setPeriod(self,period):
        self.period = period


key_words=['THREAD','THREAD IMPLEMENTATION']
stop_word='END'
threadbox={}
outStructbox={}

def outstruct(name,out_port):
    cstruct="typedef struct node{\n"
    for arg in out_port.keys():
        cstruct+=out_port[arg]+' '+arg+';\n'
    cstruct += "}"+name+'Port;\n'
    outStructbox[name] = cstruct
    #print(cstruct)


def parser_th(name,infile):

   in_port={}
   out_port={}
   for line in infile:
       if re.search('DATA', line) and re.search('PORT', line):
           port_name = line.strip('\r\n:;').split()[0]
           if re.search('IN', line):
               in_port[port_name]=line.strip('\r\n:;').split()[-1]
           if re.search('OUT', line):
               out_port[port_name] = line.strip('\r\n:;').split()[-1]
       elif re.search('EVENT', line) and re.search('PORT', line):
           port_name = line.strip('\r\n:;').split()[0]
           if re.search('IN', line):
               in_port[port_name]='bool'
           if re.search('OUT', line):
               out_port[port_name] = 'bool'

   threadbox[name]={}
   threadbox[name]['head']=""
   if len(out_port)==0:
       threadbox[name]['head']+='void '
   elif len(out_port)==1:
       threadbox[name]['head']+='int '
   else:
       outstruct(name, out_port)
       threadbox[name]['head']+= name+'Port  '

   threadbox[name]['head'] += name + '('
   for i in in_port.keys():
       threadbox[name]['head']+= str(in_port[i]+' '+i+',')

   threadbox[name]['head'] = threadbox[name]['head'][:-1]  + '){\n'

   if name in threadbox.keys():
       # 写入输出端口变量
       for out in list(out_port.keys()):
           threadbox[name]['head'] += out_port[out] + ' ' + out + ';\n'

   threadbox[name]['tail'] = ""
   if len(out_port)==1:
       result=list(out_port.keys())[0]
       threadbox[name]['tail'] += 'return '+str(result)+';\n } \n'
   elif len(out_port)>1:
       threadbox[name]['tail'] +=name+'Port result;\n'
       for out in out_port.keys():
           threadbox[name]['tail'] +='result.'+out+'='+out+';\n'
       threadbox[name]['tail'] +='return result; \n}\n'




def parser_im(name,infile):
    th=THREAD(name)
    var={}

    i=0
    for i in range(len(infile)):
        line=infile[i]
        #SUB_block
        if re.search('SUBCOMPONENTS',line):
            i+=1
            while not re.search('PROPERTIES',infile[i]):
                line=infile[i]
                var[line.strip('\r\n;').split()[0]]=line.strip('\r\n;').split()[-1]
                i+=1

        line = infile[i]
        #PRO_block
        if re.search('Priority', line):
            prio = line.strip('\n').replace('Priority', '').replace('=>', '').replace(';', '').strip(' ')
            th.setPriority(prio)
        if re.search('Dispatch_Protocol', line):
            protocol = line.strip('\n').replace('Dispatch_Protocol', '').replace('=>', '').replace(';', '').strip(' ')
            th.setDispatch_protocal(protocol)
        if re.search('Period', line):
            period = line.strip('\n').replace('Period', '').replace('=>', '').replace(';', '').strip(' ')
            th.setPeriod(period)
        if re.search('Deadline', line):
            deadline = line.strip('\n').replace('Deadline', '').replace('=>', '').replace(';', '').strip(' ')
            th.setDeadline(deadline)

         #ANNEX_block

        if re.search('ANNEX', infile[i]):
            i+=1
            while not re.search('\*\*}',infile[i]) and i<len(infile):
                if re.search('VARIABLES', infile[i]):
                    sen=re.split(r'[,:]',infile[i].strip('\r\n; ').replace('VARIABLES', ''))
                    for k in range(len(sen)-1):
                        var[sen[k]]=sen[-1]
                    i+=1
                    #print(var)
                elif re.search('TRANSITIONS', infile[i]):
                    context=""
                    i += 1
                    while not re.search('\*\*}', infile[i]) and i<len(infile):
                        if re.search('!', infile[i]):
                            for clause in infile[i].split():
                                if '!' in clause:
                                    #newclause=clause[:-2]+'=!'+ clause[:-2]+';'
                                    newclause=clause[:-2]+'=1;'
                                    infile[i]=infile[i].replace(clause,newclause)
                                    break

                        if re.search('if', infile[i]) and not re.search('end', infile[i]):
                            infile[i] = infile[i].replace(')','){')

                        elif re.search('end if', infile[i]) :
                            infile[i] = infile[i].replace('end if;',';}')
                        else:
                            infile[i] = infile[i].replace('{', '').replace('}', '').replace(';', ';\n')
                        context+=infile[i]
                        i+=1
                    context = context.replace(':=', '=')
                    #print(context)
                else:
                    i+=1


    if name in threadbox.keys():
        threadbox[name]['body']=""
        # 写入内部变量
        for v in list(var.keys()):
            threadbox[name]['body']+= var[v]+' '+v+';\n'
        #写入内容
        threadbox[name]['body'] +=context

def blockSplit(file_in):

    with codecs.open(file_in, 'r', encoding="utf-8") as in_f:
        f_sentence = list(in_f)
        #print(f_sentence)
        i=0
        while i< len(f_sentence):
            if re.search(key_words[0], f_sentence[i]) and f_sentence[i].split()[1] !='IMPLEMENTATION':
                name=f_sentence[i].split()[1]
                #print(name)
                body_th=[]
                i+=1 # 跳过THREAD声明
                while not re.search(stop_word, f_sentence[i]):
                    body_th.append(f_sentence[i])
                    i+=1
                parser_th(name,body_th)
                #print(body_th)

            elif re.search(key_words[1], f_sentence[i]):
                name = f_sentence[i].split()[2].split('.')[0]
                #print(name)
                body_im = []
                i += 1 #跳过THREAD声明
                while not re.search(stop_word, f_sentence[i]):
                    body_im.append(f_sentence[i])
                    i += 1
                parser_im(name,body_im)

                #print(body_im)
            i+=1


def Merge():
    cfile=""
    cfile+=basicfile
    for out in outStructbox.keys():
        cfile+=outStructbox[out]
    for th in threadbox.keys():
        cfile+=threadbox[th]['head']+threadbox[th]['body']+threadbox[th]['tail']

    print(cfile)
    with open('conditioner_1.c','a') as out_c_f:
        out_c_f.write(cfile + '\n')


if __name__=='__main__':
    file_in = 'conditioner.aadl'
    blockSplit(file_in)
    Merge()