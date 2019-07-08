#coding=utf-8
import json
from hcsp import *

def createStructure(dic):
    lines=[]
    for category in dic.values():
        if len(category['components']) > 0:
            hp1 = HCSP(category['name'])
            hps = []
            for com in category['components']:
                hps.append(HCSP(com['name']))

            if len(hps) > 1:
                hp2 = Parallel(*hps)
            else:
                hp2 = hps[0]

            hp = Defination(hp1, hp2)
            lines.append(hp)

            #对于声明名于应用名不一致的情况增加一条定义
            for com in category['components']:
                if 'name_impl' in com:
                    hp1 = HCSP(com['name'])
                    hp2 = HCSP(com['name_impl'])
                    hp = Defination(hp1, hp2)
                    lines.append(hp)
    return lines

def createConnections(dic):
    lines = []
    for category in dic.values():
        if len(category['connections']) > 0:
            hp1 = HCSP(category['name']+"_Conns")
            hps = []
            for com in category['connections']:
                hp_in = InputChannel(com['source'].strip().replace('.','_'),'x')
                hp_out = OutputChannel(com['destination'].strip().replace('.','_'),'x')
                hp = Sequence(*[hp_in,hp_out])
                hps.append(hp)

            if len(hps) > 1:
                hp2 = Parallel(*hps)
            else:
                hp2 = hps[0]

            hp = Defination(hp1, hp2)
            lines.append(hp)

    return lines

class Process:
    def __init__(self, process , threadlines ,protocal='HPF'):
        self.threadlines= threadlines
        self.lines=[]
        self.protocal = protocal
        self.process_name = process['name']

        self.lines.append(self._createSchedule())
        self.lines.append(self._createDispatch())
        self.lines.append(self._createChange())


    def _createSchedule(self):

        if self.protocal == 'HPF':   ##
            hp1 = HCSP('SCHEDULE_'+self.process_name)
            hps = [Assign(self.process_name+'_run_now','0'),
                   Assign(self.process_name+'_run_prior','0'),
                   Assign(self.process_name+'_ready_num','0')]

            hps3 = []
            for thread in self.threadlines:
                hps2=[]
                hps2.append(InputChannel('tranR_'+thread,'prior'))
                hps2.append('INSERT(' + thread +' , prior )')
                hps2.append(Assign(self.process_name+'_ready_num',self.process_name+'_ready_num+1'))
                hps3.append(Sequence(*hps2))

            if len(hps3)==1:
                hps3=hps3[0]
            else:
                hps3 = Parallel(*hps3)

            hps.append(Loop(hps3))
            hps.append(Loop('DISPATACH_'+self.process_name))
            hps=Sequence(*hps)
            hp = Defination(hp1,hps)

            return hp

    def _createDispatch(self):
        if self.protocal == 'HPF':  ##
            hp1 = HCSP('DISPACH_' + self.process_name)
            hps = [InputChannel(self.process_name + '_free')]
            con1 = "ready_num > 0"
            con2 = "ready_num = 0"
            con_hp1 = Sequence('CHANGE(first_ready, first_prior)',Assign(self.process_name+'_ready_num',self.process_name+'_ready_num-1'))
            con_hp2 = Sequence(Assign(self.process_name+'_run_now','0'),Assign(self.process_name+'_run_prior','0'))

            hps.append(Condition(con1,con_hp1))
            hps.append(Condition(con2, con_hp2))
            hps = Sequence(*hps)
            hp = Defination(hp1, hps)

            return hp

    def _createChange(self):
        if self.protocal == 'HPF':  ##
            hp1 = HCSP('CHANGE_' + self.process_name +'(thread, prior)')
            hps=[]
            for thread in self.threadlines:
                con = 'thread = '+thread
                con_hp = []
                con_hp.append(Assign(self.process_name + '_run_now',thread))
                con_hp.append(Assign(self.process_name + '_run_prior','prior'))
                con_hp.append(OutputChannel('run_' + thread))
                con_hp = Sequence(*con_hp)
                hps.append(Condition(con,con_hp))

            if len(hps) == 1:
                hps = hps[0]
            else:
                hps = Parallel(*hps)

            hp = Defination(hp1,hps)

            return hp

class Thread:
    def __init__(self,thread):
        self.lines = []
        self.thread_name = thread['name']
        ### 默认参数###
        self.thread_protocal = 'Periodic'
        self.thread_priority = '1'
        self.thread_deadline = '10'
        self.thread_period = '10'
        if len(thread['opas']) > 0:
            for opa in thread['opas']:
                if opa['name'] == 'Thread_Properties.Dispatch_Protocol':
                    if opa['value'] == 'Periodic':
                        self.thread_protocal = 'Periodic'

                elif opa['name'] == 'Thread_Properties.Priority':
                    self.thread_priority = opa['value']

                elif opa['name'] == 'Timing_Properties.Deadline':
                    self.thread_deadline = opa['value']

                elif opa['name'] == 'Timing_Properties.Period':
                    self.thread_period = opa['value']

        self.lines.extend(self._createThread())
        #self.lines.append(self._createReady())
        #self.lines.append(self._createAwait())
        #self.lines.append(self._createRunning())


    def _createThread(self):
        lines=[]

        hp1 = HCSP(self.thread_name+'('+self.thread_protocal+','+ self.thread_priority +','+ \
                   self.thread_deadline+','+self.thread_period+')')
        hps = Parallel(*[Loop(HCSP('ACT_'+self.thread_name)),Loop(HCSP('COM_'+self.thread_name))])
        hp = Defination(hp1,hps)
        lines.append(hp)

        if self.thread_protocal== 'Periodic':
            act_hp1 = HCSP('ACT_'+self.thread_name)
            act_hps = Sequence(*[OutputChannel(self.thread_name+'_act'),Wait(self.thread_period)])
            act_hp = Defination(act_hp1,act_hps)
        lines.append(act_hp)

        com_hp1 = HCSP('COM_' + self.thread_name)
        com_hps = [InputChannel(self.thread_name + '_act')]

        com_ready = []
        com_ready.append(Assign('t','0'))
        com_ready.append(Assign('isReady', '1'))
        com_ready.append(Loop(Condition('isReady',HCSP('Ready_'+self.thread_name))))
        com_ready = Sequence(*com_ready)

        com_running = []
        com_running.append(Assign('c', '0'))
        com_running.append(Loop(HCSP('Running_' + self.thread_name)))
        com_running = Sequence(*com_running)

        com_await = Loop(HCSP('Await_' + self.thread_name))

        com_hps.append(Parallel(*[com_ready,com_running,com_await]))
        com_hps = Sequence(*com_hps)
        com_hp = Defination(com_hp1, com_hps)

        lines.append(com_hp)

        return lines

    #def _createReady(self,thread):


    #def createAwait():

    #def createRunning():



if __name__ == '__main__':
    file = 'out.json'
    out=""
    with open(file, 'r') as f:
        dic = json.load(f)
    out += "\n".join(str(line) for line in createStructure(dic))+'\n'
    out += "\n".join(str(line) for line in createConnections(dic))+'\n'

    for category in dic.values():
        if category['category'] == 'process' and len(category['components']) > 0:
            threadlines = []
            for com in category['components']:
                if com['category'] == 'thread':
                    threadlines.append(com['name'])
            out += "\n".join(str(line) for line in Process(category,threadlines).lines) + '\n'

        elif category['category'] == 'thread':
            out += "\n".join(str(line) for line in Thread(category).lines) + '\n'


    print(out)



