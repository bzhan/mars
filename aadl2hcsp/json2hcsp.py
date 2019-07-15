"""Convert AADL model (in JSON format) to HCSP programs."""

import json
from aadl2hcsp.hcsp import *

def createStructure(dic):
    lines=[]
    for category in dic.values():
        if len(category['components']) > 0:
            hp1 = HCSP(category['name'])
            hps = []
            for com in category['components']:
                hps.append(HCSP(com['name']))

            if len(category['connections']) >0:
                hps.append(HCSP('Comms_'+category['name']))

            if len(category['category']) == 'Process':
                hps.append(HCSP('SCHEDULE_' + category['name']))

            if len(hps) > 1:
                hp2 = Parallel(*hps)
            else:
                hp2 = hps[0]

            hp = Definition(hp1, hp2)
            lines.append(hp)

            #对于声明名于应用名不一致的情况增加一条定义
            for com in category['components']:
                if 'name_impl' in com:
                    hp1 = HCSP(com['name'])
                    hp2 = HCSP(com['name_impl'])
                    hp = Definition(hp1, hp2)
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

            hp = Definition(hp1, hp2)
            lines.append(hp)

    return lines

class Process:
    def __init__(self, process , threadlines ,protocal='HPF'):
        self.threadlines= threadlines
        self.lines=[]
        self.protocal = protocal
        self.process_name = process['name']

        self.lines.append(self._createSchedule())
        self.lines.append(self._createBusy())

    def _createSchedule(self):

        if self.protocal == 'HPF':   ##
            hp1 = HCSP('SCHEDULE_'+self.process_name)
            hps = [Assign('run_now','0'),
                   Assign('run_prior','0'),
                   Assign('ready_num','0')]

            hps2 = []
            for thread in self.threadlines:
                hps2.append(self._preemptPriority(thread))
            hps2.append(self._freeAction())

            hps2 = SelectComm(*hps2)
            hps.append(Loop(hps2))
            hps= Sequence(*hps)
            hp = Definition(hp1,hps)

            return hp


    def _preemptPriority(self,thread):
        hps=[]
        hps.append(InputChannel('tran_'+str(thread)))
        con1= 'run_prior < prior'
        con2= 'run_prior > prior'
        con_hp1 = Sequence('BUSY_'+self.process_name,
                           Assign('run_now', str(thread)),
                           Assign('run_prior','prior'),
                           OutputChannel('run_'+str(thread)))

        con_hp2 = Sequence('INSERT_' + self.process_name +'('+str(thread) +')',
                           Assign('ready_num', 'ready_num+1'))

        hps.append(Condition(con1, con_hp1))
        hps.append(Condition(con2, con_hp2))

        hps = Sequence(*hps)

        return hps

    def _freeAction(self):
        hps = []
        hps.append(InputChannel('free'))
        con1 = 'ready_num > 0'
        con2 = 'ready_num = 0'
        con_hp1 = Sequence('CHANGE_' + self.process_name,
                           Assign('ready_num', 'ready_num-1'))

        con_hp2 = Sequence(Assign('run_now', '0'),
                           Assign('run_prior', '0'))

        hps.append(Condition(con1, con_hp1))
        hps.append(Condition(con2, con_hp2))

        hps = Sequence(*hps)

        return hps

    def _createBusy(self):
        hp1 = HCSP('BUSY_' + self.process_name)

        hps = []
        for thread in self.threadlines:
            con = 'run_now = '+str(thread)
            con_hp = OutputChannel('busy_'+str(thread))
            hps.append(Condition(con,con_hp))

        hps = Sequence(*hps)
        hp = Definition(hp1, hps)

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

            hp = Definition(hp1,hps)

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
        self.thread_featureIn = []
        self.thread_featureOut = []

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

        for feature in thread['features']:
            if feature['type'] == 'DataPort':
                if feature['direction'] == 'Out':
                    self.thread_featureOut.append(feature['name'])
                else:
                    self.thread_featureIn.append(feature['name'])

        self.lines.extend(self._createThread())
        self.lines.append(self._createReady())
        self.lines.append(self._createAwait())
        self.lines.append(self._createRunning())


    def _createThread(self):
        lines=[]

        hp1 = HCSP(self.thread_name)
        hps = Parallel(*[Loop(HCSP('ACT_'+self.thread_name)),
                         Loop(HCSP('DIS_'+self.thread_name)),
                         Loop(HCSP('COM_'+self.thread_name))])
        hp = Definition(hp1,hps)
        lines.append(hp)

        if self.thread_protocal == 'Periodic':
            act_hp1 = HCSP('ACT_'+self.thread_name)
            act_hps = OutputChannel('act_'+self.thread_name)
            act_hp = Definition(act_hp1,act_hps)
            lines.append(act_hp)

            dis_hp1 = HCSP('DIS_' + self.thread_name)
            dis_hps = [InputChannel('act_' + self.thread_name),
                       Wait(self.thread_period),
                       OutputChannel('dis_' + self.thread_name)]

            for feature in self.thread_featureIn:
                dis_hps.append('GetData('+feature+')')

            dis_hps.append(OutputChannel('input_'+self.thread_name, str(self.thread_featureIn)))

            dis_hps.append(Parallel(InputChannel('complete_'+self.thread_name),
                                    InputChannel('exit_'+self.thread_name)))

            dis_hps = Sequence(*dis_hps)
            dis_hp = Definition(dis_hp1, dis_hps)
            lines.append(dis_hp)

        com_hp1 = HCSP('COM_' + self.thread_name)
        com_hps = [InputChannel('dis_'+self.thread_name),
                   Assign('t','0'),
                   OutputChannel('init_'+self.thread_name, 't')]

        com_ready = Loop(HCSP('Ready_'+self.thread_name))

        com_running = []
        com_running.append(Assign('c', '0'))
        com_running.append(Loop(HCSP('Running_' + self.thread_name)))
        com_running = Sequence(*com_running)

        com_await = Loop(HCSP('Await_' + self.thread_name))

        com_annex = HCSP('Annex_' + self.thread_name)

        com_hps.append(Parallel(*[com_ready,com_running,com_await,com_annex]))
        com_hps = Sequence(*com_hps)
        com_hp = Definition(com_hp1, com_hps)

        lines.append(com_hp)

        return lines

    def _createReady(self):
        hp1 = HCSP('Ready_' + self.thread_name)
        hps = []
        hps2 = [InputChannel('init_'+self.thread_name, 't'),
                InputChannel('preempt_'+self.thread_name, 't'),
                InputChannel('unblock_'+self.thread_name, 't')]

        hps2 = SelectComm(*hps2)
        hps.append(hps2)
        hps.append(OutputChannel('tran_'+self.thread_name,'properties'))

        eqs = [('t','1')]
        constraint = 't <'+self.thread_deadline
        io_comms = [(InputChannel('run_'+self.thread_name),
                     OutputChannel('resume_'+self.thread_name, 't'))]
        hps.append(ODE_Comm(eqs,constraint,io_comms))
        con ='t='+self.thread_deadline
        con_hp = OutputChannel('exit_'+self.thread_name)
        hps.append(Condition(con,con_hp))

        hps = Sequence(*hps)
        hp = Definition(hp1, hps)

        return hp

    def _createAwait(self):
        hp1 = HCSP('Await_' + self.thread_name)
        hps = [InputChannel('block_' + self.thread_name, 't')]

        eqs = [('t', '1')]
        constraint = 't <' + self.thread_deadline
        io_comms = [(InputChannel('haveResource_' + self.thread_name),
                     OutputChannel('unblock_' + self.thread_name, 't'))]

        hps.append(ODE_Comm(eqs, constraint, io_comms))
        con = 't=' + self.thread_deadline
        con_hp = OutputChannel('exit_' + self.thread_name)
        hps.append(Condition(con, con_hp))

        hps = Sequence(*hps)
        hp = Definition(hp1, hps)

        return hp

    def _createRunning(self):
        hp1 = HCSP('Running_' + self.thread_name)
        hps = [InputChannel('resume_' + self.thread_name, 't'),
               OutputChannel('run_Annex_'+self.thread_name)]

        eqs = [('t', '1'),('c', '1')]
        constraint = 't <' + self.thread_deadline
        in1 = InputChannel('busy_' + self.thread_name)
        out1 = OutputChannel('preempt_' + self.thread_name, 't')

        in2 = InputChannel('needResource_' + self.thread_name)
        out2 = Sequence(*[OutputChannel('block_' + self.thread_name, 't'),
                          OutputChannel('free')])

        in3 = InputChannel('complete_Annex_' + self.thread_name)
        out3 = []
        for feature in self.thread_featureOut:
            out3.append('SetData('+feature+')')
        out3.append(OutputChannel('free'))
        out3.append(OutputChannel('complete'+self.thread_name))
        out3 = Sequence(*out3)


        io_comms = [(in1, out1), (in2, out2), (in3, out3)]

        hps.append(ODE_Comm(eqs, constraint, io_comms))
        con = 't=' + self.thread_deadline
        con_hp = Sequence(OutputChannel('free'),
                          OutputChannel('exit_' + self.thread_name))
        hps.append(Condition(con, con_hp))

        hps = Sequence(*hps)
        hp = Definition(hp1, hps)

        return hp
