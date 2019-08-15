"""Convert AADL model (in JSON format) to HCSP programs."""

import json
from ss2hcsp.hcsp.expr import AVar, AConst, PlusExpr, RelExpr
from ss2hcsp.hcsp.hcsp import *

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
                hp_in = InputChannel(com['source'].strip().replace('.','_'), 'x')
                hp_out = OutputChannel(com['destination'].strip().replace('.','_'), AVar('x'))
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
    def __init__(self, process , threadlines ,protocal='FIFO'):
        self.threadlines= threadlines
        self.lines=[]
        self.protocal = protocal
        self.process_name = process['name']

        self.lines.append(self._createSchedule())
        self.lines.append(self._createQueue())


    def _createSchedule(self):
        hp1 = HCSP('SCHEDULE_' + self.process_name)
        if self.protocal == 'HPF':   ##
            hps = [Assign('run_now', AConst(0)),
                   Assign('run_prior', AConst(0)),
                   Assign('ready_num', AConst(0))]

            hps2 = []
            for thread in self.threadlines:
                hps2.append(self._preemptPriority(thread))
            hps2.append(self._freeActionPriority())

            self.lines.append(self._createRun())
            self.lines.append(self._createBusy())

        elif self.protocal == 'FIFO':
            hps = [Assign('run_now', AConst(0)),
                   Assign('ready_num', AConst(0))]

            hps2 = []
            for thread in self.threadlines:
                hps2.append(self._noPreemptSequence(thread))
            hps2.append(self._freeActionSequence())

            self.lines.append(self._createRun())

        hps2 = SelectComm(*hps2)
        hps.append(Loop(hps2))
        hps= Sequence(*hps)
        hp = Definition(hp1,hps)

        return hp

    def _preemptPriority(self, thread):
        hps=[]
        hps.append(InputChannel('tran_'+str(thread), AVar('prior')))  # insert variable
        con1= RelExpr('<', AVar('run_prior'), AVar('prior'))
        con2= RelExpr('>', AVar('run_prior'), AVar('prior'))
        con_hp1 = Sequence(HCSP('BUSY_' + self.process_name),
                           Assign('run_now', AVar(thread)),
                           Assign('run_prior', AVar('prior')),
                           OutputChannel('run_' + str(thread)))  # insert output

        con_hp2 = Sequence(OutputChannel('insert_' + str(thread), AVar('prior')),
                           Assign('ready_num', PlusExpr(['+','+'], [AVar('ready_num'), AConst(1)])))

        hps.append(Condition(con1, con_hp1))
        hps.append(Condition(con2, con_hp2))

        hps = Sequence(*hps)

        return hps

    def _noPreemptSequence(self, thread):
        hps = [ InputChannel('tran_'+str(thread)), # insert variable
                OutputChannel('insert_' + str(thread)),
                Assign('ready_num', PlusExpr(['+','+'], [AVar('ready_num'), AConst(1)]))
                ]
        hps = Sequence(*hps)

        return hps

    def _freeActionPriority(self):
        hps = []
        hps.append(InputChannel('free'))  # insert variable
        con1 = RelExpr('>', AVar('ready_num'), AConst(0))
        con2 = RelExpr('==', AVar('ready_num'), AConst(0))
        con_hp1 = Sequence(OutputChannel('change_'+self.process_name),
                           InputChannel('ch_run_' + self.process_name, AVar('run_now')),
                           InputChannel('ch_prior_' + self.process_name, AVar('run_prior')),
                           HCSP('RUN_'+self.process_name),
                           Assign('ready_num', PlusExpr(['+','-'], [AVar('ready_num'), AConst(1)])))

        con_hp2 = Sequence(Assign('run_now', AConst(0)),
                           Assign('run_prior', AConst(0)))

        hps.append(Condition(con1, con_hp1))
        hps.append(Condition(con2, con_hp2))

        hps = Sequence(*hps)

        return hps

    def _freeActionSequence(self):
        hps = []
        hps.append(InputChannel('free'))  # insert variable
        con1 = RelExpr('>', AVar('ready_num'), AConst(0))
        con2 = RelExpr('==', AVar('ready_num'), AConst(0))
        con_hp1 = Sequence(OutputChannel('change_'+self.process_name),
                           InputChannel('ch_run_' + self.process_name, AVar('run_now')),
                           HCSP('RUN_'+self.process_name),
                           Assign('ready_num', PlusExpr(['+','-'], [AVar('ready_num'), AConst(1)])))

        con_hp2 = Assign('run_now', AConst(0))

        hps.append(Condition(con1, con_hp1))
        hps.append(Condition(con2, con_hp2))

        hps = Sequence(*hps)

        return hps

    def _createBusy(self):
        hp1 = HCSP('BUSY_' + self.process_name)

        hps = []
        for thread in self.threadlines:
            con = RelExpr('==', AVar('run_now'), AVar(thread))
            con_hp = OutputChannel('busy_'+str(thread))  # insert output
            hps.append(Condition(con, con_hp))

        hps = Sequence(*hps)
        hp = Definition(hp1, hps)

        return hp

    def _createRun(self):
        hp1 = HCSP('RUN_' + self.process_name)

        hps = []
        for thread in self.threadlines:
            con = RelExpr('==', AVar('run_now'), AVar(thread))
            con_hp = OutputChannel('run_'+str(thread))  # insert output
            hps.append(Condition(con,con_hp))

        hps = Sequence(*hps)
        hp = Definition(hp1, hps)

        return hp

    def _createQueue(self):
        hp1 = HCSP('QUEUE_' + self.process_name)
        self.thread_num = len(self.threadlines)
        if self.protocal == 'HPF':  ##
            hps=[]
            for i in range(self.thread_num):
                hps.append(Assign('q_'+str(i), AConst(0)))
                hps.append(Assign('p_' + str(i), AConst(0)))
            hps2 = []
            for thread in self.threadlines:
                hps2.append(self._insertPriority(thread))
            hps2.append(self._changeActionPriority())

        elif self.protocal == 'FIFO':
            hps = []
            for i in range(self.thread_num):
                hps.append(Assign('q_' + str(i), AConst(0)))
            hps2 = []
            for thread in self.threadlines:
                hps2.append(self._insertTail(thread))
            hps2.append(self._changeActionHead())

        hps2 = SelectComm(*hps2)
        hps.append(Loop(hps2))
        hps= Sequence(*hps)
        hp = Definition(hp1,hps)

        return hp

    def _insertPriority(self, thread):
        hps = []
        hps.append(InputChannel('insert_' + str(thread), AVar('prior')))  # insert variable
        con_tmp = Sequence(Assign('q_'+str(0), AVar(thread)),
                           Assign('p_'+str(0), AVar('prior')))
        for i in range(self.thread_num-1):
            con1 = RelExpr('<', AVar('p_'+str(i)), AVar('prior'))
            con2 = RelExpr('>', AVar('p_'+str(i)), AVar('prior'))
            con_hp1 = Sequence(Assign('q_'+str(i+1), AVar('q_'+str(i))),
                               Assign('p_'+str(i+1), AVar('p_'+str(i))),
                               con_tmp)  # insert output

            con_hp2 = Sequence(Assign('q_'+str(i+1), AVar(thread)),
                               Assign('p_'+str(i+1), AVar('prior')))

            con_tmp = Sequence(Condition(con1, con_hp1),
                                Condition(con2, con_hp2))
        hps.append(con_tmp)
        hps = Sequence(*hps)

        return hps

    def _insertTail(self, thread):
        hps = []
        hps.append(InputChannel('insert_' + str(thread)))  # insert variable
        con_tmp = Assign('q_' + str(self.thread_num-1), AVar(thread))
        for i in range(self.thread_num-2, -1, -1):
            con1 = RelExpr('!=', AVar('q_' + str(i)), AVar('0'))
            con2 = RelExpr('==', AVar('q_' + str(i)), AVar('0'))
            con_hp1 = con_tmp  # insert output
            con_hp2 = Assign('q_' + str(i), AVar(thread))

            con_tmp = Sequence(Condition(con1, con_hp1),
                               Condition(con2, con_hp2))
        hps.append(con_tmp)
        hps = Sequence(*hps)

        return hps


    def _changeActionPriority(self):
        hps = []
        hps.append(InputChannel('change_' + self.process_name))  # insert variable
        hps.append(OutputChannel('ch_run_' + self.process_name,AVar('q_0')))
        hps.append(OutputChannel('ch_prior_' + self.process_name, AVar('p_0')))

        for i in range(self.thread_num-1):
            hps.append(Assign('q_' + str(i), AVar('q_' + str(i + 1))))
            hps.append(Assign('p_' + str(i), AVar('p_' + str(i + 1))))

        hps.append(Assign('q_' + str(self.thread_num-1), AVar('0')))
        hps.append(Assign('p_' + str(self.thread_num-1), AVar('0')))
        hps = Sequence(*hps)

        return hps

    def _changeActionHead(self):
        hps = []
        hps.append(InputChannel('change_' + self.process_name))  # insert variable
        hps.append(OutputChannel('ch_run_' + self.process_name, AVar('q_0')))

        for i in range(self.thread_num - 1):
            hps.append(Assign('q_' + str(i), AVar('q_' + str(i + 1))))

        hps.append(Assign('q_' + str(self.thread_num - 1), AVar('0')))
        hps = Sequence(*hps)

        return hps


class Thread:
    def __init__(self,thread, annex=None):
        self.lines = []
        self.thread_name = thread['name']
        ### 默认参数###
        self.thread_protocal = 'Periodic'
        self.thread_priority = '1'
        self.thread_deadline = '10'
        self.thread_period = '10'
        self.thread_featureIn = []
        self.thread_featureOut = []
        self.thread_annex=annex

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
            act_hps = OutputChannel('act_'+self.thread_name)  # insert output
            act_hp = Definition(act_hp1,act_hps)
            lines.append(act_hp)

            dis_hp1 = HCSP('DIS_' + self.thread_name)
            dis_hps = [InputChannel('act_' + self.thread_name),  # insert variable
                       Wait(self.thread_period),
                       OutputChannel('dis_' + self.thread_name)]  # insert output

            for feature in self.thread_featureIn:
                dis_hps.append(HCSP('GetData('+feature+')'))

            dis_hps.append(OutputChannel('input_'+self.thread_name, AConst(0)))  # insert output, was AVar(self.thread_featureIn)

            dis_hps.append(SelectComm(InputChannel('complete_'+self.thread_name),  # insert variable
                                      InputChannel('exit_'+self.thread_name)))  # insert variable

            dis_hps = Sequence(*dis_hps)
            dis_hp = Definition(dis_hp1, dis_hps)
            lines.append(dis_hp)

        com_hp1 = HCSP('COM_' + self.thread_name)
        com_hps = [InputChannel('dis_'+self.thread_name),  # insert variable
                   Assign('t', AConst(0)),
                   OutputChannel('init_'+self.thread_name, AVar('t'))]

        com_ready = Loop(HCSP('Ready_'+self.thread_name))

        com_running = []
        com_running.append(Assign('c', AConst(0)))
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
        hps.append(OutputChannel('tran_'+self.thread_name, AVar('properties')))

        eqs = [('t', AConst(1))]
        constraint = RelExpr('<', AVar('t'), AVar(self.thread_deadline))
        io_comms = [(InputChannel('run_'+self.thread_name),  # insert variable
                     OutputChannel('resume_'+self.thread_name, AVar('t')))]
        hps.append(ODE_Comm(eqs,constraint,io_comms))
        con = RelExpr('==', AVar('t'), AVar(self.thread_deadline))
        con_hp = OutputChannel('exit_'+self.thread_name)  # insert output
        hps.append(Condition(con, con_hp))

        hps = Sequence(*hps)
        hp = Definition(hp1, hps)

        return hp

    def _createAwait(self):
        hp1 = HCSP('Await_' + self.thread_name)
        hps = [InputChannel('block_' + self.thread_name, 't')]

        eqs = [('t', AConst(1))]
        constraint = RelExpr('<', AVar('t'), AVar(self.thread_deadline))
        io_comms = [(InputChannel('haveResource_' + self.thread_name),  # insert variable
                     OutputChannel('unblock_' + self.thread_name, AVar('t')))]

        hps.append(ODE_Comm(eqs, constraint, io_comms))
        con = RelExpr('==', AVar('t'), AVar(self.thread_deadline))
        con_hp = OutputChannel('exit_' + self.thread_name)  # insert output
        hps.append(Condition(con, con_hp))

        hps = Sequence(*hps)
        hp = Definition(hp1, hps)

        return hp

    def _createRunning(self):
        hp1 = HCSP('Running_' + self.thread_name)
        hps = [InputChannel('resume_' + self.thread_name, 't'),
               OutputChannel('run_Annex_'+self.thread_name)]  # insert output

        eqs = [('t', AConst(1)), ('c', AConst(1))]
        constraint = RelExpr('<', AVar('t'), AVar(self.thread_deadline))
        in1 = InputChannel('busy_' + self.thread_name)  # insert variable
        out1 = OutputChannel('preempt_' + self.thread_name, AVar('t'))

        in2 = InputChannel('needResource_' + self.thread_name)  # insert variable
        out2 = Sequence(*[OutputChannel('block_' + self.thread_name, AVar('t')),
                          OutputChannel('applyResource_' + self.thread_name),
                          OutputChannel('free')])  # insert output

        in3 = InputChannel('complete_Annex_' + self.thread_name)  # insert variable
        out3 = []
        for feature in self.thread_featureOut:
            out3.append('SetData('+feature+')')
        out3.append(OutputChannel('free'))  # insert output
        out3.append(OutputChannel('complete'+self.thread_name))  # insert output
        out3 = Sequence(*out3)


        io_comms = [(in1, out1), (in2, out2), (in3, out3)]

        hps.append(ODE_Comm(eqs, constraint, io_comms))
        con = RelExpr('==', AVar('t'), AVar(self.thread_deadline))
        con_hp = Sequence(OutputChannel('free'),  # insert output
                          OutputChannel('exit_' + self.thread_name)) # insert output
        hps.append(Condition(con, con_hp))

        hps = Sequence(*hps)
        hp = Definition(hp1, hps)

        return hp
