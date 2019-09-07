"""Convert AADL model (in JSON format) to HCSP programs."""

import json
from ss2hcsp.hcsp.expr import AVar, AConst, PlusExpr, RelExpr
from ss2hcsp.hcsp.hcsp import Var, Sequence, InputChannel, OutputChannel, Loop, Wait, \
    SelectComm, Assign, ODE_Comm, Condition, Parallel, HCSPProcess

def createStructure(dic):
    process = HCSPProcess()

    for category in dic.values():
        if len(category['components']) > 0:
            hps = []
            for com in category['components']:
                hps.append(Var(com['name']))

            if len(category['connections']) >0:
                hps.append(Var('Comms_' + category['name']))

            if len(category['category']) == 'Process':
                hps.append(Var('SCHEDULE_' + category['name']))

            if len(hps) > 1:
                hp2 = Parallel(*hps)
            else:
                hp2 = hps[0]

            process.add(category['name'], hp2)

            # If name and name_impl does not agree, add new definition
            for com in category['components']:
                if 'name_impl' in com:
                    hp2 = Var(com['name_impl'])
                    process.add(com['name'], hp2)

    return process

def createConnections(dic):
    process = HCSPProcess()

    for category in dic.values():
        if len(category['connections']) > 0:
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

            process.add(category['name']+'_Conns', hp2)

    return process

class Process:
    def __init__(self, process, threadlines, protocol='FIFO'):
        self.threadlines = threadlines
        self.protocol = protocol
        self.process_name = process['name']

        self.lines = HCSPProcess()
        self._createSchedule()
        self._createQueue()

    def _createSchedule(self):
        if self.protocol == 'HPF':
            hps = [Assign('run_now', AConst(0)),
                   Assign('run_prior', AConst(0)),
                   Assign('ready_num', AConst(0))]

            hps2 = []
            for thread in self.threadlines:
                hps2.append(self._preemptPriority(thread))
            hps2.append(self._freeActionPriority())

            self._createRun()
            self._createBusy()

        elif self.protocol == 'FIFO':
            hps = [Assign('run_now', AConst(0)),
                   Assign('ready_num', AConst(0))]

            hps2 = []
            for thread in self.threadlines:
                hps2.append(self._noPreemptSequence(thread))
            hps2.append(self._freeActionSequence())

            self._createRun()

        hps2 = SelectComm(*hps2)
        hps.append(Loop(hps2))
        hps = Sequence(*hps)
        self.lines.add('SCHEDULE_' + self.process_name, hps)

    def _preemptPriority(self, thread):
        hps = []
        hps.append(InputChannel('tran_'+str(thread), AVar('prior')))  # insert variable
        con1= RelExpr('<', AVar('run_prior'), AVar('prior'))
        con2= RelExpr('>', AVar('run_prior'), AVar('prior'))
        con_hp1 = Sequence(Var('BUSY_' + self.process_name),
                           Assign('run_now', AVar(thread)),
                           Assign('run_prior', AVar('prior')),
                           OutputChannel('run_' + str(thread)))  # insert output

        con_hp2 = Sequence(OutputChannel('insert_' + str(thread), AVar('prior')),
                           Assign('ready_num', PlusExpr(['+','+'], [AVar('ready_num'), AConst(1)])))

        hps.append(Condition(con1, con_hp1))
        hps.append(Condition(con2, con_hp2))

        return Sequence(*hps)

    def _noPreemptSequence(self, thread):
        hps = [InputChannel('tran_' + str(thread)), # insert variable
               OutputChannel('insert_' + str(thread)),
               Assign('ready_num', PlusExpr(['+','+'], [AVar('ready_num'), AConst(1)]))]

        return Sequence(*hps)

    def _freeActionPriority(self):
        hps = []
        hps.append(InputChannel('free'))  # insert variable
        con1 = RelExpr('>', AVar('ready_num'), AConst(0))
        con2 = RelExpr('==', AVar('ready_num'), AConst(0))
        con_hp1 = Sequence(OutputChannel('change_' + self.process_name),
                           InputChannel('ch_run_' + self.process_name, AVar('run_now')),
                           InputChannel('ch_prior_' + self.process_name, AVar('run_prior')),
                           Var('RUN_' + self.process_name),
                           Assign('ready_num', PlusExpr(['+','-'], [AVar('ready_num'), AConst(1)])))

        con_hp2 = Sequence(Assign('run_now', AConst(0)),
                           Assign('run_prior', AConst(0)))

        hps.append(Condition(con1, con_hp1))
        hps.append(Condition(con2, con_hp2))

        return Sequence(*hps)

    def _freeActionSequence(self):
        hps = []
        hps.append(InputChannel('free'))  # insert variable
        con1 = RelExpr('>', AVar('ready_num'), AConst(0))
        con2 = RelExpr('==', AVar('ready_num'), AConst(0))
        con_hp1 = Sequence(OutputChannel('change_' + self.process_name),
                           InputChannel('ch_run_' + self.process_name, 'run_now'),
                           Var('RUN_' + self.process_name),
                           Assign('ready_num', PlusExpr(['+','-'], [AVar('ready_num'), AConst(1)])))

        con_hp2 = Assign('run_now', AConst(0))

        hps.append(Condition(con1, con_hp1))
        hps.append(Condition(con2, con_hp2))

        return Sequence(*hps)


    def _createBusy(self):
        hps = []
        for thread in self.threadlines:
            con = RelExpr('==', AVar('run_now'), AVar(thread))
            con_hp = OutputChannel('busy_'+str(thread))  # insert output
            hps.append(Condition(con, con_hp))

        self.lines.add('BUSY_' + self.process_name, hps)

    def _createRun(self):
        hps = []
        for thread in self.threadlines:
            con = RelExpr('==', AVar('run_now'), AVar(thread))
            con_hp = OutputChannel('run_'+str(thread))  # insert output
            hps.append(Condition(con,con_hp))

        if len(hps) >= 2:
            hps = Sequence(*hps)
        else:
            hps = hps[0]

        self.lines.add('RUN_' + self.process_name, hps)

    def _createQueue(self):
        self.thread_num = len(self.threadlines)
        if self.protocol == 'HPF':
            hps = []
            for i in range(self.thread_num):
                hps.append(Assign('q_'+str(i), AConst(0)))
                hps.append(Assign('p_' + str(i), AConst(0)))
            hps2 = []
            for thread in self.threadlines:
                hps2.append(self._insertPriority(thread))
            hps2.append(self._changeActionPriority())

        elif self.protocol == 'FIFO':
            hps = []
            for i in range(self.thread_num):
                hps.append(Assign('q_' + str(i), AConst(0)))
            hps2 = []
            for thread in self.threadlines:
                hps2.append(self._insertTail(thread))
            hps2.append(self._changeActionHead())

        hps2 = SelectComm(*hps2)
        hps.append(Loop(hps2))
        hps = Sequence(*hps)

        self.lines.add('QUEUE_' + self.process_name, hps)

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

        return Sequence(*hps)

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

        return Sequence(*hps)


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

        return Sequence(*hps)

    def _changeActionHead(self):
        hps = []
        hps.append(InputChannel('change_' + self.process_name))  # insert variable
        hps.append(OutputChannel('ch_run_' + self.process_name, AVar('q_0')))

        for i in range(self.thread_num - 1):
            hps.append(Assign('q_' + str(i), AVar('q_' + str(i + 1))))

        hps.append(Assign('q_' + str(self.thread_num - 1), AVar('0')))

        return Sequence(*hps)


class Thread:
    def __init__(self, thread, annex=None):
        self.thread_name = thread['name']

        # Default parameters
        self.thread_protocol = 'Periodic'
        self.thread_priority = '1'
        self.thread_deadline = '10'
        self.thread_period = '10'
        self.thread_featureIn = []
        self.thread_featureOut = []
        self.annex = annex

        if len(thread['opas']) > 0:
            for opa in thread['opas']:
                if opa['name'] == 'Thread_Properties.Dispatch_Protocol':
                    if opa['value'] == 'Periodic':
                        self.thread_protocol = 'Periodic'

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

        # Create the process
        self.lines = HCSPProcess()
        self._createThread()
        self._createReady()
        self._createAwait()
        self._createRunning()
        self._createAnnex()


    def _createThread(self):
        hps = Parallel(Loop(Var('ACT_' + self.thread_name)),
                       Loop(Var('DIS_' + self.thread_name)),
                       Loop(Var('COM_' + self.thread_name)))
        self.lines.add(self.thread_name, hps)

        if self.thread_protocol == 'Periodic':
            act_hps = OutputChannel('act_' + self.thread_name)  # insert output
            self.lines.add('ACT_' + self.thread_name, act_hps)

            dis_hps = [InputChannel('act_' + self.thread_name),  # insert variable
                       Wait(int(self.thread_period)),
                       OutputChannel('dis_' + self.thread_name)]  # insert output

            for feature in self.thread_featureIn:
                dis_hps.append(InputChannel(self.thread_name + '_' + feature, feature))

            if len(self.thread_featureIn) > 0:
                dis_hps.append(OutputChannel('input_'+self.thread_name, AVar(str(self.thread_featureIn)))) # insert output, was AVar(self.thread_featureIn)

            dis_hps.append(SelectComm(InputChannel('complete_' + self.thread_name),  # insert variable
                                      InputChannel('exit_' + self.thread_name)))  # insert variable

            dis_hps = Sequence(*dis_hps)
            self.lines.add('DIS_' + self.thread_name, dis_hps)

        com_hps = [InputChannel('dis_' + self.thread_name),  # insert variable
                   Assign('t', AConst(0)),
                   OutputChannel('init_' + self.thread_name, AVar('t'))]

        com_ready = Loop(Var('Ready_' + self.thread_name))

        com_running = []
        com_running.append(Assign('c', AConst(0)))
        com_running.append(Loop(Var('Running_' + self.thread_name)))
        com_running = Sequence(*com_running)

        com_await = Loop(Var('Await_' + self.thread_name))

        com_annex = Var('Annex_' + self.thread_name)

        com_hps.append(Parallel(*[com_ready, com_running, com_await, com_annex]))
        com_hps = Sequence(*com_hps)

        self.lines.add('COM_' + self.thread_name, com_hps)

    def _createReady(self):
        hps = []
        hps2 = [InputChannel('init_'+self.thread_name, 't'),
                InputChannel('preempt_'+self.thread_name, 't'),
                InputChannel('unblock_'+self.thread_name, 't')]

        hps2 = SelectComm(*hps2)
        hps.append(hps2)
        hps.append(OutputChannel('tran_'+self.thread_name, AVar('prior')))

        eqs = [('t', AConst(1))]
        constraint = RelExpr('<', AVar('t'), AVar(self.thread_deadline))
        io_comms = [(InputChannel('run_'+self.thread_name),  # insert variable
                     OutputChannel('resume_'+self.thread_name, AVar('t')))]
        hps.append(ODE_Comm(eqs,constraint,io_comms))
        con = RelExpr('==', AVar('t'), AVar(self.thread_deadline))
        con_hp = OutputChannel('exit_'+self.thread_name)  # insert output
        hps.append(Condition(con, con_hp))

        hps = Sequence(*hps)
        self.lines.add('Ready_' + self.thread_name, hps)

    def _createAwait(self):
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
        self.lines.add('Await_' + self.thread_name, hps)

    def _createRunning(self):
        hps = [InputChannel('resume_' + self.thread_name, 't')]
        hps.append(SelectComm(OutputChannel('start_Annex_'+self.thread_name),
                              OutputChannel('restart_Annex_'+self.thread_name)))# insert output

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
        out3.append(OutputChannel('free'))  # insert output
        out3.append(OutputChannel('complete_'+self.thread_name))  # insert output
        out3 = Sequence(*out3)

        io_comms = [(in1, out1), (in2, out2), (in3, out3)]

        hps.append(ODE_Comm(eqs, constraint, io_comms))
        con = RelExpr('==', AVar('t'), AVar(self.thread_deadline))
        con_hp = Sequence(OutputChannel('free'),  # insert output
                          OutputChannel('exit_' + self.thread_name)) # insert output
        hps.append(Condition(con, con_hp))

        hps = Sequence(*hps)
        self.lines.add('Running_' + self.thread_name, hps)

    def _createAnnex(self):
        hps = []
        hps.append(InputChannel('start_Annex_' + self.thread_name))
        if len(self.thread_featureIn) > 0:
            hps.append(InputChannel('input_' + self.thread_name, str(self.thread_featureIn)))

        if self.annex:
            hps.extend(self.annex)

        hps.append(Wait(5))
        hps.append(OutputChannel('need_Resource_' + self.thread_name))
        hps.append(InputChannel('restart_Annex_' + self.thread_name))
        hps.append(Wait(5))

        for feature in self.thread_featureOut:
            hps.append(OutputChannel(self.thread_name + '_' + feature, feature))

        hps.append(OutputChannel('complete_Annex_' + self.thread_name))
        hps = Sequence(*hps)
        self.lines.add('Annex_' + self.thread_name, hps)
