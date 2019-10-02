"""Convert AADL model (in JSON format) to HCSP programs."""

import json

from aadl2hcsp.parserAnnex import AnnexParser
from ss2hcsp.hcsp.expr import AVar, AConst, PlusExpr, RelExpr, LogicExpr, BConst, conj, NegExpr, TimesExpr
from ss2hcsp.hcsp.hcsp import Var, Sequence, InputChannel, OutputChannel, Loop, Wait, \
    SelectComm, Assign, ODE_Comm, Condition, Parallel, HCSPProcess, Skip, ITE

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
                if len(com['source'].strip().split('.')) == 2:
                    hp_in = InputChannel(com['source'].strip().replace('.','_'), 'x')
                elif len(com['source'].strip().split('.')) > 2:
                    hp_in = InputChannel('_'.join([com['source'].strip().split('.')[0], com['source'].strip().split('.')[-1]]), 'x')
                else:
                    hp_in = InputChannel(category['name'].strip() + '_' + com['source'].strip(), 'x')

                if len(com['destination'].strip().split('.')) == 2:
                    hp_out = OutputChannel(com['destination'].strip().replace('.','_'), AVar('x'))
                elif len(com['destination'].strip().split('.')) > 2:
                    hp_out = OutputChannel('_'.join([com['destination'].strip().split('.')[0], com['destination'].strip().split('.')[-1]]), AVar('x'))
                else:
                    hp_out = OutputChannel(category['name'].strip() + '_' + com['destination'].strip(), AVar('x'))

                hp = Loop(Sequence(*[hp_in,hp_out]))
                hps.append(hp)

            if len(hps) > 1:
                sub_comm, hp2=[],[]
                for i in range(len(hps)):
                   sub_comm.append((category['name']+'_Conn_'+str(i), hps[i]))
                   hp2.append(Var(category['name']+'_Conn_'+str(i)))
                process.add('Comms_'+ category['name'] , Parallel(*hp2))
                for (name, hp) in sub_comm:
                    process.add(name,hp)
            else:
                process.add('Comms_'+category['name'], hps[0])

    return process

class Abstract:
    def __init__(self, abstract, sim=None):
        self.abstract_name = abstract['name']
        self.abstract_featureIn = []
        self.abstract_featureOut = []
        self.sim = sim

        for feature in abstract['features']:
            if feature['type'].lower() == 'dataport':
                if feature['direction'].lower() == 'out':
                    self.abstract_featureOut.append(feature['name'])
                else:
                    self.abstract_featureIn.append(feature['name'])

        self.lines = HCSPProcess()
        self._createAbstract()

    def _createAbstract(self):
        out_hp, in_hp = [],[]
        for feature in self.abstract_featureOut:
            out_hp.append(OutputChannel(self.abstract_name + '_' + feature, AVar(str(feature))))

        for feature in self.abstract_featureIn:
            in_hp.append(InputChannel(self.abstract_name + '_' + feature, str(feature)))

        if len(out_hp) >= 2:
            out_hp = Sequence(*out_hp)
        else:
            out_hp = out_hp[0]

        if len(in_hp) >= 2:
            in_hp = Sequence(*in_hp)
        else:
            in_hp = in_hp[0]

        init_hp = Sequence(Assign('boxTemp', AConst(73.0)),
                           Assign('q', AConst(73.0)),
                           out_hp, in_hp)

       # if self.sim:
       #    hps.extend(self.sim)

        eqs = [('boxTemp',  TimesExpr(['*', '*'], [AConst(-0.026), PlusExpr(['+','-'], [AVar('boxTemp'), AVar('q')])])),
               ('q', AVar('heatCommand'))]

        constraint = BConst(True)
        io_comms = [(in_hp, Skip()), (out_hp, Skip())]

        hps = Loop(ODE_Comm(eqs, constraint, io_comms))


        self.lines.add(self.abstract_name, Sequence(init_hp, hps))


class Process:
    def __init__(self, process, threadlines, protocol='HPF'):
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

        elif self.protocol == 'FIFO':
            hps = [Assign('run_now', AConst(0)),
                   Assign('ready_num', AConst(0))]

            hps2 = []
            for thread in self.threadlines:
                hps2.append(self._noPreemptSequence(thread))
            hps2.append(self._freeActionSequence())


        hps2 = SelectComm(*hps2)
        hps.append(Loop(hps2))
        hps = Sequence(*hps)
        self.lines.add('SCHEDULE_' + self.process_name, hps)

    def _preemptPriority(self, thread):
        hps = []
        hps_con = InputChannel('tran_'+str(thread), 'prior')  # insert variable
        con1= RelExpr('<', AVar('run_prior'), AVar('prior'))
        con2= RelExpr('>', AVar('run_prior'), AVar('prior'))
        con_hp1 = Sequence(self._BusyProcess(),
                           Assign('run_now', AConst('"'+str(thread)+'"')),
                           Assign('run_prior', AVar('prior')),
                           OutputChannel('run_' + str(thread)))  # insert output

        con_hp2 = Sequence(OutputChannel('insert_' + str(thread), AVar('prior')),
                           Assign('ready_num', PlusExpr(['+','+'], [AVar('ready_num'), AConst(1)])))

        hps.append(Condition(con1, con_hp1))
        hps.append(Condition(con2, con_hp2))

        return (hps_con ,Sequence(*hps))

    def _noPreemptSequence(self, thread):
        hps_con = InputChannel('tran_' + str(thread)) # insert variable
        hps = [OutputChannel('insert_' + str(thread)),
               Assign('ready_num', PlusExpr(['+','+'], [AVar('ready_num'), AConst(1)]))]

        return (hps_con, Sequence(*hps))

    def _freeActionPriority(self):
        hps = []
        hps_con= InputChannel('free')  # insert variable
        con1 = RelExpr('>', AVar('ready_num'), AConst(0))
        con2 = RelExpr('==', AVar('ready_num'), AConst(0))
        con_hp1 = Sequence(OutputChannel('change_' + self.process_name),
                           InputChannel('ch_run_' + self.process_name, 'run_now'),
                           InputChannel('ch_prior_' + self.process_name, 'run_prior'),
                           self._RunProcess(),
                           Assign('ready_num', PlusExpr(['+','-'], [AVar('ready_num'), AConst(1)])))

        con_hp2 = Sequence(Assign('run_now', AConst(0)),
                           Assign('run_prior', AConst(0)))

        hps.append(Condition(con1, con_hp1))
        hps.append(Condition(con2, con_hp2))

        return (hps_con, Sequence(*hps))

    def _freeActionSequence(self):
        hps = []
        hps_con = InputChannel('free') # insert variable
        con1 = RelExpr('>', AVar('ready_num'), AConst(0))
        con2 = RelExpr('==', AVar('ready_num'), AConst(0))
        con_hp1 = Sequence(OutputChannel('change_' + self.process_name),
                           InputChannel('ch_run_' + self.process_name, 'run_now'),
                           self._RunProcess(),
                           Assign('ready_num', PlusExpr(['+','-'], [AVar('ready_num'), AConst(1)])))

        con_hp2 = Assign('run_now', AConst(0))

        hps.append(Condition(con1, con_hp1))
        hps.append(Condition(con2, con_hp2))

        return (hps_con, Sequence(*hps))


    def _BusyProcess(self):
        hps = []
        for thread in self.threadlines:
            con = RelExpr('==', AVar('run_now'), AConst('"'+str(thread)+'"'))
            con_hp = OutputChannel('busy_'+str(thread))  # insert output
            hps.append(Condition(con, con_hp))

        if len(hps) >= 2:
            hps = Sequence(*hps)
        else:
            hps = hps[0]

        return hps

    def _RunProcess(self):
        hps = []
        for thread in self.threadlines:
            con = RelExpr('==', AVar('run_now'), AConst('"'+str(thread)+'"'))
            con_hp = OutputChannel('run_'+str(thread))  # insert output
            hps.append(Condition(con,con_hp))

        if len(hps) >= 2:
            hps = Sequence(*hps)
        else:
            hps = hps[0]

        return hps

    def _createQueue(self):
        self.thread_num = len(self.threadlines)
        if self.protocol == 'HPF':
            hps = []
            for i in range(self.thread_num):
                hps.append(Assign('q_' + str(i), AConst(0)))
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

        if len(hps2) >= 2:
            hps2 = SelectComm(*hps2)
        else:
            hps2 = hps2[0]

        hps.append(Loop(hps2))
        hps = Sequence(*hps)

        self.lines.add('QUEUE_' + self.process_name, hps)

    def _insertPriority(self, thread):
        hps = []
        hps_con = InputChannel('insert_' + str(thread), 'prior')  # insert variable
        con_tmp = Sequence(Assign('q_'+str(0), AConst('"'+str(thread)+'"')),
                           Assign('p_'+str(0), AVar('prior')))
        for i in range(self.thread_num-1):
            con1 = RelExpr('<', AVar('p_'+str(i)), AVar('prior'))
            con2 = RelExpr('>', AVar('p_'+str(i)), AVar('prior'))
            con_hp1 = Sequence(Assign('q_'+str(i+1), AVar('q_'+str(i))),
                               Assign('p_'+str(i+1), AVar('p_'+str(i))),
                               con_tmp)  # insert output

            con_hp2 = Sequence(Assign('q_'+str(i+1), AConst('"'+str(thread)+'"')),
                               Assign('p_'+str(i+1), AVar('prior')))

            con_tmp = Sequence(Condition(con1, con_hp1),
                               Condition(con2, con_hp2))
        hps.append(con_tmp)

        if len(hps) >= 2:
            hps = Sequence(*hps)
        else:
            hps = hps[0]

        return (hps_con, hps)

    def _insertTail(self, thread):
        hps = []
        hps_con = InputChannel('insert_' + str(thread))  # insert variable
        con_tmp = Assign('q_' + str(self.thread_num-1), AConst('"'+str(thread)+'"'))
        for i in range(self.thread_num-2, -1, -1):
            con1 = RelExpr('!=', AVar('q_' + str(i)), AConst(0))
            con2 = RelExpr('==', AVar('q_' + str(i)), AConst(0))
            con_hp1 = con_tmp  # insert output
            con_hp2 = Assign('q_' + str(i), AConst('"'+str(thread)+'"'))

            con_tmp = Sequence(Condition(con1, con_hp1),
                               Condition(con2, con_hp2))
        hps.append(con_tmp)

        if len(hps) >=2:
            hps=Sequence(*hps)
        else:
            hps=hps[0]

        return (hps_con, hps)



    def _changeActionPriority(self):
        hps = []
        hps_con = InputChannel('change_' + self.process_name) # insert variable
        hps.append(OutputChannel('ch_run_' + self.process_name,AVar('q_0')))
        hps.append(OutputChannel('ch_prior_' + self.process_name, AVar('p_0')))

        for i in range(self.thread_num-1):
            hps.append(Assign('q_' + str(i), AVar('q_' + str(i + 1))))
            hps.append(Assign('p_' + str(i), AVar('p_' + str(i + 1))))

        hps.append(Assign('q_' + str(self.thread_num-1), AConst(0)))
        hps.append(Assign('p_' + str(self.thread_num-1), AConst(0)))

        return (hps_con, Sequence(*hps))

    def _changeActionHead(self):
        hps = []
        hps_con = InputChannel('change_' + self.process_name)  # insert variable
        hps.append(OutputChannel('ch_run_' + self.process_name, AVar('q_0')))

        for i in range(self.thread_num - 1):
            hps.append(Assign('q_' + str(i), AVar('q_' + str(i + 1))))

        hps.append(Assign('q_' + str(self.thread_num - 1), AConst(0)))

        return (hps_con, Sequence(*hps))





class Thread:
    def __init__(self, thread, annex=None):
        self.thread_name = thread['name']

        # Default parameters
        self.thread_protocol = 'Periodic'
        self.thread_priority = '1'
        self.thread_deadline = '1000'
        self.thread_period = '1000'
        self.thread_max_time = '5'
        self.thread_min_time = '1'
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

                elif opa['name'] == 'Timing_Properties.Compute_Execution_Time':
                    self.thread_min_time = opa['value'][0]
                    self.thread_max_time = opa['value'][1]

        ## change time unit from ms to s

        self.thread_min_time = 0.001*int(self.thread_min_time)
        self.thread_max_time = 0.001*int(self.thread_max_time)
        self.thread_deadline = 0.001*int(self.thread_deadline)
        self.thread_period = 0.001*int(self.thread_period)

        for feature in thread['features']:
            if feature['type'].lower() == 'dataport':
                if feature['direction'].lower() == 'out':
                    self.thread_featureOut.append(feature['name'])
                else:
                    self.thread_featureIn.append(feature['name'])

        # Create the process
        self.lines = HCSPProcess()
        self._createThread()


    def _createThread(self):
        hps = Parallel(Var('ACT_' + self.thread_name),
                       Var('DIS_' + self.thread_name),
                       Var('COM_' + self.thread_name))
        self.lines.add(self.thread_name, hps)

        if self.thread_protocol == 'Periodic':
            act_hps = Sequence(OutputChannel('act_' + self.thread_name),
                               Wait(AConst(self.thread_period)))# insert output
            self.lines.add('ACT_' + self.thread_name, Loop(act_hps))

            dis_hps = [InputChannel('act_' + self.thread_name),  # insert variable
                       OutputChannel('dis_' + self.thread_name)]  # insert output

            for feature in self.thread_featureIn:
                dis_hps.append(InputChannel(self.thread_name + '_' + feature, feature))

            for feature in self.thread_featureIn:
                dis_hps.append(OutputChannel('input_' + self.thread_name + '_' + feature, AVar(feature))) # insert output, was AVar(self.thread_featureIn)

            dis_hps.append(SelectComm((InputChannel('complete_' + self.thread_name),Skip()), # insert variable
                                       (InputChannel('exit_' + self.thread_name),Skip()))) # insert variable

            dis_hps = Sequence(*dis_hps)
            self.lines.add('DIS_' + self.thread_name, Loop(dis_hps))


        com_hps = (Parallel(*[Var('Init_' + self.thread_name),
                              Var('Ready_' + self.thread_name),
                              Var('Running_' + self.thread_name),
                              Var('Await_' + self.thread_name)]))

        self.lines.add('COM_' + self.thread_name, com_hps)
        self._createInit()
        self._createReady()
        self._createAwait()
        self._createRunning()

    def _createInit(self):
        com_init = Loop(Sequence(InputChannel('dis_' + self.thread_name),  # insert variable
                            Assign('t', AConst(0)),
                            OutputChannel('init_' + self.thread_name, AVar('t'))))

        self.lines.add('Init_' + self.thread_name, com_init)

    def _createReady(self):
        com_ready = []
        com_ready.append(Assign('prior', AConst(int(self.thread_priority))))
        hps = SelectComm((InputChannel('init_'+self.thread_name, 't'), Skip()),
                          (InputChannel('preempt_'+self.thread_name, 't'), Skip()),
                          (InputChannel('unblock_'+self.thread_name, 't'), Skip()))

        com_ready.append(hps)
        com_ready.append(OutputChannel('tran_'+self.thread_name, AVar('prior')))

        eqs = [('t', AConst(1))]
        constraint = RelExpr('<', AVar('t'), AConst(self.thread_deadline))
        io_comms = [(InputChannel('run_'+self.thread_name),  # insert variable
                     OutputChannel('resume_'+self.thread_name, AVar('t')))]
        com_ready.append(ODE_Comm(eqs,constraint,io_comms))
        con = RelExpr('==', AVar('t'), AConst(self.thread_deadline))
        con_hp = OutputChannel('exit_'+self.thread_name)  # insert output
        com_ready.append(Condition(con, con_hp))

        com_ready = Loop(Sequence(*com_ready))
        self.lines.add('Ready_' + self.thread_name, com_ready)

    def _createAwait(self):
        com_await = [InputChannel('block_' + self.thread_name, 't')]
        com_await.append(OutputChannel('applyResource_' + self.thread_name))
        eqs = [('t', AConst(1))]
        constraint = RelExpr('<', AVar('t'), AConst(self.thread_deadline))
        io_comms = [(InputChannel('haveResource_' + self.thread_name),  # insert variable
                     OutputChannel('unblock_' + self.thread_name, AVar('t')))]

        com_await.append(ODE_Comm(eqs, constraint, io_comms))
        con = RelExpr('==', AVar('t'), AConst(self.thread_deadline))
        con_hp = OutputChannel('exit_' + self.thread_name)  # insert output
        com_await.append(Condition(con, con_hp))

        com_await = Loop(Sequence(*com_await))
        self.lines.add('Await_' + self.thread_name, com_await)

    def _createRunning(self, flag='Annex'):
        FlagSet = Assign('InitFlag', AConst(0))
        hps=[]
        hps.append(Condition(RelExpr('==', AVar('InitFlag'), AConst(0)), Assign('c', AConst(0))))
        hps.append(InputChannel('resume_' + self.thread_name, 't'))

        if flag=='Annex' and self.annex:
            busy_io=(InputChannel('busy_' + self.thread_name),
                     Sequence(OutputChannel('preempt_' + self.thread_name, AVar('t')), Assign('InitFlag', AConst(0))))
            hps.append(Condition(RelExpr('==', AVar('c'), AConst(0)), SelectComm(self._Block_Annex(),busy_io)))

            con_hp=[]
            eqs = [('t', AConst(1)), ('c', AConst(1))]
            constraint_1 = RelExpr('<', AVar('t'), AConst(self.thread_deadline))
            constraint_2 = RelExpr('<', AVar('c'), AConst(self.thread_max_time))
            constraint_3 = BConst(False)
            constraint = conj(constraint_1, constraint_2, constraint_3)
            in1 = InputChannel('busy_' + self.thread_name)  # insert variable
            out1 = OutputChannel('preempt_' + self.thread_name, AVar('t'))

            in2 = InputChannel('needResource_' + self.thread_name)  # insert variable
            out2 = OutputChannel('block_' + self.thread_name, AVar('t'))

            io_comms = [(in1, out1), (in2, out2)]
            con_hp.append(ODE_Comm(eqs, constraint, io_comms))

            constraint_4 = RelExpr('<', AVar('c'), AConst(int(self.thread_min_time)))
            con_hp.append(Condition(conj(BConst(True), constraint_4), Wait(PlusExpr(['+','-'], [AConst(int(self.thread_min_time)), AVar('c')]))))

            con_hp.append(OutputChannel('free'))  # insert output

            con1 = RelExpr('<', AVar('t'), AConst(int(self.thread_deadline)))
            con_hp1 = [OutputChannel('complete_' + self.thread_name)]
            for feature in self.thread_featureOut:
                    con_hp1.append(OutputChannel(self.thread_name + '_' + feature, AVar(str(feature))))
            con_hp1.append(Assign('InitFlag', AConst(0)))  # insert output
            con_hp1=Sequence(*con_hp1)
            con_hp.append(Condition(con1, con_hp1))

            con2 = RelExpr('==', AVar('t'), AConst(int(self.thread_deadline)))
            con_hp2 = Sequence(OutputChannel('exit_' + self.thread_name),
                               Assign('InitFlag', AConst(0)))# insert output
            con_hp.append(Condition(con2, con_hp2))

            hps.append(Condition(RelExpr('==', AVar('InitFlag'), AConst(1)), Sequence(*con_hp)))

        com_running = Sequence(FlagSet, Loop(Sequence(*hps)))

        self.lines.add('Running_' + self.thread_name, com_running)


    def _Block_Annex(self):
        hps= []
        io_hps = InputChannel('input_' + self.thread_name + '_' + self.thread_featureIn[0], self.thread_featureIn[0])
        for feature in self.thread_featureIn[1:]:
            hps.append(InputChannel('input_' + self.thread_name + '_' + feature, str(feature)))
        if self.annex:
            hps.extend(self.annex)

        #hps.append(Wait(AConst(5)))
        #hps.append(OutputChannel('need_Resource_' + self.thread_name))
        #hps.append(Wait(AConst(5)))

        #for feature in self.thread_featureOut:
            #hps.append(OutputChannel(self.thread_name + '_' + feature, AVar(str(feature))))

        hps.append(Assign('InitFlag', AConst(1)))

        if len(hps) >= 2:
            hps = Sequence(*hps)
        else:
            hps = hps[0]

        return (io_hps, hps)

def convert_AADL(json_file, annex_file):
    out = HCSPProcess()

    AP = AnnexParser()
    Annexs = AP.getAnnex(annex_file)
    Annex_HP = {}
    for th in Annexs.keys():
        Annex_HP[th] = AP.createHCSP(Annexs[th])


    with open(json_file, 'r') as f:
        dic = json.load(f)

    out.extend(createStructure(dic))
    out.extend(createConnections(dic))

    for category in dic.values():
        if category['category'] == 'process' and len(category['components']) > 0:
            threadlines = []
            for com in category['components']:
                if com['category'] == 'thread':
                    threadlines.append(com['name'])
            out.extend(Process(category,threadlines).lines)

        elif category['category'] == 'thread':
            if category['name'] in Annex_HP.keys():
                out.extend(Thread(category, Annex_HP[category['name']]).lines)
            else:
                out.extend(Thread(category).lines)

        elif category['category'] == 'abstract':
            out.extend(Abstract(category).lines)

    return out
