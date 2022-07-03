import json
from string import Template
from ss2hcsp.hcsp.parser import hp_parser
from ss2hcsp.hcsp.hcsp import Assign, ITE


header = """
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <ctype.h>
#include <signal.h>
#include <time.h>
#include <string.h>
#include <math.h>
#include "isolette.h"
#include "rtwtypes.h"

/** type struct definition of components 
------------------------------------------------------
  System Component: system
  Hardware Component: processor memory bus device
  Software Component: process thread subprogram 
------------------------------------------------------  
**/

typedef struct System
{
    

} System;


typedef struct Device
{
    

} Device;

typedef struct Thread 
{
    int tid; /* The ID of a thread */
    int runCount;
    char *threadName; /*name of thread*/
    int period; /*time interval to be stimulated*/
    int priority; /*priority*/
    int deadline; /*No more than deadline*/
    char *state; /*seven state: halted, initial, waiting, ready, running, complete, finial */
    char *dispatch_protocol; /*periodic, aperiodic and et al.*/
    int maxExecutionTime; /*max execution time*/
    int minExecutionTime; /*min execution time*/
} Thread;

typedef struct Process
{
    int processNum;
    int numberOfThread;
    char *processName;
    char *scheduling_protocol;
    Thread** threadGroup;
} Process;

typedef struct Processor
{
    int processorNum;
    int numberOfProcess;
    char *processorName;
    Process** processGroup;    
} Processor;

"""

scheduler = """

/************* RMS algorithm **************/
/** rate-monotonic algorithm


void sched_RMS(struct Thread** threads)
{
     //Global clock
    int globalCouont = 0;

    //period propertiy of current running thread
    int running_period = 100000; // very big number

    //ID (in the array) of the running thread
    int running_id = -1;

    //Initialize simulink model
    isolette_initialize();

    while(globalCount < iterCount)
    {
        //Comminucate withsimulink model, print state.
        isolette_U.In1 = $out_port;
        printf("%f,%f\\n", isolette_U.In1, isolette_Y.Out1);

        isolette_step();
        $in_port = isolette_Y.Out1;

        //Stage 1: check period_triger for each thread
        for (int i = 0; i < threadNum; i++)
        {
            int temp_period = threads[i]->period;
            if (globalCount % temp_period == 0)
            {
                threads[i]->state = "READY";
                threads[i]->runCount = 0;
            }
        }

        // Stage 2: find the next running thread
        for (int i = 0; i < threadNum; i++) {
            if (threads[i]->state == "READY" && threads[i]->period < running_period) {
                running_period = threads[i]->period;
                running_id = i;
            }
        }

        if (running_id != -1) {
            threads[running_id]->state = "RUNNING";
        }

        for (int i = 0; i < threadNum; i++)
        {
            // printf("%s state: %s\\n", threads[i]->threadName, threads[i]->state);
        }

        // Stage 3: perform the running state, check if it is running over.
        for (int i = 0; i < threadNum; i++)
        {
            if (threads[i]->state == "RUNNING") //Running State
            {
                threads[i]->runCount += 1;
                behaviorExecution(threads[i]->threadName);

                if (threads[i]->runCount >= threads[i]->minExecutionTime) // Runnning Over
                {
                    threads[i]->state = "COMPLETE";
                    running_period = 0;
                    running_id = -1;
                }
                else // Not Running Over
                {
                    running_period = threads[i]->period;
                    running_id = i;
                }
            }
        } 
        globalCount += 1;
    }
}

/************* FIFO algorithm *************/

void sched_FCFS(struct Thread** threads)
{
     //Global clock
    int globalCouont = 0;

    //period propertiy of current running thread
    int running_period = 0;

    //ID (in the array) of the running thread
    int running_id = -1;

    //Initialize simulink model
    isolette_initialize();

    while(globalCount < iterCount)
    {
        //Comminucate withsimulink model, print state.
        isolette_U.In1 = $out_port;
        printf("%f,%f\\n", isolette_U.In1, isolette_Y.Out1);

        isolette_step();
        $in_port = isolette_Y.Out1;

        //Stage 1: check period_triger for each thread
        for (int i = 0; i < threadNum; i++)
        {
            int temp_period = threads[i]->period;
            if (globalCount % temp_period == 0)
            {
                threads[i]->state = "READY";
                threads[i]->runCount = 0;
            }
        }

        // Stage 2: find the next running thread
        for (int i = 0; i < threadNum; i++) {
            if (threads[i]->state == "READY" && threads[i]->period > running_period) {
                running_period = threads[i]->period;
                running_id = i;
            }
        }

        if (running_id != -1) {
            threads[running_id]->state = "RUNNING";
        }

        for (int i = 0; i < threadNum; i++)
        {
            // printf("%s state: %s\\n", threads[i]->threadName, threads[i]->state);
        }

        // Stage 3: perform the running state, check if it is running over.
        for (int i = 0; i < threadNum; i++)
        {
            if (threads[i]->state == "RUNNING") //Running State
            {
                threads[i]->runCount += 1;
                behaviorExecution(threads[i]->threadName);

                if (threads[i]->runCount >= threads[i]->minExecutionTime) // Runnning Over
                {
                    threads[i]->state = "COMPLETE";
                    running_period = 0;
                    running_id = -1;
                }
                else // Not Running Over
                {
                    running_period = threads[i]->period;
                    running_id = i;
                }
            }
        } 
        globalCount += 1;
    }
}


/************ EDF algorithm ***************/
//Earlist deadline first algorithm
void sched_EDF(struct Thread **threads, int threadNum, int iterCount)
{
    //Global clock
    int globalCouont = 0;

    //Deadline of current running thread
    int running_ddl = 100000; //very big number

    //ID (in the array) of the running thread
    int running_id = -1;

    //Initialize simulink model
    isolette_initialize();

    while(globalCount < iterCount)
    {
        //Comminucate withsimulink model, print state.
        isolette_U.In1 = $out_port;
        printf("%f,%f\\n", isolette_U.In1, isolette_Y.Out1);

        isolette_step();
        $in_port = isolette_Y.Out1;

        //Stage 1: check period_triger foreachthread
        for (int i = 0; i < threadNum; i++)
        {
            int temp_period = threads[i]->period;
            if (globalCount % temp_period == 0)
            {
                threads[i]->state = "READY";
                threads[i]->runCount = 0;
            }
        }

        // Stage 2: find the next running thread
        for (int i = 0; i < threadNum; i++) {
            if (threads[i]->state == "READY" && threads[i]->deadline < running_ddl) {
                running_ddl = threads[i]->deadline;
                running_id = i;
            }
        }

        if (running_id != -1) {
            threads[running_id]->state = "RUNNING";
        }

        for (int i = 0; i < threadNum; i++)
        {
            // printf("%s state: %s\\n", threads[i]->threadName, threads[i]->state);
        }

        // Stage 3: perform the running state, check if it is running over.
        for (int i = 0; i < threadNum; i++)
        {
            if (threads[i]->state == "RUNNING") //Running State
            {
                threads[i]->runCount += 1;
                behaviorExecution(threads[i]->threadName);

                if (threads[i]->runCount >= threads[i]->minExecutionTime) // Runnning Over
                {
                    threads[i]->state = "COMPLETE";
                    running_ddl = 0;
                    running_id = -1;
                }
                else // Not Running Over
                {
                    running_ddl = threads[i]->deadline;
                    running_id = i;
                }
            }
        } 
        globalCount += 1;
    }
};

/************ HPF algorithm **************/

int checkRunningOver(struct Thread *thrd)
{
    int isOverFlag = 0;
    int runCount_temp = thrd->runCount;
    int minExecutionTime_temp = thrd->minExecutionTime;

    return runCount_temp >= minExecutionTime_temp;
};

void sched_HPF(struct Thread **threads, int threadNum, int iterCount)
{
    // Global clock
    int globalCount = 0;

    // Priority of the running thread
    int running_prior = 0;

    // ID (in the array) of the running thread
    int running_id = -1;

    // Initialize simulink model
    isolette_initialize();

    while (globalCount < iterCount)
    {
        // Communicate with simulink model, print state.
        isolette_U.In1 = $out_port;
        printf("%f,%f\\n", isolette_U.In1, isolette_Y.Out1);

        isolette_step();
        $in_port = isolette_Y.Out1;

        // Stage 1: check period_triger for each thread
        for (int i = 0; i < threadNum; i++)
        {
            int temp_period = threads[i]->period;
            if (globalCount % temp_period == 0)
            {
                threads[i]->state = "READY";
                threads[i]->runCount = 0;
            }
        }

        // Stage 2: find the next running thread
        for (int i = 0; i < threadNum; i++) {
            if (threads[i]->state == "READY" && threads[i]->priority > running_prior) {
                running_prior = threads[i]->priority;
                running_id = i;
            }
        }

        if (running_id != -1) {
            threads[running_id]->state = "RUNNING";
        }

        for (int i = 0; i < threadNum; i++)
        {
            // printf("%s state: %s\\n", threads[i]->threadName, threads[i]->state);
        }

        // Stage 3: perform the running state, check if it is running over.
        for (int i = 0; i < threadNum; i++)
        {
            if (threads[i]->state == "RUNNING") //Running State
            {
                threads[i]->runCount += 1;
                behaviorExecution(threads[i]->threadName);

                if (threads[i]->runCount >= threads[i]->minExecutionTime) // Runnning Over
                {
                    threads[i]->state = "COMPLETE";
                    running_prior = 0;
                    running_id = -1;
                }
                else // Not Running Over
                {
                    running_prior = threads[i]->priority;
                    running_id = i;
                }
            }
        } 
        globalCount += 1;
    }
};

// Overall scheduling function
// process: process to be simulated.
// iterCount: number of iterations.
void Scheduler(struct Process* process, int iterCount)
{
    Thread** threads = process->threadGroup;
    char* sched_pro = process->scheduling_protocol;
    int threadNum = process->numberOfThread;

    for (int i = 0; i < threadNum; i++)
    {
        threads[i]->state = "INITIAL";
    }

    // Scheduling protocol will be selected depend on different algorithms
    if (strcmp(sched_pro, "RMS") == 0) {
        sched_RMS(threads);
    }
    else if (strcmp(sched_pro, "FCFS") == 0) {
        sched_FCFS(threads);
    }
    else if (strcmp(sched_pro, "HPF") == 0) {
        sched_HPF(threads, threadNum, iterCount);
    }
    else {
        printf("No matching scheduling protocol, quit!\\n");
    }
};

"""

threadTemplate = """
    Thread *$name = (Thread *)malloc(sizeof(Thread));
    $name->tid = $index;
    $name->runCount = 0;
    $name->threadName = "$name"; 
    $name->period = $period; 
    $name->priority = $priority; 
    $name->deadline = $deadline; 
    $name->state = "HALTED"; 
    $name->dispatch_protocol = "Periodic"; 
    $name->maxExecutionTime = $max_time; 
    $name->minExecutionTime = $min_time;
"""

processTemplate = """
    Process *$name = (Process *)malloc(sizeof(Process));
    $name->processNum = 1;
    $name->numberOfThread = $num_thread;
    $name->processName = "$name";
    $name->scheduling_protocol = "HPF";
    $name->threadGroup = (Thread **)malloc($num_thread * sizeof(Thread*));
"""

processorTemplate="""

"""

systemTemplate="""


"""


deviceTemplate="""


"""



def get_opas(data, name, *, default=None):
    for item in data:
        if item['name'] == name:
            return item['value']

    return default

def translate_hcsp(hp, indent):
    res = []
    if isinstance(hp, Assign):
        res.append("%s = %s;" % (hp.var_name, str(hp.expr)))
    elif isinstance(hp, ITE):
        for i, (cond, if_hp) in enumerate(hp.if_hps):
            if i == 0:
                res.append("if (%s) {" % str(cond))
            else:
                res.append("else if (%s) {" % str(cond))
            res.extend(translate_hcsp(if_hp, 4))
            res.append("}")
        if hp.else_hp is not None:
            res.append("else {")
            res.extend(translate_hcsp(hp.else_hp, 4))
            res.append("}")
    else:
        raise NotImplementedError

    return [" " * indent + line for line in res]


def translate_behavior(name, vars, hps):
    res = []
    res.append("void thread_%s()" % name)
    res.append("{")

    for var in vars:
        res.append("    float %s;" % var)

    for hp in hps:
        hp = hp_parser.parse(hp)
        res.extend(translate_hcsp(hp, 4))

    res.append("};")
    return '\n'.join(res)


def translate(json_data):
    res = ""

    res += header

    res += "/******************Behavior Execution******************/\n\n"

    # Add ports
    ports = set()
    for k, v in json_data.items():
        if 'features' in v:
            for item in v['features']:
                if 'type' in item and item['type'] == 'DataPort':
                    ports.add(item['name'])
    
    for port_name in ports:
        res += "float %s;\n" % port_name
    res += "\n"

    # Add behavior
    behavior_names = []
    for k, v in json_data.items():
        if 'Annex' in v:
            vars = v['Annex']['var']
            hps = v['Annex']['trans']['s']['content']
            name = v['name']
            behavior_names.append(name)
            res += translate_behavior(name, vars, hps)
            res += "\n\n"

    # Add behaviorExecution function
    res += "void behaviorExecution(char *threadName)\n"
    res += "{\n"

    for name in behavior_names:
        res += "    if (strcmp(threadName, \"%s\") == 0) {\n" % name
        res += "        thread_%s();\n" % name
        res += "    }\n"

    res += "};\n\n"

    # Add scheduler
    in_port = []
    out_port = []
    for k, v in json_data.items():
        if 'category' in v and v['category'] == 'system':
            for comp in v['components']:
                if comp['category'] == 'process':
                    for feature in comp['features']:
                        if feature['direction'] == '':
                            in_port.append(feature['name'])
                        else:
                            out_port.append(feature['name'])

    if len(in_port) != 1 or len(out_port) != 1:
        raise NotImplementedError

    res += Template(scheduler).substitute({
        'in_port': in_port[0],
        'out_port': out_port[0]
    })

    # Add main function
    res += "int main()\n"
    res += "{"

    thread_lst = []
    for k, v in json_data.items():
        if "category" in v and v['category'] == 'thread':
            thread_lst.append(v['name'])
            exec_time = get_opas(v['opas'], 'Timing_Properties.Compute_Execution_Time', default=[1, 1])
            s = Template(threadTemplate).substitute({
                'name': v['name'],
                'index': len(thread_lst),
                'period': get_opas(v['opas'], 'Timing_Properties.Period',
                                   default=get_opas(v['opas'], 'Timing_Properties.Deadline')),
                'priority': get_opas(v['opas'], 'Thread_Properties.Priority'),
                'deadline': get_opas(v['opas'], 'Timing_Properties.Deadline'),
                'max_time': exec_time[0],
                'min_time': exec_time[1]
            })
            res += s

    # Define process
    process_lst = []
    for k, v in json_data.items():
        if 'category' in v and v['category'] == 'process':
            process_lst.append(v['name'])
    
    if len(process_lst) != 1:
        raise NotImplementedError
    process_name = process_lst[0]

    s = Template(processTemplate).substitute({
        'name': process_name,
        'num_thread': len(thread_lst)
    })
    res += s
    for i, thread_name in enumerate(thread_lst):
        res += "    %s->threadGroup[%d] = %s;\n" % (process_name, i, thread_name)

    res += "    Scheduler(%s, 3000);\n" % process_name

    res += "}"

    return res


if __name__ == "__main__":
    with open("aadl2cwithSimulink/out_ref.json", "r") as f:
        data = json.load(f)

    res = translate(data)
    print(res)
