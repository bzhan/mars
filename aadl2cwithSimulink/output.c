
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

/******************Behavior Execution******************/

float measuredTemp;
float boxTemp;
float diff;
float heatCommand;

void thread_actuator()
{
    if (diff > 0.0) {
        heatCommand = -1.0;
    }
    else if (diff < 0.0) {
        heatCommand = 1.0;
    }
    else {
        heatCommand = 0.0;
    }
};

void thread_controller()
{
    float gain;
    gain = 10.0;
    if (measuredTemp > 100.0) {
        diff = gain*(measuredTemp-100.0);
    }
    else if (measuredTemp < 97.0) {
        diff = gain*(measuredTemp-97.0);
    }
    else {
        diff = 0.0;
    }
};

void thread_sensor()
{
    float e;
    e = 1.0;
    measuredTemp = boxTemp+e;
};

void behaviorExecution(char *threadName)
{
    if (strcmp(threadName, "actuator") == 0) {
        thread_actuator();
    }
    if (strcmp(threadName, "controller") == 0) {
        thread_controller();
    }
    if (strcmp(threadName, "sensor") == 0) {
        thread_sensor();
    }
};



/************* RMS algorithm **************/

void sched_RMS(struct Thread** threads, int threadNum, int iterCount)
{
    return;
}

/************* FIFO algorithm *************/

void sched_FCFS(struct Thread** threads, int threadNum, int iterCount)
{
    return;
}

/************* EDF algorithm *************/

void sched_EDF(struct Thread** threads, int threadNum, int iterCount)
{
    return;
}

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
        isolette_U.In1 = heatCommand;
        printf("%f,%f\n", isolette_U.In1, isolette_Y.Out1);

        isolette_step();
        boxTemp = isolette_Y.Out1;

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
            // printf("%s state: %s\n", threads[i]->threadName, threads[i]->state);
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
        sched_RMS(threads, threadNum, iterCount);
    }
    else if (strcmp(sched_pro, "FCFS") == 0) {
        sched_FCFS(threads, threadNum, iterCount);
    }
    else if (strcmp(sched_pro, "HPF") == 0) {
        sched_HPF(threads, threadNum, iterCount);
    }
    else {
        printf("No matching scheduling protocol, quit!\n");
    }
};

int main()
{
    Thread *actuator = (Thread *)malloc(sizeof(Thread));
    actuator->tid = 1;
    actuator->runCount = 0;
    actuator->threadName = "actuator"; 
    actuator->period = 10; 
    actuator->priority = 6; 
    actuator->deadline = 10; 
    actuator->state = "HALTED"; 
    actuator->dispatch_protocol = "Periodic"; 
    actuator->maxExecutionTime = 3; 
    actuator->minExecutionTime = 5;

    Thread *controller = (Thread *)malloc(sizeof(Thread));
    controller->tid = 2;
    controller->runCount = 0;
    controller->threadName = "controller"; 
    controller->period = 10; 
    controller->priority = 8; 
    controller->deadline = 10; 
    controller->state = "HALTED"; 
    controller->dispatch_protocol = "Periodic"; 
    controller->maxExecutionTime = 1; 
    controller->minExecutionTime = 1;

    Thread *sensor = (Thread *)malloc(sizeof(Thread));
    sensor->tid = 3;
    sensor->runCount = 0;
    sensor->threadName = "sensor"; 
    sensor->period = 10; 
    sensor->priority = 10; 
    sensor->deadline = 10; 
    sensor->state = "HALTED"; 
    sensor->dispatch_protocol = "Periodic"; 
    sensor->maxExecutionTime = 1; 
    sensor->minExecutionTime = 1;

    Process *heatSW = (Process *)malloc(sizeof(Process));
    heatSW->processNum = 1;
	heatSW->numberOfThread = 3;
	heatSW->processName = "heatSW";
	heatSW->scheduling_protocol = "HPF";
	heatSW->threadGroup = (Thread **)malloc(3 * sizeof(Thread*));
    heatSW->threadGroup[0] = actuator;
    heatSW->threadGroup[1] = controller;
    heatSW->threadGroup[2] = sensor;
    Scheduler(heatSW, 3000);
}
