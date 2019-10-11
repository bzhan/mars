
#include<stdio.h>
#include<stdlib.h>
#include<unistd.h>
#include<ctype.h>
#include<signal.h>
#include<time.h>
#include<string.h>
#include<math.h>
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

float diff;
float heatCommand;
float measuredTemp;
float boxTemp;

void thread_Sensor()
{
	float e;
	e = 1.0;
	measuredTemp = boxTemp + e;
};

void thread_HeatCooler()
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

void thread_regulator()
{
	float gain;
	gain = 10.0;
	if (measuredTemp > 100.0) {
		diff = gain * (measuredTemp - 100.0);
	}
	else if (measuredTemp < 97.0) {
		diff = gain * (measuredTemp - 97.0);
	}
	else {
		diff = 0.0;
	}
};

void behaviorExecution(char *threadName)
{
	if (strcmp(threadName, "Sensor") == 0) {
		thread_Sensor();
	}
	if (strcmp(threadName, "Regulator") == 0) {
		thread_regulator();
	}
	if (strcmp(threadName, "HeatCooler") == 0) {
		thread_HeatCooler();	
	}
};


/************* RMS algorithm **************/

void sched_RMS(struct Thread** threads)
{
	return;
}

/************* FIFO algorithm *************/

void sched_FCFS(struct Thread** threads)
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
		sched_RMS(threads);
	}
	else if (strcmp(sched_pro, "FCFS") == 0) {
		sched_FCFS(threads);
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
	Thread *Sensor = (Thread *)malloc(sizeof(Thread));
	Sensor->tid = 1;
	Sensor->runCount = 0;
	Sensor->threadName = "Sensor"; 
	Sensor->period = 10; 
	Sensor->priority = 6; 
	Sensor->deadline = 10; 
	Sensor->state = "HALTED"; 
	Sensor->dispatch_protocol = "Periodic"; 
	Sensor->maxExecutionTime = 1; 
	Sensor->minExecutionTime = 1; 

    Thread *HeatCooler = (Thread *)malloc(sizeof(Thread));
    HeatCooler->tid = 2;
    HeatCooler->runCount = 0;
	HeatCooler->threadName = "HeatCooler"; 
	HeatCooler->period = 10; 
	HeatCooler->priority = 8; 
	HeatCooler->deadline = 10; 
	HeatCooler->state = "HALTED"; 
	HeatCooler->dispatch_protocol = "Periodic"; 
	HeatCooler->maxExecutionTime = 1; 
	HeatCooler->minExecutionTime = 1; 

    Thread *Regulator = (Thread *)malloc(sizeof(Thread));
    Regulator->tid = 3;
    Regulator->runCount = 0;
	Regulator->threadName = "Regulator"; 
	Regulator->period = 10; 
	Regulator->priority = 10; 
	Regulator->deadline = 10; 
	Regulator->state = "HALTED"; 
	Regulator->dispatch_protocol = "Periodic"; 
	Regulator->maxExecutionTime = 3; 
	Regulator->minExecutionTime = 2; 

    Process *HeatSW = (Process *)malloc(sizeof(Process));
    HeatSW->processNum = 1;
	HeatSW->numberOfThread = 3;
	HeatSW->processName = "HeatSW";
	HeatSW->scheduling_protocol = "HPF";
	HeatSW->threadGroup = (Thread **)malloc(3 * sizeof(Thread*));
	HeatSW->threadGroup[0] = Sensor;
	HeatSW->threadGroup[1] = HeatCooler;
	HeatSW->threadGroup[2] = Regulator;

	// CPU: currently unused
	Processor *CPU = (Processor *)malloc(sizeof(Processor));
	CPU->processorNum = 1;
	CPU->numberOfProcess = 1;
	CPU->processorName = "CPU";
	CPU->processGroup = (Process**)malloc(1 * sizeof(Process*));
	CPU->processGroup[0] = HeatSW;

	Scheduler(HeatSW, 3000);
}
