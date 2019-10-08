
#include<stdio.h>
#include<stdlib.h>
#include<unistd.h>
#include<ctype.h>
#include<signal.h>
#include<time.h>
#include<string.h>
#include<math.h>

/** type struct definition of components 
------------------------------------------------------
  System Component: system
  Hardware Component: processor memory bus device
  Software Component: process thread subprogram 
------------------------------------------------------  
**/

typedef struct Process
{
	int processNum;
	int numberOfThread;
	char *processName;
	char *scheduling_protocol;
	int threadGroup[10];

	struct Process *next;
}Process ;

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

    struct Thread *next;

}Thread ;

typedef struct Processor
{
	int processorNum;
	int numberOfProcess;
	char *processorName;
	//Process processGroup[10];
	int processGroup[10];

	struct Processor *next;
	
}Processor ;


typedef struct List
{
	Thread *pfirst;
}List ;



/************* RMS algorithm **************/

/*
void sched_RMS(thread threads[])
{
	return 0;
}
*/

/************* FIFO algorithm *************/
/*
void sched_FCFS(thread threads[])
{
	return 0;
}
*/

/************ HPF algorithm **************/

void init_list(struct List *l)
{
	l->pfirst = NULL;
};


/*void printList(struct List *l)
{
	struct List *p;
	p=l;
	if(l!=NULL)
		do
	{
		printf("PrintList %s\n",p->pfirst->threadName);
		p=p->next;
 
	}
	while(p!=NULL);
}；*/

void add_thread(struct List *l, struct Thread *thrd)
{
	Thread *paux;
	Thread *temp;
	paux = thrd;
	paux->next = NULL;
	
	if(NULL == l->pfirst)
	{
		l->pfirst = paux;
		l->pfirst->next = NULL;
	}
	else
	{
		temp = l->pfirst;
		while(temp)
		{
			if(NULL == temp->next)
			{
				temp->next = paux;
				paux->next = NULL;
			}
			temp = temp->next;
		}
	}
	
};

void remove_thread(struct List *l, int tid)
{
	Thread *paux;
	paux = l->pfirst;
	if(paux == NULL)
		return;
	else
	{
		if ((paux->next == NULL) && (paux->tid == tid)) 
		{
			free(paux);
			l->pfirst = NULL;
		} 
		else 
		{
			Thread  *prev;
			prev = paux;
			do {
				if (paux->tid == tid) 
				{
					
					
					if (l->pfirst == paux)
					{
						l->pfirst = paux->next;
					}
					else
					{
						prev->next = paux->next;
					}
					free(paux);
					free(prev);
					break;
				}
				prev = paux;
				paux = paux->next;
			} while (paux != NULL);

		}
	}
};

struct Thread *find_thread(struct List *l, int id)
{
	Thread *paux;

	paux = l->pfirst;

	if (paux == NULL)
		return NULL;
	if (paux->tid == id)
		return paux;

	while (paux != NULL) {
		if (paux->tid == id)
			return paux;
		paux = paux->next;
	}
	return NULL;
};

int isInReadyQueue(struct List *l, int id)
{
	Thread *paux;
	int isInQueueFlag = 0;

	paux = l->pfirst;

	if (paux == NULL)
	{
		isInQueueFlag = 0;
	}
	else
	{
		if (paux->tid == id)
		{
			isInQueueFlag = 1;
		}
	}
	

	while (paux != NULL) 
	{
		if (paux->tid == id)
		{
			isInQueueFlag = 1;
		}
		paux = paux->next;
	}
	return isInQueueFlag;
};

int find_thread_HPF(struct List *l)
{
	Thread *paux;

	paux = l->pfirst;

	if(paux == NULL)
	{
		return 0;
	}
	
	int prior = 0;
	int id = 0;
	
	while(paux != NULL)
	{
		if((paux->state != "COMPLETE") && (paux->priority > prior))
		{
			prior = paux->priority;
			id = paux->tid;
		}
		paux = paux->next;
		
	}
	//printf("current HPF thread is %d\n", id);
	return id;

};

int checkRunningOver(struct Thread *thrd)
{
	int isOverFlag = 0;
	int runCount_temp = thrd->runCount;
	int minExecutionTime_temp = thrd->minExecutionTime;
	//printf("current thread runCount is %d\n", runCount_temp);
	if(runCount_temp >= minExecutionTime_temp)
		isOverFlag = 1;
	else
		isOverFlag = 0;

	return isOverFlag;
};

int findPrior(struct Thread *threads[], int id)
{
	int threadNum = 3;
	for(int i =0; i < threadNum; i++)
	{
		if(threads[i]->tid == id)
		{
			return threads[i]->priority;
		}
	}
	return 0;

};

void createState(struct Thread *threads[], int thread_id, char *state)
{
	int threadNum = 3;
	
	for(int i = 0; i < threadNum; i++)
	{
		if(threads[i]->tid == thread_id)
		{
			threads[i]->state = state;
		}
	}
};


void sched_HPF(struct Thread *threads[])
{
	Thread *head;
	List readyQueue;

	//printf("begin intit\n");
	init_list(&readyQueue);
	int prior = 0;
	int threadNum = 3;

	//initialize the runCount of each thread
	for(int i = 0; i < threadNum; i++)
	{
		threads[i]->runCount = 0;
	}
	
	int globalCount = 0;
	int runningFlag = 0; //if thread running, 1, else 0;
	int pthread_id;
	int running_prior;
	int running_id;
	Thread *runningThread = (Thread *)malloc(sizeof(Thread));
	Thread *pthread_temp = (Thread *)malloc(sizeof(Thread));
	Thread *pthread_rm_temp = (Thread *)malloc(sizeof(Thread));
	while(globalCount < 70)
	{
		//printf("Enter loop\n");

		//Stage 1: check period_triger for each thread
		for(int i = 0; i < threadNum; i++)
		{
			int temp_period = threads[i]->period;
			if(globalCount % temp_period == 0)
			{
				threads[i]->state = "READY";
			}
			else
			{	
				threads[i]->state = threads[i]->state;
			}		
		}

		//printf("Stage 2 begin\n");
		//Stage 2: check state for each thread
		// if Ready: Add thread to ReadyQueue
		// if Await: Add thread to ReadyQueue
		// if Runing: check RunningOver State
		// if Complelte: no change
		// if Suspend: Add to suspendQueue
		for(int i = 0; i < threadNum; i++)
		{
			if(threads[i]->state == "READY")   //Ready State
			{
				int isInReady = isInReadyQueue(&readyQueue, threads[i]->tid);
				//printf("after isInreadly \n");
				if( isInReady == 0)
				{
					//printf("Not in ReadyQueue, Add now!\n");
					pthread_temp = threads[i];
					add_thread(&readyQueue, pthread_temp);
				}			
			}
			else if(threads[i]->state =="COMPLETE") //Complete State
			{
				threads[i]->state = "COMPLETE"; 
			}
			else if(threads[i]->state == "RUNNING") //Running State
			{
				//printf("thr running thread tid is %s\n", threads[i]->state);
				int isRunningOver = checkRunningOver(threads[i]);
				//printf("isRunningOver is %d\n", isRunningOver);
				if(isRunningOver == 1) //Runnning Over
				{
					threads[i]->state = "COMPLETE";
					threads[i]->runCount = 0;
					runningFlag = 0;
					running_prior = 0;
				}
				if(isRunningOver == 0)// Not Running Over
				{
					threads[i]->state ="RUNNING";
					threads[i]->runCount += 1;
					runningFlag = 1;
					running_prior = threads[i]->priority;
					running_id = threads[i]->tid;
					runningThread = threads[i];
				}
			}
			else
			{
				threads[i]->state = "INITIAL";
			}
		} 

		//printf("Stage 3 begin\n");
		//Stage 3: ReadyQueue 
		pthread_id = find_thread_HPF(&readyQueue);
		if(runningFlag == 0)
		{	
			for(int i = 0; i < threadNum; i++)
			{
				if(threads[i]->tid == pthread_id)
				{
					threads[i]->state = "RUNNING";
					//printf("before runCount is %d\n", threads[i]->runCount);
					threads[i]->runCount += 1;
					//printf("after runCount is %d\n", threads[i]->runCount);
					runningFlag = 1;
				}
				//other threads in readyQueue				
			}
		}
		else //if(runningFlag == 1)
		{
			//printf("runningFlag is %d\n", runningFlag);
			if(findPrior(threads, pthread_id) < running_prior)
			{
				createState(threads, pthread_id, "READY");
			}
			else
			{
				createState(threads, running_id, "READY");
				pthread_temp = runningThread;
				add_thread(&readyQueue, pthread_temp);

				for(int i = 0; i < threadNum; i++)
				{
					if(threads[i]->tid == pthread_id)
					{
						threads[i]->state = "RUNNING";
						//printf("before runCount is %d\n", threads[i]->runCount);
						threads[i]->runCount += 1;
						//printf("after runCount is %d\n", threads[i]->runCount);
						runningFlag = 1;
					}				
				}

			}
		}

		for(int i = 0; i< threadNum; i++)
		{
			//printf("print state\n");
			printf("%s state: %s\n", threads[i]->threadName, threads[i]->state);
		}
		globalCount += 1;
		printf("%d\n", globalCount);

	}
};


/*Scheduler*/
void Scheduler(char* sched_pro, struct Thread *threads[])
{
	int threadNum = 3;
	//printf("the num of threads is %d\n", threadNum);

	for(int i = 0; i < threadNum; i++)
	{
		threads[i]->state = "INITIAL";
	}

	//Scheduling protocol will be selected depend on different algorithms
	/*if sched_pro == "RMS":
		sched_RMS(threads);

	else if sched_pro == "FCFS":
		sched_FCFS(threads);
	*/
	if(sched_pro == "HPF")
	{
		//printf("Enter HPF Scheduling\n" );
		sched_HPF(threads);
	}
	else
	{
		printf("No matching scheduling protocol, quit!\n");
		//break;
	}
};




/*instance of thread*/
int main()
{
	/*instance of thread*/
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
    Sensor->next = NULL;

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
    HeatCooler->next = NULL;

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
    Regulator->next = NULL;

    Process *HeatSW = (Process *)malloc(sizeof(Process));
    HeatSW->processNum = 1;
	HeatSW->numberOfThread = 3;
	HeatSW->processName = "HeatSW";
	HeatSW->scheduling_protocol = "HPF";
	HeatSW->threadGroup[0] = Sensor->tid;
	HeatSW->threadGroup[1] = HeatCooler->tid;
	HeatSW->threadGroup[2] = Regulator->tid;
	HeatSW->next = NULL;

	Processor *CPU = (Processor *)malloc(sizeof(Processor));
	CPU->processorNum = 1;
	CPU->numberOfProcess = 1;
	CPU->processorName = "CPU";
	CPU->processGroup[0] = HeatSW->processNum;
	CPU->next = NULL;

	Thread *threads[] = {Sensor, HeatCooler, Regulator};

	Scheduler(HeatSW->scheduling_protocol, threads);
}




















