#ifndef __AIRCOND_AADL_H__
#define __AIRCOND_AADL_H__

typedef struct node
{
	int tid;  /*线程标识符*/
	int priority;   /*进程优先数*/
	char state; /*进程的状态，以后可能会描述进程状态，这里先定义在这放着*/
	struct node *next; /*链指针*/
	char* dispatch_protocol;/*调度协议*/
	int deadline;/*截止时间不知道干嘛用的*/
	int period; /*线程时间间隔，也不知道干嘛用的*/
}THREAD;


extern int thread_Sensor(int heaterTemp);

extern int  *thread_HeatCooler(int command);

extern int thread_regulator(int desiredTemp, int measuredTemp);

extern void insert(THREAD *q);

extern THREAD *create_thread(int prior);

extern void firstin();

extern void CPU_schedule_thread();

extern int air_system(int measureTemp, THREAD *thread_Sensor, THREAD *thread_Regulator, THREAD *thread_HeatCooler);





#endif 