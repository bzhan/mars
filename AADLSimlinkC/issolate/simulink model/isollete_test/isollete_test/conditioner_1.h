#ifndef __CONDITIONER_1_H__
#define __CONDITIONER_1_H__

//定义线程描述符
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



extern int thread_Sensor(int thread_Sensor_heaterTemp);

extern int  thread_HeaterCooler(int thread_HeaterCooler_command);

extern int thread_Regulator(int thread_Regulator_desiredTemp, int thread_Regulator_measuredTemp);

extern void insert(THREAD *q);

extern THREAD *create_thread(int prior);

extern void firstin();

extern void CPU_schedule_thread();

extern int system_HeatRegulator(int system_HeatRegulator_desiredTemp, int system_HeatRegulator_airTemp, THREAD *thread_Regulator, THREAD *thread_HeaterCooler, THREAD *thread_Sensor);

extern int process_HeaterSW(int process_HeaterSW_desiredTemp, int process_HeaterSW_airTemp, THREAD *thread_Regulator, THREAD *thread_HeaterCooler, THREAD *thread_Sensor);



#endif 