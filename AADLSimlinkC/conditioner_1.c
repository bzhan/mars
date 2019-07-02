#include <stdio.h>
#include <math.h>
#include <string.h>
#include <stdlib.h>
#include "conditioner_1.h"


THREAD *finish, *run, *ready; //线程队列指针*
int thread_counter = 0;//用于分配tid的计数器


//线程间是可以共享某些变量的，把他们定义在下面
//各个线程的输出
float thread_Regulator_diff;
int thread_HeaterCooler_heatCooling;
float  thread_Sensor_measuredTemp;
//float desired_temperature;// = 25;

int process_HeaterSW_heatCooling;
float process_HeaterSW_measuredTemp;


//仿真输入参数
float thread_HeatCooler_Temperature; //= 19;
float thread_Sensor_heaterTemp;



float  system_HeatRegulator(float system_HeatRegulator_airTemp ,THREAD *thread_Regulator, THREAD *thread_HeaterCooler, THREAD *thread_Sensor){
	//float process_HeaterSW_desiredTemp = system_HeatRegulator_desiredTemp;////////////
	float process_HeaterSW_airTemp = system_HeatRegulator_airTemp;////////////////////
	//system_HeaterCPU_heatCooling = process_HeaterSW_heatCooling;
	//system_HeaterCPU_currentTemp = process_HeaterSW_measuredTemp;
	//static float  result[2];
	//float*  result_p;
	int result_p;
	result_p = process_HeaterSW(process_HeaterSW_airTemp,thread_Regulator, thread_HeaterCooler, thread_Sensor);
	//result[0] = *(result_p + 0);
	//result[1] = *(result_p + 1);
	return (float)result_p;
};

int process_HeaterSW(float process_HeaterSW_airTemp ,THREAD *thread_Regulator, THREAD *thread_HeaterCooler, THREAD *thread_Sensor){
	//float  thread_Regulator_desiredTemp = process_HeaterSW_desiredTemp;
	thread_Sensor_heaterTemp = process_HeaterSW_airTemp;
	insert(thread_Regulator);
	insert(thread_HeaterCooler);
	insert(thread_Sensor);
	CPU_schedule_thread();
	process_HeaterSW_heatCooling = thread_HeaterCooler_heatCooling;
	process_HeaterSW_measuredTemp = thread_Sensor_measuredTemp;
	//static float result[2];
	//result[0] = process_HeaterSW_heatCooling ;
	//result[1] = process_HeaterSW_measuredTemp ;
	int result;
	result = process_HeaterSW_heatCooling;
	return result;
};

float thread_Regulator(float  thread_Regulator_measuredTemp ){
	int  gain ;
	float diff;
    gain = 1;
    if(thread_Regulator_measuredTemp > 100){
        diff = gain*(thread_Regulator_measuredTemp - 100);
    }
    else if(thread_Regulator_measuredTemp < 98){
        diff = gain*(thread_Regulator_measuredTemp - 98);
    }
    else{
        diff = 0;
    }
    //printf("The diff is %f\n", diff);
     //diff =  thread_Regulator_desiredTemp - thread_Regulator_measuredTemp; //////////////////////////
     //thread_Regulator_heaterCommand = diff * gain  ; ////////////////////////////////
    thread_Regulator_diff = diff;
	return  thread_Regulator_diff;       //thread_Regulator_heaterCommand ;
};

float thread_HeaterCooler(float thread_HeaterCooler_command ){
	float command = thread_HeaterCooler_command; ////////////////////////////////////////////
    if (command > 0) {thread_HeaterCooler_heatCooling = -1; } //////////
     if (command < 0) {thread_HeaterCooler_heatCooling = 1;} ///////////////
     if (command == 0) {thread_HeaterCooler_heatCooling = 0; } ///////////////

	return thread_HeaterCooler_heatCooling ;
};

float thread_Sensor(float thread_Sensor_heaterTemp ){
	int  e ;
    e  = 0.1; thread_Sensor_measuredTemp = thread_Sensor_heaterTemp + e  ;  //////////////////////
	return thread_Sensor_measuredTemp ;
};

/*根据优先级的插入算法*/
void insert(THREAD *q)
{
	THREAD *p1, *s, *r;
	int b;
	s = q;  /*待插入的PCB指针*/
	p1 = ready; /*就绪队列头指针*/
	r = p1; /*r做p1的前驱指针*/
	b = 1;
	while ((p1 != NULL) && b)  /*根据优先数确定插入位置*/
	if (p1->priority >= s->priority)
	{
		r = p1;
		p1 = p1->next;
	}
	else
	{
		b = 0;
	}
	if (r != p1)  /*如果条件成立说明插入在r与p1之间*/
	{
		r->next = s;
		s->next = p1;
	}
	else
	{
		s->next = p1;  /*否则插入在就绪队列的头*/
		ready = s;
	}
};

//创建线程函数
THREAD *create_thread(int prior)
{
	THREAD *one_thread;
	one_thread = (THREAD *)malloc(sizeof(THREAD));
	one_thread->tid = thread_counter;
	one_thread->priority = prior;
	//one_thread->state = 'w';/*线程状态变为运行态,以后可能会描述进程状态，这里先放着*/
	one_thread->next = NULL;
	thread_counter = thread_counter + 1;
	return one_thread;
};

//将就绪队列中的第一个选中并运行
void firstin()
{
	run = ready;   /*就绪队列头指针赋值给运行头指针*/
	//run->state='R';   /*线程状态变为运行态,以后可能会描述进程状态，这里先放着*/
	ready = ready->next;  /*就绪对列头指针后移到下一进程*/
};

//cpu调度函数
void CPU_schedule_thread()
{
	int result;
	firstin();
	while (run != NULL)
	{

		switch (run->tid)
		{
		case 0:
			//printf("thread_Sensor is going to be run!\n");
			thread_Sensor_measuredTemp = thread_Sensor(thread_Sensor_heaterTemp);
			break;
		case 1:
			//printf("thread_regulator is going to be run!\n");
			thread_Regulator_diff = thread_Regulator(thread_Sensor_measuredTemp);
			break;
		case 2:
			//printf("thread_HeaterCooler is going to be run!\n");
			result = thread_HeaterCooler(thread_Regulator_diff);
			thread_HeaterCooler_heatCooling = result;
			break;
		}
		if (ready != NULL)
			firstin();
		else
			break;

	}
};


/*
int main()
{
    int *command;

    //测温线程优先级为10
	THREAD *thread_Sensor;
	thread_Sensor = create_thread(10);

	//指令线程优先级为8
	THREAD *thread_Regulator;
	thread_Regulator = create_thread(8);


	//温控线程优先级为6
	THREAD *thread_HeaterCooler;
	thread_HeaterCooler = create_thread(6);

    for (int i = 0; i<10; i++){
        printf("Program start...\n");
        command = system_HeatRegulator(desired_temperature,thread_HeatCooler_Temperature, thread_Sensor, thread_Regulator, thread_HeaterCooler);
        printf("the updated command is %d\n", *command);
   		thread_Regulator_heaterCommand = *command;
    }
}
*/
