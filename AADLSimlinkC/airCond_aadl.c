//generation code from AADL model
//name: air conditioner controller

#include <stdio.h>
#include <math.h>
#include <string.h>
#include <stdlib.h>
#include "airCond_aadl.h"


//定义线程描述符


THREAD *finish, *run, *ready; //线程队列指针* 
int thread_counter = 0;//用于分配tid的计数器

//线程间是可以共享某些变量的，把他们定义在下面
//各个线程的输出
int thread_Regulator_HeaterCommad;
int thread_HeatCooler_Temperature; //= 19;
int thread_HeatCooler_heating;
int thread_HeatCooler_cooling;
int  thread_Sensor_measureTemp;
int desired_temperature;

int thread_Sensor(int  heaterTemp)
{
	printf("input : heaterTemp -> %d\n", heaterTemp);
	int e;
	e = 0;
	int measuredTemp = heaterTemp + e;
	printf("output : measuredTemp -> %d\n", measuredTemp);
	printf("\n");
	return measuredTemp;
};


//温控线程函数
int  *thread_HeatCooler(int command)
{
	printf("input : command -> %d\n", command);
	int heating, cooling;

	if (command > 0)
	{
		heating = 1;
		cooling = 0;
		thread_Sensor_measureTemp += 1;
	}
	if (command == 0)
	{
		heating = 0;
		cooling = 0;
		thread_Sensor_measureTemp += 0;
	}
	if (command < 0)
	{
		cooling = 1;
		heating = 0;
		thread_Sensor_measureTemp -= 1;
	}
	static int result[3];
	result[0] = heating;
	result[1] = cooling;
	result[2] = thread_Sensor_measureTemp;
	printf("Output : heating -> %d,cooling -> %d,and temperature -> %d\n", heating, cooling, thread_Sensor_measureTemp);
	printf("\n");
	return result;
};

//命令线程执行函数
int thread_regulator(int desiredTemp, int measuredTemp)
{
	printf("Input : desiredTemp -> %d,measuredTemp -> %d\n", desiredTemp, measuredTemp);
	int gain, diff, heaterCommad;
	gain = 2;
	diff = desiredTemp - measuredTemp;
	heaterCommad = diff * gain;
	printf("Output : heaterCommad -> %d\n", heaterCommad);
	printf("\n");
	return heaterCommad;
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
		b = 0;
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
}

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
}

//将就绪队列中的第一个选中并运行
void firstin()
{
	run = ready;   /*就绪队列头指针赋值给运行头指针*/
	//run->state='R';   /*线程状态变为运行态,以后可能会描述进程状态，这里先放着*/  
	ready = ready->next;  /*就绪对列头指针后移到下一进程*/
}

//cpu调度函数
void CPU_schedule_thread()
{
	int *result;
	firstin();
	while (run != NULL)
	{

		switch (run->tid)
		{
		case 0:
			printf("thread_Sensor is going to be run!\n");
			thread_Sensor_measureTemp = thread_Sensor(thread_HeatCooler_Temperature);
			break;
		case 1:
			printf("thread_regulator is going to be run!\n");
			thread_Regulator_HeaterCommad = thread_regulator(desired_temperature, thread_Sensor_measureTemp);
			break;
		case 2:
			printf("thread_HeatCooler is going to be run!\n");
			result = thread_HeatCooler(thread_Regulator_HeaterCommad);
			thread_HeatCooler_heating = *result;
			thread_HeatCooler_cooling = *(result + 1);
			thread_HeatCooler_Temperature = *(result + 2);
			break;
		}
		if (ready != NULL)
			firstin();
		else
			break;

	}
}




int air_system(int measureTemp, THREAD *thread_Sensor, THREAD *thread_Regulator, THREAD *thread_HeatCooler)
{	
	printf("The controller begin...\n");
	int command;
	thread_HeatCooler_Temperature = measureTemp;
	printf("the measureTemp is %d\n", thread_HeatCooler_Temperature);

	insert(thread_Sensor);
	insert(thread_Regulator);
	insert(thread_HeatCooler);
	desired_temperature = 105;
	CPU_schedule_thread();
	if (thread_HeatCooler_cooling == 1)
	{
		command = 0;
	}
	else
	{
		command = 1;
	}
	return command;
};


