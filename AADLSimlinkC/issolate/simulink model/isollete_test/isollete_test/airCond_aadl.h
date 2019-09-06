#ifndef __AIRCOND_AADL_H__
#define __AIRCOND_AADL_H__

typedef struct node
{
	int tid;  /*�̱߳�ʶ��*/
	int priority;   /*����������*/
	char state; /*���̵�״̬���Ժ���ܻ���������״̬�������ȶ����������*/
	struct node *next; /*��ָ��*/
	char* dispatch_protocol;/*����Э��*/
	int deadline;/*��ֹʱ�䲻֪�������õ�*/
	int period; /*�߳�ʱ������Ҳ��֪�������õ�*/
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