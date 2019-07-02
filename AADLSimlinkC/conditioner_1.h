#ifndef __CONDITIONER_1_H__
#define __CONDITIONER_1_H__

//�����߳�������
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



extern float thread_Sensor(float thread_Sensor_heaterTemp);

extern float  thread_HeaterCooler(float thread_HeaterCooler_command);

extern float thread_Regulator(float thread_Regulator_measuredTemp);

extern void insert(THREAD *q);

extern THREAD *create_thread(int prior);

extern void firstin();

extern void CPU_schedule_thread();

extern float system_HeatRegulator(float system_HeatRegulator_airTemp, THREAD *thread_Regulator, THREAD *thread_HeaterCooler, THREAD *thread_Sensor);

extern int process_HeaterSW(float process_HeaterSW_airTemp, THREAD *thread_Regulator, THREAD *thread_HeaterCooler, THREAD *thread_Sensor);



#endif
