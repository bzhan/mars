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