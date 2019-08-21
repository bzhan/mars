int system_HeatRegulator(int system_HeatRegulator_desiredTemp , int system_HeatRegulator_airTemp ,THREAD *thread_Regulator, THREAD *thread_HeaterCooler, THREAD *thread_Sensor){
	int process_HeaterSW_desiredTemp = system_HeatRegulator_desiredTemp;
	int process_HeaterSW_airTemp = system_HeatRegulator_airTemp;
	// system_HeatRegulator_heatCooling = process_HeaterSW_heatCooling;
	// system_HeatRegulator_currentTemp = process_HeaterSW_measuredTemp;
	static int result[2];
	int *result_p;
	result_p = process_HeaterSW(process_HeaterSW_desiredTemp, process_HeaterSW_airTemp,thread_Regulator, thread_HeaterCooler, thread_Sensor);
	result[0] = *(result_p + 0);
	result[1] = *(result_p + 1);
	return result;
};

int process_HeaterSW(int process_HeaterSW_desiredTemp , int process_HeaterSW_airTemp ,THREAD *thread_Regulator, THREAD *thread_HeaterCooler, THREAD *thread_Sensor){
	int thread_Regulator_desiredTemp = process_HeaterSW_desiredTemp;
	int thread_Sensor_heaterTemp = process_HeaterSW_airTemp;
	insert(thread_Regulator);
	insert(thread_HeaterCooler);
	insert(thread_Sensor);
	CPU_schedule_thread();
	process_HeaterSW_heatCooling = thread_HeaterCooler_heatCooling;
	process_HeaterSW_measuredTemp = thread_Sensor_measuredTemp;
	static int result[2];
	result[0] = process_HeaterSW_heatCooling ;
	result[1] = process_HeaterSW_measuredTemp ;
	return result;
};

int thread_Regulator(int thread_Regulator_desiredTemp, int thread_Regulator_measuredTemp){
	int  diff, gain ;
    gain = 2;     diff =  thread_Regulator_desiredTemp - thread_Regulator_measuredTemp;     thread_Regulator_heaterCommand = diff * gain  ;
	return thread_Regulator_heaterCommand;
};

int thread_HeaterCooler(int thread_HeaterCooler_command){
	int  Temp ;
    if (thread_HeaterCooler_command > 0){ thread_HeaterCooler_heatCooling = 1;  }//     if (thread_HeaterCooler_command < 0){ thread_HeaterCooler_heatCooling = -1; }//     if (thread_HeaterCooler_command == 0){ thread_HeaterCooler_heatCooling = 0; }//  ;
	return thread_HeaterCooler_heatCooling;
};

int thread_Sensor(int thread_Sensor_heaterTemp){
	int  e ;
    e = 1; thread_Sensor_measuredTemp = thread_Sensor_heaterTemp + e  ;
	return thread_Sensor_measuredTemp;
};

