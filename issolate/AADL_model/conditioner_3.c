int thread_Regulator(int desiredTemp 
int measuredTemp 
return heaterCommand ;
Periodic
8
20ms
20ms
int  diff, gain ;
gain = 2;
diff =  desiredTemp - measuredTemp;
heaterCommand = diff * gain ;
int thread_HeaterCooler(int command 
return temperature ;
return heating ;
return cooling ;
Periodic
6
20ms
20ms
if (command >= 0) heating!; Temp = Temp + 1 end if;
if (command < 0) cooling!; Temp = Temp - 1 end if;
temperature = Temp ;
int thread_Sensor(int heaterTemp 
return measuredTemp ;
Periodic
10
20ms
20ms
int  e ;
e = 1; measuredTemp = heaterTemp + e ;
