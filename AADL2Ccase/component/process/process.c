#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <ctype.h>
#include <signal.h>
#include <time.h>
#include <string.h>
#include <math.h>
#include "isolette.h"
#include "rtwtypes.h"

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
    Thread** threadGroup;
} Process;



int main()
{
    Process *heatSW = (Process *)malloc(sizeof(Process));
    heatSW->processNum = 1;
    heatSW->numberOfThread = 3;
    heatSW->processName = "heatSW";
    heatSW->scheduling_protocol = "HPF";
    heatSW->threadGroup = (Thread **)malloc(3 * sizeof(Thread*));
    heatSW->threadGroup[0] = actuator;
    heatSW->threadGroup[1] = controller;
    heatSW->threadGroup[2] = sensor;


}