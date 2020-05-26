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


typedef struct Prcessor
{
    int tid;
    char *processorName;
    char *scheduling_protocol;

} Processor;


float desiredTemp;
bool heating;
bool cooling;
float currentTemp;



int main()
{
    


}