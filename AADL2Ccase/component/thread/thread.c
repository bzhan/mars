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

typedef struct Thread 
{
    int tid; /* The ID of a thread */
    int runCount;
    char *threadName; /*name of thread*/
    int period; /*time interval to be stimulated*/
    int priority; /*priority*/
    int deadline; /*No more than deadline*/
    char *state; /*seven state: halted, initial, waiting, ready, running, complete, finial */
    char *dispatch_protocol; /*periodic, aperiodic and et al.*/
    int maxExecutionTime; /*max execution time*/
    int minExecutionTime; /*min execution time*/
} Thread;


/******************Behavior Execution******************/

float heatCommand;
float measuredTemp;
float diff;
float boxTemp;


void thread_actuator()
{
    if (diff > 0.0) {
        heatCommand = -1.0;
    }
    else if (diff < 0.0) {
        heatCommand = 1.0;
    }
    else {
        heatCommand = 0.0;
    }
};

void thread_controller()
{
    float gain;
    gain = 10.0;
    if (measuredTemp > 100.0) {
        diff = gain*(measuredTemp-100.0);
    }
    else if (measuredTemp < 97.0) {
        diff = gain*(measuredTemp-97.0);
    }
    else {
        diff = 0.0;
    }

};

void thread_sensor()
{
    float e;
    e = 1.0;
    measuredTemp = boxTemp+e;

};

void behaviorExecution(char *threadName)
{
    if (strcmp(threadName, "actuator") == 0) {
        thread_actuator();
    }
    if (strcmp(threadName, "controller") == 0) {
        thread_controller();
    }
    if (strcmp(threadName, "sensor") == 0) {
        thread_sensor();
    }
};


int main()
{
    Thread *actuator = (Thread *)malloc(sizeof(Thread));
    actuator->tid = 1;
    actuator->runCount = 0;
    actuator->threadName = "actuator"; 
    actuator->period = 10; 
    actuator->priority = 6; 
    actuator->deadline = 10; 
    actuator->state = "HALTED"; 
    actuator->dispatch_protocol = "Sporadic"; 
    actuator->maxExecutionTime = 1; 
    actuator->minExecutionTime = 1;

    Thread *controller = (Thread *)malloc(sizeof(Thread));
    controller->tid = 2;
    controller->runCount = 0;
    controller->threadName = "controller"; 
    controller->period = 10; 
    controller->priority = 8; 
    controller->deadline = 10; 
    controller->state = "HALTED"; 
    controller->dispatch_protocol = "Sporadic"; 
    controller->maxExecutionTime = 1; 
    controller->minExecutionTime = 1;

    Thread *sensor = (Thread *)malloc(sizeof(Thread));
    sensor->tid = 3;
    sensor->runCount = 0;
    sensor->threadName = "sensor"; 
    sensor->period = 10; 
    sensor->priority = 10; 
    sensor->deadline = 10; 
    sensor->state = "HALTED"; 
    sensor->dispatch_protocol = "Periodic"; 
    sensor->maxExecutionTime = 1; 
    sensor->minExecutionTime = 1;


}