#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <ctype.h>
#include <signal.h>
#include <time.h>
#include <string.h>
#include <math.h>


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

//GLobal Port Management
float process_calculator_operand1;
float process_calculator_operand2;
bool process_calculator_add;
bool process_calculator_sub;
bool process_calculator_mul;
bool process_calculator_div;
bool process_calculator_mod;
bool process_calculator_rem;
bool process_calculator_rnd;
bool process_calculator_fac;
bool process_calculator_pow;
bool process_calculator_ln;
bool process_calculator_log;
bool process_calculator_exp;
bool process_calculator_sin;
bool process_calculator_cos;
bool process_calculator_tan;
float process_calculator_result;



int main()
{
    Process *calculator = (Process *)malloc(sizeof(Process));
    calculator->processNum = 1;
    calculator->numberOfThread = 1;
    calculator->processName = "calculator";
    calculator->scheduling_protocol = "HPF";
    calculator->threadGroup = (Thread **)malloc(1 * sizeof(Thread*));
    calculator->threadGroup[0] = calc;

}