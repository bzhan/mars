// isollete_test.cpp : Defines the entry point for the console application.
//

	/*
	* File: ert_main.c
	*
	* Code generated for Simulink model 'isolette'.
	*
	* Model version                  : 1.2
	* Simulink Coder version         : 8.10 (R2016a) 10-Feb-2016
	* C/C++ source code generated on : Fri Feb 22 10:14:33 2019
	*
	* Target selection: ert.tlc
	* Embedded hardware selection: Intel->x86-64 (Windows64)
	* Code generation objectives: Unspecified
	* Validation result: Not run
	*/

#include <stddef.h>
#include <stdio.h>   /* This ert_main.c example uses printf/fflush */
#include <stdbool.h>
#include "isolette.h"                  /* Model's header file */
#include "rtwtypes.h"
//#include "airCond_aadl.h"
#include "conditioner_1.h"


	/*
	* Associating rt_OneStep with a real-time clock or interrupt service routine
	* is what makes the generated code "real-time".  The function rt_OneStep is
	* always associated with the base rate of the model.  Subrates are managed
	* by the base rate from inside the generated code.  Enabling/disabling
	* interrupts and floating point context switches are target specific.  This
	* example code indicates where these should take place relative to executing
	* the generated code step function.  Overrun behavior should be tailored to
	* your application needs.  This example simply sets an error status in the
	* real-time model and returns from rt_OneStep.
	*/
	void rt_OneStep(THREAD *thread_Sensor, THREAD *thread_Regulator, THREAD *thread_HeatCooler);
	void rt_OneStep(THREAD *thread_Sensor, THREAD *thread_Regulator, THREAD *thread_HeatCooler)
	{
		static boolean_T OverrunFlag = false;

        //FILE *fp;
        //if((fp=fopen("123.txt","a"))==NULL)
        //    printf("file cannot open \n");
        //else
        //    printf("file opened for writing \n");



		/* Disable interrupts here */

		/* Check for overrun */
		if (OverrunFlag) {
			rtmSetErrorStatus(isolette_M, "Overrun");
			return;
		}

		OverrunFlag = true;

		/* Save FPU context here (if necessary) */
		/* Re-enable timer or interrupt here */
		/* Set model inputs here */
		//isolette_U.In1 = 4;
		/* Step the model for base rate */
		//printf("The command is %f\n", isolette_U.In1);
		isolette_step();

		//isolette_U.In1 = air_system((int)isolette_Y.Out1, thread_Sensor, thread_Regulator, thread_HeatCooler);
		isolette_U.In1 = system_HeatRegulator(isolette_Y.Out1, thread_Regulator, thread_HeatCooler, thread_Sensor);
			//air_system((int)isolette_Y.Out1);

		printf("The Air Value is %f\n", isolette_Y.Out1);

		FILE *fpWrite=fopen("air.txt","a");
		if(fpWrite==NULL)
        {
            return 0;
        }
        else
        {
            fprintf(fpWrite, "%f\n", isolette_Y.Out1);
        }
        fclose(fpWrite);






		//printf("The command is %f\n", isolette_U.In1);
		/* Get model outputs here */
		//printf("**************************************\n");

		/* Indicate task complete */
		OverrunFlag = false;

		/* Disable interrupts here */
		/* Restore FPU context here (if necessary) */
		/* Enable interrupts here */
	}

	/*
	* The example "main" function illustrates what is required by your
	* application code to initialize, execute, and terminate the generated code.
	* Attaching rt_OneStep to a real-time clock is target specific.  This example
	* illustrates how you do this relative to initializing the model.
	*/
int_T main(int_T argc, const char *argv[])
	{
		/* Unused arguments */
		(void)(argc);
		(void)(argv);

		/* Initialize model */
		isolette_initialize();
		isolette_U.In1 = 1;
		/* Simulating the model step behavior (in non real-time) to
		*  simulate model behavior at stop time.
		*/

		//²âÎÂÏß³ÌÓÅÏÈ¼¶Îª10
		THREAD *thread_Sensor;
		thread_Sensor = create_thread(10);

		//Ö¸ÁîÏß³ÌÓÅÏÈ¼¶Îª8
		THREAD *thread_Regulator;
		thread_Regulator = create_thread(8);


		//ÎÂ¿ØÏß³ÌÓÅÏÈ¼¶Îª6
		THREAD *thread_HeatCooler;
		thread_HeatCooler = create_thread(6);

		int count = 0;
		while ((count < 3000) && (rtmGetErrorStatus(isolette_M) == (NULL)) && !rtmGetStopRequested
			(isolette_M)) {
			rt_OneStep(thread_Sensor, thread_Regulator, thread_HeatCooler);
			count += 1;
		}

		/* Disable rt_OneStep() here */
		while (1);
		/* Terminate model */
		isolette_terminate();

		return 0;
	}

	/*
	* File trailer for generated code.
	*
	* [EOF]
	*/


