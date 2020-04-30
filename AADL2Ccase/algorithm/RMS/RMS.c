
/************ RMS algorithm **************/

int checkRunningOver(struct Thread *thrd)
{
    int isOverFlag = 0;
    int runCount_temp = thrd->runCount;
    int minExecutionTime_temp = thrd->minExecutionTime;

    return runCount_temp >= minExecutionTime_temp;
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

void sched_RMS(struct Thread **threads, int threadNum, int iterCount)
{
    // Global clock
    int globalCount = 0;

    // Period of the running thread
    int running_period = 0;

    // ID (in the array) of the running thread
    int running_id = -1;

    // Initialize simulink model
    isolette_initialize();

    while (globalCount < iterCount)
    {
        // Communicate with simulink model, print state.
        isolette_U.In1 = heatCommand;
        //printf("%f,%f\n", isolette_U.In1, isolette_Y.Out1);

        isolette_step();
        boxTemp = isolette_Y.Out1;

        // Stage 1: check period_triger for each thread
        for (int i = 0; i < threadNum; i++)
        {
            int temp_period = threads[i]->period;
            if (globalCount % temp_period == 0)
            {
                threads[i]->state = "READY";
                threads[i]->runCount = 0;
            }
        }

        // Stage 2: find the next running thread
        for (int i = 0; i < threadNum; i++) {
            if (threads[i]->state == "READY" && threads[i]->period > running_period) {
                running_period = threads[i]->period;
                running_id = i;
            }
        }

        if (running_id != -1) {
            threads[running_id]->state = "RUNNING";
        }

        for (int i = 0; i < threadNum; i++)
        {
            // printf("%s state: %s\n", threads[i]->threadName, threads[i]->state);
        }

        // Stage 3: perform the running state, check if it is running over.
        for (int i = 0; i < threadNum; i++)
        {
            if (threads[i]->state == "RUNNING") //Running State
            {
                threads[i]->runCount += 1;
                behaviorExecution(threads[i]->threadName);
            

                if (threads[i]->runCount >= threads[i]->minExecutionTime) // Runnning Over
                {
                    threads[i]->state = "COMPLETE";
                    running_period = 0;
                    running_id = -1;
                }
                else // Not Running Over
                {
                    running_period = threads[i]->period;
                    running_id = i;
                }
            }
        } 
        globalCount += 1;
    }
};

// Overall scheduling function
// process: process to be simulated.
// iterCount: number of iterations.
void Scheduler(struct Process* process, int iterCount)
{
    Thread** threads = process->threadGroup;
    char* sched_pro = process->scheduling_protocol;
    int threadNum = process->numberOfThread;

    for (int i = 0; i < threadNum; i++)
    {
        threads[i]->state = "INITIAL";
    }

    // Scheduling protocol will be selected
    // depend on different algorithms
    if (strcmp(sched_pro, "RMS") == 0) {
        sched_RMS(threads, threadNum, iterCount);
    }
    else if (strcmp(sched_pro, "FCFS") == 0) {
        sched_FCFS(threads, threadNum, iterCount);
    }
    else if (strcmp(sched_pro, "HPF") == 0) {
        sched_HPF(threads, threadNum, iterCount);
    }
    else if (strcmp(sched_pro, "EDF") == 0) {
        sched_EDF(threads, threadNum, iterCount);
    }
    else {
        printf("No matching scheduling protocol, quit!\n");
    }
};