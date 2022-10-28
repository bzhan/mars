#ifndef hcsp2c_h
#define hcsp2c_h

#include <unistd.h>
#include <math.h>
#include <time.h>
#include <float.h>
#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <assert.h>
#include <stdarg.h>
#include <string.h>

// 1 for real-time simulation, 0 for as-fast-as-possible.
int SIMULATE_REAL_TIME = 0;

#define PI 3.14
#define G 9.8
#define true 1
#define false 0
#define abs fabs

static long long tm_to_ns(struct timespec tm) {
    return tm.tv_sec * 1000000000 + tm.tv_nsec;
}

void copyByType(void* dst, void* src, int type);

// type: 0 -> input, 1 -> output
typedef struct {
    int type; 
    int channelNo;
    void* pos;
}
Channel;

typedef struct {
    int length;
    char* str;
}
String;

typedef struct {
    int length;
    void** addr;
}
List;

String* strInit(char* input) {
    String* new_str = (String*)malloc(sizeof(String));
    new_str->length = strlen(input) + 1;
    new_str->str = (char*)malloc(sizeof(char) * new_str->length);
    strcpy(new_str->str, input);
    return new_str;
}

void strCopy(String* dst, String* src) {
    dst->length = src->length;
    dst->str = (char*)malloc(sizeof(char) * dst->length);
    strcpy(dst->str, src->str);
}

int strEqual(String a, String b) {
    if (a.length != b.length) {
        return 0;
    }
    if (strcmp((char*)a.str, (char*)b.str) != 0) {
        return 0;
    }
    return 1;
}

void strDestroy(String** input) {
    free((*input)->str);
    free(*input);
    return;
}

List* listInit() {
    List* list = (List*)malloc(sizeof(List));
    list->length = 0;
    list->addr = NULL;
    return list;
}

void listCopy(List* dst, List* src) {
    assert(dst->length >= src->length);
    dst->length = src->length;
    void** new_list = (void**)malloc(sizeof(void*) * src->length);
    if (src->length > 0) {
        memcpy(new_list, src->addr, (src->length) * sizeof(void*));
    }
    dst->addr = new_list;
}

List* listPush(List* list, void* input, int type) {
    void** new_list = (void**)malloc(sizeof(void*) * (list->length + 1));
    if (list->length > 0) {
        memcpy(new_list, list->addr, (list->length) * sizeof(void*));
    }   

    if (type == 1) {
        new_list[(list->length)] = malloc(sizeof(double));
    } else if (type == 2) {
        new_list[(list->length)] = malloc(sizeof(String));
    } else if (type == 3) {
        new_list[(list->length)] = malloc(sizeof(List));
    } else {
        printf("Pop ERROR: type doesn't match.");
    }
    
    copyByType((new_list[(list->length)]), input, type);
    free(list->addr);
    list->addr = new_list;
    list->length += 1;
    return list;
}

List* listPushExpr(List* list, double input) {
    void** new_list = (void**)malloc(sizeof(void*) * (list->length + 1));
    if (list->length > 0) {
        memcpy(new_list, list->addr, (list->length) * sizeof(void*));
    }
    new_list[(list->length)] = malloc(sizeof(double));
    *((double*)new_list[(list->length)]) = input;
    free(list->addr);
    list->addr = new_list;
    list->length += 1;
    return list;
}

List* listPop(List* list) {
    if (list->length > 0) {
        void** new_list = (void**)malloc(sizeof(void*) * (list->length - 1));
        memcpy(new_list, list->addr, (list->length - 1) * sizeof(void*));
        free(list->addr);
        list->addr = new_list;
        list->length -= 1;
    } else if (list->length == 0) {
        printf("Pop ERROR: list is empty");
    }
    return list;
}

void* listBottom(List* list) {
    if (list->length == 0) {
        printf("Bottom ERROR: list is empty");
    }
    return *(void**)(list->addr);
}

void* listTop(List* list) {
    if (list->length == 0) {
        printf("Top ERROR: list is empty");
    }
    return *(void**)(list->addr + list->length - 1);
}

void* listGet(List* list, int num) {
    if (list->length <= num) {
        printf("Get ERROR: length of list is %d, but try to get index %d.\n", list->length, num);
    }
    return *(void**)(list->addr + num);
}

// Global lock on the thread and channel states.
pthread_mutex_t mutex;

// Array of conditions, one of each thread.
pthread_cond_t* cond;

// Number of threads.
int numThread;

// Array of thread state (one for each thread).
int* threadState;

// Thread states. Nonnegative integers mean communicating on channel i.
int STATE_STOPPED = -5;
int STATE_WAITING = -4;
int STATE_WAITING_AVAILABLE = -3;
int STATE_UNAVAILABLE = -2;
int STATE_AVAILABLE = -1;

// Whether thread is permanently waiting for some communication.
int* threadPermWait;

// Index of each thread.
int* threadNums;

// Array of input tokens, one for each channel.
// For each channel, if a thread is waiting to input on that channel, this is
// index of that thread. Otherwise -1.
int* channelInput;

// Array of output tokens, one for each channel.
// For each channel, if a thread is waiting to output on that channel, this is
// index of that thread. Otherwise -1.
int* channelOutput;

// Array of addresses of channel values, one for each channel.
void** channelContent;

// Channel names
char** channelNames;

// Channel types, 0 -> undef, 1 -> double, 2 -> string, 3 -> list
int* channelTypes;

// Maximum time of simulation
double maxTime;

// Current global clock
double currentTime;

// Previous global clock when output
double prevTime;

// Starting system time in nanoseconds
struct timespec start_tm;
struct timespec current_tm;

// Local clocks for each thread
double* localTime;

// Last recorded clocks for each thread
double* recordTime;

// Return value for exit
int retVal;


void updateCurrentTime(int thread) {
    // Update global clock to be minimum of all local clocks
    double minLocal = DBL_MAX;
    for (int i = 0; i < numThread; i++) {
        if (threadPermWait[i] == 0 && threadState[i] != STATE_STOPPED && localTime[i] < minLocal) {
            minLocal = localTime[i];
        }
    }

    if (minLocal == DBL_MAX) {
        printf("deadlock\n");
        exit(0);
    }

    if (currentTime < minLocal) {
        currentTime = minLocal;
        if (SIMULATE_REAL_TIME) {
            clock_gettime(CLOCK_REALTIME, &current_tm);
            long long systemDiff = tm_to_ns(current_tm) - tm_to_ns(start_tm);
            long long logicalDiff = (long long) (currentTime * 1000000000.0);
            if (logicalDiff - systemDiff > 1000000) {
                usleep(logicalDiff - systemDiff);
            }
        }
    }

    // If new global clock exceeds maximum simulation time, stop the program
    if (currentTime > maxTime) {
        exit(0);
    }

    // If new global clock equals time of some local thread,
    // wake up that local thread
    for (int i = 0; i < numThread; i++) {
        if (i != thread && localTime[i] == currentTime && threadState[i] == STATE_WAITING) {
            threadState[i] = STATE_UNAVAILABLE;
            pthread_cond_signal(&cond[i]);
        }
        if (i != thread && localTime[i] == currentTime && threadState[i] == STATE_WAITING_AVAILABLE) {
            threadState[i] = STATE_AVAILABLE;
            pthread_cond_signal(&cond[i]);
        }
    }
}

void delay(int thread, double seconds) {
    // Take the global lock
    pthread_mutex_lock(&mutex);

    // Increment local clock
    localTime[thread] += seconds;

    updateCurrentTime(thread);

    // If local clock is greater than global clock, go into wait mode
    if (localTime[thread] > currentTime) {
        threadState[thread] = STATE_WAITING;
        pthread_cond_wait(&cond[thread], &mutex);
    }

    pthread_mutex_unlock(&mutex);
}

// I introduced this function to test ODE without communication, 
// but the output of this function confilicts with that of input,
// so it is not used now.
void recordAndPrintTime(int thread) {
    printf("delay %.3f\n", localTime[thread] - recordTime[thread]);
    recordTime[thread] = localTime[thread];
}

void copyByType(void* dst, void* src, int type) {
    if (type == 1) {
        *((double*) dst) = *((double*) src);
    } else if (type == 2) {
        strCopy(((String*) dst), ((String*) src));
    } else if (type == 3) {
        listCopy(((List*) dst), ((List*) src));
    } else if (type == 0) {
    } else {
        printf("copy error: type = %d", type);
    }
}

void init(int threadNumber, int channelNumber) {
    // Allocate thread and channel states.
    numThread = threadNumber;
    threadState = (int*) malloc(threadNumber * sizeof(int));
    threadNums = (int*) malloc(threadNumber * sizeof(int));
    threadPermWait = (int*) malloc(threadNumber * sizeof(int));
    cond = (pthread_cond_t*) malloc(threadNumber * sizeof(pthread_cond_t));
    channelInput = (int*) malloc(channelNumber * sizeof(int));
    channelOutput = (int*) malloc(channelNumber * sizeof(int));
    channelContent = (void**) malloc(channelNumber * sizeof(void*));
    channelNames = (char**) malloc(channelNumber * sizeof(char*));
    channelTypes = (int*) malloc(channelNumber * sizeof(int));

    // Initialize thread and channel states.
    pthread_mutex_init(&mutex, NULL);
    for (int i = 0; i < threadNumber; i++) {
        threadState[i] = STATE_UNAVAILABLE;
        threadNums[i] = i;
        threadPermWait[i] = 0;
        pthread_cond_init(&cond[i], NULL);

    }
    for (int i = 0; i < channelNumber; i++) {
        channelInput[i] = -1;
        channelOutput[i] = -1;
    }

    currentTime = 0.0;
    prevTime = 0.0;
    clock_gettime(CLOCK_REALTIME, &start_tm);
    localTime = (double*) malloc(threadNumber * sizeof(double*));
    recordTime = (double*) malloc(threadNumber * sizeof(double*));
    for (int i = 0; i < threadNumber; i++) {
        localTime[i] = 0.0;
        recordTime[i] = 0.0;
    }
}

void run(int threadNumber, int channelNumber, void*(**threadFuns)(void*)) {
    // Allocate each channel content
    for (int i = 0; i < channelNumber; i++) {
        if (channelTypes[i] == 1) {
            channelContent[i] = (void*) malloc(1 * sizeof(double));
        } else if (channelTypes[i] == 2) {
            channelContent[i] = (void*) malloc(1 * sizeof(String));
        } else if (channelTypes[i] == 3) {
            channelContent[i] = (void*) malloc(1 * sizeof(List));
        } else if (channelTypes[i] == 0) {
            channelContent[i] = (void*) malloc(1 * sizeof(double));
        } else {
            printf("Failed init for error channel type: %s %d", channelNames[i], channelTypes[i]);
        }
    }

    // Create each thread
    pthread_t threads[threadNumber];
    for (int i = 0; i < threadNumber; i++) {
        assert(pthread_create(&threads[i], NULL, threadFuns[i], &threadNums[i]) == 0);
    }

    // Wait for each thread to finish
    void *status;
    for (int i = 0; i < threadNumber; i++) {
        pthread_join(threads[i], &status);
    }
}

void destroy(int threadNumber, int channelNumber) {
    // Release thread and channel states.
    pthread_mutex_destroy(&mutex);
    for (int i = 0; i < threadNumber; i++) {
        pthread_cond_destroy(&cond[i]);
    }
    free(threadState);
    free(threadNums);
    free(cond);
    free(channelInput);
    free(channelOutput);
    free(channelContent);
}

void copyFromChannel(Channel ch) {
    if (currentTime - prevTime > 1e-3) {
        printf("delay %.3f\n", currentTime - prevTime);
        prevTime = currentTime;
    }

    // Copy data from channelContent
    copyByType(ch.pos, channelContent[ch.channelNo], channelTypes[ch.channelNo]);
    if (channelTypes[ch.channelNo] == 1) {
        printf("IO %s %.3f\n", channelNames[ch.channelNo], *((double*) ch.pos));
    } else if (channelTypes[ch.channelNo] == 2) {
        printf("IO %s \"%s\"\n", channelNames[ch.channelNo], ((String*) ch.pos) -> str);
    } else if (channelTypes[ch.channelNo] == 3) {
        printf("IO %s", channelNames[ch.channelNo]);
        for (int i = 0; i < ((List*) ch.pos) -> length; i++) {
            printf(" %3f", *((double *)(((List*) ch.pos) -> addr + i)));
        }
        printf("\n");
    } else if (channelTypes[ch.channelNo] == 0) {
        printf("IO %s\n", channelNames[ch.channelNo]);
    } else {
        ;
    }
}

void copyToChannel(Channel ch) {
    copyByType(channelContent[ch.channelNo], ch.pos, channelTypes[ch.channelNo]);
}

// ch?x:
// ch must be an input channel
void input(int thread, Channel ch) {
    // Take the global lock, and set the channelInput state.
    pthread_mutex_lock(&mutex);
    channelInput[ch.channelNo] = thread;

    if (channelOutput[ch.channelNo] != -1 &&
            (threadState[channelOutput[ch.channelNo]] == STATE_AVAILABLE ||
             threadState[channelOutput[ch.channelNo]] == STATE_WAITING_AVAILABLE)) {
        // If output is available, signal the output side
        threadState[channelOutput[ch.channelNo]] = ch.channelNo;

        // Copy data from channelContent
        copyFromChannel(ch);

        // Update local time
        if (localTime[thread] < localTime[channelOutput[ch.channelNo]]) {
            localTime[thread] = localTime[channelOutput[ch.channelNo]];
        }

        pthread_cond_signal(&cond[channelOutput[ch.channelNo]]);
        pthread_cond_wait(&cond[thread], &mutex);
        threadState[thread] = STATE_UNAVAILABLE;
        channelInput[ch.channelNo] = -1;
    } else {
        // Otherwise, wait for the output
        threadState[thread] = STATE_AVAILABLE;
        threadPermWait[thread] = 1;
        updateCurrentTime(thread);
        pthread_cond_wait(&cond[thread], &mutex);

        // Copy data from channelContent
        copyFromChannel(ch);

        // Update local time
        if (localTime[thread] < localTime[channelOutput[ch.channelNo]]) {
            localTime[thread] = localTime[channelOutput[ch.channelNo]];
        }
        threadState[thread] = STATE_UNAVAILABLE;
        threadPermWait[thread] = 0;
        channelInput[ch.channelNo] = -1;
        pthread_cond_signal(&cond[channelOutput[ch.channelNo]]);
    }

    pthread_mutex_unlock(&mutex);
}

// ch!e
// ch must be an output channel
void output(int thread, Channel ch) {
    // Take the global lock, set the channelOutput state and channel content.
    pthread_mutex_lock(&mutex);
    channelOutput[ch.channelNo] = thread;

    // Copy data to channel
    copyToChannel(ch);

    if (channelInput[ch.channelNo] != -1 &&
            (threadState[channelInput[ch.channelNo]] == STATE_AVAILABLE ||
             threadState[channelInput[ch.channelNo]] == STATE_WAITING_AVAILABLE)) {
        // If input is available, signal the input side
        threadState[channelInput[ch.channelNo]] = ch.channelNo;

        // Update local time
        if (localTime[thread] < localTime[channelInput[ch.channelNo]]) {
            localTime[thread] = localTime[channelInput[ch.channelNo]];
        }

        pthread_cond_signal(&cond[channelInput[ch.channelNo]]);
        pthread_cond_wait(&cond[thread], &mutex);
        threadState[thread] = STATE_UNAVAILABLE;
        channelOutput[ch.channelNo] = -1;
    } else {
        // Otherwise, wait for the input
        threadState[thread] = STATE_AVAILABLE;
        threadPermWait[thread] = 1;
        updateCurrentTime(thread);
        pthread_cond_wait(&cond[thread], &mutex);

        // Update local time
        if (localTime[thread] < localTime[channelInput[ch.channelNo]]) {
            localTime[thread] = localTime[channelInput[ch.channelNo]];
        }
        threadState[thread] = STATE_UNAVAILABLE;
        threadPermWait[thread] = 0;
        channelOutput[ch.channelNo] = -1;
        pthread_cond_signal(&cond[channelInput[ch.channelNo]]);
    }

    pthread_mutex_unlock(&mutex);
}

/*
 * External choice
 *
 * thread: current thread
 * nums: number of channels to wait for
 * chs: array of input/output channels.
 */
int externalChoice(int thread, int nums, Channel* chs) {
    // Take the global lock
    pthread_mutex_lock(&mutex);

    int curChannel;

    for (int i = 0; i < nums; i++) {
        curChannel = chs[i].channelNo;
        if (chs[i].type == 0) {
            // If channel is for input
            channelInput[curChannel] = thread;
            if (channelOutput[curChannel] != -1 &&
                    (threadState[channelOutput[curChannel]] == STATE_AVAILABLE ||
                     threadState[channelOutput[curChannel]] == STATE_WAITING_AVAILABLE)) {
                // If output is available, signal to the output side
                threadState[channelOutput[curChannel]] = curChannel;

                // Copy data from channelContent
                copyFromChannel(chs[i]);

                // Update local time
                if (localTime[thread] < localTime[channelOutput[curChannel]]) {
                    localTime[thread] = localTime[channelOutput[curChannel]];
                }

                pthread_cond_signal(&cond[channelOutput[curChannel]]);
                pthread_cond_wait(&cond[thread], &mutex);
                threadState[thread] = STATE_UNAVAILABLE;
                for (int j = 0; j <= i; j++) {
                    if (chs[j].type == 0) {
                        channelInput[chs[j].channelNo] = -1;
                    } else {
                        channelOutput[chs[j].channelNo] = -1;
                    }
                }
                pthread_mutex_unlock(&mutex);  
                return i;
            }
        } else {
            // If channel is for output
            channelOutput[curChannel] = thread;

            // Copy data to channel
            copyToChannel(chs[i]);

            if (channelInput[curChannel] != -1 &&
                    (threadState[channelInput[curChannel]] == STATE_AVAILABLE ||
                     threadState[channelInput[curChannel]] == STATE_WAITING_AVAILABLE)) {
                // If input is available, signal to the input side
                threadState[channelInput[curChannel]] = curChannel;

                // Update local time
                if (localTime[thread] < localTime[channelInput[curChannel]]) {
                    localTime[thread] = localTime[channelInput[curChannel]];
                }

                pthread_cond_signal(&cond[channelInput[curChannel]]);
                pthread_cond_wait(&cond[thread], &mutex);
                threadState[thread] = STATE_UNAVAILABLE;
                for (int j = 0; j <= i; j++) {
                    if (chs[j].type == 0) {
                        channelInput[chs[j].channelNo] = -1;
                    } else {
                        channelOutput[chs[j].channelNo] = -1;
                    }
                }
                pthread_mutex_unlock(&mutex);  
                return i;
            }
        }
    }

    // If no matching channel is found, wait for matches.
    threadState[thread] = STATE_AVAILABLE;
    threadPermWait[thread] = 1;
    updateCurrentTime(thread);
    pthread_cond_wait(&cond[thread], &mutex);

    // At this point, already found a match.
    int match_index = threadState[thread];
    assert (match_index >= 0);
    curChannel = match_index;
    for (int j = 0; j < nums; j++) {
        if (chs[j].channelNo == match_index) {
            match_index = j;
            break;
        }
    }

    if (chs[match_index].type == 0) {
        // Waiting results in input
        copyFromChannel(chs[match_index]);

        // Update local time
        if (localTime[thread] < localTime[channelOutput[curChannel]]) {
            localTime[thread] = localTime[channelOutput[curChannel]];
        }
        threadState[thread] = STATE_UNAVAILABLE;
        threadPermWait[thread] = 0;
        for (int j = 0; j < nums; j++) {
            if (chs[j].type == 0) {
                channelInput[chs[j].channelNo] = -1;
            } else {
                channelOutput[chs[j].channelNo] = -1;
            }
        }
        pthread_cond_signal(&cond[channelOutput[curChannel]]);
    } else {
        // Waiting results in output

        // Update local time
        if (localTime[thread] < localTime[channelInput[curChannel]]) {
            localTime[thread] = localTime[channelInput[curChannel]];
        }
        threadState[thread] = STATE_UNAVAILABLE;
        threadPermWait[thread] = 0;
        for (int j = 0; j < nums; j++) {
            if (chs[j].type == 0) {
                channelInput[chs[j].channelNo] = -1;
            } else {
                channelOutput[chs[j].channelNo] = -1;
            }
        }
        pthread_cond_signal(&cond[channelInput[curChannel]]);
    }

    pthread_mutex_unlock(&mutex);  
    return match_index;
}

/*
 * Interrupt: initialization
 *
 * This function initializes channelInput and channelOutput, to indicate
 * that the current thread is ready.
 *
 * thread: current thread
 * nums: number of channels to wait for
 * chs: array of input/output channels
 */
void interruptInit(int thread, int nums, Channel* chs) {
    // Take the global lock
    pthread_mutex_lock(&mutex);

    int curChannel;

    for (int i = 0; i < nums; i++) {
        curChannel = chs[i].channelNo;
        if (chs[i].type == 0) {
            channelInput[curChannel] = thread;
        } else {
            channelOutput[curChannel] = thread;
            copyToChannel(chs[i]);
        }
    }

    threadState[thread] = STATE_AVAILABLE;
    pthread_mutex_unlock(&mutex);
    return;
}

/*
 * Interrupt: delay and wait for the given communications
 *
 * thread: current thread
 * seconds: number of seconds to wait
 * nums: number of channels to wait for
 * chs: array of input/output channels
 *
 * Return -1 if waiting finished without a communication, and index of
 * communication otherwise.
 */
int interruptPoll(int thread, double seconds, int nums, Channel* chs) {
    // Take the global lock
    pthread_mutex_lock(&mutex);

    // Update output values
    int curChannel;

    for (int i = 0; i < nums; i++) {
        curChannel = chs[i].channelNo;
        if (chs[i].type == 0) {
            ;
        } else {
            copyToChannel(chs[i]);
        }
    }

    // Increment local clock
    localTime[thread] += seconds;

    updateCurrentTime(thread);

    // If local clock is greater than global clock, go into wait mode
    if (localTime[thread] > currentTime) {
        threadState[thread] = STATE_WAITING_AVAILABLE;
        pthread_cond_wait(&cond[thread], &mutex);
    }

    // Wake up from waiting is due to one of two reasons: the waiting time
    // is over, or there is a communication ready. This is distinguished by
    // threadState.

    if (threadState[thread] == STATE_AVAILABLE) {
        pthread_mutex_unlock(&mutex);
        return -1;
    }

    // At this point, already found a match.
    int match_index = threadState[thread];
    assert (match_index >= 0);
    curChannel = match_index;
    for (int j = 0; j < nums; j++) {
        if (chs[j].channelNo == match_index) {
            match_index = j;
            break;
        }
    }

    if (chs[match_index].type == 0) {
        // Waiting results in input
        copyFromChannel(chs[match_index]);

        // Update local time
        if (localTime[thread] < localTime[channelOutput[curChannel]]) {
            localTime[thread] = localTime[channelOutput[curChannel]];
        }
        threadState[thread] = STATE_UNAVAILABLE;
        for (int j = 0; j < nums; j++) {
            if (chs[j].type == 0) {
                channelInput[chs[j].channelNo] = -1;
            } else {
                channelOutput[chs[j].channelNo] = -1;
            }
        }
        pthread_cond_signal(&cond[channelOutput[curChannel]]);
    } else {
        // Waiting results in output

        // Update local time
        if (localTime[thread] < localTime[channelInput[curChannel]]) {
            localTime[thread] = localTime[channelInput[curChannel]];
        }
        threadState[thread] = STATE_UNAVAILABLE;
        for (int j = 0; j < nums; j++) {
            if (chs[j].type == 0) {
                channelInput[chs[j].channelNo] = -1;
            } else {
                channelOutput[chs[j].channelNo] = -1;
            }
        }
        pthread_cond_signal(&cond[channelInput[curChannel]]);
    }

    pthread_mutex_unlock(&mutex);  
    return match_index;
}

/*
 * Interrupt: stop waiting for communications
 * 
 * thread: current thread
 * nums: number of channels to wait for
 * chs: array of input/output channels
 */
void interruptClear(int thread, int nums, Channel* chs) {
    // Take the global lock
    pthread_mutex_lock(&mutex);

    threadState[thread] = STATE_UNAVAILABLE;
    for (int j = 0; j < nums; j++) {
        if (chs[j].type == 0) {
            channelInput[chs[j].channelNo] = -1;
        } else {
            channelOutput[chs[j].channelNo] = -1;
        }
    }

    pthread_mutex_unlock(&mutex);
    return;
}

double randomDouble01 () {
    int ans = rand();
    return (double)rand()/(double)RAND_MAX;
}

double randomInt () {
    int symbol = rand() % 2;
    if (symbol) {
        return (double)rand();
    } else {
        return -(double)rand() - 1.0;
    }
}

double randomInterval (double left, double right) {
    assert(right >= left);
    double mid = randomDouble01();
    return mid * (right - left) + left;
}

double randomDouble () {
    return randomInt () + randomDouble01();
}

int getIChoice() {
    return rand() % 2;
}

double min(int n, ...) {
    va_list vap;
    double s = DBL_MAX;
    va_start(vap, n);
    for (int i = 0;i < n;i++) {
        double mid = va_arg(vap, double);
        if (mid < s) {
            s = mid;
        }
    }
    va_end(vap);
    return s;
}

double max(int n, ...) {
    va_list vap;
    double s = DBL_MIN;
    va_start(vap, n);
    for (int i = 0;i < n;i++) {
        double mid = va_arg(vap, double);
        if (mid > s) {
            s = mid;
        }
    }
    va_end(vap);
    return s;
}


#endif /* hcsp2c_h */