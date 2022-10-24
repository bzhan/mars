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

#define PI 3.14
#define G 9.8
#define true 1
#define false 0
#define abs fabs

static long long tm_to_ns(struct timespec tm) {
    return tm.tv_sec * 1000000000 + tm.tv_nsec;
}

static struct timespec ns_to_tm(long long ns) {
    struct timespec tm;
    tm.tv_sec = ns / 1000000000 ;
    tm.tv_nsec = ns - (tm.tv_sec * 1000000000);
    return tm;
}


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
    double* addr;
}
ListNum;

typedef struct {
    int length;
    intptr_t* addr;
}
List;

String* strInit(char* input) {
    String* new_str = (String*)malloc(sizeof(String));
    new_str->length = strlen(input) + 1;
    new_str->str = (char*)malloc(sizeof(char) * new_str->length);
    new_str->str = strcpy(new_str->str, input);
    return new_str;
}

void strCopy(String* dst, String* src) {
    dst->length = src->length;
    dst->str = (char*)malloc(sizeof(char) * dst->length);
    dst->str = strcpy(dst->str, src->str);
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
    intptr_t* new_list = (intptr_t*)malloc(sizeof(intptr_t) * src->length);
    if (src->length > 0) {
        memcpy(new_list, src->addr, (src->length) * sizeof(intptr_t));
    }
    dst->addr = new_list;
}

void listPush(List* list, intptr_t input) {
    intptr_t* new_list = (intptr_t*)malloc(sizeof(intptr_t) * (list->length + 1));
    if (list->length > 0) {
        memcpy(new_list, list->addr, (list->length) * sizeof(intptr_t));
    }
    memcpy(new_list + list->length, &input, sizeof(intptr_t));
    free(list->addr);
    list->addr = new_list;
    list->length += 1;
}

void listPop(List* list) {
    if (list->length > 0) {
        intptr_t* new_list = (intptr_t*)malloc(sizeof(intptr_t) * (list->length - 1));
        memcpy(new_list, list->addr + 1, (list->length - 1) * sizeof(intptr_t));
        free(list->addr);
        list->addr = new_list;
        list->length -= 1;
    }    
}

intptr_t listBottom(List* list) {
    return *(intptr_t*)(list->addr + list->length - 1);
}

intptr_t listTop(List* list) {
    return *(intptr_t*)(list->addr);
}

intptr_t listGet(List* list, int num) {
    return *(intptr_t*)(list->addr + num);
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
int STATE_WAITING = -4;
int STATE_WAITING_AVAILABLE = -3;
int STATE_UNAVAILABLE = -2;
int STATE_AVAILABLE = -1;

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

// Local clocks for each thread
double* localTime;

// Return value for exit
int retVal;


void updateCurrentTime(int thread) {
    // Update global clock to be minimum of all local clocks
    double minLocal = DBL_MAX;
    for (int i = 0; i < numThread; i++) {
        if (threadState[i] != STATE_AVAILABLE && localTime[i] < minLocal) {
            minLocal = localTime[i];
        }
    }

    if (minLocal == DBL_MAX) {
        printf("deadlock\n");
        exit(0);
    }

    currentTime = minLocal;

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

void init(int threadNumber, int channelNumber) {
    // Allocate thread and channel states.
    numThread = threadNumber;
    threadState = (int*) malloc(threadNumber * sizeof(int));
    threadNums = (int*) malloc(threadNumber * sizeof(int));
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
        pthread_cond_init(&cond[i], NULL);

    }
    for (int i = 0; i < channelNumber; i++) {
        channelInput[i] = -1;
        channelOutput[i] = -1;
    }

    currentTime = 0.0;
    localTime = (double*) malloc(threadNumber * sizeof(double*));
    for (int i = 0; i < threadNumber; i++) {
        localTime[i] = 0.0;
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
        if (channelTypes[ch.channelNo] == 1) {
            *((double*) ch.pos) = *((double*) channelContent[ch.channelNo]);
            printf("IO %s %.3f\n", channelNames[ch.channelNo], *((double*) ch.pos));
        } else if (channelTypes[ch.channelNo] == 2) {
            strCopy(((String*) ch.pos), ((String*) channelContent[ch.channelNo]));
            printf("IO %s %s\n", channelNames[ch.channelNo], ((String*) ch.pos) -> str);
        } else if (channelTypes[ch.channelNo] == 3) {
            listCopy(((List*) ch.pos), ((List*) channelContent[ch.channelNo]));
            printf("IO %s", channelNames[ch.channelNo]);
            for (int i = 0; i < ((List*) ch.pos) -> length; i++) {
                printf(" %3f", *((double *)(((List*) ch.pos) -> addr + i)));
            }
            printf("\n");
        } else {
            ;
        }

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
        updateCurrentTime(thread);
        pthread_cond_wait(&cond[thread], &mutex);

        // Copy data from channelContent
        if (channelTypes[ch.channelNo] == 1) {
            *((double*) ch.pos) = *((double*) channelContent[ch.channelNo]);
            printf("IO %s %.3f\n", channelNames[ch.channelNo], *((double*) ch.pos));
        } else if (channelTypes[ch.channelNo] == 2) {
            strCopy(((String*) ch.pos), ((String*) channelContent[ch.channelNo]));
            printf("IO %s %s\n", channelNames[ch.channelNo], ((String*) ch.pos) -> str);
        } else if (channelTypes[ch.channelNo] == 3) {
            listCopy(((List*) ch.pos), ((List*) channelContent[ch.channelNo]));
            printf("IO %s", channelNames[ch.channelNo]);
            for (int i = 0; i < ((List*) ch.pos) -> length; i++) {
                printf(" %3f", *((double*)(((List*) ch.pos) -> addr + i)));
            }
            printf("\n");
        } else {
            printf("Error channel type: %d", channelTypes[ch.channelNo]);
        }

        // Update local time
        if (localTime[thread] < localTime[channelOutput[ch.channelNo]]) {
            localTime[thread] = localTime[channelOutput[ch.channelNo]];
        }
        threadState[thread] = STATE_UNAVAILABLE;
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

    if (channelTypes[ch.channelNo] == 1) {
        *((double*) channelContent[ch.channelNo]) = *((double*) ch.pos);
    } else if (channelTypes[ch.channelNo] == 2) {
        strCopy(((String*) channelContent[ch.channelNo]), ((String*) ch.pos));
    } else if (channelTypes[ch.channelNo] == 3) {
        listCopy(((List*) channelContent[ch.channelNo]), ((List*) ch.pos));
    } else {
        ;
    }

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
        updateCurrentTime(thread);
        pthread_cond_wait(&cond[thread], &mutex);

        // Update local time
        if (localTime[thread] < localTime[channelInput[ch.channelNo]]) {
            localTime[thread] = localTime[channelInput[ch.channelNo]];
        }
        threadState[thread] = STATE_UNAVAILABLE;
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
                *((double*) chs[i].pos) = *((double*) channelContent[curChannel]);
                printf("IO %s %.3f\n", channelNames[curChannel], *((double*) chs[i].pos));

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
            *((double*) channelContent[curChannel]) = *((double*) chs[i].pos);
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
    updateCurrentTime(thread);
    pthread_cond_wait(&cond[thread], &mutex);

    // At this point, already found a match.
    int match_index = threadState[thread];
    assert (match_index >= 0);
    curChannel = chs[match_index].channelNo;

    if (chs[match_index].type == 0) {
        // Waiting results in input
        *((double*) chs[match_index].pos) = *((double*) channelContent[curChannel]);
        printf("IO %s %.3f\n", channelNames[curChannel], *((double*) chs[match_index].pos));

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
            *((double*) channelContent[curChannel]) = *((double*) chs[i].pos);
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
            *((double*) channelContent[curChannel]) = *((double*) chs[i].pos);
        }
    }

    // Increment local clock
    localTime[thread] += seconds;
    if (localTime[thread] > 10.0) {
        exit(0);
    }

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
    curChannel = chs[match_index].channelNo;

    if (chs[match_index].type == 0) {
        // Waiting results in input
        *((double*) chs[match_index].pos) = *((double*) channelContent[curChannel]);
        printf("IO %s %.3f\n", channelNames[curChannel], *((double*) chs[match_index].pos));

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