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
extern int SIMULATE_REAL_TIME;

#define PI 3.1415926
#define G 9.8
#define true 1
#define false 0
#define abs fabs

int equalInLimit(double a, double b);

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

String* strInit(char* input);

void strCopy(String* dst, String* src);

int strEqual(String a, String b);

void strDestroy(String** input);

List* listInit();

void listCopy(List* dst, List* src);

List* listPush(List* list, void* input, int type);

List* listPushExpr(List* list, double input);

List* listPop(List* list);

List* listPopBack(List* list);

void* listBottom(List* list);

void* listTop(List* list);

void* listGet(List* list, int num);

List* listDel(List* list, int num);

void* listGetMax(List* list);

void* listGetMaxList(List* list);

List* listDel0(List* list, void* input, int type);

// Global lock on the thread and channel states.
extern pthread_mutex_t mutex;

// Array of conditions, one of each thread.
extern pthread_cond_t* cond;

// Number of threads.
extern int numThread;

// Array of thread state (one for each thread).
extern int* threadState;

// Thread states. Nonnegative integers mean communicating on channel i.
extern int STATE_STOPPED;
extern int STATE_WAITING;
extern int STATE_WAITING_AVAILABLE;
extern int STATE_UNAVAILABLE;
extern int STATE_AVAILABLE;

// Whether thread is permanently waiting for some communication.
extern int* threadPermWait;

// Index of each thread.
extern int* threadNums;

// Array of input tokens, one for each channel.
// For each channel, if a thread is waiting to input on that channel, this is
// index of that thread. Otherwise -1.
extern int* channelInput;

// Array of output tokens, one for each channel.
// For each channel, if a thread is waiting to output on that channel, this is
// index of that thread. Otherwise -1.
extern int* channelOutput;

// Array of addresses of channel values, one for each channel.
extern void** channelContent;

// Channel names
extern char** channelNames;

// Channel types, 0 -> undef, 1 -> double, 2 -> string, 3 -> list
extern int* channelTypes;

// Maximum time of simulation
extern double maxTime;

// Current global clock
extern double currentTime;

// Previous global clock when output
extern double prevTime;

// Starting system time in nanoseconds
extern struct timespec start_tm;
extern struct timespec current_tm;

// Local clocks for each thread
extern double* localTime;

// Last recorded clocks for each thread
extern double* recordTime;

// Return value for exit
extern int retVal;


void updateCurrentTime(int thread);

void delay(int thread, double seconds);

// I introduced this function to test ODE without communication, 
// but the output of this function confilicts with that of input,
// so it is not used now.
void recordAndPrintTime(int thread);

void copyByType(void* dst, void* src, int type);

void init(int threadNumber, int channelNumber);

void run(int threadNumber, int channelNumber, void*(**threadFuns)(void*));

void destroy(int threadNumber, int channelNumber);

void copyFromChannel(Channel ch);

void copyToChannel(Channel ch);

// ch?x:
// ch must be an input channel
void input(int thread, Channel ch);

// ch!e
// ch must be an output channel
void output(int thread, Channel ch);

/*
 * External choice
 *
 * thread: current thread
 * nums: number of channels to wait for
 * chs: array of input/output channels.
 */
int externalChoice(int thread, int nums, Channel* chs);

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
void interruptInit(int thread, int nums, Channel* chs);

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
int interruptPoll(int thread, double seconds, int nums, Channel* chs);

/*
 * Interrupt: stop waiting for communications
 * 
 * thread: current thread
 * nums: number of channels to wait for
 * chs: array of input/output channels
 */
void interruptClear(int thread, int nums, Channel* chs);

double randomDouble01 ();

double randomInt ();

double randomInterval (double left, double right);

double randomDouble ();

int getIChoice();

double min(int n, ...);

double max(int n, ...);

#endif /* hcsp2c_h */