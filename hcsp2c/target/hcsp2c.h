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

#define PI 3.14
#define G 9.8
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

void delay(double seconds) {
  clock_t start = clock();
  while ((double)(clock() - start) < CLOCKS_PER_SEC * seconds);
}

// type: 0 -> input, 1 -> output
typedef struct {
    int type; 
    int channelNo;
    double* pos;
}
Channel;

// #define channelNumber 2
// #define threadNumbers 2

pthread_mutex_t mutex;
pthread_cond_t* cond;

// -2 -> unavailable, -1 -> available, i -> comm in channel i

int* threadState;
int* threadNums;

int* channelInput;
int* channelOutput;
int* channelContent;

void init(int threadNumber, int channelNumber, void*(**threadFuns)(void*) ) {
    threadState = (int*)malloc(threadNumber * sizeof(int));
    threadNums = (int*)malloc(threadNumber * sizeof(int));
    cond = (pthread_cond_t*)malloc(threadNumber * sizeof(pthread_cond_t));
    channelInput = (int*)malloc(channelNumber * sizeof(int));
    channelOutput = (int*)malloc(channelNumber * sizeof(int));
    channelContent = (int*)malloc(channelNumber * sizeof(int));
    pthread_mutex_init(&mutex, NULL);
    for (int i = 0; i < threadNumber; i++) {
        threadState[i] = -2;
        threadNums[i] = i;
        pthread_cond_init(&cond[i], NULL);
    }
    for (int i = 0; i < channelNumber; i++) {
        channelInput[i] = -1;
        channelOutput[i] = -1;
    }

    pthread_t threads[threadNumber];
    for (int i = 0; i < threadNumber; i++) {
        assert(pthread_create(&threads[i], NULL, threadFuns[i], &threadNums[i]) == 0);
    }
    void *status;
    for (int i = 0; i < threadNumber; i++) {
        pthread_join(threads[i], &status);
    }

}


void destroy(int threadNumber, int channelNumber) {
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

// ch?x
void input(int thread, Channel ch) {
    pthread_mutex_lock(&mutex);
    channelInput[ch.channelNo] = thread;

    if (channelOutput[ch.channelNo] != -1 && threadState[channelOutput[ch.channelNo]] == -1) {
        threadState[channelOutput[ch.channelNo]] = ch.channelNo;
        pthread_cond_signal(&cond[channelOutput[ch.channelNo]]);
    } else {
        threadState[thread] = -1;
        pthread_cond_wait(&cond[thread], &mutex);
    }
    
    *(ch.pos) = channelContent[ch.channelNo];
    threadState[thread] = -2;
    channelInput[ch.channelNo] = -1;
    pthread_mutex_unlock(&mutex);
}

// ch!e
void output(int thread, Channel ch) {
    pthread_mutex_lock(&mutex);
    channelOutput[ch.channelNo] = thread;
    channelContent[ch.channelNo] = *(ch.pos);

    if (channelInput[ch.channelNo] != -1 && threadState[channelInput[ch.channelNo]] == -1) {
        threadState[channelInput[ch.channelNo]] = ch.channelNo;
        pthread_cond_signal(&cond[channelInput[ch.channelNo]]);
    } else {
        threadState[thread] = -1;
        pthread_cond_wait(&cond[thread], &mutex);
    }

    threadState[thread] = -2;
    channelOutput[ch.channelNo] = thread;
    pthread_mutex_unlock(&mutex);
}

// external choice
int externalChoice(int thread, int nums, Channel* chs) {
    pthread_mutex_lock(&mutex);
    int match_index = -1;
    for (int i = 0; i < nums; i++) {
        if (chs[i].type == 0) {
            channelInput[chs[i].channelNo] = thread;
            if (match_index == -1 && channelOutput[chs[i].channelNo] != -1 && threadState[channelOutput[chs[i].channelNo]] == -1) {
                threadState[channelOutput[chs[i].channelNo]] = chs[i].channelNo;
                match_index = chs[i].channelNo;
                pthread_cond_signal(&cond[channelOutput[chs[i].channelNo]]);
                break;
            }
        } else {
            channelOutput[chs[i].channelNo] = thread;
            channelContent[chs[i].channelNo] = *(chs[i].pos);
            if (match_index == -1 && channelInput[chs[i].channelNo] != -1 && threadState[channelInput[chs[i].channelNo]] == -1) {
                threadState[channelInput[chs[i].channelNo]] = chs[i].channelNo;
                match_index = chs[i].channelNo;
                pthread_cond_signal(&cond[channelInput[chs[i].channelNo]]);
                break;
            }
        }
    }
    if (match_index == -1) {
        threadState[thread] = -1;
        pthread_cond_wait(&cond[thread], &mutex);
        match_index = threadState[thread];
        // printf("match_index: %d \n", match_index); 
        // printf("thread: %d \n", thread); 
        // fflush(stdout);
    }
    assert (match_index >= 0);
    int ans = -1;
    for (int i = 0; i < nums; i++) {
        if (chs[i].type == 0) {
            channelInput[chs[i].channelNo] = -1;
            if (chs[i].channelNo == match_index) {
                *(chs[i].pos) = channelContent[chs[i].channelNo];
                ans = i;
            }
        } else {
            channelOutput[chs[i].channelNo] = -1;
            if (chs[i].channelNo == match_index) {
                ans = i;
            }
        }
    }
    threadState[thread] = -2;
    pthread_mutex_unlock(&mutex);  
    return ans;  
}

// external choice in ODE
int timedExternalChoice1(int thread, int nums, double waitTime, Channel* chs) {
    pthread_mutex_lock(&mutex);
    int match_index = -1;
    for (int i = 0; i < nums; i++) {
        if (chs[i].type == 0) {
            channelInput[chs[i].channelNo] = thread;
            if (match_index == -1 && channelOutput[chs[i].channelNo] != -1 && threadState[channelOutput[chs[i].channelNo]] == -1) {
                threadState[channelOutput[chs[i].channelNo]] = chs[i].channelNo;
                match_index = chs[i].channelNo;
                pthread_cond_signal(&cond[channelOutput[chs[i].channelNo]]);
                break;
            }
        } else {
            channelOutput[chs[i].channelNo] = thread;
            if (match_index == -1 && channelInput[chs[i].channelNo] != -1 && threadState[channelInput[chs[i].channelNo]] == -1) {
                threadState[channelInput[chs[i].channelNo]] = chs[i].channelNo;
                match_index = chs[i].channelNo;
                pthread_cond_signal(&cond[channelInput[chs[i].channelNo]]);
                break;
            }
        }
    }
    if (match_index == -1) {
        threadState[thread] = -1;
        struct timespec start_tm;
        struct timespec end_tm;
        double timeout = waitTime * 1000000000;
        clock_gettime(CLOCK_REALTIME, &start_tm);
        end_tm = ns_to_tm(tm_to_ns(start_tm) + (long long)timeout);
        pthread_cond_timedwait(&cond[thread], &mutex, &end_tm);
        match_index = threadState[thread];

        // printf("match_index: %d \n", match_index); 
        // printf("thread: %d \n", thread); 
        // fflush(stdout);
    }
    return match_index;
}

int timedExternalChoice2(int thread, int nums, int match_index, Channel* chs) {
    assert (match_index >= -1);
    int ans = -1;
    for (int i = 0; i < nums; i++) {
        if (chs[i].type == 0) {
            channelInput[chs[i].channelNo] = -1;
            if (chs[i].channelNo == match_index) {
                *(chs[i].pos) = channelContent[chs[i].channelNo];
                ans = i;
            }
        } else {
            channelOutput[chs[i].channelNo] = -1;
            if (chs[i].channelNo == match_index) {
                channelContent[chs[i].channelNo] = *(chs[i].pos);
                ans = i;
            }
        }
    }
    threadState[thread] = -2;
    pthread_mutex_unlock(&mutex);  
    return ans;
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