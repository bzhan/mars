//
//  main.c
//  Simulink2C
//
//  Created by Zsio Iung on 2021/3/29.
//  Copyright © 2021 Xiong Xu. All rights reserved.
//
#define BUF_SIZE 10
#define StepSize 1 // ms

#include<stdio.h>

#include "vehicle_imp.h"
#include "PI_ctr_imp.h"
#include "emerg_imp.h"
#include "comp_obs_pos_imp.h"
#include "pan_ctr_th_imp.h"
#include "velo_voter_imp.h"
#include "img_acq_imp.h"

// Global clock (s)
int globalClock = 0;

// Shared variables
float img = 0.0; // camera --> img_acq.imp
float proc_img = 0.0; // imp_acq.imp --> comp_obs_pos.imp
float obs_pos_radar = 0.0; // radar --> comp_obs_pos.imp
float obs_pos = 0.0; // comp_obs_pos.imp --> emerg_ctr.imp
float cmd = 0.0; // emerg_ctr.imp --> actuator
float veh_pos = 0.0; // GPS --> emerg_ctr.imp
float veh_v = 0.0; // velo_voter.imp --> emerg_ctr.imp
float des_a = 0.0; // PI_ctr_imp --> emerg_ctr.imp
float laser_valid = -1.0; // laser --> velo_voter.imp
float laser_v = 0.0; // laser --> velo_voter.imp
float wheel_valid = -1.0; // wheel --> velo_voter.imp
float wheel_v = 0.0; // wheel --> velo_voter.imp
float des_v = 0.0; // pan_ctr_th.imp --> PI_ctr.imp
float veh_a = 0.0; // actuator --> vehicle.imp
float veh_s = 0.0; // GPS --> vehicle.imp
float veh_l_v = 0.0; // vehicle.imp --> laser
float veh_w_v = 0.0; // vehicle.imp --> wheel

typedef struct {
  int front;
  int rear;
  char buffer[BUF_SIZE];
} Queue;

// Buffers for storing events
Queue dec_buffer = {0, 0}; // user_panel --> pan_ctr_th.imp
Queue inc_buffer = {0, 0}; // user_panel --> pan_ctr_th.imp

int isEmpty(Queue queue) {
  return queue.front == queue.rear;
}

void enqueue(Queue *queue, char event) {
  int new_rear = (queue->rear + 1) % BUF_SIZE;
  if (new_rear == queue->front)
    return;
  queue->buffer[queue->rear] = event;
  queue->rear = new_rear;
}

char dequeue(Queue *queue) {
  if (isEmpty(*queue))
    return -1;
  char head = queue->buffer[queue->front];
  queue->front = (queue->front + 1) % BUF_SIZE;
  return head;
}


float compute_value(float startT, float endT, float startV, float endV, float currT) {
  float slope = (startV - endV) / (startT - endT);
  return startV + slope * (currT - startT);
}

typedef struct {
  char *name;
  int period; // (ms)
  void (*produce_data) (void);
} Device;

// produce_data of camera
static void camera_data(void) {
  img = -1.0;
}

// produce_data of radar
static void radar_data(void) {
  if (globalClock < 6000)
    obs_pos_radar = 0.0;
  else if (globalClock < 10000)
    obs_pos_radar = compute_value(6000, 10000, 25, 30, globalClock);
  else if (globalClock < 14000)
    obs_pos_radar = 0.0;
  else
    obs_pos_radar = 45.0;
}

// produce_data of actuator
static void actuator_data(void) {
  veh_a = cmd;
}

// produce_data of GPS
static void gps_data(void) {
  veh_pos = veh_s;
}

// produce_data of laser
static void laser_data() {
  laser_valid = 1.0;
  laser_v = veh_l_v + 0.0;
}

// produce_data of wheel
static void wheel_data() {
  wheel_valid = 1.0;
  wheel_v = veh_w_v + 0.0;
}

// produce_data of user_panel
static void user_panel_event() {
  if (globalClock < 1) {
    for (int count = 0; count < 5; count++)
      enqueue(&inc_buffer, '+');
  }
  else if (globalClock >= 4000 && globalClock < 4001) {
    for (int count = 0; count < 2; count++)
      enqueue(&dec_buffer, '-');
  }
}

Device camera = {"camera", 200, camera_data};
Device radar = {"radar", 10, radar_data};
Device actuator = {"actuator", 2, actuator_data};
Device gps = {"gps", 6, gps_data};
Device laser = {"laser", 10, laser_data};
Device wheel = {"wheel", 10, wheel_data};
Device user_panel = {"user_panel", StepSize, user_panel_event};

typedef struct {
  int tid; /* The ID of a thread */
  int runClock; /* (ms) */
  int waitClock; /* (ms) */
  char *threadName; /*name of thread*/
  int period; /*time interval to be stimulated (ms)*/
  int priority; /*priority*/
  int deadline; /*No more than deadline (ms)*/
  char *state; /*seven state: inactive, ready, running */
  char *dispatch_protocol; /*periodic, aperiodic and et al.*/
  int minExecutionTime; /*min execution time (ms)*/
  int maxExecutionTime; /*max execution time (ms)*/
  
  void (*initialize) (void);
  void (*execute) (void);
  void (*finialize) (void);
} Thread;

void trig_pan_ctr_th() {
  char event;
  if (!isEmpty(inc_buffer)) {
    event = dequeue(&inc_buffer);
    pan_ctr_th_rtU.inc = 0 - pan_ctr_th_rtU.inc;
  }
  if (!isEmpty(dec_buffer)) {
    event = dequeue(&dec_buffer);
    pan_ctr_th_rtU.dec = 0 - pan_ctr_th_rtU.dec;
  }
}

Thread img_acq = {0, 0, 0, "img_acq", 50, 1, 50, "inactive", "periodic", 10, 40, img_acq_imp_initialize, img_acq_imp_step, img_acq_imp_finalize};
Thread comp_obs_pos = {1, 0, 0, "comp_obs_pos", 100, 1, 100, "inactive", "periodic", 20, 50, comp_obs_pos_imp_initialize, comp_obs_pos_imp_step, comp_obs_pos_imp_finalize};
Thread emerg = {2, 0, 0, "emerg", 5, 2, 5, "inactive", "periodic", 1, 1, emerg_imp_initialize, emerg_imp_step, emerg_imp_finalize};
Thread PI_ctr = {3, 0, 0, "PI_ctr", 5, 1, 5, "inactive", "periodic", 1, 1, PI_ctr_imp_initialize, PI_ctr_imp_step, PI_ctr_imp_finalize};
Thread velo_voter = {4, 0, 0, "velo_voter", 8, 1, 8, "inactive", "periodic", 1, 1, velo_voter_imp_initialize, velo_voter_imp_step, velo_voter_imp_finalize};
Thread pan_ctr_th = {5, 0, 0, "pan_ctr_th", -1, 0, 100, "inactive", "aperiodic", 20, 20, trig_pan_ctr_th, pan_ctr_th_imp_step, pan_ctr_th_imp_finalize};

void schedule_HPF(Thread **threads, int threadNum, Device **devices, int deviceNum, float stopTime) {
  // Print data to files
//  FILE *fp_img, *fp_proc_img, *fp_obs_pos_radar, *fp_obs_pos, *fp_cmd, *fp_veh_a, *fp_veh_s, *fp_veh_pos, *fp_veh_v, *fp_des_a, *fp_des_v, *fp_veh_l_v, *fp_laser_valid, *fp_laser_v, *fp_veh_w_v, *fp_wheel_valid, *fp_wheel_v;
//  fp_img = fopen("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/img.txt", "w");
//  fp_proc_img = fopen("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/proc_img.txt", "w");
//  fp_obs_pos_radar = fopen("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/obs_pos_radar.txt", "w");
//  fp_obs_pos = fopen("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/obs_pos.txt", "w");
//  fp_cmd = fopen("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/cmd.txt", "w");
//  fp_veh_a = fopen("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/veh_a.txt", "w");
//  fp_veh_s = fopen("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/veh_s.txt", "w");
//  fp_veh_pos = fopen("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/veh_pos.txt", "w");
//  fp_veh_v = fopen("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/veh_v.txt", "w");
//  fp_des_a = fopen("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/des_a.txt", "w");
//  fp_des_v = fopen("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/des_v.txt", "w");
//  fp_veh_l_v = fopen("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/veh_l_v.txt", "w");
//  fp_laser_valid = fopen("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/laser_valid.txt", "w");
//  fp_laser_v = fopen("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/laser_v.txt", "w");
//  fp_veh_w_v = fopen("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/veh_w_v.txt", "w");
//  fp_wheel_valid = fopen("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/wheel_valid.txt", "w");
//  fp_wheel_v = fopen("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/wheel_v.txt", "w");
  
  int running_prior = -1; // Priority of the running thread
  int running_id = -1; // ID (in the array) of the running thread

  // Initialize the vehicle model
  vehicle_imp_initialize();
  
  // Initial pan_ctr_th.imp
  pan_ctr_th_imp_initialize();
  pan_ctr_th_imp_step();
  
  while (globalClock <= stopTime) {
//    fprintf(fp_img, "%f,", img);
//    fprintf(fp_proc_img, "%f,", proc_img);
//    fprintf(fp_obs_pos_radar, "%f,", obs_pos_radar);
//    fprintf(fp_obs_pos, "%f,", obs_pos);
//    fprintf(fp_cmd, "%f,", cmd);
//    fprintf(fp_veh_a, "%f,", veh_a);
//    fprintf(fp_veh_s, "%f,", veh_s);
//    fprintf(fp_veh_pos, "%f,", veh_pos);
//    fprintf(fp_veh_v, "%f,", veh_v);
//    fprintf(fp_des_a, "%f,", des_a);
//    fprintf(fp_des_v, "%f,", des_v);
//    fprintf(fp_veh_l_v, "%f,", veh_l_v);
//    fprintf(fp_laser_valid, "%f,", laser_valid);
//    fprintf(fp_laser_v, "%f,", laser_v);
//    fprintf(fp_veh_w_v, "%f,", veh_w_v);
//    fprintf(fp_wheel_valid, "%f,", wheel_valid);
//    fprintf(fp_wheel_v, "%f,", wheel_v);
    // Continuous behaviour
    vehicle_rtU.veh_a = veh_a;
    vehicle_imp_step();
    veh_l_v = vehicle_rtY.veh_l_v;
    veh_w_v = vehicle_rtY.veh_w_v;
    veh_s = vehicle_rtY.veh_s;
    // fprintf(fp, "%f,", veh_l_v);
    
    // Devices produce data
    for (int i = 0; i < deviceNum; i++)
      if (globalClock % devices[i]->period == 0)
        devices[i]->produce_data();
    // fprintf(fp, "%f,", obs_pos_radar);
    
    // Stage 0: Activation
    for (int i = 0; i < threadNum; i++) {
      if (strcmp(threads[i]->state, "inactive") == 0) {
        if (strcmp(threads[i]->dispatch_protocol, "periodic") == 0) {
          if (globalClock % threads[i]->period == 0) {
            threads[i]->state = "ready";
            threads[i]->initialize();
            // threads[i]->waitClock = 0;
          }
        } else if (strcmp(threads[i]->dispatch_protocol, "aperiodic") == 0) {
          if (strcmp(threads[i]->threadName, "pan_ctr_th") == 0 && !(isEmpty(inc_buffer) && isEmpty(dec_buffer))) {
            threads[i]->state = "ready";
            threads[i]->initialize();
            // threads[i]->waitClock = 0;
          }
        }
      }
    }
    
    // Stage 1: Selection
    int last_running_id = running_id;
    for (int i = 0; i < threadNum; i++) {
      if (strcmp(threads[i]->state, "ready") == 0 && threads[i]->priority >= running_prior) {
        running_prior = threads[i]->priority;
        running_id = i;
      }
    }
    threads[running_id]->state = "running";
    // If the last running thread was preempted
    if (last_running_id != -1 && running_id != last_running_id) {
      if (threads[last_running_id]->runClock >= threads[last_running_id]->minExecutionTime) {
        // The preempted thread must output data and then exit.
        threads[last_running_id]->finialize();
        threads[last_running_id]->state = "inactive";
        threads[last_running_id]->runClock = 0;
        threads[last_running_id]->waitClock = 0;
      } else {
        threads[last_running_id]->state = "ready";
      }
    }
    // If no threads are activated
    if (running_id == -1) {
      globalClock += StepSize;
      continue;
    }
    
    // Stage 2: Execution
    threads[running_id]->execute();
    threads[running_id]->runClock += StepSize;
    threads[running_id]->waitClock += StepSize;
    if (threads[running_id]->waitClock + StepSize > threads[running_id]->deadline || threads[running_id]->runClock + StepSize > threads[running_id]->maxExecutionTime) {
      // If not necessary, threads do not output data.
      threads[running_id]->finialize();
      threads[running_id]->state = "inactive";
      threads[running_id]->runClock = 0;
      threads[running_id]->waitClock = 0;
      running_prior = -1;
      running_id = -1;
    }
    
    // Stage 3: Take one step
    for (int i = 0; i < threadNum; i++) {
      if (strcmp(threads[i]->state, "ready") == 0) {
        threads[i]->waitClock += StepSize;
        if (threads[i]->waitClock > threads[i]->deadline) {
          threads[i]->state = "inactive";
          threads[i]->runClock = 0;
          threads[i]->waitClock = 0;
        }
      }
    }
    
    globalClock += StepSize;
  }
//  fclose(fp_img); fclose(fp_proc_img); fclose(fp_obs_pos_radar); fclose(fp_obs_pos); fclose(fp_cmd); fclose(fp_veh_a); fclose(fp_veh_s); fclose(fp_veh_pos); fclose(fp_veh_v); fclose(fp_des_a); fclose(fp_des_v); fclose(fp_veh_l_v); fclose(fp_laser_valid); fclose(fp_laser_v); fclose(fp_veh_w_v); fclose(fp_wheel_valid); fclose(fp_wheel_v);
}

int main()
{
  int threadNum = 6;
  Thread *threads[6] = {&img_acq, &comp_obs_pos, &emerg, &PI_ctr, &velo_voter, &pan_ctr_th};
  
  int deviceNum = 7;
  Device *devices[7] = {&camera, &radar, &actuator, &gps, &laser, &wheel, &user_panel};

  int stopTime = 20000; // (ms)
  
  schedule_HPF(threads, threadNum, devices, deviceNum, stopTime);
  
  printf("%d\n", globalClock);
  
  return 0;
}
