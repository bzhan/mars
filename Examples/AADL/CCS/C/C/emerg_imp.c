/*
 * File: emerg_imp.c
 *
 * Code generated for Simulink model 'emerg_imp'.
 *
 * Model version                  : 1.5
 * Simulink Coder version         : 8.14 (R2018a) 06-Feb-2018
 * C/C++ source code generated on : Mon Mar 29 16:56:42 2021
 *
 * Target selection: ert.tlc
 * Embedded hardware selection: Intel->x86-64 (Mac OS X)
 * Code generation objectives:
 *    1. Execution efficiency
 *    2. RAM efficiency
 * Validation result: Not run
 */

#include "emerg_imp.h"

/* Named constants for Chart: '<Root>/emerg_imp' */
#define max_v                          (10.0)
#define min_a                          (-3.0)
#define period                         (0.005)

/* Block signals and states (default storage) */
emerg_DW emerg_rtDW;

/* External inputs (root inport signals with default storage) */
emerg_ExtU emerg_rtU;

/* External outputs (root outports fed by signals with default storage) */
emerg_ExtY emerg_rtY;

/* Real-time model */
//RT_MODEL rtM_;
//RT_MODEL *const rtM = &rtM_;

/* Forward declaration for local functions */
static real_T V_lim(real_T s);

/* Function for Chart: '<Root>/emerg_imp' */
static real_T V_lim(real_T s)
{
  real_T v_lim;
  real_T distance;

  /* Inport: '<Root>/obs_pos' */
  distance = emerg_rtU.obs_pos - s;
  if ((emerg_rtU.obs_pos <= 0.0) || (distance >= 16.666666666666668)) {
    v_lim = max_v;
  } else if (distance >= 0.0) {
    v_lim = sqrt(6.0 * distance);
  } else {
    v_lim = 0.0;
  }

  return v_lim;
}

/* Model step function */
void emerg_imp_step(void)
{
  real_T next_v;

  /* Chart: '<Root>/emerg_imp' incorporates:
   *  Inport: '<Root>/des_a'
   *  Inport: '<Root>/veh_pos'
   *  Inport: '<Root>/veh_v'
   */
  if (emerg_rtDW.is_active_c3_emerg_imp == 0U) {
    emerg_rtDW.is_active_c3_emerg_imp = 1U;
  } else {
    next_v = emerg_rtU.des_a * period + emerg_rtU.veh_v;
    if (next_v <= V_lim(0.5 * emerg_rtU.des_a * period * period + (emerg_rtU.veh_v * period
          + emerg_rtU.veh_pos))) {
      /* Outport: '<Root>/cmd' */
      emerg_rtY.cmd = emerg_rtU.des_a;
    } else if (emerg_rtU.veh_v <= V_lim(emerg_rtU.veh_v * period + emerg_rtU.veh_pos)) {
      /* Outport: '<Root>/cmd' */
      emerg_rtY.cmd = 0.0;
    } else {
      /* Outport: '<Root>/cmd' */
      emerg_rtY.cmd = min_a;
    }
  }

  /* End of Chart: '<Root>/emerg_imp' */
}

/* Model initialize function */
void emerg_imp_initialize(void)
{
  /* (no initialization code required) */
  emerg_rtU.obs_pos = obs_pos;
  emerg_rtU.veh_pos = veh_pos;
  emerg_rtU.veh_v = veh_v;
  emerg_rtU.des_a = des_a;
}

void emerg_imp_finalize(void)
{
  cmd = emerg_rtY.cmd;
}

/*
 * File trailer for generated code.
 *
 * [EOF]
 */
