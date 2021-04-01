/*
 * File: comp_obs_pos_imp.c
 *
 * Code generated for Simulink model 'comp_obs_pos_imp'.
 *
 * Model version                  : 1.2
 * Simulink Coder version         : 8.14 (R2018a) 06-Feb-2018
 * C/C++ source code generated on : Mon Mar 29 16:40:45 2021
 *
 * Target selection: ert.tlc
 * Embedded hardware selection: Intel->x86-64 (Mac OS X)
 * Code generation objectives:
 *    1. Execution efficiency
 *    2. RAM efficiency
 * Validation result: Not run
 */

#include "comp_obs_pos_imp.h"

/* External inputs (root inport signals with default storage) */
comp_obs_pos_ExtU comp_obs_pos_rtU;

/* External outputs (root outports fed by signals with default storage) */
comp_obs_pos_ExtY comp_obs_pos_rtY;

/* Real-time model */
// RT_MODEL rtM_;
// RT_MODEL *const rtM = &rtM_;

/* Model step function */
void comp_obs_pos_imp_step(void)
{
  real_T u0;
  real_T tmp;

  /* Switch: '<Root>/Switch' incorporates:
   *  Inport: '<Root>/obs_pos_radar'
   *  Inport: '<Root>/proc_img'
   */
  if (comp_obs_pos_rtU.proc_img > 0.0) {
    u0 = comp_obs_pos_rtU.proc_img;
  } else {
    u0 = comp_obs_pos_rtU.obs_pos_radar;
  }

  /* End of Switch: '<Root>/Switch' */

  /* Switch: '<Root>/Switch1' incorporates:
   *  Inport: '<Root>/obs_pos_radar'
   *  Inport: '<Root>/proc_img'
   */
  if (comp_obs_pos_rtU.obs_pos_radar > 0.0) {
    tmp = comp_obs_pos_rtU.obs_pos_radar;
  } else {
    tmp = comp_obs_pos_rtU.proc_img;
  }

  /* End of Switch: '<Root>/Switch1' */

  /* MinMax: '<Root>/Min' */
  u0 = fmin(u0, tmp);

  /* Saturate: '<Root>/Saturation' */
  if (u0 > 100.0) {
    /* Outport: '<Root>/obs_pos' */
    comp_obs_pos_rtY.obs_pos = 100.0;
  } else if (u0 < 0.0) {
    /* Outport: '<Root>/obs_pos' */
    comp_obs_pos_rtY.obs_pos = 0.0;
  } else {
    /* Outport: '<Root>/obs_pos' */
    comp_obs_pos_rtY.obs_pos = u0;
  }

  /* End of Saturate: '<Root>/Saturation' */
}

/* Model initialize function */
void comp_obs_pos_imp_initialize(void)
{
  /* (no initialization code required) */
  comp_obs_pos_rtU.proc_img = proc_img;
  comp_obs_pos_rtU.obs_pos_radar = obs_pos_radar;
}

void comp_obs_pos_imp_finalize(void)
{
  obs_pos = comp_obs_pos_rtY.obs_pos;
}
/*
 * File trailer for generated code.
 *
 * [EOF]
 */
