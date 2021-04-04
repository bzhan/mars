/*
 * File: velo_voter_imp.c
 *
 * Code generated for Simulink model 'velo_voter_imp'.
 *
 * Model version                  : 1.3
 * Simulink Coder version         : 8.14 (R2018a) 06-Feb-2018
 * C/C++ source code generated on : Mon Mar 29 19:00:48 2021
 *
 * Target selection: ert.tlc
 * Embedded hardware selection: Intel->x86-64 (Mac OS X)
 * Code generation objectives:
 *    1. Execution efficiency
 *    2. RAM efficiency
 * Validation result: Not run
 */
#include "velo_voter_imp.h"

/* External inputs (root inport signals with default storage) */
velo_voter_ExtU velo_voter_rtU;

/* External outputs (root outports fed by signals with default storage) */
velo_voter_ExtY velo_voter_rtY;

/* Real-time model */
//RT_MODEL rtM_;
//RT_MODEL *const rtM = &rtM_;

/* Model step function */
void velo_voter_imp_step(void)
{
  real_T tmp;
  real_T tmp_0;

  /* Switch: '<Root>/Switch' incorporates:
   *  Inport: '<Root>/laser_v'
   *  Inport: '<Root>/wheel_v'
   *  Inport: '<Root>/wheel_valid'
   */
  if (velo_voter_rtU.wheel_valid > 0.0) {
    tmp = velo_voter_rtU.wheel_v;
  } else {
    tmp = velo_voter_rtU.laser_v;
  }

  /* End of Switch: '<Root>/Switch' */

  /* Switch: '<Root>/Switch1' incorporates:
   *  Inport: '<Root>/laser_v'
   *  Inport: '<Root>/laser_valid'
   *  Inport: '<Root>/wheel_v'
   */
  if (velo_voter_rtU.laser_valid > 0.0) {
    tmp_0 = velo_voter_rtU.laser_v;
  } else {
    tmp_0 = velo_voter_rtU.wheel_v;
  }

  /* End of Switch: '<Root>/Switch1' */

  /* Outport: '<Root>/veh_v' incorporates:
   *  Constant: '<Root>/Constant'
   *  Product: '<Root>/Divide'
   *  Sum: '<Root>/Add'
   */
  velo_voter_rtY.veh_v = (tmp + tmp_0) / 2.0;
}

/* Model initialize function */
void velo_voter_imp_initialize(void)
{
  /* (no initialization code required) */
  velo_voter_rtU.laser_valid = laser_valid;
  velo_voter_rtU.laser_v = laser_v;
  velo_voter_rtU.wheel_valid = wheel_valid;
  velo_voter_rtU.wheel_v = wheel_v;
}

void velo_voter_imp_finalize(void)
{
  veh_v = velo_voter_rtY.veh_v;
}
/*
 * File trailer for generated code.
 *
 * [EOF]
 */
