/*
 * File: PI_ctr_imp.c
 *
 * Code generated for Simulink model 'PI_ctr_imp'.
 *
 * Model version                  : 1.2
 * Simulink Coder version         : 8.14 (R2018a) 06-Feb-2018
 * C/C++ source code generated on : Mon Mar 29 20:55:38 2021
 *
 * Target selection: ert.tlc
 * Embedded hardware selection: Intel->x86-64 (Mac OS X)
 * Code generation objectives:
 *    1. Execution efficiency
 *    2. RAM efficiency
 * Validation result: Not run
 */

#include "PI_ctr_imp.h"

/* Block signals and states (default storage) */
PI_ctr_DW PI_ctr_rtDW;

/* External inputs (root inport signals with default storage) */
PI_ctr_ExtU PI_ctr_rtU;

/* External outputs (root outports fed by signals with default storage) */
PI_ctr_ExtY PI_ctr_rtY;

/* Model step function */
void PI_ctr_imp_step(void)
{
  real_T rtb_Sum;
  real_T rtb_SumFdbk;
  real_T rtb_SumFdbk_0;

  /* Sum: '<Root>/Add' incorporates:
   *  Inport: '<Root>/des_v'
   *  Inport: '<Root>/veh_v'
   */
  rtb_Sum = PI_ctr_rtU.des_v - PI_ctr_rtU.veh_v;

  /* Sum: '<S1>/Sum Fdbk' */
  rtb_SumFdbk = rtb_Sum + PI_ctr_rtDW.Integrator_DSTATE;

  /* Saturate: '<S1>/Saturate Fdbk' */
  if (rtb_SumFdbk > 3.0) {
    rtb_SumFdbk_0 = 3.0;
  } else if (rtb_SumFdbk < -3.0) {
    rtb_SumFdbk_0 = -3.0;
  } else {
    rtb_SumFdbk_0 = rtb_SumFdbk;
  }

  /* End of Saturate: '<S1>/Saturate Fdbk' */

  /* DiscreteIntegrator: '<S1>/Integrator' incorporates:
   *  Sum: '<S1>/SumI1'
   *  Sum: '<S1>/SumI2'
   */
  rtb_SumFdbk = ((rtb_SumFdbk_0 - rtb_SumFdbk) + rtb_Sum) * 0.001 +
    PI_ctr_rtDW.Integrator_DSTATE;

  /* Sum: '<S1>/Sum' */
  rtb_Sum += rtb_SumFdbk;

  /* Saturate: '<S1>/Saturate' */
  if (rtb_Sum > 3.0) {
    /* Outport: '<Root>/des_a' */
    PI_ctr_rtY.des_a = 3.0;
  } else if (rtb_Sum < -3.0) {
    /* Outport: '<Root>/des_a' */
    PI_ctr_rtY.des_a = -3.0;
  } else {
    /* Outport: '<Root>/des_a' */
    PI_ctr_rtY.des_a = rtb_Sum;
  }

  /* End of Saturate: '<S1>/Saturate' */

  /* Update for DiscreteIntegrator: '<S1>/Integrator' */
  PI_ctr_rtDW.Integrator_DSTATE = rtb_SumFdbk;
}

/* Model initialize function */
void PI_ctr_imp_initialize(void)
{
  /* (no initialization code required) */
  PI_ctr_rtU.veh_v = veh_v;
  PI_ctr_rtU.des_v = des_v;
}

void PI_ctr_imp_finalize(void)
{
  des_a = PI_ctr_rtY.des_a;
}

/*
 * File trailer for generated code.
 *
 * [EOF]
 */
