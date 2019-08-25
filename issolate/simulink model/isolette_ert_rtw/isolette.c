/*
 * File: isolette.c
 *
 * Code generated for Simulink model 'isolette'.
 *
 * Model version                  : 1.2
 * Simulink Coder version         : 8.10 (R2016a) 10-Feb-2016
 * C/C++ source code generated on : Fri Feb 22 10:14:33 2019
 *
 * Target selection: ert.tlc
 * Embedded hardware selection: Intel->x86-64 (Windows64)
 * Code generation objectives: Unspecified
 * Validation result: Not run
 */

#include "isolette.h"
#include "isolette_private.h"

/* Block signals (auto storage) */
B_isolette_T isolette_B;

/* Continuous states */
X_isolette_T isolette_X;

/* Block states (auto storage) */
DW_isolette_T isolette_DW;

/* External inputs (root inport signals with auto storage) */
ExtU_isolette_T isolette_U;

/* External outputs (root outports fed by signals with auto storage) */
ExtY_isolette_T isolette_Y;

/* Real-time model */
RT_MODEL_isolette_T isolette_M_;
RT_MODEL_isolette_T *const isolette_M = &isolette_M_;

/*
 * This function updates continuous states using the ODE3 fixed-step
 * solver algorithm
 */
static void rt_ertODEUpdateContinuousStates(RTWSolverInfo *si )
{
  /* Solver Matrices */
  static const real_T rt_ODE3_A[3] = {
    1.0/2.0, 3.0/4.0, 1.0
  };

  static const real_T rt_ODE3_B[3][3] = {
    { 1.0/2.0, 0.0, 0.0 },

    { 0.0, 3.0/4.0, 0.0 },

    { 2.0/9.0, 1.0/3.0, 4.0/9.0 }
  };

  time_T t = rtsiGetT(si);
  time_T tnew = rtsiGetSolverStopTime(si);
  time_T h = rtsiGetStepSize(si);
  real_T *x = rtsiGetContStates(si);
  ODE3_IntgData *id = (ODE3_IntgData *)rtsiGetSolverData(si);
  real_T *y = id->y;
  real_T *f0 = id->f[0];
  real_T *f1 = id->f[1];
  real_T *f2 = id->f[2];
  real_T hB[3];
  int_T i;
  int_T nXc = 2;
  rtsiSetSimTimeStep(si,MINOR_TIME_STEP);

  /* Save the state values at time t in y, we'll use x as ynew. */
  (void) memcpy(y, x,
                (uint_T)nXc*sizeof(real_T));

  /* Assumes that rtsiSetT and ModelOutputs are up-to-date */
  /* f0 = f(t,y) */
  rtsiSetdX(si, f0);
  isolette_derivatives();

  /* f(:,2) = feval(odefile, t + hA(1), y + f*hB(:,1), args(:)(*)); */
  hB[0] = h * rt_ODE3_B[0][0];
  for (i = 0; i < nXc; i++) {
    x[i] = y[i] + (f0[i]*hB[0]);
  }

  rtsiSetT(si, t + h*rt_ODE3_A[0]);
  rtsiSetdX(si, f1);
  isolette_step();
  isolette_derivatives();

  /* f(:,3) = feval(odefile, t + hA(2), y + f*hB(:,2), args(:)(*)); */
  for (i = 0; i <= 1; i++) {
    hB[i] = h * rt_ODE3_B[1][i];
  }

  for (i = 0; i < nXc; i++) {
    x[i] = y[i] + (f0[i]*hB[0] + f1[i]*hB[1]);
  }

  rtsiSetT(si, t + h*rt_ODE3_A[1]);
  rtsiSetdX(si, f2);
  isolette_step();
  isolette_derivatives();

  /* tnew = t + hA(3);
     ynew = y + f*hB(:,3); */
  for (i = 0; i <= 2; i++) {
    hB[i] = h * rt_ODE3_B[2][i];
  }

  for (i = 0; i < nXc; i++) {
    x[i] = y[i] + (f0[i]*hB[0] + f1[i]*hB[1] + f2[i]*hB[2]);
  }

  rtsiSetT(si, tnew);
  rtsiSetSimTimeStep(si,MAJOR_TIME_STEP);
}

/* Model step function */
void isolette_step(void)
{
  if (rtmIsMajorTimeStep(isolette_M)) {
    /* set solver stop time */
    rtsiSetSolverStopTime(&isolette_M->solverInfo,
                          ((isolette_M->Timing.clockTick0+1)*
      isolette_M->Timing.stepSize0));
  }                                    /* end MajorTimeStep */

  /* Update absolute time of base rate at minor time step */
  if (rtmIsMinorTimeStep(isolette_M)) {
    isolette_M->Timing.t[0] = rtsiGetT(&isolette_M->solverInfo);
  }

  /* Integrator: '<S1>/Integrator1' */
  if (isolette_DW.Integrator1_IWORK != 0) {
    isolette_X.Integrator1_CSTATE = isolette_ConstB.Constant1;
  }

  /* Outport: '<Root>/Out1' incorporates:
   *  Integrator: '<S1>/Integrator1'
   */
  isolette_Y.Out1 = isolette_X.Integrator1_CSTATE;

  /* Integrator: '<S1>/Integrator' */
  if (isolette_DW.Integrator_IWORK != 0) {
    isolette_X.Integrator_CSTATE = isolette_ConstB.Constant;
  }

  /* Gain: '<S1>/Gain' incorporates:
   *  Integrator: '<S1>/Integrator'
   *  Integrator: '<S1>/Integrator1'
   *  Sum: '<S1>/Sum'
   */
  isolette_B.Gain = (isolette_X.Integrator1_CSTATE -
                     isolette_X.Integrator_CSTATE) * -0.026;

  /* Switch: '<S1>/Switch' incorporates:
   *  Constant: '<S1>/Constant'
   *  Constant: '<S1>/Constant1'
   *  Inport: '<Root>/In1'
   */
  if (isolette_U.In1 > 0.0) {
    isolette_B.Switch = 1.0;
  } else {
    isolette_B.Switch = -1.0;
  }

  /* End of Switch: '<S1>/Switch' */
  if (rtmIsMajorTimeStep(isolette_M)) {
    /* Update for Integrator: '<S1>/Integrator1' */
    isolette_DW.Integrator1_IWORK = 0;

    /* Update for Integrator: '<S1>/Integrator' */
    isolette_DW.Integrator_IWORK = 0;
  }                                    /* end MajorTimeStep */

  if (rtmIsMajorTimeStep(isolette_M)) {
    rt_ertODEUpdateContinuousStates(&isolette_M->solverInfo);

    /* Update absolute time for base rate */
    /* The "clockTick0" counts the number of times the code of this task has
     * been executed. The absolute time is the multiplication of "clockTick0"
     * and "Timing.stepSize0". Size of "clockTick0" ensures timer will not
     * overflow during the application lifespan selected.
     */
    ++isolette_M->Timing.clockTick0;
    isolette_M->Timing.t[0] = rtsiGetSolverStopTime(&isolette_M->solverInfo);

    {
      /* Update absolute timer for sample time: [0.01s, 0.0s] */
      /* The "clockTick1" counts the number of times the code of this task has
       * been executed. The resolution of this integer timer is 0.01, which is the step size
       * of the task. Size of "clockTick1" ensures timer will not overflow during the
       * application lifespan selected.
       */
      isolette_M->Timing.clockTick1++;
    }
  }                                    /* end MajorTimeStep */
}

/* Derivatives for root system: '<Root>' */
void isolette_derivatives(void)
{
  XDot_isolette_T *_rtXdot;
  _rtXdot = ((XDot_isolette_T *) isolette_M->ModelData.derivs);

  /* Derivatives for Integrator: '<S1>/Integrator1' */
  _rtXdot->Integrator1_CSTATE = isolette_B.Gain;

  /* Derivatives for Integrator: '<S1>/Integrator' */
  _rtXdot->Integrator_CSTATE = isolette_B.Switch;
}

/* Model initialize function */
void isolette_initialize(void)
{
  /* Registration code */

  /* initialize real-time model */
  (void) memset((void *)isolette_M, 0,
                sizeof(RT_MODEL_isolette_T));

  {
    /* Setup solver object */
    rtsiSetSimTimeStepPtr(&isolette_M->solverInfo,
                          &isolette_M->Timing.simTimeStep);
    rtsiSetTPtr(&isolette_M->solverInfo, &rtmGetTPtr(isolette_M));
    rtsiSetStepSizePtr(&isolette_M->solverInfo, &isolette_M->Timing.stepSize0);
    rtsiSetdXPtr(&isolette_M->solverInfo, &isolette_M->ModelData.derivs);
    rtsiSetContStatesPtr(&isolette_M->solverInfo, (real_T **)
                         &isolette_M->ModelData.contStates);
    rtsiSetNumContStatesPtr(&isolette_M->solverInfo,
      &isolette_M->Sizes.numContStates);
    rtsiSetNumPeriodicContStatesPtr(&isolette_M->solverInfo,
      &isolette_M->Sizes.numPeriodicContStates);
    rtsiSetPeriodicContStateIndicesPtr(&isolette_M->solverInfo,
      &isolette_M->ModelData.periodicContStateIndices);
    rtsiSetPeriodicContStateRangesPtr(&isolette_M->solverInfo,
      &isolette_M->ModelData.periodicContStateRanges);
    rtsiSetErrorStatusPtr(&isolette_M->solverInfo, (&rtmGetErrorStatus
      (isolette_M)));
    rtsiSetRTModelPtr(&isolette_M->solverInfo, isolette_M);
  }

  rtsiSetSimTimeStep(&isolette_M->solverInfo, MAJOR_TIME_STEP);
  isolette_M->ModelData.intgData.y = isolette_M->ModelData.odeY;
  isolette_M->ModelData.intgData.f[0] = isolette_M->ModelData.odeF[0];
  isolette_M->ModelData.intgData.f[1] = isolette_M->ModelData.odeF[1];
  isolette_M->ModelData.intgData.f[2] = isolette_M->ModelData.odeF[2];
  isolette_M->ModelData.contStates = ((X_isolette_T *) &isolette_X);
  rtsiSetSolverData(&isolette_M->solverInfo, (void *)
                    &isolette_M->ModelData.intgData);
  rtsiSetSolverName(&isolette_M->solverInfo,"ode3");
  rtmSetTPtr(isolette_M, &isolette_M->Timing.tArray[0]);
  isolette_M->Timing.stepSize0 = 0.01;
  rtmSetFirstInitCond(isolette_M, 1);

  /* block I/O */
  (void) memset(((void *) &isolette_B), 0,
                sizeof(B_isolette_T));

  /* states (continuous) */
  {
    (void) memset((void *)&isolette_X, 0,
                  sizeof(X_isolette_T));
  }

  /* states (dwork) */
  (void) memset((void *)&isolette_DW, 0,
                sizeof(DW_isolette_T));

  /* external inputs */
  isolette_U.In1 = 0.0;

  /* external outputs */
  isolette_Y.Out1 = 0.0;

  /* InitializeConditions for Integrator: '<S1>/Integrator1' incorporates:
   *  InitializeConditions for Integrator: '<S1>/Integrator'
   */
  if (rtmIsFirstInitCond(isolette_M)) {
    isolette_X.Integrator1_CSTATE = 100.0;
    isolette_X.Integrator_CSTATE = 97.0;
  }

  isolette_DW.Integrator1_IWORK = 1;

  /* End of InitializeConditions for Integrator: '<S1>/Integrator1' */

  /* InitializeConditions for Integrator: '<S1>/Integrator' */
  isolette_DW.Integrator_IWORK = 1;

  /* set "at time zero" to false */
  if (rtmIsFirstInitCond(isolette_M)) {
    rtmSetFirstInitCond(isolette_M, 0);
  }
}

/* Model terminate function */
void isolette_terminate(void)
{
  /* (no terminate code required) */
}

/*
 * File trailer for generated code.
 *
 * [EOF]
 */
