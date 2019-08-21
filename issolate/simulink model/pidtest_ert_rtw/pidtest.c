/*
 * File: pidtest.c
 *
 * Code generated for Simulink model 'pidtest'.
 *
 * Model version                  : 1.1
 * Simulink Coder version         : 8.6 (R2014a) 27-Dec-2013
 * C/C++ source code generated on : Wed Oct 24 11:33:41 2018
 *
 * Target selection: ert.tlc
 * Embedded hardware selection: 32-bit Generic
 * Code generation objectives: Unspecified
 * Validation result: Not run
 */

#include "pidtest.h"
#include "pidtest_private.h"

/* Block signals (auto storage) */
B_pidtest_T pidtest_B;

/* Continuous states */
X_pidtest_T pidtest_X;

/* Block states (auto storage) */
DW_pidtest_T pidtest_DW;

/* External inputs (root inport signals with auto storage) */
ExtU_pidtest_T pidtest_U;

/* External outputs (root outports fed by signals with auto storage) */
ExtY_pidtest_T pidtest_Y;

/* Real-time model */
RT_MODEL_pidtest_T pidtest_M_;
RT_MODEL_pidtest_T *const pidtest_M = &pidtest_M_;

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
  int_T nXc = 1;
  rtsiSetSimTimeStep(si,MINOR_TIME_STEP);

  /* Save the state values at time t in y, we'll use x as ynew. */
  (void) memcpy(y, x,
                (uint_T)nXc*sizeof(real_T));

  /* Assumes that rtsiSetT and ModelOutputs are up-to-date */
  /* f0 = f(t,y) */
  rtsiSetdX(si, f0);
  pidtest_derivatives();

  /* f(:,2) = feval(odefile, t + hA(1), y + f*hB(:,1), args(:)(*)); */
  hB[0] = h * rt_ODE3_B[0][0];
  for (i = 0; i < nXc; i++) {
    x[i] = y[i] + (f0[i]*hB[0]);
  }

  rtsiSetT(si, t + h*rt_ODE3_A[0]);
  rtsiSetdX(si, f1);
  pidtest_step();
  pidtest_derivatives();

  /* f(:,3) = feval(odefile, t + hA(2), y + f*hB(:,2), args(:)(*)); */
  for (i = 0; i <= 1; i++) {
    hB[i] = h * rt_ODE3_B[1][i];
  }

  for (i = 0; i < nXc; i++) {
    x[i] = y[i] + (f0[i]*hB[0] + f1[i]*hB[1]);
  }

  rtsiSetT(si, t + h*rt_ODE3_A[1]);
  rtsiSetdX(si, f2);
  pidtest_step();
  pidtest_derivatives();

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
void pidtest_step(void)
{
  if (rtmIsMajorTimeStep(pidtest_M)) {
    /* set solver stop time */
    if (!(pidtest_M->Timing.clockTick0+1)) {
      rtsiSetSolverStopTime(&pidtest_M->solverInfo,
                            ((pidtest_M->Timing.clockTickH0 + 1) *
        pidtest_M->Timing.stepSize0 * 4294967296.0));
    } else {
      rtsiSetSolverStopTime(&pidtest_M->solverInfo,
                            ((pidtest_M->Timing.clockTick0 + 1) *
        pidtest_M->Timing.stepSize0 + pidtest_M->Timing.clockTickH0 *
        pidtest_M->Timing.stepSize0 * 4294967296.0));
    }
  }                                    /* end MajorTimeStep */

  /* Update absolute time of base rate at minor time step */
  if (rtmIsMinorTimeStep(pidtest_M)) {
    pidtest_M->Timing.t[0] = rtsiGetT(&pidtest_M->solverInfo);
  }

  {
    real_T *lastU;
    real_T rtb_Derivative;

    /* Outputs for Atomic SubSystem: '<Root>/Subsystem' */
    /* Product: '<S1>/Product1' incorporates:
     *  Inport: '<Root>/In1'
     *  Inport: '<Root>/In3'
     */
    pidtest_B.Product1 = pidtest_U.In3 * pidtest_U.In1;

    /* Derivative: '<S1>/Derivative' */
    if ((pidtest_DW.TimeStampA >= pidtest_M->Timing.t[0]) &&
        (pidtest_DW.TimeStampB >= pidtest_M->Timing.t[0])) {
      rtb_Derivative = 0.0;
    } else {
      rtb_Derivative = pidtest_DW.TimeStampA;
      lastU = &pidtest_DW.LastUAtTimeA;
      if (pidtest_DW.TimeStampA < pidtest_DW.TimeStampB) {
        if (pidtest_DW.TimeStampB < pidtest_M->Timing.t[0]) {
          rtb_Derivative = pidtest_DW.TimeStampB;
          lastU = &pidtest_DW.LastUAtTimeB;
        }
      } else {
        if (pidtest_DW.TimeStampA >= pidtest_M->Timing.t[0]) {
          rtb_Derivative = pidtest_DW.TimeStampB;
          lastU = &pidtest_DW.LastUAtTimeB;
        }
      }

      rtb_Derivative = (pidtest_B.Product1 - *lastU) / (pidtest_M->Timing.t[0] -
        rtb_Derivative);
    }

    /* End of Derivative: '<S1>/Derivative' */

    /* Product: '<S1>/Product' incorporates:
     *  Inport: '<Root>/In1'
     *  Inport: '<Root>/In2'
     */
    pidtest_B.Product = pidtest_U.In2 * pidtest_U.In1;

    /* Outport: '<Root>/Out1' incorporates:
     *  Inport: '<Root>/In1'
     *  Inport: '<Root>/In4'
     *  Integrator: '<S1>/Integrator'
     *  Product: '<S1>/Product2'
     *  Sum: '<S1>/Add'
     */
    pidtest_Y.Out1 = (pidtest_X.Integrator_CSTATE + rtb_Derivative) +
      pidtest_U.In1 * pidtest_U.In4;

    /* End of Outputs for SubSystem: '<Root>/Subsystem' */
  }

  if (rtmIsMajorTimeStep(pidtest_M)) {
    real_T *lastU;

    /* Update for Atomic SubSystem: '<Root>/Subsystem' */
    /* Update for Derivative: '<S1>/Derivative' */
    if (pidtest_DW.TimeStampA == (rtInf)) {
      pidtest_DW.TimeStampA = pidtest_M->Timing.t[0];
      lastU = &pidtest_DW.LastUAtTimeA;
    } else if (pidtest_DW.TimeStampB == (rtInf)) {
      pidtest_DW.TimeStampB = pidtest_M->Timing.t[0];
      lastU = &pidtest_DW.LastUAtTimeB;
    } else if (pidtest_DW.TimeStampA < pidtest_DW.TimeStampB) {
      pidtest_DW.TimeStampA = pidtest_M->Timing.t[0];
      lastU = &pidtest_DW.LastUAtTimeA;
    } else {
      pidtest_DW.TimeStampB = pidtest_M->Timing.t[0];
      lastU = &pidtest_DW.LastUAtTimeB;
    }

    *lastU = pidtest_B.Product1;

    /* End of Update for Derivative: '<S1>/Derivative' */
    /* End of Update for SubSystem: '<Root>/Subsystem' */
  }                                    /* end MajorTimeStep */

  if (rtmIsMajorTimeStep(pidtest_M)) {
    rt_ertODEUpdateContinuousStates(&pidtest_M->solverInfo);

    /* Update absolute time for base rate */
    /* The "clockTick0" counts the number of times the code of this task has
     * been executed. The absolute time is the multiplication of "clockTick0"
     * and "Timing.stepSize0". Size of "clockTick0" ensures timer will not
     * overflow during the application lifespan selected.
     * Timer of this task consists of two 32 bit unsigned integers.
     * The two integers represent the low bits Timing.clockTick0 and the high bits
     * Timing.clockTickH0. When the low bit overflows to 0, the high bits increment.
     */
    if (!(++pidtest_M->Timing.clockTick0)) {
      ++pidtest_M->Timing.clockTickH0;
    }

    pidtest_M->Timing.t[0] = rtsiGetSolverStopTime(&pidtest_M->solverInfo);
  }                                    /* end MajorTimeStep */
}

/* Derivatives for root system: '<Root>' */
void pidtest_derivatives(void)
{
  XDot_pidtest_T *_rtXdot;
  _rtXdot = ((XDot_pidtest_T *) pidtest_M->ModelData.derivs);

  /* Derivatives for Atomic SubSystem: '<Root>/Subsystem' */
  /* Derivatives for Integrator: '<S1>/Integrator' */
  _rtXdot->Integrator_CSTATE = pidtest_B.Product;

  /* End of Derivatives for SubSystem: '<Root>/Subsystem' */
}

/* Model initialize function */
void pidtest_initialize(void)
{
  /* Registration code */

  /* initialize non-finites */
  rt_InitInfAndNaN(sizeof(real_T));

  /* initialize real-time model */
  (void) memset((void *)pidtest_M, 0,
                sizeof(RT_MODEL_pidtest_T));

  {
    /* Setup solver object */
    rtsiSetSimTimeStepPtr(&pidtest_M->solverInfo, &pidtest_M->Timing.simTimeStep);
    rtsiSetTPtr(&pidtest_M->solverInfo, &rtmGetTPtr(pidtest_M));
    rtsiSetStepSizePtr(&pidtest_M->solverInfo, &pidtest_M->Timing.stepSize0);
    rtsiSetdXPtr(&pidtest_M->solverInfo, &pidtest_M->ModelData.derivs);
    rtsiSetContStatesPtr(&pidtest_M->solverInfo, (real_T **)
                         &pidtest_M->ModelData.contStates);
    rtsiSetNumContStatesPtr(&pidtest_M->solverInfo,
      &pidtest_M->Sizes.numContStates);
    rtsiSetErrorStatusPtr(&pidtest_M->solverInfo, (&rtmGetErrorStatus(pidtest_M)));
    rtsiSetRTModelPtr(&pidtest_M->solverInfo, pidtest_M);
  }

  rtsiSetSimTimeStep(&pidtest_M->solverInfo, MAJOR_TIME_STEP);
  pidtest_M->ModelData.intgData.y = pidtest_M->ModelData.odeY;
  pidtest_M->ModelData.intgData.f[0] = pidtest_M->ModelData.odeF[0];
  pidtest_M->ModelData.intgData.f[1] = pidtest_M->ModelData.odeF[1];
  pidtest_M->ModelData.intgData.f[2] = pidtest_M->ModelData.odeF[2];
  pidtest_M->ModelData.contStates = ((X_pidtest_T *) &pidtest_X);
  rtsiSetSolverData(&pidtest_M->solverInfo, (void *)
                    &pidtest_M->ModelData.intgData);
  rtsiSetSolverName(&pidtest_M->solverInfo,"ode3");
  rtmSetTPtr(pidtest_M, &pidtest_M->Timing.tArray[0]);
  pidtest_M->Timing.stepSize0 = 0.2;

  /* block I/O */
  (void) memset(((void *) &pidtest_B), 0,
                sizeof(B_pidtest_T));

  /* states (continuous) */
  {
    (void) memset((void *)&pidtest_X, 0,
                  sizeof(X_pidtest_T));
  }

  /* states (dwork) */
  (void) memset((void *)&pidtest_DW, 0,
                sizeof(DW_pidtest_T));

  /* external inputs */
  (void) memset((void *)&pidtest_U, 0,
                sizeof(ExtU_pidtest_T));

  /* external outputs */
  pidtest_Y.Out1 = 0.0;

  /* InitializeConditions for Atomic SubSystem: '<Root>/Subsystem' */
  /* InitializeConditions for Integrator: '<S1>/Integrator' */
  pidtest_X.Integrator_CSTATE = 0.0;

  /* InitializeConditions for Derivative: '<S1>/Derivative' */
  pidtest_DW.TimeStampA = (rtInf);
  pidtest_DW.TimeStampB = (rtInf);

  /* End of InitializeConditions for SubSystem: '<Root>/Subsystem' */
}

/* Model terminate function */
void pidtest_terminate(void)
{
  /* (no terminate code required) */
}

/*
 * File trailer for generated code.
 *
 * [EOF]
 */
