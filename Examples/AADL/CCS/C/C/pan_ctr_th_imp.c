/*
 * File: pan_ctr_th_imp.c
 *
 * Code generated for Simulink model 'pan_ctr_th_imp'.
 *
 * Model version                  : 1.1
 * Simulink Coder version         : 8.14 (R2018a) 06-Feb-2018
 * C/C++ source code generated on : Mon Mar 29 19:27:32 2021
 *
 * Target selection: ert.tlc
 * Embedded hardware selection: Intel->x86-64 (Mac OS X)
 * Code generation objectives:
 *    1. Execution efficiency
 *    2. RAM efficiency
 * Validation result: Not run
 */
#include "pan_ctr_th_imp.h"

/* Named constants for Chart: '<Root>/pan_ctr_th_imp' */
#define event_dec                      (1)
#define event_inc                      (0)
#include "solver_zc.h"
#include "zero_crossing_types.h"
#ifndef slZcHadEvent
#define slZcHadEvent(ev, zcsDir)       (((ev) & (zcsDir)) != 0x00 )
#endif

#ifndef slZcUnAliasEvents
#define slZcUnAliasEvents(evL, evR)    ((((slZcHadEvent((evL), (SL_ZCS_EVENT_N2Z)) && slZcHadEvent((evR), (SL_ZCS_EVENT_Z2P))) || (slZcHadEvent((evL), (SL_ZCS_EVENT_P2Z)) && slZcHadEvent((evR), (SL_ZCS_EVENT_Z2N)))) ? (SL_ZCS_EVENT_NUL) : (evR)))
#endif

/* Block signals and states (default storage) */
pan_ctr_th_DW pan_ctr_th_rtDW;

/* Previous zero-crossings (trigger) states */
PrevZCX rtPrevZCX;

/* External inputs (root inport signals with default storage) */
pan_ctr_th_ExtU pan_ctr_th_rtU; // Modified by Xiong

/* External outputs (root outports fed by signals with default storage) */
pan_ctr_th_ExtY pan_ctr_th_rtY;

/* Real-time model */
//RT_MODEL rtM_;
//RT_MODEL *const rtM = &rtM_;

/* Forward declaration for local functions */
static void chartstep_c3_pan_ctr_th_imp(const int32_T *sfEvent);
extern ZCEventType rt_ZCFcn(ZCDirection zcDir, ZCSigState *prevZc, real_T
  currValue);

/* Detect zero crossings events. */
ZCEventType rt_ZCFcn(ZCDirection zcDir, ZCSigState* prevZc, real_T currValue)
{
  slZcEventType zcsDir;
  slZcEventType tempEv;
  ZCEventType zcEvent = NO_ZCEVENT;    /* assume */

  /* zcEvent matrix */
  static const slZcEventType eventMatrix[4][4] = {
    /*          ZER              POS              NEG              UNK */
    { SL_ZCS_EVENT_NUL, SL_ZCS_EVENT_Z2P, SL_ZCS_EVENT_Z2N, SL_ZCS_EVENT_NUL },/* ZER */

    { SL_ZCS_EVENT_P2Z, SL_ZCS_EVENT_NUL, SL_ZCS_EVENT_P2N, SL_ZCS_EVENT_NUL },/* POS */

    { SL_ZCS_EVENT_N2Z, SL_ZCS_EVENT_N2P, SL_ZCS_EVENT_NUL, SL_ZCS_EVENT_NUL },/* NEG */

    { SL_ZCS_EVENT_NUL, SL_ZCS_EVENT_NUL, SL_ZCS_EVENT_NUL, SL_ZCS_EVENT_NUL }/* UNK */
  };

  /* get prevZcEvent and prevZcSign from prevZc */
  slZcEventType prevEv = (slZcEventType)(((uint8_T)(*prevZc)) >> 2);
  slZcSignalSignType prevSign = (slZcSignalSignType)(((uint8_T)(*prevZc)) &
    (uint8_T)0x03);

  /* get current zcSignal sign from current zcSignal value */
  slZcSignalSignType currSign = (slZcSignalSignType)((currValue) > 0.0 ?
    SL_ZCS_SIGN_POS :
    ((currValue) < 0.0 ? SL_ZCS_SIGN_NEG : SL_ZCS_SIGN_ZERO));

  /* get current zcEvent based on prev and current zcSignal value */
  slZcEventType currEv = eventMatrix[prevSign][currSign];

  /* get slZcEventType from ZCDirection */
  switch (zcDir) {
   case ANY_ZERO_CROSSING:
    zcsDir = SL_ZCS_EVENT_ALL;
    break;

   case FALLING_ZERO_CROSSING:
    zcsDir = SL_ZCS_EVENT_ALL_DN;
    break;

   case RISING_ZERO_CROSSING:
    zcsDir = SL_ZCS_EVENT_ALL_UP;
    break;

   default:
    zcsDir = SL_ZCS_EVENT_NUL;
    break;
  }

  /*had event, check if double zc happend remove double detection. */
  if (slZcHadEvent(currEv, zcsDir)) {
    currEv = (slZcEventType)(slZcUnAliasEvents(prevEv, currEv));
  } else {
    currEv = SL_ZCS_EVENT_NUL;
  }

  /* Update prevZc */
  tempEv = (slZcEventType)(currEv << 2);/* shift left by 2 bits */
  *prevZc = (ZCSigState)((currSign) | (tempEv));
  if ((currEv & SL_ZCS_EVENT_ALL_DN) != 0) {
    zcEvent = FALLING_ZCEVENT;
  } else if ((currEv & SL_ZCS_EVENT_ALL_UP) != 0) {
    zcEvent = RISING_ZCEVENT;
  } else {
    zcEvent = NO_ZCEVENT;
  }

  return zcEvent;
}                                      /* rt_ZCFcn */

/* Function for Chart: '<Root>/pan_ctr_th_imp' */
static void chartstep_c3_pan_ctr_th_imp(const int32_T *sfEvent)
{
  /* Chart: '<Root>/pan_ctr_th_imp' incorporates:
   *  Outport: '<Root>/des_v'
   */
  if (pan_ctr_th_rtDW.is_active_c3_pan_ctr_th_imp == 0U) {
    pan_ctr_th_rtDW.is_active_c3_pan_ctr_th_imp = 1U;

    /* Outport: '<Root>/des_v' */
    pan_ctr_th_rtY.des_v = 0.0;
  } else {
    switch (*sfEvent) {
     case event_inc:
      pan_ctr_th_rtY.des_v++;
      break;

     case event_dec:
      pan_ctr_th_rtY.des_v--;
      break;
    }
  }

  /* End of Chart: '<Root>/pan_ctr_th_imp' */
}

/* Model step function */
void pan_ctr_th_imp_step(void)
{
  int32_T sfEvent;
  ZCEventType zcEvent_idx_0;
  ZCEventType zcEvent_idx_1;

  /* Chart: '<Root>/pan_ctr_th_imp' incorporates:
   *  TriggerPort: '<S1>/input events'
   */
  /* Inport: '<Root>/inc' */
  zcEvent_idx_0 = rt_ZCFcn(ANY_ZERO_CROSSING,&rtPrevZCX.pan_ctr_th_imp_Trig_ZCE
    [0],
    (pan_ctr_th_rtU.inc));

  /* Inport: '<Root>/dec' */
  zcEvent_idx_1 = rt_ZCFcn(ANY_ZERO_CROSSING,&rtPrevZCX.pan_ctr_th_imp_Trig_ZCE
    [1],
    (pan_ctr_th_rtU.dec));
  if ((zcEvent_idx_0 != NO_ZCEVENT) || (zcEvent_idx_1 != NO_ZCEVENT)) {
    if ((int8_T)zcEvent_idx_0 != 0) {
      sfEvent = event_inc;
      chartstep_c3_pan_ctr_th_imp(&sfEvent);
    }

    if ((int8_T)zcEvent_idx_1 != 0) {
      sfEvent = event_dec;
      chartstep_c3_pan_ctr_th_imp(&sfEvent);
    }
  }
}

/* Model initialize function */
void pan_ctr_th_imp_initialize(void)
{
  rtPrevZCX.pan_ctr_th_imp_Trig_ZCE[0] = UNINITIALIZED_ZCSIG;
  rtPrevZCX.pan_ctr_th_imp_Trig_ZCE[1] = UNINITIALIZED_ZCSIG;
  // Added by Xiong
  pan_ctr_th_rtU.inc = 1;
  pan_ctr_th_rtU.dec = 1;
}

void pan_ctr_th_imp_finalize(void)
{
  des_v = pan_ctr_th_rtY.des_v;
}
/*
 * File trailer for generated code.
 *
 * [EOF]
 */
