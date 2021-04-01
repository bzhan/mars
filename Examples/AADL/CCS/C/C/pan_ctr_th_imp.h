/*
 * File: pan_ctr_th_imp.h
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

#ifndef RTW_HEADER_pan_ctr_th_imp_h_
#define RTW_HEADER_pan_ctr_th_imp_h_
#ifndef pan_ctr_th_imp_COMMON_INCLUDES_
# define pan_ctr_th_imp_COMMON_INCLUDES_
#include "rtwtypes.h"
#include "zero_crossing_types.h"
#include "rtw_continuous.h"
#include "rtw_solver.h"
#endif                                 /* pan_ctr_th_imp_COMMON_INCLUDES_ */

/* Macros for accessing real-time model data structure */
//#ifndef rtmGetErrorStatus
//# define rtmGetErrorStatus(rtm)        ((rtm)->errorStatus)
//#endif
//
//#ifndef rtmSetErrorStatus
//# define rtmSetErrorStatus(rtm, val)   ((rtm)->errorStatus = (val))
//#endif

/* Forward declaration for rtModel */
// typedef struct tag_RTM RT_MODEL;

/* Block signals and states (default storage) for system '<Root>' */
typedef struct {
  uint8_T is_active_c3_pan_ctr_th_imp; /* '<Root>/pan_ctr_th_imp' */
} pan_ctr_th_DW;

/* Zero-crossing (trigger) state */
typedef struct {
  ZCSigState pan_ctr_th_imp_Trig_ZCE[2];/* '<Root>/pan_ctr_th_imp' */
} PrevZCX;

/* External inputs (root inport signals with default storage) */
typedef struct {
  real_T inc;                          /* '<Root>/inc' */
  real_T dec;                          /* '<Root>/dec' */
} pan_ctr_th_ExtU;

/* External outputs (root outports fed by signals with default storage) */
typedef struct {
  real_T des_v;                        /* '<Root>/des_v' */
} pan_ctr_th_ExtY;

/* Real-time Model Data Structure */
//struct tag_RTM {
//  const char_T * volatile errorStatus;
//};

/* Block signals and states (default storage) */
extern pan_ctr_th_DW pan_ctr_th_rtDW;

/* External inputs (root inport signals with default storage) */
extern pan_ctr_th_ExtU pan_ctr_th_rtU;

/* External outputs (root outports fed by signals with default storage) */
extern pan_ctr_th_ExtY pan_ctr_th_rtY;

/* Model entry point functions */
extern void pan_ctr_th_imp_initialize(void);
extern void pan_ctr_th_imp_step(void);
extern void pan_ctr_th_imp_finalize(void);

extern float des_v;
//extern Queue inc_buffer, dec_buffer;
/* Real-time Model object */
// extern RT_MODEL *const rtM;

/*-
 * The generated code includes comments that allow you to trace directly
 * back to the appropriate location in the model.  The basic format
 * is <system>/block_name, where system is the system number (uniquely
 * assigned by Simulink) and block_name is the name of the block.
 *
 * Use the MATLAB hilite_system command to trace the generated code back
 * to the model.  For example,
 *
 * hilite_system('<S3>')    - opens system 3
 * hilite_system('<S3>/Kp') - opens and selects block Kp which resides in S3
 *
 * Here is the system hierarchy for this model
 *
 * '<Root>' : 'pan_ctr_th_imp'
 * '<S1>'   : 'pan_ctr_th_imp/pan_ctr_th_imp'
 */
#endif                                 /* RTW_HEADER_pan_ctr_th_imp_h_ */

/*
 * File trailer for generated code.
 *
 * [EOF]
 */
