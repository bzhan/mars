/*
 * File: emerg_imp.h
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

#ifndef RTW_HEADER_emerg_imp_h_
#define RTW_HEADER_emerg_imp_h_
#include <math.h>
#ifndef emerg_imp_COMMON_INCLUDES_
# define emerg_imp_COMMON_INCLUDES_
#include "rtwtypes.h"
#endif                                 /* emerg_imp_COMMON_INCLUDES_ */

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
  uint8_T is_active_c3_emerg_imp;      /* '<Root>/emerg_imp' */
} emerg_DW;

/* External inputs (root inport signals with default storage) */
typedef struct {
  real_T obs_pos;                      /* '<Root>/obs_pos' */
  real_T veh_pos;                      /* '<Root>/veh_pos' */
  real_T veh_v;                        /* '<Root>/veh_v' */
  real_T des_a;                        /* '<Root>/des_a' */
} emerg_ExtU;

/* External outputs (root outports fed by signals with default storage) */
typedef struct {
  real_T cmd;                          /* '<Root>/cmd' */
} emerg_ExtY;

/* Real-time Model Data Structure */
//struct tag_RTM {
//  const char_T * volatile errorStatus;
//};

/* Block signals and states (default storage) */
extern emerg_DW emerg_rtDW;

/* External inputs (root inport signals with default storage) */
extern emerg_ExtU emerg_rtU;

/* External outputs (root outports fed by signals with default storage) */
extern emerg_ExtY emerg_rtY;

/* Model entry point functions */
extern void emerg_imp_initialize(void);
extern void emerg_imp_step(void);
extern void emerg_imp_finalize(void);

extern float obs_pos, cmd, veh_pos, veh_v, des_a;
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
 * '<Root>' : 'emerg_imp'
 * '<S1>'   : 'emerg_imp/emerg_imp'
 */
#endif                                 /* RTW_HEADER_emerg_imp_h_ */

/*
 * File trailer for generated code.
 *
 * [EOF]
 */
