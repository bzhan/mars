/*
 * File: velo_voter_imp.h
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

#ifndef RTW_HEADER_velo_voter_imp_h_
#define RTW_HEADER_velo_voter_imp_h_
#ifndef velo_voter_imp_COMMON_INCLUDES_
# define velo_voter_imp_COMMON_INCLUDES_
#include "rtwtypes.h"
#include "rtw_continuous.h"
#include "rtw_solver.h"
#endif                                 /* velo_voter_imp_COMMON_INCLUDES_ */

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

/* External inputs (root inport signals with default storage) */
typedef struct {
  real_T wheel_valid;                  /* '<Root>/wheel_valid' */
  real_T wheel_v;                      /* '<Root>/wheel_v' */
  real_T laser_valid;                  /* '<Root>/laser_valid' */
  real_T laser_v;                      /* '<Root>/laser_v' */
} velo_voter_ExtU;

/* External outputs (root outports fed by signals with default storage) */
typedef struct {
  real_T veh_v;                        /* '<Root>/veh_v' */
} velo_voter_ExtY;

/* Real-time Model Data Structure */
//struct tag_RTM {
//  const char_T * volatile errorStatus;
//};

/* External inputs (root inport signals with default storage) */
extern velo_voter_ExtU velo_voter_rtU;

/* External outputs (root outports fed by signals with default storage) */
extern velo_voter_ExtY velo_voter_rtY;

/* Model entry point functions */
extern void velo_voter_imp_initialize(void);
extern void velo_voter_imp_step(void);
extern void velo_voter_imp_finalize(void);

extern float laser_valid, laser_v, wheel_valid, wheel_v, veh_v;
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
 * '<Root>' : 'velo_voter_imp'
 */
#endif                                 /* RTW_HEADER_velo_voter_imp_h_ */

/*
 * File trailer for generated code.
 *
 * [EOF]
 */
