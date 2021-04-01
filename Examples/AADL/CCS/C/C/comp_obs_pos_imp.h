/*
 * File: comp_obs_pos_imp.h
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

#ifndef RTW_HEADER_comp_obs_pos_imp_h_
#define RTW_HEADER_comp_obs_pos_imp_h_
#include <math.h>
#ifndef comp_obs_pos_imp_COMMON_INCLUDES_
# define comp_obs_pos_imp_COMMON_INCLUDES_
#include "rtwtypes.h"
#include "rtw_continuous.h"
#include "rtw_solver.h"
#endif                                 /* comp_obs_pos_imp_COMMON_INCLUDES_ */

/* Macros for accessing real-time model data structure */
//#ifndef rtmGetErrorStatus
//# define rtmGetErrorStatus(rtm)        ((rtm)->errorStatus)
//#endif

//#ifndef rtmSetErrorStatus
//# define rtmSetErrorStatus(rtm, val)   ((rtm)->errorStatus = (val))
//#endif

/* Forward declaration for rtModel */
// typedef struct tag_RTM RT_MODEL;

/* External inputs (root inport signals with default storage) */
typedef struct {
  real_T proc_img;                     /* '<Root>/proc_img' */
  real_T obs_pos_radar;                /* '<Root>/obs_pos_radar' */
} comp_obs_pos_ExtU;

/* External outputs (root outports fed by signals with default storage) */
typedef struct {
  real_T obs_pos;                      /* '<Root>/obs_pos' */
} comp_obs_pos_ExtY;

/* Real-time Model Data Structure */
// struct tag_RTM {
//  const char_T * volatile errorStatus;
// };

/* External inputs (root inport signals with default storage) */
extern comp_obs_pos_ExtU comp_obs_pos_rtU;

/* External outputs (root outports fed by signals with default storage) */
extern comp_obs_pos_ExtY comp_obs_pos_rtY;

/* Model entry point functions */
extern void comp_obs_pos_imp_initialize(void);
extern void comp_obs_pos_imp_step(void);
extern void comp_obs_pos_imp_finalize(void);

extern float proc_img, obs_pos_radar, obs_pos;
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
 * '<Root>' : 'comp_obs_pos_imp'
 */
#endif                                 /* RTW_HEADER_comp_obs_pos_imp_h_ */

/*
 * File trailer for generated code.
 *
 * [EOF]
 */
