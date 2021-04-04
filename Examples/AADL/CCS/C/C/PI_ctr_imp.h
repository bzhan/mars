/*
 * File: PI_ctr_imp.h
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

#ifndef RTW_HEADER_PI_ctr_imp_h_
#define RTW_HEADER_PI_ctr_imp_h_
#ifndef PI_ctr_imp_COMMON_INCLUDES_
# define PI_ctr_imp_COMMON_INCLUDES_
#include "rtwtypes.h"
#endif                                 /* PI_ctr_imp_COMMON_INCLUDES_ */

/* Macros for accessing real-time model data structure */

/* Block signals and states (default storage) for system '<Root>' */
typedef struct {
  real_T Integrator_DSTATE;            /* '<S1>/Integrator' */
} PI_ctr_DW;

/* External inputs (root inport signals with default storage) */
typedef struct {
  real_T des_v;                        /* '<Root>/des_v' */
  real_T veh_v;                        /* '<Root>/veh_v' */
} PI_ctr_ExtU;

/* External outputs (root outports fed by signals with default storage) */
typedef struct {
  real_T des_a;                        /* '<Root>/des_a' */
} PI_ctr_ExtY;

/* Block signals and states (default storage) */
extern PI_ctr_DW PI_ctr_rtDW;

/* External inputs (root inport signals with default storage) */
extern PI_ctr_ExtU PI_ctr_rtU;

/* External outputs (root outports fed by signals with default storage) */
extern PI_ctr_ExtY PI_ctr_rtY;

/* Model entry point functions */
extern void PI_ctr_imp_initialize(void);
extern void PI_ctr_imp_step(void);
extern void PI_ctr_imp_finalize(void);

extern float veh_v, des_v, des_a;
/*-
 * These blocks were eliminated from the model due to optimizations:
 *
 * Block '<S1>/Integral Gain' : Eliminated nontunable gain of 1
 * Block '<S1>/Kb' : Eliminated nontunable gain of 1
 * Block '<S1>/Proportional Gain' : Eliminated nontunable gain of 1
 */

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
 * '<Root>' : 'PI_ctr_imp'
 * '<S1>'   : 'PI_ctr_imp/Discrete PID Controller'
 */
#endif                                 /* RTW_HEADER_PI_ctr_imp_h_ */

/*
 * File trailer for generated code.
 *
 * [EOF]
 */
