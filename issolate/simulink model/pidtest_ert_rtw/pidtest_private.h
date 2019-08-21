/*
 * File: pidtest_private.h
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

#ifndef RTW_HEADER_pidtest_private_h_
#define RTW_HEADER_pidtest_private_h_
#include "rtwtypes.h"

/* Private macros used by the generated code to access rtModel */
#ifndef rtmIsMajorTimeStep
# define rtmIsMajorTimeStep(rtm)       (((rtm)->Timing.simTimeStep) == MAJOR_TIME_STEP)
#endif

#ifndef rtmIsMinorTimeStep
# define rtmIsMinorTimeStep(rtm)       (((rtm)->Timing.simTimeStep) == MINOR_TIME_STEP)
#endif

#ifndef rtmGetTPtr
# define rtmGetTPtr(rtm)               ((rtm)->Timing.t)
#endif

#ifndef rtmSetTPtr
# define rtmSetTPtr(rtm, val)          ((rtm)->Timing.t = (val))
#endif

#ifndef __RTWTYPES_H__
#error This file requires rtwtypes.h to be included
#endif                                 /* __RTWTYPES_H__ */

/* private model entry point functions */
extern void pidtest_derivatives(void);

#endif                                 /* RTW_HEADER_pidtest_private_h_ */

/*
 * File trailer for generated code.
 *
 * [EOF]
 */
