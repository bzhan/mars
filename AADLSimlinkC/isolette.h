/*
 * File: isolette.h
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

#ifndef RTW_HEADER_isolette_h_
#define RTW_HEADER_isolette_h_
#include <string.h>
#ifndef isolette_COMMON_INCLUDES_
# define isolette_COMMON_INCLUDES_
#include "rtwtypes.h"
#include "rtw_continuous.h"
#include "rtw_solver.h"
#endif                                 /* isolette_COMMON_INCLUDES_ */

#include "isolette_types.h"

/* Macros for accessing real-time model data structure */
#ifndef rtmGetErrorStatus
# define rtmGetErrorStatus(rtm)        ((rtm)->errorStatus)
#endif

#ifndef rtmSetErrorStatus
# define rtmSetErrorStatus(rtm, val)   ((rtm)->errorStatus = (val))
#endif

#ifndef rtmGetStopRequested
# define rtmGetStopRequested(rtm)      ((rtm)->Timing.stopRequestedFlag)
#endif

#ifndef rtmSetStopRequested
# define rtmSetStopRequested(rtm, val) ((rtm)->Timing.stopRequestedFlag = (val))
#endif

#ifndef rtmGetStopRequestedPtr
# define rtmGetStopRequestedPtr(rtm)   (&((rtm)->Timing.stopRequestedFlag))
#endif

#ifndef rtmGetT
# define rtmGetT(rtm)                  (rtmGetTPtr((rtm))[0])
#endif

/* Block signals (auto storage) */
typedef struct {
  real_T Gain;                         /* '<S1>/Gain' */
  real_T Switch;                       /* '<S1>/Switch' */
} B_isolette_T;

/* Block states (auto storage) for system '<Root>' */
typedef struct {
  int_T Integrator1_IWORK;             /* '<S1>/Integrator1' */
  int_T Integrator_IWORK;              /* '<S1>/Integrator' */
} DW_isolette_T;

/* Continuous states (auto storage) */
typedef struct {
  real_T Integrator1_CSTATE;           /* '<S1>/Integrator1' */
  real_T Integrator_CSTATE;            /* '<S1>/Integrator' */
} X_isolette_T;

/* State derivatives (auto storage) */
typedef struct {
  real_T Integrator1_CSTATE;           /* '<S1>/Integrator1' */
  real_T Integrator_CSTATE;            /* '<S1>/Integrator' */
} XDot_isolette_T;

/* State disabled  */
typedef struct {
  boolean_T Integrator1_CSTATE;        /* '<S1>/Integrator1' */
  boolean_T Integrator_CSTATE;         /* '<S1>/Integrator' */
} XDis_isolette_T;

/* Invariant block signals (auto storage) */
typedef struct {
  const real_T Constant1;              /* '<Root>/Constant1' */
  const real_T Constant;               /* '<Root>/Constant' */
} ConstB_isolette_T;

#ifndef ODE3_INTG
#define ODE3_INTG

/* ODE3 Integration Data */
typedef struct {
  real_T *y;                           /* output */
  real_T *f[3];                        /* derivatives */
} ODE3_IntgData;

#endif

/* External inputs (root inport signals with auto storage) */
typedef struct {
  real_T In1;                          /* '<Root>/In1' */
} ExtU_isolette_T;

/* External outputs (root outports fed by signals with auto storage) */
typedef struct {
  real_T Out1;                         /* '<Root>/Out1' */
} ExtY_isolette_T;

/* Real-time Model Data Structure */
struct tag_RTM_isolette_T {
  const char_T *errorStatus;
  RTWSolverInfo solverInfo;

  /*
   * ModelData:
   * The following substructure contains information regarding
   * the data used in the model.
   */
  struct {
    X_isolette_T *contStates;
    int_T *periodicContStateIndices;
    real_T *periodicContStateRanges;
    real_T *derivs;
    boolean_T *contStateDisabled;
    boolean_T zCCacheNeedsReset;
    boolean_T derivCacheNeedsReset;
    boolean_T blkStateChange;
    real_T odeY[2];
    real_T odeF[3][2];
    ODE3_IntgData intgData;
  } ModelData;

  /*
   * Sizes:
   * The following substructure contains sizes information
   * for many of the model attributes such as inputs, outputs,
   * dwork, sample times, etc.
   */
  struct {
    int_T numContStates;
    int_T numPeriodicContStates;
    int_T numSampTimes;
  } Sizes;

  /*
   * Timing:
   * The following substructure contains information regarding
   * the timing information for the model.
   */
  struct {
    uint32_T clockTick0;
    time_T stepSize0;
    uint32_T clockTick1;
    boolean_T firstInitCondFlag;
    SimTimeStep simTimeStep;
    boolean_T stopRequestedFlag;
    time_T *t;
    time_T tArray[2];
  } Timing;
};

/* Block signals (auto storage) */
extern B_isolette_T isolette_B;

/* Continuous states (auto storage) */
extern X_isolette_T isolette_X;

/* Block states (auto storage) */
extern DW_isolette_T isolette_DW;

/* External inputs (root inport signals with auto storage) */
extern ExtU_isolette_T isolette_U;

/* External outputs (root outports fed by signals with auto storage) */
extern ExtY_isolette_T isolette_Y;
extern const ConstB_isolette_T isolette_ConstB;/* constant block i/o */

/* Model entry point functions */
extern void isolette_initialize(void);
extern void isolette_step(void);
extern void isolette_terminate(void);

/* Real-time Model object */
extern RT_MODEL_isolette_T *const isolette_M;

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
 * '<Root>' : 'isolette'
 * '<S1>'   : 'isolette/Subsystem'
 */
#endif                                 /* RTW_HEADER_isolette_h_ */

/*
 * File trailer for generated code.
 *
 * [EOF]
 */
