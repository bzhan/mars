//
//  img_acq_imp.h
//  Simulink2C
//
//  Created by Zsio Iung on 2021/3/30.
//  Copyright © 2021 Xiong Xu. All rights reserved.
//
#include "rtwtypes.h"

typedef struct
{
  real_T img;
  real_T proc_img;
} img_acq_DATA;

extern img_acq_DATA img_acq_rtDATA;

extern void img_acq_imp_initialize(void);
extern void img_acq_imp_step(void);
extern void img_acq_imp_finalize(void);
extern float img, proc_img;
