//
//  img_acq_imp.c
//  Simulink2C
//
//  Created by Zsio Iung on 2021/3/30.
//  Copyright © 2021 Xiong Xu. All rights reserved.
//

#include "img_acq_imp.h"
//#include "global.h"
#include <stdio.h>

img_acq_DATA img_acq_rtDATA;

void img_acq_imp_initialize()
{
  img_acq_rtDATA.img = img;
}

void img_acq_imp_step()
{
  img_acq_rtDATA.proc_img = img_acq_rtDATA.img;
}

void img_acq_imp_finalize()
{
  proc_img = img_acq_rtDATA.proc_img;
}
