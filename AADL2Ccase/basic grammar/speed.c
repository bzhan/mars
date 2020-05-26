#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <ctype.h>
#include <signal.h>
#include <time.h>
#include <string.h>
#include <math.h>
#include "data_model.h"




//Size Unit
#define bits 1
#define Bytes bits * 8
#define KByte Bytes * 1000
#define MByte KByte * 1000
#define	GByte MByte * 1000
#define TByte GByte * 1000


//Time Unit
//ps, ns => ps * 1000, us => ns * 1000, ms => us * 1000, 
//sec => ms * 1000, min => sec * 60, hr => min * 60);
#define ps 1
#define ns ps * 1000
#define us ns * 1000
#define ms us * 1000
#define sec ms * 1000
#define min sec * 60
#define hr min * 60


//Rate Unit
//Data_Rate_Units: type	units (bitsps, Bytesps => bitsps * 8, KBytesps => Bytesps * 1000,
// MBytesps => KBytesps * 1000, GBytesps => MBytesps * 1000);

#define bitsps 1
#define Bytesps bitsps * 8
#define KByteps Bytesps * 1000
#define MByteps KByteps * 1000
#define	GByteps MByteps * 1000
#define TByteps GByteps * 1000


//Processor_Speed_Units: type units (KIPS, MIPS => KIPS * 1000, GIPS => MIPS * 1000);
#define KIPS 1
#define MIPS KIPS * 1000
#define GIPS MIPS * 1000

