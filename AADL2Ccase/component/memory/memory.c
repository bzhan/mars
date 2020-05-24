#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <ctype.h>
#include <signal.h>
#include <time.h>
#include <string.h>
#include <math.h>
#include "isolette.h"
#include "rtwtypes.h"

/** type struct definition of components 
------------------------------------------------------
  System Component: system
  Hardware Component: processor memory bus device
  Software Component: process thread subprogram 
------------------------------------------------------  
**/

typedef struct Memory
{
    int tid; /* The ID of a memory */
    int Byte_count;
    char *line_size;
    char *cache_type;
    char *Set_associativity;
    char *write_policy;
    char *replacement_policy;
    int cache_level;
    int set_size;
    char *cache_coherency_protocol;

} Memory;



int main()
{
    Thread *l1_cache = (Memory *)malloc(sizeof(Memory));
    l1_cache->tid = 1; /* The ID of a memory */
    l1_cache->Byte_count = 8000;
    l1_cache->line_size = 32Bytes;
    l1_cache->cache_type = Instruction_Cache;
    l1_cache->Set_associativity = Set_Associative;
    l1_cache->write_policy = No_Allocated_Write_Through;
    l1_cache->replacement_policy = LRR;
    l1_cache->cache_level = 1;
    l1_cache->set_size = 2;
    l1_cache->cache_coherency_protocol = Private_Invalid;


}