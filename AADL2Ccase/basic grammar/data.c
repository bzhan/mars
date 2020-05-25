#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <ctype.h>
#include <signal.h>
#include <time.h>
#include <string.h>
#include <math.h>
#include "data_model.h"


typedef struct Base_Type
{
    char *typeName;
    char *cType;

} Base_Type;

#define Boolean bool
#define Integer int
#define Float	float
#define Character char
#define String char*

int main()
{
	Base_Type *Boolean = (Base_Type *)malloc(sizeof(Base_Type));
	Boolean->typeName = "Boolean";
	Boolean->cType = "bool";

	Base_Type *Integer = (Base_Type *)malloc(sizeof(Base_Type));
	Integer->typeName = "Integer";
	Integer->cType = "int";

	Base_Type *Float = (Base_Type *)malloc(sizeof(Base_Type));
	Float->typeName = "Float";
	Float->cType = "float";

	Base_Type *Character = (Base_Type *)malloc(sizeof(Base_Type));
	Character->typeName = "Character";
	Character->cType = "char";

	Base_Type *String = (Base_Type *)malloc(sizeof(Base_Type));
	String->typeName = "String";
	String->cType = "char*";

    


}






