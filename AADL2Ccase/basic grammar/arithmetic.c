#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <ctype.h>
#include <signal.h>
#include <time.h>
#include <string.h>
#include <math.h>
#include "data_model.h"


typedef struct Arith_Type
{
    char *typeName;
    char *cType;
    char Supported_Operators[];
    char Supported_Relations[];

} Arith_Type;

#define Boolean bool
#define Integer int
#define Float	float
#define Character char
#define String char*

int main()
{
	Arith_Type *Boolean = (Arith_Type *)malloc(sizeof(Arith_Type));
	Boolean->typeName = "Boolean";
	Boolean->cType = "bool";
	Boolean->Supported_Operators = ["+", "-"];
	Boolean->Supported_Relations = ["=", "!="];

	Arith_Type *Integer = (Arith_Type *)malloc(sizeof(Arith_Type));
	Integer->typeName = "Integer";
	Integer->cType = "int";
	Boolean->Supported_Operators = ["+", "*", "-", "/", "mod", "rem", "**"];
	Boolean->Supported_Relations = ["=", "!=", "<", "<=", ">=", ">"];

	Arith_Type *Float = (Arith_Type *)malloc(sizeof(Arith_Type));
	Float->typeName = "Float";
	Float->cType = "float";
	Boolean->Supported_Operators = ["+", "*", "-", "/", "**"];
	Boolean->Supported_Relations = ["=", "!=", "<", "<=", ">=", ">"];

	Arith_Type *Character = (Arith_Type *)malloc(sizeof(Arith_Type));
	Character->typeName = "Character";
	Character->cType = "char";
	Boolean->Supported_Operators = ["+", "-"];
	Boolean->Supported_Relations = ["=", "!=", "<", "<=", ">=", ">"];

	Arith_Type *String = (Arith_Type *)malloc(sizeof(Arith_Type));
	String->typeName = "String";
	String->cType = "char*";
	Boolean->Supported_Operators = ["+", "-"];
	Boolean->Supported_Relations = ["=", "!=", "<", "<=", ">=", ">"];

    


}






