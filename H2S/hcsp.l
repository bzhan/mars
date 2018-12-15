%{
   #include <iostream>
   #include "ArithExpression.h"
   #include "BoolExpression.h"
   #include "DifferentialEquations.h"
   #include "HcspProcess.h"
   #include "hcsp.tab.h"

   static int lineno = 1;

   int yyerror(const string s)
   {
     cout<<s<<" at line "<<lineno<<" token : "<<yytext<<endl;
     return 1;
   }
%}

%%

RVar               return TOKRVAR;
SVar               return TOKSVAR;
BVar               return TOKBVAR;
Real               return TOKKEYREAL;
diff               return TOKKEYDIFF;

skip               {yylval.pspval = yytext; return TOKPSP;}
true|false         {yylval.boolval = yytext; return TOKBOOL;}
True|False         {yylval.fboolval = yytext; return TOKFBOOL;}

LI                 {return TOKPLI;}

ALL                {return TOKFALL;}
EX                 {return TOKFEX;}

\|\|               {return TOKPCON;}

\!                 {return TOKPOUT;}
\?                 {return TOKPIN;}
:=                 {return TOKPASS;}
\&\&               {return TOKPAND;}
\[\[\>             {return TOKPINT;}
\-\>               {return TOKPIMP;}

\;                 {return TOKPSQU;}
\[\[               {return TOKPEXT;}
\*\*               {return TOKPREP;}

\=\>               {return TOKFIMP;}
\<\=\>             {return TOKFEQU;}

\[\=\]             {return TOKBEQ;}
\[\<\]             {return TOKBLT;}
\[\>\]             {return TOKBGT;}
\[\<\=\]           {return TOKBLE;}
\[\>\=\]           {return TOKBGE;}

[a-zA-Z][a-zA-Z0-9_]*         {yylval.varval = yytext; return TOKVAR;}
[0-9]*\.[0-9]+|[0-9]+         {yylval.realval = yytext; return TOKREAL;}
\"[^\"]*\"                    {yylval.constrval = yytext; return TOKSTRING;}

[\-\+\*\/\(\)\,]              return *yytext;
[\~\=\>\<\&\|\']              return *yytext;
\n                            {lineno++;} /*eat '\n'*/
[ \t]+                        /*eat whitespace*/
.                             yyerror("Illegal term");
%%
