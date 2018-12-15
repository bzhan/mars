%{
  #include "ArithExpression.h"
  #include "BoolExpression.h"
  #include "DifferentialEquations.h"
  #include "HcspProcess.h"

  extern int yyerror(const string s);
  int yylex(void);
%}

%union
{
  char* realval;
  char* boolval;
  char* varval;
  char* constrval;
  char* fboolval;
  char* pspval;
  Node* nPtr;
  ArithExpression* aExp;
  BoolExpression* bExp;
  DifferentialEquations* dEqu;
  HcspProcess* hPro;
};

%token <varval> TOKVAR
%token <realval> TOKREAL
%token <constrval> TOKSTRING
%token <boolval> TOKBOOL
%token <fboolval> TOKFBOOL
%token <pspval> TOKPSP
%token TOKRVAR TOKSVAR TOKBVAR TOKKEYREAL TOKKEYDIFF

%left TOKPCON
%left TOKPSQU TOKPLI TOKPEXT
%nonassoc TOKPREP
%nonassoc TOKPIMP
%nonassoc TOKPASS TOKPAND TOKPINT
%nonassoc TOKPIN TOKPOUT

%nonassoc TOKFALL TOKFEX
%right TOKFEQU               
%right '|' TOKFIMP           
%right '&'                   
%nonassoc '~'               
%left TOKBEQ TOKBLT TOKBGT TOKBLE TOKBGE             

%left '-''+'                 
%left '*''/'                 
%left '('')'
%nonassoc UMINUS

%type <nPtr> proc1 diff1 chout chin cond inter form1 aexp1 rvar var
%type <aExp> aexp
%type <bExp> form
%type <hPro> proc
%type <dEqu> diff

%%

input:
    | input line                
;

line:
    proc                               {$1->printTree($1->getRoot());Simulink::toMdl();}
    /* | diff '\n'                     {$1->printTree($1->getRoot());Simulink::toMdl();} */
    /* | form '\n'                     {$1->printTree($1->getRoot());Simulink::toMdl();} */
;

proc:
    proc1                           {$$ = new HcspProcess($1);$$->autoLayout($$->getRoot());$$->toSimulink($$->getRoot());}

proc1:
     TOKPSP                         {$$ = BasicNode::new_content_Node($1);}
     | chout                        {$$ = $1;}
     | chin                         {$$ = $1;}
     | var TOKPASS aexp             {$$ = BasicNode::new_operator_Node(":=",2,$1,$3->getRoot());}
     | cond                         {$$ = $1;}
     /* | inter                        {$$ = $1;} */
     | cond TOKPINT '(' inter ')'   {$$ = BasicNode::new_operator_Node("[[>",2,$1,$4);}
     | form TOKPIMP proc1           {$$ = BasicNode::new_operator_Node("IMP",2,$1->getRoot(),$3);}
     | proc1 TOKPSQU proc1          {$$ = BasicNode::new_operator_Node(";",2,$1,$3);}
     | proc1 TOKPLI proc1           {$$ = BasicNode::new_operator_Node("LI",2,$1,$3);}
     /* | proc1 TOKPEXT proc1          {$$ = BasicNode::new_operator_Node("[[",2,$1,$3);} */
     | proc1 '*'                    {$$ = BasicNode::new_operator_Node("REP",1,$1);}
     | proc1 TOKPCON proc1          {$$ = BasicNode::new_operator_Node("CON",2,$1,$3);}
     | '('proc1')'                  {$$ = $2;}
;

chin:
    var TOKPIN var                 {$$ = BasicNode::new_operator_Node("?",2,$1,$3);}
;

chout:
     var TOKPOUT aexp              {$$ = BasicNode::new_operator_Node("!",2,$1,$3->getRoot());}
;

cond:
    '<''<' diff TOKPAND form '>''>'      {$$ = BasicNode::new_operator_Node("AND",2,$3->getRoot(),$5->getRoot());}
;

diff:
     diff1                         {$$ = new DifferentialEquations($1);/*$$->autoLayout($$->getRoot());$$->toSimulink($$->getRoot());*/}
;

diff1:
     TOKKEYDIFF '(' var ')' '=' '=' aexp {$$ = BasicNode::new_operator_Node("\'=",2,$3,$7->getRoot());}
     | diff1 ',' diff1             {$$ = BasicNode::new_operator_Node("DIFF",2,$1,$3);}
;

inter:
     chin TOKPIMP proc1            {$$ = BasicNode::new_operator_Node(";",2,$1,$3);}
     | chout TOKPIMP proc1         {$$ = BasicNode::new_operator_Node(";",2,$1,$3);}
     | inter TOKPEXT inter         {$$ = BasicNode::new_operator_Node("[[",2,$1,$3);}
     | '('inter')'                 {$$ = $2;}
;

form:
    form1                         {$$ = new BoolExpression($1);$$->shrinkTree($$->getRoot());/*$$->autoLayout($$->getRoot());$$->toSimulink($$->getRoot());*/}

form1:  
     TOKFBOOL                     {$$ = BasicNode::new_content_Node($1);}
     | aexp TOKBEQ aexp           {$$ = BasicNode::new_operator_Node("=",2,$1->getRoot(),$3->getRoot());}
     | aexp TOKBLT aexp           {$$ = BasicNode::new_operator_Node("<",2,$1->getRoot(),$3->getRoot());}
     | aexp TOKBLE aexp           {$$ = BasicNode::new_operator_Node("<",2,$1->getRoot(),$3->getRoot());}
     | aexp TOKBGT aexp           {$$ = BasicNode::new_operator_Node(">",2,$1->getRoot(),$3->getRoot());}
     | aexp TOKBGE aexp           {$$ = BasicNode::new_operator_Node(">",2,$1->getRoot(),$3->getRoot());}
     | form1 '&' form1           {$$ = BasicNode::new_operator_Node("&",2,$1,$3);}
     | form1 '|' form1           {$$ = BasicNode::new_operator_Node("|",2,$1,$3);}
     | form1 TOKFIMP form1       {$$ = BasicNode::new_operator_Node("|",2,BasicNode::new_operator_Node("~",1,$1),$3);}
     | form1 TOKFEQU form1       {$$ = BasicNode::new_operator_Node("&",2,BasicNode::new_operator_Node("|",2,BasicNode::new_operator_Node("~",1,$1),$3),BasicNode::new_operator_Node("|",2,BasicNode::new_operator_Node("~",1,$3),$1));}
     | TOKFALL var form1         {$$ = BasicNode::new_operator_Node("ALL",2,$2,$3);}
     | TOKFEX var form1          {$$ = BasicNode::new_operator_Node("EX",2,$2,$3);}
     |'~' form1                  {$$ = BasicNode::new_operator_Node("~",1,$2);}
     | '('form1')'               {$$ = $2;}
;

aexp:
    aexp1                        {$$ = new ArithExpression($1);$$->shrinkTree($$->getRoot());//$$->toSimulink($$->getRoot());
}

aexp1:                        
     TOKKEYREAL TOKREAL          {$$ = BasicNode::new_content_Node($2);}
     | TOKKEYREAL '-' TOKREAL    {$$ = BasicNode::new_operator_Node("-",1,BasicNode::new_content_Node($3));}
     | var                       {$$ = $1;}
     | rvar                      {$$ = $1;}
     | aexp1 '+' aexp1           {$$ = BasicNode::new_operator_Node("+",2,$1,$3);} 
     | aexp1 '-' aexp1           {$$ = BasicNode::new_operator_Node("-",2,$1,$3);}
     | aexp1 '*' aexp1           {$$ = BasicNode::new_operator_Node("*",2,$1,$3);} 
     | aexp1 '/' aexp1           {$$ = BasicNode::new_operator_Node("/",2,$1,$3);}
     | '-' aexp1 %prec UMINUS    {$$ = BasicNode::new_operator_Node("-",1,$2);}
     | '('aexp1')'               {$$ = $2;}
;

rvar:
    TOKRVAR var              {$$ = BasicNode::mod_index_Node("RVar",$2);}
;

var:
    TOKVAR                   {$$ = BasicNode::new_index_Node("",BasicNode::transVar($1));}
;

%%

int yywrap()
{
  return 1;
}

int main(int argc,char **argv)
{
  yyparse();
  return 0;
}
