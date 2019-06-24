theory Writer1PDef
	imports "Writer1ADef"
begin

(*Define the processes for fuctions.*)
definition min :: "exp => exp => exp" where"min(exp1, exp2) == (if formT(exp1[<]exp2) then exp1 else exp2)"
(*Define the process.*)
definition PWriter11 :: proc where
"PWriter11 == IF (num[=](Real 0)) (<(WTrue) && (WTrue)>:(l[=](Real 0.01));assSF1;(num:=(Real 1);assSF2;empty(EL);assSF3;(addL EL SE);assSF4;empty(NL);assSF5;(addL NL (Real 1))))"
definition PWriter12 :: proc where
"PWriter12 == IF (num[=](Real 1)) 
              (BC_1!!SE ;assSF6; 
               ((BR_1??SE;assSF7;(addL EL SE);assSF8;(addL NL (Real 1));assSF9;num:=(Real 1)) [[ BO_1??vBO1);assSF10;
               num:=(num[+](Real 1));assSF11;delL(NL);assSF12;(addL NL num))"
definition PWriter13 :: proc where
"PWriter13 == IF (num[=](Real 2)) (delL(EL);assSF13;delL(NL);assSF14;IF isEmpty(EL) (num:=(Real 0);assSF15;SE:=(String '''');assSF16;Skip);assSF17;IF([~]isEmpty(EL)) (SE:=readL(EL);assSF18;num:=readL(NL)))"
definition PWriter14 :: proc where
"PWriter14 == ((num:=(Real 0);assSF19;SE:=(String '''');assSF20;(actpushing:=(Real 0));assSF21;(actidle:=(Real 0)));assSF22;Skip);assSF23;(PWriter11;assSF24;PWriter12;assSF25;PWriter13)*"

definition PWriter15 :: proc where
"PWriter15 == (actpushing:=(Real 0));assSF26;(actidle:=(Real 0));assSF27;
(unsent:=(a);assSF28;Skip;assSF29;actidle:=(Real 1);assSF30;Skip);assSF31;
(BC_1??E1;assSF32;VO1??a1;assSF33;VO1??cansend1;assSF34;VO1??flag1;assSF35;VO1??unsent1;assSF36;
 IF (actpushing[=](Real 1)) 
 (IF ((done1[=](Real 0))[&]unsent[<=](Real 0)) (actpushing:=(Real 0);assSF37;actidle:=(Real 1);assSF38;done1:=(Real 1));assSF39;
  IF ((done1[=](Real 0))[&]cansend[=](Real 1)) (unsent :=( unsent [-] (Real 1));assSF40;actpushing:=(Real 0);assSF41;actpushing:=(Real 1);assSF42;done1:=(Real 1));assSF43;
  IF (done1[=](Real 0)) (flag:=(Real 0))
 );assSF44;
 IF (actidle[=](Real 1)) 
 (IF ((done1[=](Real 0))[&]unsent[>](Real 0)) (actidle:=(Real 0);assSF45;actpushing:=(Real 1);assSF46;done1:=(Real 1));assSF47;
  IF (done1[=](Real 0)) (flag:=(Real 1);assSF48;Skip)
 );assSF49;
 BO_1!!(String '''');assSF50;VI1!!a1;assSF51;VI1!!cansend1;assSF52;VI1!!flag1;assSF53;VI1!!unsent1)*"

definition PWriter1 :: proc where
"PWriter1 == PWriter14||PWriter15"
end
