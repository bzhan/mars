theory Writer1PDef
	imports "Writer1ADef"
begin

(*Define the processes for fuctions.*)
definition min :: "exp => exp => exp" where"min(exp1, exp2) == (if formT(exp1[<]exp2) then exp1 else exp2)"
(*Define the process.*)
definition PWriter11 :: proc where
"PWriter11 == IF (num[=](Real 0)) (<(WTrue) && (WTrue)>:(l[=](Real 0.01));assSF1;(num:=(Real 1);assSF2;empty(EL);assSF3;(addL EL SE);assSF4;empty(NL);assSF5;(addL NL (Real 1))))"
definition PWriter12 :: proc where
"PWriter12 == VO1!!a;assSF6;VO1!!cansend;assSF7;VO1!!flag;assSF8;VO1!!unsent"
definition PWriter13 :: proc where
"PWriter13 == VI1??a;assSF9;VI1??cansend;assSF10;VI1??flag;assSF11;VI1??unsent"
definition PWriter14 :: proc where
"PWriter14 == IF (num[=](Real 1)) (BC_1!!SE;assSF12;PWriter12 ;assSF13; ((BR_1??SE;assSF14;(addL EL SE);assSF15;(addL NL (Real 1));assSF16;num:=(Real 1)) [[ BO_1??vBO1;assSF17;PWriter13);assSF18;num:=(num[+](Real 1));assSF19;delL(NL);assSF20;(addL NL num))"
definition PWriter15 :: proc where
"PWriter15 == IF (num[=](Real 2)) (delL(EL);assSF21;delL(NL);assSF22;IF isEmpty(EL) (num:=(Real 0);assSF23;SE:=(String '''');assSF24;Skip);assSF25;IF([~]isEmpty(EL)) (SE:=readL(EL);assSF26;num:=readL(NL)))"
definition PWriter16 :: proc where
"PWriter16 == ((num:=(Real 0);assSF27;SE:=(String '''');assSF28;(actpushing:=(Real 0));assSF29;(actidle:=(Real 0)));assSF30;Skip);assSF31;(PWriter11;assSF32;PWriter12;assSF33;PWriter13)*"
definition PWriter17 :: proc where
"PWriter17 == (actpushing:=(Real 0));assSF34;(actidle:=(Real 0));assSF35;
(unsent:=(a);assSF36;Skip;assSF37;actidle:=(Real 1);assSF38;Skip);assSF39;
(BC_1??E1;assSF40;VO1??a1;assSF41;VO1??cansend1;assSF42;VO1??flag1;assSF43;VO1??unsent1;assSF44;IF (actpushing[=](Real 1)) (IF ((done1[=](Real 0))[&]unsent[<=](Real 0)) (actpushing:=(Real 0);assSF45;actidle:=(Real 1);assSF46;done1:=(Real 1));assSF47;
IF ((done1[=](Real 0))[&]cansend[=](Real 1)) (unsent :=( unsent [-] (Real 1));assSF48;actpushing:=(Real 0);assSF49;actpushing:=(Real 1);assSF50;done1:=(Real 1));assSF51;
IF (done1[=](Real 0)) (flag:=(Real 0)));assSF52;
IF (actidle[=](Real 1)) (IF ((done1[=](Real 0))[&]unsent[>](Real 0)) (actidle:=(Real 0);assSF53;actpushing:=(Real 1);assSF54;done1:=(Real 1));assSF55;
IF (done1[=](Real 0)) (flag:=(Real 1);assSF56;Skip));assSF57;
BO_1!!(String '''');assSF58;VI1!!a1;assSF59;VI1!!cansend1;assSF60;VI1!!flag1;assSF61;VI1!!unsent1)*"
definition PWriter1 :: proc where
"PWriter1 == PWriter16||PWriter17"
end
