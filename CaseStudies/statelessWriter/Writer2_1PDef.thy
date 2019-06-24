theory Writer2_1PDef
	imports "Writer2_1ADef"
begin

(*Define the processes for fuctions.*)
definition min :: "exp => exp => exp" where"min(exp1, exp2) == (if formT(exp1[<]exp2) then exp1 else exp2)"
(*Define the process.*)
definition PWriter2_11 :: proc where
"PWriter2_11 == IF (num[=](Real 0)) (<(WTrue) && (WTrue)>:(l[=](Real 0.01));assSF1;(num:=(Real 1);assSF2;empty(EL);assSF3;(addL EL SE);assSF4;empty(NL);assSF5;(addL NL (Real 1))))"
definition PWriter2_12 :: proc where
"PWriter2_12 == VO1!!a;assSF6;VO1!!cansend;assSF7;VO1!!flag;assSF8;VO1!!heartbeat;assSF9;VO1!!i"
definition PWriter2_13 :: proc where
"PWriter2_13 == VI1??a;assSF10;VI1??cansend;assSF11;VI1??flag;assSF12;VI1??heartbeat;assSF13;VI1??i"
definition PWriter2_14 :: proc where
"PWriter2_14 == IF (num[=](Real 1)) (BC_1!!SE;assSF14;PWriter2_12 ;assSF15; ((BR_1??SE;assSF16;(addL EL SE);assSF17;(addL NL (Real 1));assSF18;num:=(Real 1)) [[ BO_1??vBO1;assSF19;PWriter2_13);assSF20;num:=(num[+](Real 1));assSF21;delL(NL);assSF22;(addL NL num))"
definition PWriter2_15 :: proc where
"PWriter2_15 == IF (num[=](Real 2)) (delL(EL);assSF23;delL(NL);assSF24;IF isEmpty(EL) (num:=(Real 0);assSF25;SE:=(String '''');assSF26;Skip);assSF27;IF([~]isEmpty(EL)) (SE:=readL(EL);assSF28;num:=readL(NL)))"
definition PWriter2_16 :: proc where
"PWriter2_16 == ((num:=(Real 0);assSF29;SE:=(String '''');assSF30;(actpushing:=(Real 0));assSF31;(actidle:=(Real 0)));assSF32;Skip);assSF33;(PWriter2_11;assSF34;PWriter2_12;assSF35;PWriter2_13)*"
definition PWriter2_17 :: proc where
"PWriter2_17 == (actpushing:=(Real 0));assSF36;(actidle:=(Real 0));assSF37;
(i:=(a);assSF38;Skip;assSF39;heartbeat:=(Real 0);assSF40;heartbeat:=(Real 0);assSF41;Skip;assSF42;actidle:=(Real 1);assSF43;Skip);assSF44;
(BC_1??E1;assSF45;VO1??a1;assSF46;VO1??cansend1;assSF47;VO1??flag1;assSF48;VO1??heartbeat1;assSF49;VO1??i1;assSF50;IF (actpushing[=](Real 1)) (IF ((done1[=](Real 0))[&]i[<=](Real 0)) (actpushing:=(Real 0);assSF51;heartbeat:=(Real 0);assSF52;heartbeat:=(Real 0);assSF53;Skip;assSF54;actidle:=(Real 1);assSF55;done1:=(Real 1));assSF56;
IF ((done1[=](Real 0))) (actpushing:=(Real 0);assSF57;actpushing:=(Real 1);assSF58;done1:=(Real 1));assSF59;
IF (done1[=](Real 0)) (flag:=(Real 0)));assSF60;
IF (actidle[=](Real 1)) (IF ((done1[=](Real 0))[&]i[>](Real 0)) (actidle:=(Real 0);assSF61;actpushing:=(Real 1);assSF62;done1:=(Real 1));assSF63;
IF ((done1[=](Real 0))[&]E1[=](String ''after(heartbeatPeriod,sec)'')) (heartbeat:=(Real 1);assSF64;actidle:=(Real 0);assSF65;heartbeat:=(Real 0);assSF66;Skip;assSF67;actidle:=(Real 1);assSF68;done1:=(Real 1));assSF69;
IF (done1[=](Real 0)) (flag:=(Real 1);assSF70;Skip));assSF71;
BO_1!!(String '''');assSF72;VI1!!a1;assSF73;VI1!!cansend1;assSF74;VI1!!flag1;assSF75;VI1!!heartbeat1;assSF76;VI1!!i1)*"
definition PWriter2_1 :: proc where
"PWriter2_1 == PWriter2_16||PWriter2_17"
end
