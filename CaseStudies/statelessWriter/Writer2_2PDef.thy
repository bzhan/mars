theory Writer2_2PDef
	imports "Writer2_2ADef"
begin

(*Define the processes for fuctions.*)
definition min :: "exp => exp => exp" where"min(exp1, exp2) == (if formT(exp1[<]exp2) then exp1 else exp2)"
(*Define the process.*)
definition PWriter2_21 :: proc where
"PWriter2_21 == IF (num[=](Real 0)) (<(WTrue) && (WTrue)>:(l[=](Real 0.01));assSF1;(num:=(Real 1);assSF2;empty(EL);assSF3;(addL EL SE);assSF4;empty(NL);assSF5;(addL NL (Real 1))))"
definition PWriter2_22 :: proc where
"PWriter2_22 == VO1!!cansend;assSF6;VO1!!ACKNACK;assSF7;VO1!!flag;assSF8;VO1!!re_changes"
definition PWriter2_23 :: proc where
"PWriter2_23 == VI1??cansend;assSF9;VI1??ACKNACK;assSF10;VI1??flag;assSF11;VI1??re_changes"
definition PWriter2_24 :: proc where
"PWriter2_24 == IF (num[=](Real 1)) (BC_1!!SE;assSF12;PWriter2_22 ;assSF13; ((BR_1??SE;assSF14;(addL EL SE);assSF15;(addL NL (Real 1));assSF16;num:=(Real 1)) [[ BO_1??vBO1;assSF17;PWriter2_23);assSF18;num:=(num[+](Real 1));assSF19;delL(NL);assSF20;(addL NL num))"
definition PWriter2_25 :: proc where
"PWriter2_25 == IF (num[=](Real 2)) (delL(EL);assSF21;delL(NL);assSF22;IF isEmpty(EL) (num:=(Real 0);assSF23;SE:=(String '''');assSF24;Skip);assSF25;IF([~]isEmpty(EL)) (SE:=readL(EL);assSF26;num:=readL(NL)))"
definition PWriter2_26 :: proc where
"PWriter2_26 == ((num:=(Real 0);assSF27;SE:=(String '''');assSF28;(actrepairing:=(Real 0));assSF29;(actwaiting:=(Real 0));assSF30;(actmust_repair:=(Real 0)));assSF31;Skip);assSF32;(PWriter2_21;assSF33;PWriter2_22;assSF34;PWriter2_23)*"
definition PWriter2_27 :: proc where
"PWriter2_27 == (actrepairing:=(Real 0));assSF35;(actwaiting:=(Real 0));assSF36;(actmust_repair:=(Real 0));assSF37;
(re_changes:=(Real 0);assSF38;Skip;assSF39;actwaiting:=(Real 1);assSF40;Skip);assSF41;
(BC_1??E1;assSF42;VO1??cansend1;assSF43;VO1??ACKNACK1;assSF44;VO1??flag1;assSF45;VO1??re_changes1;assSF46;IF (actrepairing[=](Real 1)) (IF ((done1[=](Real 0))[&]re_changes[=](Real 0)) (actrepairing:=(Real 0);assSF47;actwaiting:=(Real 1);assSF48;done1:=(Real 1));assSF49;
IF ((done1[=](Real 0))[&]cansend[=](Real 1)) (re_changes :=( re_changes [-] (Real 1));assSF50;actrepairing:=(Real 0);assSF51;actrepairing:=(Real 1);assSF52;done1:=(Real 1));assSF53;
IF (done1[=](Real 0)) (flag:=(Real 0)));assSF54;
IF (actwaiting[=](Real 1)) (IF ((done1[=](Real 0))[&]re_changes[>](Real 0)) (actwaiting:=(Real 0);assSF55;actmust_repair:=(Real 1);assSF56;done1:=(Real 1));assSF57;
IF ((done1[=](Real 0))[&]ACKNACK[=](Real 1)) (re_changes :=( re_changes [+] (Real 1));assSF58;actwaiting:=(Real 0);assSF59;actwaiting:=(Real 1);assSF60;done1:=(Real 1));assSF61;
IF (done1[=](Real 0)) (flag:=(Real 1);assSF62;Skip));assSF63;
IF (actmust_repair[=](Real 1)) (IF ((done1[=](Real 0))[&]E1[=](String ''after(ResponseDelay,sec)'')) (actmust_repair:=(Real 0);assSF64;actrepairing:=(Real 1);assSF65;done1:=(Real 1));assSF66;
IF ((done1[=](Real 0))[&]ACKNACK[=](Real 1)) (re_changes :=( re_changes [+] (Real 1));assSF67;actmust_repair:=(Real 0);assSF68;actmust_repair:=(Real 1);assSF69;done1:=(Real 1));assSF70;
IF (done1[=](Real 0)) (flag:=(Real 1);assSF71;Skip));assSF72;
BO_1!!(String '''');assSF73;VI1!!cansend1;assSF74;VI1!!ACKNACK1;assSF75;VI1!!flag1;assSF76;VI1!!re_changes1)*"
definition PWriter2_2 :: proc where
"PWriter2_2 == PWriter2_26||PWriter2_27"
end
