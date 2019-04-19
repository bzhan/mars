theory FirstPDef
	imports "FirstADef"
begin

(*Define the processes for fuctions.*)
definition min :: "exp => exp => exp" where"min(exp1, exp2) == (if formT(exp1[<]exp2) then exp1 else exp2)"
(*Define the process.*)
definition PFirst1 :: proc where
"PFirst1 == IF (num[=](Real 0)) (<(WTrue) && (WTrue)>:(l[=](Real 1));assSF49;(num:=(Real 1);assSF50;empty(EL);assSF51;(addL EL SE);assSF52;empty(NL);assSF53;(addL NL (Real 1))))"
definition PFirst2 :: proc where
"PFirst2 == IF (num[=](Real 1)) (BC_1!!SE ;assSF54; ((BR_1??SE;assSF55;(addL EL SE);assSF56;(addL NL (Real 1));assSF57;num:=(Real 1)) [[ BO_1??vBO1);assSF58;num:=(num[+](Real 1));assSF59;delL(NL);assSF60;(addL NL num))"
definition PFirst3 :: proc where
"PFirst3 == IF (num[=](Real 2)) (delL(EL);assSF61;delL(NL);assSF62;IF isEmpty(EL) (num:=(Real 0);assSF63;SE:=(String '''');assSF64;Ch_First_1_0!!x;assSF65;Ch_First_1_0!!x);assSF66;IF([~]isEmpty(EL)) (SE:=readL(EL);assSF67;num:=readL(NL)))"
definition PFirst4 :: proc where
"PFirst4 == ((num:=(Real 0);assSF68;SE:=(String '''');assSF69;(actOn:=(Real 0));assSF70;(actOff:=(Real 0)));assSF71;Ch_First_1_0!!x);assSF72;(PFirst1;assSF73;PFirst2;assSF74;PFirst3)*"
definition PFirst5 :: proc where
"PFirst5 == (actOn:=(Real 0));assSF75;(actOff:=(Real 0));assSF76;
(x:=(Real 0);assSF77;;assSF78; x := x [+] (Real 1);assSF79; x := x [+] (Real 1);assSF80;Skip);assSF81;
(BC_1??E1;assSF82;VO1??x1;assSF83;IF (actOn[=](Real 1)) (IF ((done1[=](Real 0))) (actOn:=(Real 0);assSF84; x := x [+] (Real 1);assSF85; x := x [+] (Real 1);assSF86;;assSF87;actOff:=(Real 1);assSF88;done1:=(Real 1)));assSF89;
IF (actOff[=](Real 1)) (IF ((done1[=](Real 0))) (actOff:=(Real 0);assSF90; x := x [+] (Real 1);assSF91; x := x [+] (Real 1);assSF92;;assSF93;actOn:=(Real 1);assSF94;done1:=(Real 1)));assSF95;
BO_1!!(String '''');assSF96;VI1!!x1)*)"
definition PFirst :: proc where
"PFirst == PSecond4||PSecond5||PFirst9||PFirst10"
end
