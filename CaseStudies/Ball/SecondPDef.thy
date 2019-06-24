theory SecondPDef
	imports "SecondADef"
begin

(*Define the processes for fuctions.*)
definition min :: "exp => exp => exp" where"min(exp1, exp2) == (if formT(exp1[<]exp2) then exp1 else exp2)"
(*Define the process.*)
definition PSecond1 :: proc where
"PSecond1 == IF (num[=](Real 0)) ((<(WTrue) && (WTrue)>:(l[=](Real 1));assSF1;Ch_First_1_0??x);assSF2;(num:=(Real 1);assSF3;empty(EL);assSF4;(addL EL E);assSF5;empty(NL);assSF6;(addL NL (Real 1))))"
definition PSecond2 :: proc where
"PSecond2 == IF (num[=](Real 1)) (BC_1!!E ;assSF7; ((BR_1??E;assSF8;(addL EL E);assSF9;(addL NL (Real 1));assSF10;num:=(Real 1)) [[ BO_1??vBO1);assSF11;num:=(num[+](Real 1));assSF12;delL(NL);assSF13;(addL NL num))"
definition PSecond3 :: proc where
"PSecond3 == IF (num[=](Real 2)) (delL(EL);assSF14;delL(NL);assSF15;IF isEmpty(EL) (num:=(Real 0);assSF16;E:=(String '''');assSF17;);assSF18;IF([~]isEmpty(EL)) (E:=readL(EL);assSF19;num:=readL(NL)))"
definition PSecond4 :: proc where
"PSecond4 == ((num:=(Real 0);assSF20;E:=(String '''');assSF21;(actOn:=(Real 0));assSF22;(actOff:=(Real 0)));assSF23;);assSF24;(PSecond1;assSF25;PSecond2;assSF26;PSecond3)*"
definition PSecond5 :: proc where
"PSecond5 == (actOn:=(Real 0));assSF27;(actOff:=(Real 0));assSF28;
( y := 2 * x;assSF29; y := 2 * x;assSF30;);assSF31;
(BC_1??E1;assSF32;VO1??x1;assSF33;VO1??y1;assSF34;IF (actOn[=](Real 1)) (IF ((done1[=](Real 0))) (actOn:=(Real 0);assSF35; y := y + 10;assSF36; y := y + 10;assSF37;;assSF38;actOff:=(Real 1);assSF39;done1:=(Real 1)));assSF40;
IF (actOff[=](Real 1)) (IF ((done1[=](Real 0))) (actOff:=(Real 0);assSF41; y := 2 * x;assSF42; y := 2 * x;assSF43;;assSF44;actOn:=(Real 1);assSF45;done1:=(Real 1)));assSF46;
BO_1!!(String '''');assSF47;VI1!!x1;assSF48;VI1!!y1)*"
definition PSecond :: proc where
"PSecond == PSecond4||PSecond5"
end
