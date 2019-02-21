theory ChartPDef
	imports "ChartADef"
begin

(*Define the processes for fuctions.*)
definition min :: "exp => exp => exp" where"min(exp1, exp2) == (if formT(exp1[<]exp2) then exp1 else exp2)"
(*Define the process.*)
definition PChart1 :: proc where
"PChart1 == IF (num[=](Real 0)) (<(WTrue) && (WTrue)>:(l[=](Real inf));assSF1;(num:=(Real 1);assSF2;empty(EL);assSF3;(addL EL E);assSF4;empty(NL);assSF5;(addL NL (Real 1))))"
definition PChart2 :: proc where
"PChart2 == IF (num[=](Real 1)) (BC_1!!E ;assSF6; ((BR_1??E;assSF7;(addL EL E);assSF8;(addL NL (Real 1));assSF9;num:=(Real 1)) [[ BO_1??vBO1);assSF10;num:=(num[+](Real 1));assSF11;delL(NL);assSF12;(addL NL num))"
definition PChart3 :: proc where
"PChart3 == IF (num[=](Real 2)) (delL(EL);assSF13;delL(NL);assSF14;IF isEmpty(EL) (num:=(Real 0);assSF15;E:=(String '''');assSF16;);assSF17;IF([~]isEmpty(EL)) (E:=readL(EL);assSF18;num:=readL(NL)))"
definition PChart4 :: proc where
"PChart4 == ((num:=(Real 0);assSF19;E:=(String '''');assSF20;(actOn:=(Real 0));assSF21;(actOff:=(Real 0)));assSF22;);assSF23;(PChart1;assSF24;PChart2;assSF25;PChart3)*"
definition PChart5 :: proc where
"PChart5 == (actOn:=(Real 0));assSF26;(actOff:=(Real 0));assSF27;
(flag:=(Real 1);assSF28;flag:=(Real 1);assSF29;);assSF30;
(BC_1??E1;assSF31;VO1??a1;assSF32;VO1??flag1;assSF33;IF (actOn[=](Real 1)) (IF ((done1[=](Real 0))[&]a[>=](Real 0)) (actOn:=(Real 0);assSF34;flag:=(Real 1);assSF35;flag:=(Real 1);assSF36;;assSF37;actOff:=(Real 1);assSF38;done1:=(Real 1)));assSF39;
IF (actOff[=](Real 1)) (IF ((done1[=](Real 0))[&]a[>]0) (actOff:=(Real 0);assSF40;flag:=0;assSF41;flag:=0;assSF42;;assSF43;actOn:=(Real 1);assSF44;done1:=(Real 1)));assSF45;
BO_1!!(String '''');assSF46;VI1!!a1;assSF47;VI1!!flag1)*"
definition PChart :: proc where
"PChart == PChart4||PChart5"
end
