theory ChartPDef
	imports "ChartADef"
begin

(*Define the processes for fuctions.*)
definition min :: "exp => exp => exp" where"min(exp1, exp2) == (if formT(exp1[<]exp2) then exp1 else exp2)"
(*Define the process.*)
definition PChart1 :: proc where
"PChart1 == IF (num[=](Real 0)) ((<(WTrue) && (WTrue)>:(l[=](Real 1));assSF1;Ch_Integrator_1_2??h);assSF2;(num:=(Real 1);assSF3;empty(EL);assSF4;(addL EL E);assSF5;empty(NL);assSF6;(addL NL (Real 1))))"
definition PChart2 :: proc where
"PChart2 == IF (num[=](Real 1)) (BC_1!!E ;assSF7; ((BR_1??E;assSF8;(addL EL E);assSF9;(addL NL (Real 1));assSF10;num:=(Real 1)) [[ BO_1??vBO1);assSF11;num:=(num[+](Real 1));assSF12;delL(NL);assSF13;(addL NL num))"
definition PChart3 :: proc where
"PChart3 == IF (num[=](Real 2)) (delL(EL);assSF14;delL(NL);assSF15;IF isEmpty(EL) (num:=(Real 0);assSF16;E:=(String '''');assSF17;Ch_Chart_1_0!!v;assSF18;Ch_Chart_1_0!!v);assSF19;IF([~]isEmpty(EL)) (E:=readL(EL);assSF20;num:=readL(NL)))"
definition PChart4 :: proc where
"PChart4 == ((num:=(Real 0);assSF21;E:=(String '''');assSF22;(acton:=(Real 0));assSF23;(actoff:=(Real 0)));assSF24;Ch_Chart_1_0!!v);assSF25;(PChart1;assSF26;PChart2;assSF27;PChart3)*"
definition PChart5 :: proc where
"PChart5 == (acton:=(Real 0));assSF28;(actoff:=(Real 0));assSF29;
(v:=(Real 1);assSF30;v:=(Real 1);assSF31;);assSF32;
(BC_1??E1;assSF33;VO1??h1;assSF34;VO1??v1;assSF35;IF (acton[=](Real 1)) (IF ((done1[=](Real 0))[&]h[>=]5.9) (acton:=(Real 0);assSF36;v:=0;assSF37;v:=0;assSF38;;assSF39;actoff:=(Real 1);assSF40;done1:=(Real 1)));assSF41;
IF (actoff[=](Real 1)) (IF ((done1[=](Real 0))[&]h[<=]4.1) (actoff:=(Real 0);assSF42;v:=(Real 1);assSF43;v:=(Real 1);assSF44;;assSF45;acton:=(Real 1);assSF46;done1:=(Real 1)));assSF47;
BO_1!!(String '''');assSF48;VI1!!h1;assSF49;VI1!!v1)*"
definition PChart :: proc where
"PChart == PChart4||PChart5"
end
