theory ChartPDef
	imports "ChartADef"
begin

(*Define the processes for fuctions.*)
definition min :: "exp => exp => exp" where"min(exp1, exp2) == (if formT(exp1[<]exp2) then exp1 else exp2)"
(*Define the process.*)
definition PChart1 :: proc where
"PChart1 == (actOn:=(Real 0));assSF1;(actOff:=(Real 0));assSF2;
(flag:=(Real 1);assSF3;flag:=(Real 1);assSF4;);assSF5;
(BC_1??E1;assSF6;VO1??a1;assSF7;VO1??flag1;assSF8;IF (actOn[=](Real 1)) (IF ((done1[=](Real 0))[&]a[>=](Real 0)) (actOn:=(Real 0);assSF9;flag:=(Real 1);assSF10;flag:=(Real 1);assSF11;;assSF12;actOff:=(Real 1);assSF13;done1:=(Real 1)));assSF14;
IF (actOff[=](Real 1)) (IF ((done1[=](Real 0))[&]a[>]0) (actOff:=(Real 0);assSF15;flag:=0;assSF16;flag:=0;assSF17;;assSF18;actOn:=(Real 1);assSF19;done1:=(Real 1)));assSF20;
BO_1!!(String '''');assSF21;VI1!!a1;assSF22;VI1!!flag1)*"
definition PChart :: proc where
"PChart == PChart1"
end
