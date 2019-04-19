theory ChartPDef
	imports "ChartADef"
begin

(*Define the processes for fuctions.*)
definition min :: "exp => exp => exp" where"min(exp1, exp2) == (if formT(exp1[<]exp2) then exp1 else exp2)"
(*Define the process.*)
definition PChart1 :: proc where
"PChart1 == IF (num[=](Real 0)) (<(WTrue) && (WTrue)>:(l[=](Real 100));assSF1;(num:=(Real 1);assSF2;empty(EL);assSF3;(addL EL SE);assSF4;empty(NL);assSF5;(addL NL (Real 1))))"
definition PChart2 :: proc where
"PChart2 == IF (num[=](Real 1)) (BC_1!!SE ;assSF6; ((BR_1??SE;assSF7;(addL EL SE);assSF8;(addL NL (Real 1));assSF9;num:=(Real 1)) [[ BO_1??vBO1);assSF10;num:=(num[+](Real 1));assSF11;delL(NL);assSF12;(addL NL num))"
definition PChart3 :: proc where
"PChart3 == IF (num[=](Real 2)) (delL(EL);assSF13;delL(NL);assSF14;IF isEmpty(EL) (num:=(Real 0);assSF15;SE:=(String '''');assSF16;Skip);assSF17;IF([~]isEmpty(EL)) (SE:=readL(EL);assSF18;num:=readL(NL)))"
definition PChart4 :: proc where
"PChart4 == ((num:=(Real 0);assSF19;SE:=(String '''');assSF20;(actFalling:=(Real 0)));assSF21;Skip);assSF22;(PChart1;assSF23;PChart2;assSF24;PChart3)*"

definition p_dot :: exp where
"p_dot == RVar ''p_dot''"
definition v_dot :: exp where
"v_dot == RVar ''v_dot''"

definition PChart5 :: proc where
"PChart5 ==
 (actFalling:=(Real 0)); assSF25;
 (p:=(Real 10);assSF26;v:=(Real 15);assSF27;Skip); assSF28;
 (BC_1??E1; assSF29; VO1??p_out1; assSF30; VO1??v_out1; assSF31; VO1??p1; assSF32; 
  VO1??v1; assSF33;
  IF (actFalling[=](Real 1))
     (IF ((done1[=](Real 0))[&]p[<=](Real 0)[&]v[<](Real 0))
         (p:=(Real 0); assSF34; v:=((Real -0.8)[*]v); assSF35; actFalling:=(Real 0); assSF36;
          actFalling:=(Real 1); assSF37; done1:=(Real 1)) ; assSF38;
      IF (done1[=](Real 0))
         (p_dot:=v; assSF39;
          v_dot:=(Real -9.81);assSF40;
          p_out:=p;assSF41;
          v_out:=v); assSF42;
      BO_1!!(String ''''); assSF43; VI1!!p_out1; assSF44;
      VI1!!v_out1; assSF45; VI1!!p1; assSF46; VI1!!v1)*)"

definition PChart :: proc where
"PChart == PChart4||PChart5"
end
