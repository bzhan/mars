
theory Lander1
    imports HHLProver.HHLProver
begin

definition landerinv :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
"landerinv t V F m = (-1139598426176000000000*F^2 + 6016579819909859424000*F*m - 
 15025282795421706426953*m^2 + 6579819920896000000000*F^2*t - 
 32152462695621728000000*F*m*t + 38191371615549881350000*m^2*t - 
 63926169690400000000*F*m*t^2 - 9482947285373987200000*m^2*t^2 + 
 90382078252408000000*m^2*t^3 + 12597135205472000000*m^2*t^4 - 
 1659591880613072768000*F*m*V - 5070724623344300111384*m^2*V + 
 11298598523808000000000*F*m*t*V - 29051341984741759604000*m^2*t*V - 
 12905500940447680000000*m^2*t^2*V + 3452247087952000000*m^2*t^3*V - 
 2216823024256000*F*m*V^2 - 3754952256975690758168*m^2*V^2 + 
 4369639740028640264000*m^2*t*V^2 - 
 4290324517728000000000*m^2*t^2*V^2 - 10509874347360*m^2*V^3 + 
 8711967253392000*m^2*t*V^3 - 1751645724560*m^2*V^4)/(1/(160000000000000000000*m^2))"


text \<open>Variables\<close>

definition Fc :: char where "Fc = CHR ''a''"
definition M :: char where "M = CHR ''b''"
definition T :: char where "T = CHR ''c''"
definition V :: char where "V = CHR ''d''"


text \<open>Processes\<close>

definition P0 :: proc where
  "P0 =
    Fc ::= (\<lambda>_. 2835);
    V ::= (\<lambda>_. -1.5);
    M ::= (\<lambda>_. 759.5);
    Rep (
      Fc ::= (\<lambda>s. (-(s Fc / s M - 3.732) * 0.01 + 3.732 - (s V - (-1.5)) * 0.6) * s M);
      T ::= (\<lambda>_. 0);
      Cont (ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s Fc / s M - 3.732), M := (\<lambda>s. s Fc / 2500 * (-1)), T := (\<lambda>_. 1)))) ((\<lambda>s. s T < 0.128))
    )"

lemma test:
  fixes a :: real and 
    b :: real
  shows "a\<^sup>2 + 2 * a * b + b\<^sup>2 \<ge> 0"
  by sos

lemma test2:
  fixes a :: real and 
    b :: real
  shows "0.386144 * a\<^sup>2 + 0.342381 * a * b + 0.174365 * b\<^sup>2 \<ge> 0"
  by sos



end
