
theory Lander1
    imports HHLProver.HHLProver
begin

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

lemma test3:
  fixes t :: real and v :: real and w :: real
  shows "157.012952954 + 141.341201479 * t + 58.1598340769 * v - 60.7449205372 * w + 1008.28101708 * t^2 - 309.691980674 * t * v + 10.860795109 * v^2 - 200.880013191 * t * w - 6.83268943808 * v * w + 6.77142466675 * w^2 + 5.49958984968 * t^3 - 658.038845577 * t^2 * v - 177.484858505 * t * v^2 - 0.000109226476568 * v^3 - 806.123988697 * t^2 * w - 60.1986626786 * t * v * w + 0.000654569168604 * v^2 * w + 14.7503967518 * t * w^2 - 0.00205162606814 * v * w^2 - 0.00201138823846 * w^3 + 359.760061472 * t^4 - 47.9842001641 * t^3 * v + 952.749881726 * t^2 * v^2 - 0.00010078396595 * t * v^3 - 4.31991776136 * 10 ^(0 - 9) * v^4 - 45.8590909182 * t^3 * w + 946.414495353 * t^2 * v * w - 0.0006047037957 * t * v^2 * w - 3.45593420909 * 10 ^ (0 - 8) * v^3 * w + 299.922922376 * t^2 * w^2 + 0.0183019308754 * t * v * w^2 + 8.10354315198 * 10^(0-8) * v^2 * w^2 + 0.0118438941894 * t * w^3 + 2.34662253376 * 10^(0-7) * v * w^3 + 3.3965365482 * 10^(0-7)*w^4\<ge>0"
  apply (simp add:power2_eq_square power3_eq_cube power4_eq_xxxx)
  sorry


lemma test4:
  fixes t :: real and v :: real and w :: real
  shows "122.922143264 + 230.196370173 * t + 28.1829661815 * v - 54.5632660846*w+6.90571475568 * v^2-1.99190578286 * v *w+6.91824015655*w^2-0.000117062088517 * v^3+0.000815452777971 * v^2*w-0.00201558412314 * v *w^2-0.00198623306063*w^3-1.37292117664*10^(0-8) * v^4-1.09833694131*10^(0-7)* v^3*w+7.29891062357*10^(0-8)* v^2*w^2+1.45359209693*10^(0-7)* v *w^3+2.12960370373*10^(0-7)*w^4-130.387297739*t*w-17.6283709313*t * v-154.758635072*t* v^2-119.786803239*t* v *w-6.65875161084*t*w^2-0.000119087360197*t * v^3+0.0116024568726*t*w^3+0.0179354226975*t* v *w^2-0.00071452416118*t * v^2*w+1483.86882388*t^2-1337.53293434*t^2*w-1347.21078785*t^2* v+1278.77339856*t^2* v^2+1389.78792947* t^2 * v * w + 458.847359266 * t^2 * w^2 \<ge> 0"
  apply (simp add:power2_eq_square power3_eq_cube power4_eq_xxxx)
  sorry
  
  
 

end
