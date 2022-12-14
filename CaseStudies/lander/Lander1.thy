
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
      Fc ::= (\<lambda>s. (-(s Fc / s M - 3.732) * 0.01 + 3.732 - (s V - -1.5) * 0.6) * s M);
      T ::= (\<lambda>_. 0);
      Cont (ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s Fc / s M - 3.732), M := (\<lambda>s. s Fc / 2500 * -1), T := (\<lambda>_. 1)))) ((\<lambda>s. s T < 0.128))
    )"


end
