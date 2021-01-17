
theory Lander2
    imports HHLProver.HHLProver
begin

text \<open>Variables\<close>

definition Fc :: char where "Fc = CHR ''a''"
definition M :: char where "M = CHR ''b''"
definition V :: char where "V = CHR ''c''"


text \<open>Processes\<close>

definition P0 :: proc where
  "P0 =
    Fc ::= (\<lambda>_. 2835);
    Rep (
      Cm (''ch_Fc''[!](\<lambda>s. s Fc));
      Cm (''ch_v''[?]V);
      Cm (''ch_m''[?]M);
      Fc ::= (\<lambda>s. (-(s Fc / s M - 3.732) * 0.01 + 3.732 - (s V - (-1.5)) * 0.6) * s M);
      Wait ((\<lambda>_. 0.128))
    )"

definition P1 :: proc where
  "P1 =
    V ::= (\<lambda>_. -1.5);
    M ::= (\<lambda>_. 759.5);
    Rep (
      Interrupt (ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s Fc / s M - 3.732), M := (\<lambda>s. s Fc / 2500 * (-1))))) ((\<lambda>_. True))
      [(''ch_v''[!](\<lambda>s. s V), Skip), (''ch_m''[!](\<lambda>s. s M), Skip), (''ch_Fc''[?]Fc, Skip)]
    )"


end
