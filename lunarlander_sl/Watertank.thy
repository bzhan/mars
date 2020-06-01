theory Watertank
  imports BigStep
begin


locale watertank =
  fixes Qmax :: real and
    r :: real and
    g :: real and
    period :: real
  assumes
    Qmax_val: "Qmax = 0.007" and
    r_val: "r = 0.0254" and
    g_val: "g = 9.8" and
    period_val: "period = 0.01"
begin

definition H :: char where "H = CHR ''h''"
definition V :: char where "V = CHR ''v''"
definition T :: char where "T = CHR ''t''"

lemma vars_distinct: "H \<noteq> V" "V \<noteq> H" "H \<noteq> T" "T \<noteq> H" "V \<noteq> T" "T \<noteq> V"
  unfolding H_def V_def T_def by auto

definition plant :: proc where
  "plant = Rep (
    T ::= (\<lambda>_. 0);
    Cont (ODE ((\<lambda>_ _. 0)(H := (\<lambda>s. s V * Qmax - pi * r^2 * sqrt(2 * g * s H)), T := (\<lambda>_. 1)))) (\<lambda>s. s T < period);
    Cm (''wl''[!](\<lambda>s. s H));
    Cm (''cc''[?]V))"

definition controller :: proc where
  "controller = Rep (
    Wait period;
    Cm (''wl''[?]H);
    (IF (\<lambda>s. s H \<le> 0.31) (V ::= (\<lambda>_. 1)) Skip);
    (IF (\<lambda>s. s H \<ge> 0.59) (V ::= (\<lambda>_. 0)) Skip);
    Cm (''cc''[!](\<lambda>s. s V)))"

definition model :: pproc where
  "model = PProc [plant, controller]"


end



end
