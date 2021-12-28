theory Scratch
  imports Complex_Main Ordinary_Differential_Equations.Flow
begin

(*
datatype val =
    Nil
  | Str string
  | Real real
  | Array "val list"

term "Real 3"
term "Array [Real 2, Str ''abc'']"
term "Array [Array [Real 2, Real 3], Array [Real 1, Real 2]]"
*)



type_synonym var = char

type_synonym state = "char \<Rightarrow> real"

type_synonym exp = "state \<Rightarrow> real"

type_synonym fform = "state \<Rightarrow> bool"

type_synonym 'a ext_state = "'a \<times> state"

type_synonym 'a ext_exp = "'a ext_state \<Rightarrow> real"

type_synonym 'a ext_fform = "'a ext_state \<Rightarrow> bool"

type_synonym cname = string

type_synonym rdy_info = "cname set \<times> cname set"


(*
datatype scheduler =
  sch (pool:"(int \<times> string) list") (run_now:int) (run_prior:int)
*)

datatype scheduler =
  sch (pool:"(int \<times> string) list")

datatype 'a comm =
  Send cname "'a ext_exp"        ("_[!]_" [110,108] 100)
| Receive cname var     ("_[?]_" [110,108] 100)

(*
fun Estatelist :: "scheduler ext_state \<Rightarrow> (int \<times> string) list" where
  "Estatelist ((sch a b c) , d) = a"
*)

fun Estatelist :: "scheduler ext_state \<Rightarrow> (int \<times> string) list" where
  "Estatelist (sch a , d) = a"

datatype 'a proc =
  Cm "'a comm"
| Skip
| Assign var "'a ext_exp"             ("_ ::= _" [99,95] 94)
| Basic "'a \<Rightarrow> 'a"
| Seq "'a proc" "'a proc"           ("_; _" [91,90] 90)
| Wait "'a ext_exp"

datatype 'a gstate =
  EmptyState
| EState "'a ext_state"
| ParState "'a gstate"  "'a gstate"


datatype 'a pproc =
  Single "'a proc"
| Parallel "'a pproc" "cname set" "'a pproc"


datatype comm_type = In | Out | IO

datatype 'a trace_block =
  CommBlock comm_type cname real
| WaitBlock ereal "real \<Rightarrow> 'a gstate" rdy_info

abbreviation "InBlock ch v \<equiv> CommBlock In ch v"
abbreviation "OutBlock ch v \<equiv> CommBlock Out ch v"
abbreviation "IOBlock ch v \<equiv> CommBlock IO ch v"

fun WaitBlk :: "ereal \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> 'a trace_block" where
  "WaitBlk (ereal d) p rdy = WaitBlock (ereal d) (\<lambda>\<tau>\<in>{0..d}. p \<tau>) rdy"
| "WaitBlk PInfty p rdy = WaitBlock PInfty (\<lambda>\<tau>\<in>{0..}. p \<tau>) rdy"
| "WaitBlk MInfty p rdy = WaitBlock MInfty (\<lambda>_. undefined) rdy"

lemma WaitBlk_simps [simp]:
  "WaitBlk (ereal d) p rdy = WaitBlock (ereal d) (\<lambda>\<tau>\<in>{0..d}. p \<tau>) rdy"
  "WaitBlk \<infinity> p rdy = WaitBlock \<infinity> (\<lambda>\<tau>\<in>{0..}. p \<tau>) rdy"
  "WaitBlk (-\<infinity>) p rdy = WaitBlock (-\<infinity>) (\<lambda>_. undefined) rdy"
  apply auto
  using WaitBlk.simps(2) infinity_ereal_def 
  apply metis
  using WaitBlk.simps(3) 
  by (metis MInfty_eq_minfinity)

declare WaitBlk.simps [simp del]

lemma WaitBlk_not_Comm [simp]:
  "WaitBlk d p rdy \<noteq> CommBlock ch_type ch v"
  "CommBlock ch_type ch v \<noteq> WaitBlk d p rdy"
  by (cases d, auto)+


lemma restrict_cong_to_eq:
  fixes x :: real
  shows "restrict p1 {0..t} = restrict p2 {0..t} \<Longrightarrow> 0 \<le> x \<Longrightarrow> x \<le> t \<Longrightarrow> p1 x = p2 x"
  apply (auto simp add: restrict_def) by metis

lemma restrict_cong_to_eq2:
  fixes x :: real
  shows "restrict p1 {0..} = restrict p2 {0..} \<Longrightarrow> 0 \<le> x \<Longrightarrow> p1 x = p2 x"
  apply (auto simp add: restrict_def) by metis

lemma WaitBlk_ext:
  fixes t1 t2 :: ereal
    and hist1 hist2 :: "real \<Rightarrow> 'a gstate"
  shows "t1 = t2 \<Longrightarrow>
   (\<And>\<tau>::real. 0 \<le> \<tau> \<Longrightarrow> \<tau> \<le> t1 \<Longrightarrow> hist1 \<tau> = hist2 \<tau>) \<Longrightarrow> rdy1 = rdy2 \<Longrightarrow>
   WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2"
  apply (cases t1)
  apply (auto simp add: restrict_def)
  apply (rule ext) by auto

lemma WaitBlk_ext_real:
  fixes t1 :: real
    and t2 :: real
  shows "t1 = t2 \<Longrightarrow> (\<And>\<tau>. 0 \<le> \<tau> \<Longrightarrow> \<tau> \<le> t1 \<Longrightarrow> hist1 \<tau> = hist2 \<tau>) \<Longrightarrow> rdy1 = rdy2 \<Longrightarrow>
         WaitBlk (ereal t1) hist1 rdy1 = WaitBlk (ereal t2) hist2 rdy2"
  by (auto simp add: restrict_def)

lemma WaitBlk_cong:
  "WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2 \<Longrightarrow> t1 = t2 \<and> rdy1 = rdy2"
  apply (cases t1) by (cases t2, auto)+

lemma WaitBlk_cong2:
  assumes "WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2"
    and "0 \<le> t" "t \<le> t1"
  shows "hist1 t = hist2 t"
proof -
  have a: "t1 = t2" "rdy1 = rdy2"
    using assms WaitBlk_cong 
    by blast+
  show ?thesis
  proof (cases t1)
    case (real r)
    have real2: "t2 = ereal r"
      using real a by auto
    show ?thesis
      using assms(1)[unfolded real real2]
      apply auto using restrict_cong_to_eq assms ereal_less_eq(3) real by blast
  next
    case PInf
    have PInf2: "t2 = \<infinity>"
      using PInf a by auto
    show ?thesis
      using assms(1)[unfolded PInf PInf2] restrict_cong_to_eq2 assms by auto
  next
    case MInf
    show ?thesis
      using assms MInf by auto
  qed
qed

lemma WaitBlk_split1:
  fixes t1 :: real
  assumes "WaitBlk t p1 rdy = WaitBlk t p2 rdy"
    and "0 < t1" "ereal t1 < t"
  shows "WaitBlk (ereal t1) p1 rdy = WaitBlk (ereal t1) p2 rdy"
proof (cases t)
  case (real r)
  show ?thesis
    apply auto apply (rule ext) subgoal for x
      using assms[unfolded real] 
      using restrict_cong_to_eq[of p1 r p2 x] by auto
    done
next
  case PInf
  show ?thesis
    apply auto apply (rule ext) subgoal for x
      using assms[unfolded PInf] restrict_cong_to_eq2[of p1 p2 x] by auto
    done
next
  case MInf
  then show ?thesis
    using assms by auto
qed

lemma WaitBlk_split2:
  fixes t1 :: real
  assumes "WaitBlk t p1 rdy = WaitBlk t p2 rdy"
    and "0 < t1" "ereal t1 < t"
  shows "WaitBlk (t - ereal t1) (\<lambda>\<tau>::real. p1 (\<tau> + t1)) rdy =
         WaitBlk (t - ereal t1) (\<lambda>\<tau>::real. p2 (\<tau> + t1)) rdy"
proof (cases t)
  case (real r)
  have a: "t - ereal t1 = ereal (r - t1)"
    unfolding real by auto
  show ?thesis
    unfolding a apply auto apply (rule ext) subgoal for x
      using assms[unfolded real]
      using restrict_cong_to_eq[of p1 r p2 "x + t1"] by auto
    done
next
  case PInf
  have a: "t - ereal t1 = \<infinity>"
    unfolding PInf by auto
  show ?thesis
    unfolding a
    apply auto
    apply (rule ext) subgoal for x
      using assms[unfolded PInf] restrict_cong_to_eq2[of p1 p2 "x + t1"] by auto
    done
next
  case MInf
  then show ?thesis
    using assms by auto
qed

lemmas WaitBlk_split = WaitBlk_split1 WaitBlk_split2
declare WaitBlk_simps [simp del]

type_synonym 'a trace = "'a trace_block list"

type_synonym 'a tassn = "'a trace \<Rightarrow> bool"


inductive big_step :: "'a proc \<Rightarrow> 'a ext_state \<Rightarrow> 'a trace \<Rightarrow> 'a ext_state \<Rightarrow> bool" where
  skipB: "big_step Skip s [] s"
| assignB: "big_step (var ::= e) (a,s) [] (a,s(var := e (a,s)))"
| seqB: "big_step p1 s1 tr1 s2 \<Longrightarrow>
         big_step p2 s2 tr2 s3 \<Longrightarrow>
         big_step (p1; p2) s1 (tr1 @ tr2) s3"
| basicB: "big_step (Basic f) (a,s) [] (f a, s)"
| sendB1: "big_step (Cm (ch[!]e)) s [OutBlock ch (e s)] s"
| sendB2: "(d::real) > 0 \<Longrightarrow> big_step (Cm (ch[!]e)) s
            [WaitBlk d (\<lambda>_. EState s) ({ch}, {}),
             OutBlock ch (e s)] s"
| receiveB1: "big_step (Cm (ch[?]var)) (a,s) [InBlock ch v] (a,s(var := v))"
| receiveB2: "(d::real) > 0 \<Longrightarrow> big_step (Cm (ch[?]var)) (a,s)
            [WaitBlk d (\<lambda>_. EState (a,s)) ({}, {ch}),
             InBlock ch v] (a,s(var := v))"
| waitB1: "e s > 0 \<Longrightarrow> big_step (Wait e) s [WaitBlk (e s) (\<lambda>_. EState s) ({}, {})] s"
| waitB2: "\<not> e s > 0 \<Longrightarrow> big_step (Wait e) s [] s"

inductive_cases skipE: "big_step Skip s1 tr s2"
inductive_cases assignE: "big_step (Assign var e) s1 tr s2"
inductive_cases sendE: "big_step (Cm (ch[!]e)) s1 tr s2"
inductive_cases receiveE: "big_step (Cm (ch[?]var)) s1 tr s2"
inductive_cases seqE: "big_step (Seq p1 p2) s1 tr s2"
inductive_cases basicE: "big_step (Basic f) s1 tr s2"
inductive_cases waitE: "big_step (Wait e) s1 tr s2"

type_synonym 'a assn = "'a ext_state \<Rightarrow> 'a trace \<Rightarrow> bool"

definition Valid :: "'a assn \<Rightarrow> 'a proc \<Rightarrow> 'a assn \<Rightarrow> bool" ("\<Turnstile> ({(1_)}/ (_)/ {(1_)})" 50) where
  "\<Turnstile> {P} c {Q} \<longleftrightarrow> (\<forall>s1 tr1 s2 tr2. P s1 tr1 \<longrightarrow> big_step c s1 tr2 s2 \<longrightarrow> Q s2 (tr1 @ tr2))"

definition entails :: "'a assn \<Rightarrow> 'a assn \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>A" 25) where
  "(P \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<forall>s tr. P s tr \<longrightarrow> Q s tr)"

lemma entails_refl [simp]:
  "P \<Longrightarrow>\<^sub>A P"
  unfolding entails_def by auto

lemma entails_trans:
  "(P \<Longrightarrow>\<^sub>A Q) \<Longrightarrow> (Q \<Longrightarrow>\<^sub>A R) \<Longrightarrow> (P \<Longrightarrow>\<^sub>A R)"
  unfolding entails_def by auto

lemma Valid_ex_pre:
  "(\<And>v. \<Turnstile> {P v} c {Q}) \<Longrightarrow> \<Turnstile> {\<lambda>s t. \<exists>v. P v s t} c {Q}"
  unfolding Valid_def by auto

lemma Valid_ex_post:
  "\<exists>v. \<Turnstile> {P} c {Q v} \<Longrightarrow> \<Turnstile> {P} c {\<lambda>s t. \<exists>v. Q v s t}"
  unfolding Valid_def by blast

lemma Valid_and_pre:
  "(P1 \<Longrightarrow> \<Turnstile> {P} c {Q}) \<Longrightarrow> \<Turnstile> {\<lambda>s t. P1 \<and> P s t} c {Q}"
  unfolding Valid_def by auto

theorem Valid_weaken_pre:
  "P \<Longrightarrow>\<^sub>A P' \<Longrightarrow> \<Turnstile> {P'} c {Q} \<Longrightarrow> \<Turnstile> {P} c {Q}"
  unfolding Valid_def entails_def by blast

theorem Valid_strengthen_post:
  "Q \<Longrightarrow>\<^sub>A Q' \<Longrightarrow> \<Turnstile> {P} c {Q} \<Longrightarrow> \<Turnstile> {P} c {Q'}"
  unfolding Valid_def entails_def by blast

theorem Valid_skip:
  "\<Turnstile> {P} Skip {P}"
  unfolding Valid_def
  by (auto elim: skipE)

theorem Valid_assign:
  "\<Turnstile> {\<lambda>(a,s). Q (a,s(var := e (a,s)))} var ::= e {Q}"
  unfolding Valid_def
  by (auto elim: assignE)

theorem Valid_send:
  "\<Turnstile> {\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]) \<and>
              (\<forall>d::real>0. Q s (tr @ [WaitBlk d (\<lambda>_. EState s) ({ch}, {}), OutBlock ch (e s)]))}
       Cm (ch[!]e) {Q}"
  unfolding Valid_def
  by (auto elim: sendE)

theorem Valid_receive:
  "\<Turnstile> {\<lambda>(a,s) tr. (\<forall>v. Q (a,s(var := v)) (tr @ [InBlock ch v])) \<and>
              (\<forall>d::real>0. \<forall>v. Q (a,s(var := v))
                (tr @ [WaitBlk d (\<lambda>_. EState (a,s)) ({}, {ch}), InBlock ch v]))}
       Cm (ch[?]var) {Q}"
  unfolding Valid_def
  by (auto elim: receiveE)

theorem Valid_seq:
  "\<Turnstile> {P} c1 {Q} \<Longrightarrow> \<Turnstile> {Q} c2 {R} \<Longrightarrow> \<Turnstile> {P} c1; c2 {R}"
  unfolding Valid_def
  apply (auto elim!: seqE) by fastforce

theorem Valid_basic:
  "\<Turnstile> {\<lambda>(a,s). Q (f a,s)} Basic f {Q}"
  unfolding Valid_def
  by (auto elim: basicE)

theorem Valid_wait:
  "\<Turnstile> {\<lambda>s tr. if e s > 0 then 
                Q s (tr @ [WaitBlk (e s) (\<lambda>_. EState s) ({}, {})])
              else Q s tr} Wait e {Q}"
  unfolding Valid_def
  by (auto elim: waitE)

definition entails_tassn :: "'a tassn \<Rightarrow> 'a tassn \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>t" 25) where
  "(P \<Longrightarrow>\<^sub>t Q) \<longleftrightarrow> (\<forall>tr. P tr \<longrightarrow> Q tr)"

lemma entails_tassn_refl [simp]:
  "P \<Longrightarrow>\<^sub>t P"
  unfolding entails_tassn_def by auto

lemma entails_tassn_trans:
  "(P \<Longrightarrow>\<^sub>t Q) \<Longrightarrow> (Q \<Longrightarrow>\<^sub>t R) \<Longrightarrow> (P \<Longrightarrow>\<^sub>t R)"
  unfolding entails_tassn_def by auto

lemma entails_tassn_ex_pre:
  "(\<And>x. P x \<Longrightarrow>\<^sub>t Q) \<Longrightarrow> (\<lambda>tr. (\<exists>x. P x tr)) \<Longrightarrow>\<^sub>t Q"
  by (auto simp add: entails_tassn_def)

lemma entails_tassn_ex_post:
  "(\<exists>x. P \<Longrightarrow>\<^sub>t Q x) \<Longrightarrow> P \<Longrightarrow>\<^sub>t (\<lambda>tr. (\<exists>x. Q x tr))"
  by (auto simp add: entails_tassn_def)

definition emp_assn :: "'a tassn" ("emp\<^sub>t") where
  "emp\<^sub>t = (\<lambda>tr. tr = [])"

definition join_assn :: "'a tassn \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" (infixr "@\<^sub>t" 65) where
  "P @\<^sub>t Q = (\<lambda>tr. \<exists>tr1 tr2. P tr1 \<and> Q tr2 \<and> tr = tr1 @ tr2)"

definition magic_wand_assn :: "'a tassn \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" (infixr "@-" 65) where
  "Q @- P = (\<lambda>tr. \<forall>tr1. Q tr1 \<longrightarrow> P (tr @ tr1))"

definition all_assn :: "('b \<Rightarrow> 'a tassn) \<Rightarrow> 'a tassn" (binder "\<forall>\<^sub>t" 10) where
  "(\<forall>\<^sub>tv. P v) = (\<lambda>tr. \<forall>v. P v tr)"

definition ex_assn :: "('b \<Rightarrow> 'a tassn) \<Rightarrow> 'a tassn" (binder "\<exists>\<^sub>t" 10) where
  "(\<exists>\<^sub>tv. P v) = (\<lambda>tr. \<exists>v. P v tr)"

definition conj_assn :: "'a tassn \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" (infixr "\<and>\<^sub>t" 35) where
  "(P \<and>\<^sub>t Q) = (\<lambda>tr. P tr \<and> Q tr)"

definition disj_assn :: "'a tassn \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" (infixr "\<or>\<^sub>t" 25) where
  "(P \<or>\<^sub>t Q) = (\<lambda>tr. P tr \<or> Q tr)"

definition imp_assn :: "'a tassn \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" (infixr "\<longrightarrow>\<^sub>t" 25) where
  "(P \<longrightarrow>\<^sub>t Q) = (\<lambda>tr. P tr \<longrightarrow> Q tr)"

definition pure_assn :: "bool \<Rightarrow> 'a tassn" ("\<up>") where
  "\<up>b = (\<lambda>_. b)"

inductive out_assn :: "'a gstate \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> 'a tassn" ("Out\<^sub>t") where
  "Out\<^sub>t s ch v [OutBlock ch v]"
| "(d::real) > 0 \<Longrightarrow> Out\<^sub>t s ch v [WaitBlk (ereal d) (\<lambda>_. s) ({ch}, {}), OutBlock ch v]"

inductive in_assn :: "'a gstate \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> 'a tassn" ("In\<^sub>t") where
  "In\<^sub>t s ch v [InBlock ch v]"
| "(d::real) > 0 \<Longrightarrow> In\<^sub>t s ch v [WaitBlk (ereal d) (\<lambda>_. s) ({}, {ch}), InBlock ch v]"

inductive io_assn :: "cname \<Rightarrow> real \<Rightarrow> 'a tassn" ("IO\<^sub>t") where
  "IO\<^sub>t ch v [IOBlock ch v]"

inductive wait_assn :: "real \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> 'a tassn" ("Wait\<^sub>t") where
  "d > 0 \<Longrightarrow> Wait\<^sub>t d p rdy [WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy]"
| "d \<le> 0 \<Longrightarrow> Wait\<^sub>t d p rdy []"


lemma emp_unit_left [simp]:
  "(emp\<^sub>t @\<^sub>t P) = P"
  unfolding join_assn_def emp_assn_def by auto

lemma emp_unit_right [simp]:
  "(P @\<^sub>t emp\<^sub>t) = P"
  unfolding join_assn_def emp_assn_def by auto

lemma join_assoc:
  "(P @\<^sub>t Q) @\<^sub>t R = P @\<^sub>t (Q @\<^sub>t R)"
  unfolding join_assn_def by fastforce

lemma entails_mp_emp:
  "emp\<^sub>t \<Longrightarrow>\<^sub>t P @- P"
  unfolding entails_tassn_def emp_assn_def magic_wand_assn_def by auto

lemma entails_mp:
  "Q \<Longrightarrow>\<^sub>t P @- (Q @\<^sub>t P)"
  unfolding entails_tassn_def magic_wand_assn_def join_assn_def by auto

lemma magic_wand_mono:
  "P \<Longrightarrow>\<^sub>t Q \<Longrightarrow> (R @- P) \<Longrightarrow>\<^sub>t (R @- Q)"
  unfolding entails_tassn_def magic_wand_assn_def by auto

definition false_assn :: "'a tassn" ("false\<^sub>A") where
  "false_assn tr = False"

lemma false_assn_entails [simp]:
  "false\<^sub>A \<Longrightarrow>\<^sub>t P"
  by (simp add: entails_tassn_def false_assn_def)

lemma pure_assn_entails [simp]:
  "(\<up>b \<and>\<^sub>t P \<Longrightarrow>\<^sub>t Q) = (b \<longrightarrow> P \<Longrightarrow>\<^sub>t Q)"
  unfolding entails_tassn_def conj_assn_def pure_assn_def by auto

lemma entails_tassn_cancel_left:
  "Q \<Longrightarrow>\<^sub>t R \<Longrightarrow> P @\<^sub>t Q \<Longrightarrow>\<^sub>t P @\<^sub>t R"
  by (auto simp add: entails_tassn_def join_assn_def)

lemma entails_tassn_cancel_right:
  "P \<Longrightarrow>\<^sub>t Q \<Longrightarrow> P @\<^sub>t R \<Longrightarrow>\<^sub>t Q @\<^sub>t R"
  by (auto simp add: entails_tassn_def join_assn_def)

lemma entails_tassn_cancel_both:
  "P \<Longrightarrow>\<^sub>t Q \<Longrightarrow> R \<Longrightarrow>\<^sub>t S \<Longrightarrow> P @\<^sub>t R \<Longrightarrow>\<^sub>t Q @\<^sub>t S"
  by (auto simp add: entails_tassn_def join_assn_def)

lemma entails_tassn_conj:
  "P \<Longrightarrow>\<^sub>t Q \<Longrightarrow> P \<Longrightarrow>\<^sub>t R \<Longrightarrow> P \<Longrightarrow>\<^sub>t (Q \<and>\<^sub>t R)"
  by (auto simp add: entails_tassn_def conj_assn_def)

lemma entails_tassn_exI:
  "P \<Longrightarrow>\<^sub>t Q x \<Longrightarrow> P \<Longrightarrow>\<^sub>t (\<exists>\<^sub>t x. Q x)"
  unfolding ex_assn_def entails_tassn_def by auto

lemma conj_join_distrib [simp]:
  "(\<up>b \<and>\<^sub>t P) @\<^sub>t Q = (\<up>b \<and>\<^sub>t (P @\<^sub>t Q))"
  by (auto simp add: join_assn_def conj_assn_def pure_assn_def)

lemma conj_join_distrib2 [simp]:
  "(\<lambda>tr. b \<and> P tr) @\<^sub>t Q = (\<up>b \<and>\<^sub>t (P @\<^sub>t Q))"
  by (auto simp add: pure_assn_def conj_assn_def join_assn_def)

lemma false_join:
"Q \<Longrightarrow>\<^sub>t false\<^sub>A \<Longrightarrow> (P @\<^sub>t Q) \<Longrightarrow>\<^sub>t false\<^sub>A"
  by(auto simp add: entails_tassn_def false_assn_def join_assn_def)

lemma wait_le_zero [simp]:
  "d \<le> 0 \<Longrightarrow> Wait\<^sub>t d p rdy = emp\<^sub>t"
  apply (rule ext) subgoal for tr
    apply auto
     apply (cases rule: wait_assn.cases)
    apply (auto simp add: emp_assn_def)
    by (auto intro: wait_assn.intros)
  done

text \<open>Simpler forms of weakest precondition\<close>

theorem Valid_send':
  "\<Turnstile> {\<lambda>s. Out\<^sub>t (EState s) ch (e s) @- Q s}
       Cm (ch[!]e)
      {Q}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_send)
  unfolding entails_def magic_wand_assn_def
  by (auto intro: out_assn.intros)

theorem Valid_receive':
  "\<Turnstile> {\<lambda>(a,s). \<forall>\<^sub>tv. In\<^sub>t (EState (a,s)) ch v @- Q (a,s(var := v))}
       Cm (ch[?]var)
      {Q}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_receive)
  unfolding entails_def magic_wand_assn_def all_assn_def
  by (simp add: in_assn.intros(1) in_assn.intros(2))

theorem Valid_wait':
  "\<Turnstile>
    {\<lambda>s. if e s > 0 then Wait\<^sub>t (e s) (\<lambda>_. EState s) ({}, {}) @- Q s else Q s}
      Wait e
    {Q}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_wait)
  unfolding entails_def magic_wand_assn_def
  by (auto intro: wait_assn.intros)


text \<open>Strongest postcondition forms\<close>

theorem Valid_assign_sp:
  "\<Turnstile> {\<lambda>(a,s) t. P (a,s) t}
       Assign var e
      {\<lambda>(a,s) t. \<exists>x. s var = e (a,s(var := x)) \<and> P (a,s(var := x)) t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_assign)
  apply (auto simp add: entails_def)
  subgoal for a s tr
    apply (rule exI[where x="s var"])
    by auto
  done

theorem Valid_basic_sp:
  "\<Turnstile> {\<lambda>(a,s) t. P (a,s) t}
       Basic f
      {\<lambda>(a,s) t. \<exists>x. a = f x \<and> P (x,s) t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_basic)
  by (auto simp add: entails_def)
  

theorem Valid_send_sp:
  "\<Turnstile> {\<lambda>s t. P s t}
       Cm (ch[!]e)
     {\<lambda>s t. (P s @\<^sub>t Out\<^sub>t (EState s) ch (e s)) t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_send')
  by (auto simp add: entails_def magic_wand_assn_def join_assn_def)

theorem Valid_receive_sp:
  "\<Turnstile> {\<lambda>(a,s) t. P (a,s) t}
       Cm (ch[?]var)
      {\<lambda>(a,s) t. \<exists>x v. (\<up>(s var = v) \<and>\<^sub>t (P(a,s(var := x)) @\<^sub>t In\<^sub>t (EState (a,s(var := x))) ch v)) t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_receive)
  unfolding entails_def
  apply (auto simp add: join_assn_def)
  subgoal for a s tr v
    apply (rule exI[where x="s var"])
    apply (rule exI[where x=v])
    apply (auto simp add: conj_assn_def pure_assn_def)
    apply (rule exI[where x=tr]) by (auto intro: in_assn.intros)
  subgoal for a s tr d v
    apply (rule exI[where x="s var"])
    apply (rule exI[where x=v])
    apply (auto simp add: conj_assn_def pure_assn_def)
    apply (rule exI[where x=tr])
    apply auto apply (rule in_assn.intros) by auto
  done

theorem Valid_wait_sp:
  "\<Turnstile> {\<lambda>s t. P s t}
      Wait e
     {\<lambda>s t. (P s @\<^sub>t (if e s > 0 then Wait\<^sub>t (e s) (\<lambda>_. EState s) ({}, {}) else emp\<^sub>t)) t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_wait')
  by (auto simp add: entails_def join_assn_def magic_wand_assn_def emp_assn_def)







inductive wait_in_assn :: "real \<Rightarrow> (real \<Rightarrow> 'a ext_state) \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> rdy_info \<Rightarrow> 'a tassn" ("WaitIn\<^sub>t") where
  "WaitIn\<^sub>t 0 p ch v rdy [InBlock ch v]"
| "d > 0 \<Longrightarrow> WaitIn\<^sub>t d p ch v rdy [WaitBlk d (\<lambda>\<tau>. EState (p \<tau>)) rdy, InBlock ch v]"

inductive wait_out_assn :: "real \<Rightarrow> (real \<Rightarrow> 'a ext_state) \<Rightarrow> cname \<Rightarrow> 'a ext_exp \<Rightarrow> rdy_info \<Rightarrow> 'a tassn" ("WaitOut\<^sub>t") where
  "WaitOut\<^sub>t 0 p ch e rdy [OutBlock ch (e (p 0))]"
| "d > 0 \<Longrightarrow> WaitOut\<^sub>t d p ch e rdy [WaitBlk d (\<lambda>\<tau>. EState (p \<tau>)) rdy, OutBlock ch (e (p d))]"


subsection \<open>Combining two traces\<close>

text \<open>Whether two rdy_infos from different processes are compatible.\<close>
fun compat_rdy :: "rdy_info \<Rightarrow> rdy_info \<Rightarrow> bool" where
  "compat_rdy (r11, r12) (r21, r22) = (r11 \<inter> r22 = {} \<and> r12 \<inter> r21 = {})"

text \<open>Merge two rdy infos\<close>
fun merge_rdy :: "rdy_info \<Rightarrow> rdy_info \<Rightarrow> rdy_info" where
  "merge_rdy (r11, r12) (r21, r22) = (r11 \<union> r21, r12 \<union> r22)"


lemma WaitBlk_eq_combine:
  assumes "WaitBlk d1 p1 rdy1 = WaitBlk d1' p1' rdy1'"
    and "WaitBlk d1 p2 rdy2 = WaitBlk d1' p2' rdy2'"
   shows "WaitBlk d1 (\<lambda>\<tau>. ParState (p1 \<tau>) (p2 \<tau>)) (merge_rdy rdy1 rdy2) =
          WaitBlk d1' (\<lambda>\<tau>. ParState (p1' \<tau>) (p2' \<tau>)) (merge_rdy rdy1' rdy2')"
proof -
  have a1: "d1 = d1'" "rdy1 = rdy1'" "rdy2 = rdy2'"
    using assms WaitBlk_cong by blast+
  have a2: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> d1 \<Longrightarrow> p1 t = p1' t"
    using assms(1) WaitBlk_cong2 by blast
  have a3: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> d1 \<Longrightarrow> p2 t = p2' t"
    using assms(2) WaitBlk_cong2 by blast
  show ?thesis
  proof (cases d1)
    case (real r)
    have b: "d1' = ereal r"
      using real a1(1) by auto
    show ?thesis
      unfolding real b apply (auto simp add: WaitBlk_simps)
       apply (rule ext) apply auto
      subgoal for x apply (rule a2) by (auto simp add: real)
      subgoal for x apply (rule a3) by (auto simp add: real)
      using a1 by auto
  next
    case PInf
    have b: "d1' = \<infinity>"
      using PInf a1 by auto
    show ?thesis
      unfolding PInf b infinity_ereal_def
      apply (auto simp: WaitBlk_simps)
       apply (rule ext) apply auto
      subgoal for x apply (rule a2) by (auto simp add: PInf)
      subgoal for x apply (rule a3) by (auto simp add: PInf)
      using a1 by auto
  next
    case MInf
    have b: "d1' = - \<infinity>"
      using MInf a1 by auto
    show ?thesis
      unfolding MInf b
      by (auto simp: a1 WaitBlk_simps)
  qed
qed


text \<open>combine_blocks comms tr1 tr2 tr means tr1 and tr2 combines to tr, where
comms is the list of internal communication channels.\<close>
inductive combine_blocks :: "cname set \<Rightarrow> 'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace \<Rightarrow> bool" where
  \<comment> \<open>Empty case\<close>
  combine_blocks_empty:
  "combine_blocks comms [] [] []"

  \<comment> \<open>Paired communication\<close>
| combine_blocks_pair1:
  "ch \<in> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (InBlock ch v # blks1) (OutBlock ch v # blks2) (IOBlock ch v # blks)"
| combine_blocks_pair2:
  "ch \<in> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (OutBlock ch v # blks1) (InBlock ch v # blks2) (IOBlock ch v # blks)"

  \<comment> \<open>Unpaired communication\<close>
| combine_blocks_unpair1:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (CommBlock ch_type ch v # blks1) blks2 (CommBlock ch_type ch v # blks)"
| combine_blocks_unpair2:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms blks1 (CommBlock ch_type ch v # blks2) (CommBlock ch_type ch v # blks)"

  \<comment> \<open>Wait\<close>
| combine_blocks_wait1:
  "combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState ((\<lambda>x::real. hist1 x) \<tau>) ((\<lambda>x::real. hist2 x) \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlk t (\<lambda>x::real. hist1 x) rdy1 # blks1)
                        (WaitBlk t (\<lambda>x::real. hist2 x) rdy2 # blks2)
                        (WaitBlk t hist rdy # blks)"
| combine_blocks_wait2:
  "combine_blocks comms blks1 (WaitBlk (t2 - t1) (\<lambda>\<tau>. (\<lambda>x::real. hist2 x) (\<tau> + t1)) rdy2 # blks2) blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 < t2 \<Longrightarrow> t1 > 0 \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState ((\<lambda>x::real. hist1 x) \<tau>) ((\<lambda>x::real. hist2 x) \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlk t1 (\<lambda>x::real. hist1 x) rdy1 # blks1)
                        (WaitBlk t2 (\<lambda>x::real. hist2 x) rdy2 # blks2)
                        (WaitBlk t1 hist rdy # blks)"
| combine_blocks_wait3:
  "combine_blocks comms (WaitBlk (t1 - t2) (\<lambda>\<tau>. (\<lambda>x::real. hist1 x) (\<tau> + t2)) rdy1 # blks1) blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 > t2 \<Longrightarrow> t2 > 0 \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState ((\<lambda>x::real. hist1 x) \<tau>) ((\<lambda>x::real. hist2 x) \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlk t1 (\<lambda>x::real. hist1 x) rdy1 # blks1)
                        (WaitBlk t2 (\<lambda>x::real. hist2 x) rdy2 # blks2)
                        (WaitBlk t2 hist rdy # blks)"
| combine_blocks_emp1:
  "combine_blocks comms blks1 [] blks \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState ((\<lambda>x::real. hist1 x) \<tau>) EmptyState) \<Longrightarrow>
   combine_blocks comms (WaitBlk t (\<lambda>x::real. hist1 x) rdy1 # blks1)
                        []
                        (WaitBlk t hist rdy1 # blks)"
| combine_blocks_emp2:
  "combine_blocks comms [] blks2 blks \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState EmptyState ((\<lambda>x::real. hist2 x) \<tau>)) \<Longrightarrow>
   combine_blocks comms []
                        (WaitBlk t (\<lambda>x::real. hist2 x) rdy2 # blks2)
                        (WaitBlk t hist rdy2 # blks)"

subsection \<open>Basic elimination rules\<close>

named_theorems sync_elims


lemma combine_blocks_pairE [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<in> comms \<Longrightarrow> ch2 \<in> comms \<Longrightarrow>
   (\<And>tr'. ch1 = ch2 \<Longrightarrow> v1 = v2 \<Longrightarrow> (ch_type1 = In \<and> ch_type2 = Out \<or> ch_type1 = Out \<and> ch_type2 = In) \<Longrightarrow>
   tr = IOBlock ch1 v1 # tr' \<Longrightarrow> combine_blocks comms tr1 tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE1 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow> ch2 \<in> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 (CommBlock ch_type2 ch2 v2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE1' [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<in> comms \<Longrightarrow> ch2 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE2 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow> ch2 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 (CommBlock ch_type2 ch2 v2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_pairE2 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   ch1 \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_pairE2' [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch2 \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE3 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 (WaitBlk d2 p2 rdy2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE3' [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch2 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_waitE1 [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   \<not>compat_rdy rdy1 rdy2 \<Longrightarrow> P"
proof (induct rule: combine_blocks.cases)
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 rdy t)
  then show ?case
    by (metis WaitBlk_cong list.inject)
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  then show ?case 
    by (metis WaitBlk_cong list.inject)
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  then show ?case 
    by (metis WaitBlk_cong list.inject)
qed (auto)

lemma combine_blocks_waitE2 [sync_elims]:
  "combine_blocks comms (WaitBlk d p1 rdy1 # tr1) (WaitBlk d p2 rdy2 # tr2) tr \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   (\<And>tr'. tr = WaitBlk d (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) # tr' \<Longrightarrow>
           combine_blocks comms tr1 tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
proof (induct rule: combine_blocks.cases)
  case (combine_blocks_wait1 comms' blks1 blks2 blks rdy1' rdy2' hist hist1 hist2 rdy t)
  have a: "d = t" "rdy1 = rdy1'" "rdy2 = rdy2'" "tr1 = blks1" "tr2 = blks2" 
    using combine_blocks_wait1(2,3) by (auto simp add: WaitBlk_cong)
  have b: "WaitBlk d (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) =
           WaitBlk t (\<lambda>t. ParState (hist1 t) (hist2 t)) (merge_rdy rdy1' rdy2')"
    apply (rule WaitBlk_eq_combine) using combine_blocks_wait1(2,3) by auto 
  show ?case
    apply (rule combine_blocks_wait1)
    unfolding b using combine_blocks_wait1(4) unfolding a combine_blocks_wait1(7,8)
    by (auto simp add: combine_blocks_wait1(1,5))
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  have a: "d = ereal t1" "d = t2"
    using combine_blocks_wait2(2,3) by (auto simp add: WaitBlk_cong)
  show ?case
    using a combine_blocks_wait2(7) by auto
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  have a: "d = ereal t2" "d = t1"
    using combine_blocks_wait3(2,3) by (auto simp add: WaitBlk_cong)
  show ?case
    using a combine_blocks_wait3(7) by auto
qed (auto)

lemma combine_blocks_waitE3 [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   0 < d1 \<Longrightarrow> d1 < d2 \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   (\<And>tr'. tr = WaitBlk d1 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) # tr' \<Longrightarrow>
           combine_blocks comms tr1 (WaitBlk (d2 - d1) (\<lambda>t. p2 (t + d1)) rdy2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow> P"
proof (induct rule: combine_blocks.cases)
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 rdy t)
  have a: "t = ereal d1" "t = d2"
    using combine_blocks_wait1(2,3) WaitBlk_cong by blast+
  then show ?case
    using combine_blocks_wait1(10) by auto
next
  case (combine_blocks_wait2 comms' blks1 t2 t1 hist2 rdy2' blks2 blks rdy1' hist hist1 rdy)
  have a: "d1 = t1" "d2 = t2" "rdy1 = rdy1'" "rdy2 = rdy2'" "tr1 = blks1" "tr2 = blks2" 
    using combine_blocks_wait2(2,3) using WaitBlk_cong by blast+
  have a2: "WaitBlk d2 p2 rdy2 = WaitBlk d2 hist2 rdy2"
    using combine_blocks_wait2(3) unfolding a[symmetric] by auto
  have a3: "WaitBlk d1 p2 rdy2 = WaitBlk d1 hist2 rdy2"
           "WaitBlk (d2 - d1) (\<lambda>\<tau>. p2 (\<tau> + d1)) rdy2 = WaitBlk (d2 - d1) (\<lambda>\<tau>. hist2 (\<tau> + d1)) rdy2"
    using WaitBlk_split[OF a2] combine_blocks_wait2 by auto
  have b: "WaitBlk d1 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) =
           WaitBlk t1 (\<lambda>t. ParState (hist1 t) (hist2 t)) (merge_rdy rdy1' rdy2')"
    apply (rule WaitBlk_eq_combine)
    using combine_blocks_wait2.hyps(2) a(1,4) a3 by auto
  show ?case
    apply (rule combine_blocks_wait2) unfolding a3 b
    using combine_blocks_wait2(4) unfolding combine_blocks_wait2(9,10)
    by (auto simp add: a combine_blocks_wait2(1,5))
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  have "ereal d1 = t1" "d2 = ereal t2"
    using combine_blocks_wait3(2,3) by (auto simp add: WaitBlk_cong)
  then show ?case
    using combine_blocks_wait3(7,12) by auto
qed (auto)

lemma combine_blocks_waitE4 [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   0 < d2 \<Longrightarrow> d2 < d1 \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   (\<And>tr'. tr = WaitBlk d2 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) # tr' \<Longrightarrow>
           combine_blocks comms (WaitBlk (d1 - d2) (\<lambda>t. p1 (t + d2)) rdy1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
proof (induct rule: combine_blocks.cases)
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 rdy t)
  have "d1 = t" "ereal d2 = t"
    using combine_blocks_wait1(2,3) by (auto simp add: WaitBlk_cong)
  then show ?case
    using combine_blocks_wait1(10) by auto
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  have "d1 = ereal t1" "ereal d2 = t2"
    using combine_blocks_wait2(2,3) by (auto simp add: WaitBlk_cong)
  then show ?case
    using combine_blocks_wait2(7,12) by auto
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1' blks1 blks2 blks rdy2' hist hist2 rdy)
  have a: "d1 = t1" "d2 = t2" "rdy1 = rdy1'" "rdy2 = rdy2'"
          "tr1 = blks1" "tr2 = blks2" 
    using combine_blocks_wait3(2,3) using WaitBlk_cong by blast+
  have a2: "WaitBlk d1 p1 rdy1 = WaitBlk d1 hist1 rdy1"
    using combine_blocks_wait3(2) unfolding a[symmetric] by auto
  have a3: "WaitBlk d2 p1 rdy1 = WaitBlk d2 hist1 rdy1"
           "WaitBlk (d1 - d2) (\<lambda>\<tau>. p1 (\<tau> + d2)) rdy1 = WaitBlk (d1 - d2) (\<lambda>\<tau>. hist1 (\<tau> + d2)) rdy1"
    using WaitBlk_split[OF a2] combine_blocks_wait3 by auto
  have b: "WaitBlk d2 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) =
           WaitBlk d2 (\<lambda>t. ParState (hist1 t) (hist2 t)) (merge_rdy rdy1' rdy2')"
    apply (rule WaitBlk_eq_combine)
    using combine_blocks_wait3 a(2,3) a3 by auto
  show ?case
    apply (rule combine_blocks_wait3) unfolding a3 b
    using combine_blocks_wait3(4) unfolding combine_blocks_wait3(9,10)
    by (auto simp add: a combine_blocks_wait3)
qed (auto)

lemma combine_blocks_emptyE1 [sync_elims]:
  "combine_blocks comms [] [] tr \<Longrightarrow> tr = []"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_emptyE2 [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) [] tr \<Longrightarrow>
   (\<And>tr'. tr = WaitBlk d1 (\<lambda>t. ParState (p1 t) EmptyState) rdy1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 [] tr' \<Longrightarrow> P) \<Longrightarrow> P"
proof (induct rule: combine_blocks.cases)
  case (combine_blocks_emp1 comms1 blks1 blks hist hist1 t rdy1')
  have a: "tr1 = blks1" "d1 = t" "rdy1 = rdy1'"
    using combine_blocks_emp1(2)
    by (auto simp add: WaitBlk_cong)
  have b: "p1 \<tau> = hist1 \<tau>" if "0 \<le> \<tau>" and "ereal \<tau> \<le> d1" for \<tau>
    using a combine_blocks_emp1(2)
    using WaitBlk_cong2 that by blast
  have c: "combine_blocks comms tr1 [] blks"
    using combine_blocks_emp1(1,5) a(1) by auto
  have d: "tr = WaitBlk d1 (\<lambda>t. ParState (p1 t) EmptyState) rdy1 # blks"
    unfolding combine_blocks_emp1(4)
    apply auto
    apply (rule WaitBlk_ext)
    unfolding combine_blocks_emp1(6)
    using a b by auto
  show ?case
    apply (rule combine_blocks_emp1)
    apply (rule d) by (rule c)
qed (auto)

lemma combine_blocks_emptyE2' [sync_elims]:
  "combine_blocks comms [] (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   (\<And>tr'. tr = WaitBlk d2 (\<lambda>t. ParState EmptyState (p2 t)) rdy2 # tr' \<Longrightarrow>
           combine_blocks comms [] tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
proof (induct rule: combine_blocks.cases)
  case (combine_blocks_emp2 comms' blks2 blks hist hist2 t rdy2')
  have a: "tr2 = blks2" "d2 = t" "rdy2 = rdy2'"
    using combine_blocks_emp2(3)
    by (auto simp add: WaitBlk_cong)
  have b: "p2 \<tau> = hist2 \<tau>" if "0 \<le> \<tau>" and "ereal \<tau> \<le> d2" for \<tau>
    using a combine_blocks_emp2(3)
    using WaitBlk_cong2 that by blast
  have c: "combine_blocks comms [] tr2 blks"
    using combine_blocks_emp2(1,5) a(1) by auto
  have d: "tr = WaitBlk d2 (\<lambda>t. ParState EmptyState (p2 t)) rdy2 # blks"
    unfolding combine_blocks_emp2(4)
    apply auto
    apply (rule WaitBlk_ext)
    unfolding combine_blocks_emp2(6)
    using a b by auto
  show ?case
    apply (rule combine_blocks_emp2)
    apply (rule d) by (rule c)
qed (auto)

lemma combine_blocks_emptyE3 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) [] tr \<Longrightarrow>
   (\<And>tr'. ch1 \<notin> comms \<Longrightarrow> tr = CommBlock ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 [] tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_emptyE3' [sync_elims]:
  "combine_blocks comms [] (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   (\<And>tr'. ch2 \<notin> comms \<Longrightarrow> tr = CommBlock ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms [] tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)


subsection \<open>Big-step semantics for parallel processes.\<close>

inductive par_big_step :: "'a pproc \<Rightarrow> 'a gstate \<Rightarrow> 'a trace \<Rightarrow> 'a gstate \<Rightarrow> bool" where
  SingleB: "big_step p s1 tr s2 \<Longrightarrow> par_big_step (Single p) (EState s1) tr (EState s2)"
| ParallelB:
    "par_big_step p1 s11 tr1 s12 \<Longrightarrow>
     par_big_step p2 s21 tr2 s22 \<Longrightarrow>
     combine_blocks chs tr1 tr2 tr \<Longrightarrow>
     par_big_step (Parallel p1 chs p2) (ParState s11 s21) tr (ParState s12 s22)"


subsection \<open>Validity for parallel programs\<close>

text \<open>Assertion on global state\<close>
type_synonym 'a gs_assn = "'a gstate \<Rightarrow> bool"

text \<open>Assertion on global state and trace\<close>
type_synonym 'a gassn = "'a gstate \<Rightarrow> 'a trace \<Rightarrow> bool"

fun par_assn :: "'a gs_assn \<Rightarrow> 'a gs_assn \<Rightarrow> 'a gs_assn" where
  "par_assn P Q (EState s) \<longleftrightarrow> False"
| "par_assn P Q EmptyState \<longleftrightarrow> False"
| "par_assn P Q (ParState l r) \<longleftrightarrow> P l \<and> Q r"

fun sing_assn :: "'a ext_fform \<Rightarrow> 'a gs_assn" where
  "sing_assn P (EState s) = P s"
| "sing_assn P EmptyState \<longleftrightarrow> False"
| "sing_assn P (ParState _ _) = False"

fun sing_gassn :: "'a assn \<Rightarrow> 'a gassn" where
  "sing_gassn Q (EState s) tr = Q s tr"
| "sing_gassn Q EmptyState tr \<longleftrightarrow> False"
| "sing_gassn Q (ParState _ _) tr = False"

definition pair_assn :: "'a ext_fform \<Rightarrow> 'a ext_fform \<Rightarrow> 'a gs_assn" where
  "pair_assn P Q = par_assn (sing_assn P) (sing_assn Q)"

fun sync_gassn :: "cname set \<Rightarrow> 'a gassn \<Rightarrow> 'a gassn \<Rightarrow> 'a gassn" where
  "sync_gassn chs P Q (EState s) tr = False"
| "sync_gassn chs P Q EmptyState tr = False"
| "sync_gassn chs P Q (ParState l r) tr \<longleftrightarrow> (\<exists>tr1 tr2. P l tr1 \<and> Q r tr2 \<and> combine_blocks chs tr1 tr2 tr)"

definition ParValid :: "'a gs_assn \<Rightarrow> 'a pproc \<Rightarrow> 'a gassn \<Rightarrow> bool" ("\<Turnstile>\<^sub>p ({(1_)}/ (_)/ {(1_)})" 50) where
  "\<Turnstile>\<^sub>p {P} c {Q} \<longleftrightarrow> (\<forall>s1 s2 tr2. P s1 \<longrightarrow> par_big_step c s1 tr2 s2 \<longrightarrow> Q s2 tr2)"

inductive_cases SingleE: "par_big_step (Single p) s1 tr s2"
thm SingleE

inductive_cases ParallelE: "par_big_step (Parallel p1 ch p2) s1 tr s2"
thm ParallelE

lemma ParValid_Single:
  assumes "\<Turnstile> {\<lambda>(a,s) tr. P (a,s) \<and> tr = []} c {Q}"
  shows "\<Turnstile>\<^sub>p {sing_assn P} Single c {sing_gassn Q}"
  using assms unfolding ParValid_def Valid_def
  by (smt (z3) SingleE append_self_conv2 case_prodI2' sing_assn.simps(1) sing_gassn.simps(1))

lemma ParValid_Parallel:
  assumes "\<Turnstile>\<^sub>p {P1} p1 {Q1}"
    and "\<Turnstile>\<^sub>p {P2} p2 {Q2}"
  shows "\<Turnstile>\<^sub>p {par_assn P1 P2} Parallel p1 chs p2 {sync_gassn chs Q1 Q2}"
  unfolding ParValid_def apply clarify
  apply (elim ParallelE) apply auto
  subgoal for tr2 s11 tr1 s12 s21 tr2' s22
    apply (rule exI[where x=tr1])
    apply auto
    subgoal using assms(1) unfolding ParValid_def by auto
    apply (rule exI[where x=tr2'])
    using assms(2) unfolding ParValid_def by auto
  done

lemma ParValid_conseq:
  assumes "\<Turnstile>\<^sub>p {P} c {Q}"
    and "\<And>s. P' s \<Longrightarrow> P s"
    and "\<And>s tr. Q s tr \<Longrightarrow> Q' s tr"
  shows "\<Turnstile>\<^sub>p {P'} c {Q'}"
  using assms unfolding ParValid_def by blast

text \<open>Version for two processes\<close>

lemma ParValid_Parallel':
  assumes "\<Turnstile> {\<lambda>(a,s) tr. P1 (a,s) \<and> emp\<^sub>t tr} p1 {Q1}"
    and "\<Turnstile> {\<lambda>(a,s) tr. P2 (a,s) \<and> emp\<^sub>t tr} p2 {Q2}"
  shows "\<Turnstile>\<^sub>p
    {pair_assn P1 P2}
      Parallel (Single p1) chs (Single p2)
    {sync_gassn chs (sing_gassn Q1) (sing_gassn Q2)}"
  unfolding pair_assn_def
  apply (rule ParValid_Parallel)
  using ParValid_Single assms unfolding emp_assn_def by auto

subsection \<open>Combination on assertions\<close>

definition combine_assn :: "cname set \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "combine_assn chs P Q = (\<lambda>tr. \<exists>tr1 tr2. P tr1 \<and> Q tr2 \<and> combine_blocks chs tr1 tr2 tr)"

lemma combine_assn_ex_pre_left:
  assumes "\<And>x. combine_assn chs (P x) Q \<Longrightarrow>\<^sub>t R"
  shows "combine_assn chs (\<lambda>tr. \<exists>x. P x tr) Q \<Longrightarrow>\<^sub>t R"
  using assms by (auto simp add: combine_assn_def entails_tassn_def)

lemma combine_assn_ex_pre_right:
  assumes "\<And>x. combine_assn chs P (Q x) \<Longrightarrow>\<^sub>t R"
  shows "combine_assn chs P (\<lambda>tr. \<exists>x. Q x tr) \<Longrightarrow>\<^sub>t R"
  using assms by (auto simp add: combine_assn_def entails_tassn_def)

lemma combine_assn_mono:
  assumes "P \<Longrightarrow>\<^sub>t P'"
    and "Q \<Longrightarrow>\<^sub>t Q'"
  shows "combine_assn chs P Q \<Longrightarrow>\<^sub>t combine_assn chs P' Q'"
  using assms by (auto simp add: combine_assn_def entails_tassn_def)

lemma combine_assn_emp [simp]:
  "combine_assn chs emp\<^sub>t emp\<^sub>t = emp\<^sub>t"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: emp_assn_def elim: sync_elims)
  by (rule combine_blocks_empty)

lemma combine_assn_emp_in:
  "ch \<in> chs \<Longrightarrow> combine_assn chs emp\<^sub>t (In\<^sub>t s ch v @\<^sub>t P) = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: in_assn.cases)
  by (auto elim: sync_elims)

lemma combine_assn_in_emp:
  "ch \<in> chs \<Longrightarrow> combine_assn chs (In\<^sub>t s ch v @\<^sub>t P) emp\<^sub>t = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: in_assn.cases)
    by (auto elim: sync_elims)
  

lemma combine_assn_emp_out:
  "ch \<in> chs \<Longrightarrow> combine_assn chs emp\<^sub>t (Out\<^sub>t s ch v @\<^sub>t P) = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: out_assn.cases)
  by (auto elim: sync_elims)

lemma combine_assn_out_emp:
  "ch \<in> chs \<Longrightarrow> combine_assn chs (Out\<^sub>t s ch v @\<^sub>t P) emp\<^sub>t = false\<^sub>A"
  unfolding combine_assn_def
  apply (rule ext)
  apply (auto simp add: false_assn_def emp_assn_def join_assn_def elim!: out_assn.cases)
  by (auto elim: sync_elims)

lemma combine_assn_out_in:
  "ch \<in> chs \<Longrightarrow>
   combine_assn chs (Out\<^sub>t s1 ch v @\<^sub>t P) (In\<^sub>t s2 ch w @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (\<up>(v = w) \<and>\<^sub>t (IO\<^sub>t ch v @\<^sub>t combine_assn chs P Q))"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def pure_assn_def conj_assn_def io_assn.simps
                        out_assn.simps in_assn.simps)
  subgoal by (auto elim: sync_elims)
  subgoal apply (elim combine_blocks_pairE) by auto
  by (auto elim!: sync_elims)

lemma combine_assn_out_in':
  "ch \<in> chs \<Longrightarrow>
   combine_assn chs (Out\<^sub>t s1 ch v) (In\<^sub>t s2 ch w) \<Longrightarrow>\<^sub>t
   (\<up>(v = w) \<and>\<^sub>t (IO\<^sub>t ch v))"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def pure_assn_def conj_assn_def
                        io_assn.simps out_assn.simps in_assn.simps)
  by (auto elim: sync_elims)

lemma combine_assn_out_in'_tr:
  "combine_assn chs (Out\<^sub>t s1 ch v) (In\<^sub>t s2 ch w) tr \<Longrightarrow>
   ch \<in> chs \<Longrightarrow>
   v = w \<and> IO\<^sub>t ch v tr"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def pure_assn_def conj_assn_def
                        io_assn.simps out_assn.simps in_assn.simps)
  by (auto elim: sync_elims)

lemma combine_assn_in_out:
  "ch \<in> chs \<Longrightarrow>
   combine_assn chs (In\<^sub>t s1 ch v @\<^sub>t P) (Out\<^sub>t s2 ch w @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (\<up>(v = w) \<and>\<^sub>t (IO\<^sub>t ch v @\<^sub>t combine_assn chs P Q))"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def pure_assn_def conj_assn_def io_assn.simps
                        out_assn.simps in_assn.simps)
  subgoal by (auto elim: sync_elims)
  subgoal apply (elim combine_blocks_pairE) by auto
  by (auto elim!: sync_elims)

lemma combine_assn_in_out':
  "ch \<in> chs \<Longrightarrow>
   combine_assn chs (In\<^sub>t s1 ch v ) (Out\<^sub>t s2 ch w ) \<Longrightarrow>\<^sub>t
   (\<up>(v = w) \<and>\<^sub>t (IO\<^sub>t ch v ))"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def pure_assn_def conj_assn_def
                        io_assn.simps out_assn.simps in_assn.simps)
  by (auto elim: sync_elims)

lemma combine_assn_wait_emp:
  assumes "d > 0"
  shows "combine_assn chs (Wait\<^sub>t d p rdy @\<^sub>t P) emp\<^sub>t \<Longrightarrow>\<^sub>t (Wait\<^sub>t d (\<lambda>t. ParState (p t) EmptyState) rdy @\<^sub>t combine_assn chs P emp\<^sub>t)"
  unfolding combine_assn_def
  apply (simp add: entails_tassn_def wait_assn.simps emp_assn_def join_assn_def )
  using assms by (auto elim!: sync_elims)

lemma combine_assn_emp_wait:
  assumes "d > 0"
  shows "combine_assn chs emp\<^sub>t (Wait\<^sub>t d p rdy @\<^sub>t P) \<Longrightarrow>\<^sub>t (Wait\<^sub>t d (\<lambda>t. ParState EmptyState (p t)) rdy @\<^sub>t combine_assn chs emp\<^sub>t P)"
  unfolding combine_assn_def
  apply (simp add: entails_tassn_def wait_assn.simps emp_assn_def join_assn_def)
  using assms by (auto elim!: sync_elims)

lemma combine_assn_wait:
  "compat_rdy rdy1 rdy2 \<Longrightarrow>
   d > 0 \<Longrightarrow>
   combine_assn chs (Wait\<^sub>t d p rdy1 @\<^sub>t P) (Wait\<^sub>t d q rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (Wait\<^sub>t d (\<lambda>t. ParState (p t) (q t)) (merge_rdy rdy1 rdy2) @\<^sub>t combine_assn chs P Q)"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def wait_assn.simps)
  apply (elim combine_blocks_waitE2) by auto

lemma combine_assn_wait_in:
  assumes "ch \<in> chs"
    and "compat_rdy rdy1 ({}, {ch})"
  shows "combine_assn chs (Wait\<^sub>t d p rdy1 @\<^sub>t P) (In\<^sub>t s ch v @\<^sub>t Q) \<Longrightarrow>\<^sub>t
   (Wait\<^sub>t d (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({}, {ch})) @\<^sub>t
    combine_assn chs P (In\<^sub>t s ch v @\<^sub>t Q))"
proof (cases "d > 0")
  case True
  have *: "(Wait\<^sub>t d (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({}, {ch})) @\<^sub>t combine_assn chs P (In\<^sub>t s ch v @\<^sub>t Q)) tr"
    if "(Wait\<^sub>t d p rdy1 @\<^sub>t P) tr1" "(In\<^sub>t s ch v @\<^sub>t Q) tr2" "combine_blocks chs tr1 tr2 tr" for tr tr1 tr2
  proof -
    from that(1)[unfolded join_assn_def]
    obtain tr11 tr12 where a: "Wait\<^sub>t d p rdy1 tr11" "P tr12" "tr1 = tr11 @ tr12"
      by auto
    from that(2)[unfolded join_assn_def]
    obtain tr21 tr22 where b: "In\<^sub>t s ch v tr21" "Q tr22" "tr2 = tr21 @ tr22"
      by auto
    have c: "tr11 = [WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy1]"
      using True a(1) wait_assn.cases by fastforce
    have d: "(Wait\<^sub>t d (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({}, {ch})) @\<^sub>t
             combine_assn chs P (In\<^sub>t s ch v @\<^sub>t Q)) tr"
      if "0 < (d2::real)"
         "combine_blocks chs (WaitBlk d p rdy1 # tr12)
          (WaitBlk d2 (\<lambda>_. s) ({}, {ch}) # InBlock ch v # tr22) tr" for d2
    proof -
      have "d < d2 \<or> d = d2 \<or> d > d2" by auto
      then show ?thesis
      proof (elim disjE)
        assume d1: "d < d2"
        have d1': "ereal d < ereal d2"
          using d1 by auto
        show ?thesis
          using that(2)
          apply (elim combine_blocks_waitE3)
            apply (rule True) apply (rule d1') using assms(2) apply simp
          subgoal for blks'
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({}, {ch}))]"])
            apply (rule exI[where x=blks'])
            apply (rule conjI)
            subgoal using True by (simp add: wait_assn.simps)
            apply (rule conjI)
             prefer 2 subgoal using d1 by auto
            unfolding combine_assn_def
            apply (rule exI[where x=tr12])
            apply (rule exI[where x="WaitBlk (d2 - d) (\<lambda>_. s) ({}, {ch}) # InBlock ch v # tr22"])
            apply (rule conjI)
            subgoal by (rule a(2))
            apply (rule conjI)
             prefer 2 subgoal by auto
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlk (d2 - d) (\<lambda>_. s) ({}, {ch}), InBlock ch v]"])
            apply (rule exI[where x=tr22])
            using b(2) d1 by (auto intro: in_assn.intros)
          done
      next
        assume d2: "d = d2"
        show ?thesis
          using that(2) unfolding d2[symmetric]
          apply (elim combine_blocks_waitE2)
          using assms(2) apply simp
          subgoal for blks'
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlk d (\<lambda>t. ParState (p t) s) (merge_rdy rdy1 ({}, {ch}))]"])
            apply (rule exI[where x=blks'])
            apply (rule conjI)
            subgoal using True by (simp add: wait_assn.simps)
            apply (rule conjI)
             prefer 2 subgoal by auto
            unfolding combine_assn_def
            apply (rule exI[where x=tr12])
            apply (rule exI[where x="InBlock ch v # tr22"])
            apply (rule conjI)
            subgoal using a(2) by auto
            apply (rule conjI)
            subgoal apply (subst join_assn_def)
              apply (rule exI[where x="[InBlock ch v]"])
              apply (rule exI[where x=tr22])
              by (auto intro: in_assn.intros b(2))
            by auto
          done
      next
        assume d3: "d > d2"
        have d3': "ereal d > ereal d2"
          using d3 by auto
        show ?thesis
          using that(2)
          apply (elim combine_blocks_waitE4)
          apply (rule that(1)) apply (rule d3')
           using assms(2) apply simp
          apply (elim combine_blocks_pairE2')
          using assms by auto
      qed
    qed
    show ?thesis
      using b(1) apply (cases rule: in_assn.cases)
      subgoal
        by (metis Cons_eq_appendI a(3) assms(1) b(3) c combine_blocks_pairE2' that(3))
      subgoal for d2
        using that(3) unfolding a(3) b(3) c
        using d assms(2) by auto
      done
  qed
  show ?thesis
    apply (subst combine_assn_def)
    apply (auto simp add: entails_tassn_def)
    using * by auto
next
  case False
  show ?thesis
    using False wait_le_zero by auto
qed

lemma combine_assn_waitout_wait:
  assumes "ch \<in> chs"
    and "compat_rdy rdy rdy2"
    and "d2 > 0"
  shows "combine_assn chs (WaitOut\<^sub>t d p ch e rdy @\<^sub>t P) (Wait\<^sub>t d2 p2 rdy2 @\<^sub>t Q) \<Longrightarrow>\<^sub>t 
         (\<up>(d \<ge> d2) \<and>\<^sub>t (Wait\<^sub>t d2 (\<lambda>t. ParState (EState (p t)) (p2 t)) (merge_rdy rdy rdy2) @\<^sub>t
                        combine_assn chs (WaitOut\<^sub>t (d - d2) (\<lambda>t. p (t + d2)) ch e rdy @\<^sub>t P) Q))"
proof -
  have *: "(\<up> (d2 \<le> d) \<and>\<^sub>t
        Wait\<^sub>t d2 (\<lambda>t. ParState (EState (p t)) (p2 t)) (merge_rdy rdy rdy2) @\<^sub>t
        combine_assn chs (WaitOut\<^sub>t (d - d2) (\<lambda>t. p (t + d2)) ch e rdy @\<^sub>t P) Q) tr"
    if "(WaitOut\<^sub>t d p ch e rdy @\<^sub>t P) tr1"
       "(Wait\<^sub>t d2 p2 rdy2 @\<^sub>t Q) tr2"
       "combine_blocks chs tr1 tr2 tr" for tr tr1 tr2
  proof -
    from that(1)[unfolded join_assn_def]
    obtain tr11 tr12 where a: "WaitOut\<^sub>t d p ch e rdy tr11" "P tr12" "tr1 = tr11 @ tr12"
      by auto
    from that(2)[unfolded join_assn_def]
    obtain tr21 tr22 where b: "Wait\<^sub>t d2 p2 rdy2 tr21" "Q tr22" "tr2 = tr21 @ tr22"
      by auto
    have c: "tr21 = [WaitBlk d2 p2 rdy2]"
      using b(1) wait_assn.cases assms(3) by fastforce
    have d: "(\<up> (d2 \<le> d) \<and>\<^sub>t
             Wait\<^sub>t d2 (\<lambda>t. ParState (EState (p t)) (p2 t)) (merge_rdy rdy rdy2) @\<^sub>t
             combine_assn chs (WaitOut\<^sub>t (d - d2) (\<lambda>t. p (t + d2)) ch e rdy @\<^sub>t P) Q) tr"
      if "0 < (d::real)"
         "combine_blocks chs (WaitBlk d (\<lambda>\<tau>. EState (p \<tau>)) rdy # OutBlock ch (e (p d)) # tr12)
                             (WaitBlk d2 p2 rdy2 # tr22) tr"
    proof -
      have "d < d2 \<or> d = d2 \<or> d > d2" by auto
      then show ?thesis
      proof (elim disjE)
        assume d1: "d < d2"
        have d1': "ereal d < ereal d2"
          using d1 by auto
        show ?thesis
          using that(2)
          apply (elim combine_blocks_waitE3) apply (rule that(1))
            apply (rule d1') apply (rule assms(2))
          using assms(1) combine_blocks_pairE2 by blast
      next
        assume d2: "d = d2"
        show ?thesis
          using that(2)
          unfolding d2[symmetric]
          apply (elim combine_blocks_waitE2)
           apply (rule assms(2))
          subgoal for blks'
            unfolding pure_assn_def conj_assn_def
            apply (rule conjI)
            subgoal by auto
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlk d (\<lambda>t. ParState (EState (p t)) (p2 t)) (merge_rdy rdy rdy2)]"])
            apply (rule exI[where x=blks'])
            apply (rule conjI)
            subgoal using d2 assms(3) by (auto intro: wait_assn.intros)
            apply (rule conjI)
             prefer 2 subgoal by auto
            unfolding combine_assn_def
            apply (rule exI[where x="OutBlock ch (e (p d)) # tr12"])
            apply (rule exI[where x=tr22])
            apply (rule conjI)
             prefer 2 subgoal using b(2) by auto
            unfolding join_assn_def
            apply (rule exI[where x="[OutBlock ch (e (p d))]"])
            apply (rule exI[where x=tr12])
            by (auto simp add: a(2) wait_out_assn.simps)
          done
      next
        assume d3: "d > d2"
        have d3': "ereal d > ereal d2"
          using d3 by auto
        show ?thesis
          using that(2)
          apply (elim combine_blocks_waitE4) apply (rule \<open>0 < d2\<close>)
            apply (rule d3') apply (rule assms(2))
          subgoal for blks'
            unfolding pure_assn_def conj_assn_def
            apply (rule conjI)
            subgoal using d3 by auto
            apply (subst join_assn_def)
            apply (rule exI[where x="[WaitBlk d2 (\<lambda>t. ParState (EState (p t)) (p2 t)) (merge_rdy rdy rdy2)]"])
            apply (rule exI[where x=blks'])
            apply (rule conjI)
            subgoal using assms(3) by (auto intro: wait_assn.intros)
            apply (rule conjI)
             prefer 2 subgoal by auto
            unfolding combine_assn_def
            apply (rule exI[where x="WaitBlk (d - d2) (\<lambda>t. EState (p (t + d2))) rdy # OutBlock ch (e (p d)) # tr12"])
            apply (rule exI[where x=tr22])
            apply (rule conjI)
             prefer 2 subgoal apply (rule conjI)
               apply (rule b(2)) by auto
            unfolding join_assn_def
            apply (rule exI[where x="[WaitBlk (d - d2) (\<lambda>t. EState (p (t + d2))) rdy, OutBlock ch (e (p d))]"])
            apply (rule exI[where x=tr12])
            apply (rule conjI)
            subgoal
              using wait_out_assn.intros(2)[of "d - d2" "\<lambda>t. p (t + d2)" ch e rdy]
              by (simp add: d3)
            using a(2) by auto
          done
      qed
    qed
    show ?thesis
      using a(1) apply (cases rule: wait_out_assn.cases)
      subgoal
        using that(3) unfolding a(3) b(3) c
        apply auto
        using assms combine_blocks_pairE2 by blast
      subgoal
        using that(3) unfolding a(3) b(3) c
        apply auto using d by auto
      done
  qed
  show ?thesis
    apply (subst combine_assn_def)
    apply (auto simp add: entails_tassn_def)
    using * by auto
qed

lemma combine_assn_waitout_in:
  assumes "ch \<in> chs"
    and "ch \<in> fst rdy"
  shows "combine_assn chs (WaitOut\<^sub>t d p ch e rdy @\<^sub>t P) (In\<^sub>t s ch v @\<^sub>t Q) \<Longrightarrow>\<^sub>t 
         (\<up>(d = 0) \<and>\<^sub>t \<up>(v = e (p 0)) \<and>\<^sub>t
          (IO\<^sub>t ch v @\<^sub>t combine_assn chs P Q))"
proof -
  have *: "(\<up> (d = 0) \<and>\<^sub>t \<up> (v = e (p 0)) \<and>\<^sub>t IO\<^sub>t ch v @\<^sub>t combine_assn chs P Q) tr"
    if "(WaitOut\<^sub>t d p ch e rdy @\<^sub>t P) tr1"
       "(In\<^sub>t s ch v @\<^sub>t Q) tr2"
       "combine_blocks chs tr1 tr2 tr" for tr tr1 tr2
  proof -
    from that(1)[unfolded join_assn_def]
    obtain tr11 tr12 where a: "WaitOut\<^sub>t d p ch e rdy tr11" "P tr12" "tr1 = tr11 @ tr12"
      by auto
    from that(2)[unfolded join_assn_def]
    obtain tr21 tr22 where b: "In\<^sub>t s ch v tr21" "Q tr22" "tr2 = tr21 @ tr22"
      by auto
    show ?thesis
      using a(1) apply (cases rule: wait_out_assn.cases)
      subgoal
        using b(1) apply (cases rule: in_assn.cases)
        subgoal
          using that(3) unfolding a(3) b(3) apply auto
          apply (elim combine_blocks_pairE) using assms(1) apply auto
          apply (auto simp add: conj_assn_def pure_assn_def join_assn_def)
          apply (rule exI[where x="[IOBlock ch (e (p 0))]"])
          apply (auto intro: io_assn.intros)
          unfolding combine_assn_def using a(2) b(2) by auto
        subgoal
          using that(3) unfolding a(3) b(3) apply auto
          apply (elim combine_blocks_pairE2) by (rule assms)
        done
      using b(1) apply (cases rule: in_assn.cases)
      using that(3) unfolding a(3) b(3) apply auto
      subgoal apply (elim combine_blocks_pairE2') by (rule assms)
      subgoal for d' apply (elim combine_blocks_waitE1)
        using assms(2) apply (cases rdy) by auto
      done
  qed
  show ?thesis
    apply (subst combine_assn_def)
    apply (auto simp add: entails_tassn_def)
    using * by auto
qed

lemma combine_assn_waitout_emp:
  assumes "ch \<in> chs"
  shows "combine_assn chs (WaitOut\<^sub>t d p ch e rdy @\<^sub>t P) emp\<^sub>t \<Longrightarrow>\<^sub>t false\<^sub>A"
  unfolding combine_assn_def
  apply (auto simp add: entails_tassn_def join_assn_def emp_assn_def false_assn_def wait_out_assn.simps)
  using assms by (auto elim: sync_elims)

subsection \<open>Assertions for global states\<close>

definition entails_gassn :: "'a gassn \<Rightarrow> 'a gassn \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>g" 25) where
  "(P \<Longrightarrow>\<^sub>g Q) \<longleftrightarrow> (\<forall>s tr. P s tr \<longrightarrow> Q s tr)"

definition state_gassn :: "'a gs_assn \<Rightarrow> 'a gassn" where
  "state_gassn P = (\<lambda>s tr. P s)"

fun left_gassn :: "'a gs_assn \<Rightarrow> 'a gassn" where
  "left_gassn P (EState s) tr = False"
| "left_gassn P (EmptyState) tr = False"
| "left_gassn P (ParState s1 s2) tr = P s1"

fun right_gassn :: "'a gs_assn \<Rightarrow> 'a gassn" where
  "right_gassn P (EState s) tr = False"
| "right_gassn P (EmptyState) tr = False"
| "right_gassn P (ParState s1 s2) tr = P s2"

definition trace_gassn :: "'a tassn \<Rightarrow> 'a gassn" where
  "trace_gassn P = (\<lambda>s tr. P tr)"

definition and_gassn :: "'a gassn \<Rightarrow> 'a gassn \<Rightarrow> 'a gassn" (infixr "\<and>\<^sub>g" 35) where
  "(P \<and>\<^sub>g Q) = (\<lambda>s tr. P s tr \<and> Q s tr)"

definition ex_gassn :: "('b \<Rightarrow> 'a gassn) \<Rightarrow> 'a gassn" (binder "\<exists>\<^sub>g" 10) where
  "(\<exists>\<^sub>g x. P x) = (\<lambda>s tr. \<exists>x. P x s tr)"

lemma ParValid_conseq':
  assumes "\<Turnstile>\<^sub>p {P} c {Q}"
    and "\<And>s. P' s \<Longrightarrow> P s"
    and "Q \<Longrightarrow>\<^sub>g Q'"
  shows "\<Turnstile>\<^sub>p {P'} c {Q'}"
  using assms ParValid_conseq unfolding entails_gassn_def by blast

lemma sync_gassn_ex_pre_left:
  assumes "\<And>x. sync_gassn chs (P x) Q \<Longrightarrow>\<^sub>g R"
  shows "sync_gassn chs (\<exists>\<^sub>g x. P x) Q \<Longrightarrow>\<^sub>g R"
  apply (auto simp add: entails_gassn_def)
  subgoal for s tr
    apply (cases s) apply auto
    unfolding ex_gassn_def apply auto
    using assms entails_gassn_def 
    by (smt (z3) sync_gassn.simps(3))
  done

lemma sync_gassn_ex_pre_right:
  assumes "\<And>x. sync_gassn chs P (Q x) \<Longrightarrow>\<^sub>g R"
  shows "sync_gassn chs P (\<exists>\<^sub>g x. Q x) \<Longrightarrow>\<^sub>g R"
  apply (auto simp add: entails_gassn_def)
  subgoal for s tr
    apply (cases s) apply auto
    unfolding ex_gassn_def apply auto
    using assms entails_gassn_def 
    by (smt (z3) sync_gassn.simps(3))
  done

lemma entails_ex_gassn:
  assumes "\<exists>x. P \<Longrightarrow>\<^sub>g Q x"
  shows "P \<Longrightarrow>\<^sub>g (\<exists>\<^sub>g x. Q x)"
  using assms unfolding entails_gassn_def ex_gassn_def by auto

lemma sing_gassn_split:
  "sing_gassn (\<lambda>s tr. P s \<and> Q tr) = (state_gassn (sing_assn P) \<and>\<^sub>g trace_gassn Q)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (cases s) by (auto simp add: state_gassn_def trace_gassn_def and_gassn_def)
  done

lemma sing_gassn_split2:
  "sing_gassn (\<lambda>s. \<up>(b s) \<and>\<^sub>t Q s) = (state_gassn (sing_assn b) \<and>\<^sub>g sing_gassn Q)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (cases s)
    by (auto simp add: state_gassn_def trace_gassn_def and_gassn_def conj_assn_def pure_assn_def)
  done

lemma sing_gassn_ex:
  "sing_gassn (\<lambda>s tr. \<exists>x. P x s tr) = (\<exists>\<^sub>gx. sing_gassn (\<lambda>s tr. P x s tr))"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (cases s) by (auto simp add: ex_gassn_def)
  done

lemma sync_gassn_state_left:
  "sync_gassn chs (state_gassn P1 \<and>\<^sub>g P2) Q = (left_gassn P1 \<and>\<^sub>g sync_gassn chs P2 Q)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (cases s) by (auto simp add: and_gassn_def state_gassn_def)
  done

lemma sync_gassn_state_right:
  "sync_gassn chs P (state_gassn Q1 \<and>\<^sub>g Q2) = (right_gassn Q1 \<and>\<^sub>g sync_gassn chs P Q2)"
  apply (rule ext) apply (rule ext)
  subgoal for s tr
    apply (cases s) by (auto simp add: and_gassn_def state_gassn_def)
  done

lemma sync_gassn_traces:
  "sync_gassn chs (trace_gassn P) (trace_gassn Q) \<Longrightarrow>\<^sub>g trace_gassn (combine_assn chs P Q)"
  unfolding entails_gassn_def apply auto
  subgoal for s tr
    apply (cases s) by (auto simp add: trace_gassn_def combine_assn_def)
  done

lemma entails_trace_gassn:
  "P \<Longrightarrow>\<^sub>t Q \<Longrightarrow> trace_gassn P \<Longrightarrow>\<^sub>g trace_gassn Q"
  unfolding entails_tassn_def entails_gassn_def trace_gassn_def by auto 

lemma and_entails_gassn:
  "P2 \<Longrightarrow>\<^sub>g P2' \<Longrightarrow> P1 \<and>\<^sub>g P2' \<Longrightarrow>\<^sub>g Q \<Longrightarrow> P1 \<and>\<^sub>g P2 \<Longrightarrow>\<^sub>g Q"
  unfolding entails_gassn_def and_gassn_def by auto

lemma and_entails_gassn2:
  "P3 \<Longrightarrow>\<^sub>g P3' \<Longrightarrow> P1 \<and>\<^sub>g P2 \<and>\<^sub>g P3' \<Longrightarrow>\<^sub>g Q \<Longrightarrow> P1 \<and>\<^sub>g P2 \<and>\<^sub>g P3 \<Longrightarrow>\<^sub>g Q"
  unfolding entails_gassn_def and_gassn_def by auto

lemma sync_gassn_expand:
  "sync_gassn chs (sing_gassn P) (sing_gassn Q) s tr \<Longrightarrow>
    (\<And>s1 s2. s = ParState (EState s1) (EState s2) \<Longrightarrow> combine_assn chs (P s1) (Q s2) tr \<Longrightarrow> R) \<Longrightarrow> R"
  apply (cases s)
  subgoal by simp
  subgoal for s' by auto
  subgoal for s1 s2
    apply (cases s1) prefer 2 
    subgoal for s1'
      apply (cases s2) prefer 2
      subgoal for s2'
        by (auto simp add: combine_assn_def)
      by auto
    by auto
  done

lemma combine_assn_and_left:
  "combine_assn chs (\<up>b \<and>\<^sub>t P) Q = ((\<up>b) \<and>\<^sub>t combine_assn chs P Q)"
  by (auto simp add: combine_assn_def conj_assn_def pure_assn_def)

lemma combine_assn_and_right:
  "combine_assn chs P (\<up>b \<and>\<^sub>t Q) = ((\<up>b) \<and>\<^sub>t combine_assn chs P Q)"
  by (auto simp add: combine_assn_def conj_assn_def pure_assn_def)






definition prior :: char where "prior = CHR ''x''"
definition run_prior :: char where "run_prior = CHR ''y''"
definition run_now :: char where "run_now = CHR ''z''"

lemma vars_distinct [simp]: "prior \<noteq> run_prior" "prior \<noteq> run_now" 
                            "run_prior \<noteq> prior" "run_prior \<noteq> run_now"
                            "run_now \<noteq> prior"  "run_now \<noteq> run_prior"
    apply(auto simp add:prior_def run_prior_def run_now_def)
  done

definition initf :: "scheduler \<Rightarrow> scheduler" where
"initf a = sch [] "

definition p1 :: "scheduler proc" where
"p1 = Basic initf; run_prior ::= (\<lambda> s. -1); run_now ::= (\<lambda> s. -1); Cm (''schtest''[?] prior)"


lemma l1:
"\<Turnstile> {\<lambda>(a,s) tr. P1 (a,s) \<and> emp\<^sub>t tr} p1 {\<lambda>(a,s) tr. \<exists> x.  In\<^sub>t (EState (sch [], s(prior := x))) ''schtest'' (s prior)  tr}"
  unfolding p1_def
  apply (rule Valid_seq)
  apply (rule Valid_basic_sp[simplified])
  apply (rule Valid_seq)
   apply(rule Valid_assign_sp[simplified])
  apply (rule Valid_seq)
   apply (rule Valid_assign_sp[simplified])
  apply (rule Valid_strengthen_post)
   prefer 2
   apply (rule Valid_receive_sp[simplified])
  by (auto simp add:pure_assn_def conj_assn_def initf_def entails_def)

definition p2 :: "scheduler proc" where
"p2 =Cm (''schtest''[!] (\<lambda> (a,s). 0))"

lemma l2:
"\<Turnstile> {\<lambda>(a,s) tr. P2 (a,s) \<and> emp\<^sub>t tr} p2 {\<lambda>(a,s) tr.  (Out\<^sub>t (EState (a,s)) ''schtest'' 0)  tr}"
  unfolding p2_def
  apply (rule Valid_strengthen_post)
  prefer 2
   apply (rule Valid_send_sp[simplified])
  apply (auto simp add: entails_def pure_assn_def conj_assn_def)
  done


lemma combine:
"combine_assn {''schtest''} 
(In\<^sub>t (EState (sch [], b1(prior := x))) ''schtest'' (b1 prior))
(Out\<^sub>t (EState (a2, b2)) ''schtest'' 0) \<Longrightarrow>\<^sub>t
((IO\<^sub>t ''schtest'' 0))"
  apply(rule entails_tassn_trans)
  apply(rule combine_assn_in_out')
  by auto

thm combine_assn_in_out

definition system :: "scheduler pproc" where
  "system = Parallel (Single p1)
                     {''schtest''}
                     (Single p2)"

lemma system:
"  \<Turnstile>\<^sub>p {pair_assn P1 P2}
      system
    {trace_gassn (IO\<^sub>t ''schtest'' 0)}"
 unfolding system_def
  apply (rule ParValid_conseq')
   apply (rule ParValid_Parallel')
 apply (rule l1)
   apply (rule l2)
  apply auto
  apply(auto simp add: entails_gassn_def trace_gassn_def)
  subgoal for s tr
    apply (cases s)
      apply auto
    subgoal for s1 s2 tr1 tr2
      apply(cases s1) 
        apply auto
      apply(cases s2)
        apply auto
      subgoal for a1 b1 x a2 b2
        using combine[of b1 x a2 b2]
        by (auto simp add: combine_assn_def entails_tassn_def)
      done
    done
  done
