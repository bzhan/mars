theory newParallel
  imports ContinuousInv BigStepParallel Complementlemma

begin


inductive out_inv_assn :: "(gstate \<Rightarrow> real \<Rightarrow> bool) \<Rightarrow> cname \<Rightarrow> tassn" ("Outinv\<^sub>t") where
  "r s v \<Longrightarrow> Outinv\<^sub>t r ch [OutBlock ch v]"
| "(d::real) > 0 \<Longrightarrow> r s v \<Longrightarrow> Outinv\<^sub>t r ch [WaitBlk (ereal d) (\<lambda>_. s) ({ch}, {}), OutBlock ch v]"
| "r s v \<Longrightarrow>Outinv\<^sub>t r ch  [WaitBlk \<infinity> (\<lambda>_. s) ({ch}, {})]"

inductive in_inv_assn :: "(gstate \<Rightarrow> real \<Rightarrow> bool) \<Rightarrow> cname  \<Rightarrow> tassn" ("Ininv\<^sub>t") where
  "r s v \<Longrightarrow> Ininv\<^sub>t r ch [InBlock ch v]"
| "(d::real) > 0 \<Longrightarrow> r s v \<Longrightarrow> Ininv\<^sub>t r ch [WaitBlk (ereal d) (\<lambda>_. s) ({}, {ch}), InBlock ch v]"
| "r s v \<Longrightarrow> Ininv\<^sub>t r ch  [WaitBlk \<infinity> (\<lambda>_. s) ({}, {ch})]"

inductive io_inv_assn :: "(gstate \<Rightarrow> real \<Rightarrow> bool) \<Rightarrow> cname \<Rightarrow> tassn" ("IOinv\<^sub>t") where
  "r s v \<Longrightarrow> IOinv\<^sub>t r ch [IOBlock ch v]"

inductive wait_inv_assn :: "(gstate \<Rightarrow>  bool) \<Rightarrow> rdy_info \<Rightarrow> tassn" ("Waitinv\<^sub>t") where
  " Waitinv\<^sub>t r rdy []"
| "(\<forall>t\<in>{0..d}. r (p t)) \<Longrightarrow> Waitinv\<^sub>t r rdy [WaitBlk (ereal d) p rdy]" 


inductive s2gs1 :: "(state \<Rightarrow> bool) \<Rightarrow> (gstate \<Rightarrow> bool)" where
 "p s \<Longrightarrow> s2gs1 p (State s)"

inductive s2gs2 :: "(state \<Rightarrow> real \<Rightarrow> bool) \<Rightarrow> (gstate \<Rightarrow> real \<Rightarrow> bool)" where
 "p s v \<Longrightarrow> s2gs2 p (State s) v"



end