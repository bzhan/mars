theory AssumeGuarantee
  imports ext_Complementlemma
begin

(*Output v on channel ch at any time, followed by trace satisfying P. *)
inductive out_orig_assn :: "cname \<Rightarrow> real \<Rightarrow> 'a gstate \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "P tr \<Longrightarrow> (out_orig_assn ch v s P) (OutBlock ch v # tr)"
| "P tr \<Longrightarrow> d > 0 \<Longrightarrow> (out_orig_assn ch v s P) (WaitBlk d (\<lambda>\<tau>. s) ({ch}, {}) # OutBlock ch v # tr)"

inductive out_0orig_assn :: "cname \<Rightarrow> real \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "P tr \<Longrightarrow> (out_0orig_assn ch v P) (OutBlock ch v # tr)"


(* Output v on channel ch is ready during a time within the set S,
   followed by trace satisfying P. *)
inductive out_guar_assn :: "cname \<Rightarrow> real \<Rightarrow> 'a gstate \<Rightarrow> real set \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "P tr \<Longrightarrow> 0 \<in> S \<Longrightarrow> (out_guar_assn ch v s S P) (OutBlock ch v # tr)"
| "P tr \<Longrightarrow> 0 \<in> S \<Longrightarrow> d2 > 0 \<Longrightarrow> (out_guar_assn ch v s S P)
      (WaitBlk d2 (\<lambda>\<tau>. s) ({ch}, {}) # OutBlock ch v # tr)"
| "P tr \<Longrightarrow> d1 \<in> S \<Longrightarrow> d1 > 0 \<Longrightarrow> (out_guar_assn ch v s S P)
      (WaitBlk d1 (\<lambda>\<tau>. s) ({}, {}) # OutBlock ch v # tr)"
| "P tr \<Longrightarrow> d1 \<in> S \<Longrightarrow> d1 > 0 \<Longrightarrow> d2 > 0 \<Longrightarrow> (out_guar_assn ch v s S P)
      (WaitBlk d1 (\<lambda>\<tau>. s) ({}, {}) # WaitBlk d2 (\<lambda>\<tau>. s) ({ch}, {}) # OutBlock ch v # tr)"

(* Immediately ready for output on channel ch. If the environment provides the
   corresponding input at a time within the set S, then the output value
   is v and the ensuring trace satisfies P. *)
inductive out_tassm_assn :: "cname \<Rightarrow> real \<Rightarrow> 'a gstate \<Rightarrow> real set \<Rightarrow>(real \<Rightarrow> 'a tassn) \<Rightarrow> 'a tassn" where
  "P 0 tr \<Longrightarrow> 0 \<in> S \<Longrightarrow> (out_tassm_assn ch v s S P) (OutBlock ch v # tr)"
| "P d tr \<Longrightarrow> d \<in> S \<Longrightarrow> d > 0 \<Longrightarrow> (out_tassm_assn ch v s S P)
      (WaitBlk d (\<lambda>\<tau>. s) ({ch}, {}) # OutBlock ch v # tr)"
| "0 \<notin> S \<Longrightarrow> (out_tassm_assn ch v s S P) (OutBlock ch w # tr)"
| "d \<notin> S \<Longrightarrow> d > 0 \<Longrightarrow> (out_tassm_assn ch v s S P)
      (WaitBlk d (\<lambda>\<tau>. s) ({ch}, {}) # OutBlock ch w # tr)"

inductive out_0assm_assn :: "cname \<Rightarrow> real \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "P tr \<Longrightarrow> (out_0assm_assn ch v P) (OutBlock ch v # tr)"
| "d > 0 \<Longrightarrow> ch \<in> fst rdy \<Longrightarrow> (out_0assm_assn ch v P) (WaitBlk d p rdy # tr)"

inductive out_0assm_rdy_assn :: "cname \<Rightarrow> real \<Rightarrow> rdy_info \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "P tr \<Longrightarrow> (out_0assm_rdy_assn ch v rdy P) (OutBlock ch v # tr)"
| "d > 0 \<Longrightarrow> (out_0assm_rdy_assn ch v rdy P) (WaitBlk d p rdy # tr)"

lemma out_orig_assn_tran:
  assumes "P \<Longrightarrow>\<^sub>t Q"
  shows "out_orig_assn ch v s P \<Longrightarrow>\<^sub>t out_orig_assn ch v s Q"
  unfolding entails_tassn_def
  apply auto
  subgoal for tr
    apply(cases rule: out_orig_assn.cases[of ch v s P tr])
        apply auto
    subgoal for tr'
      apply(rule out_orig_assn.intros(1))
      using assms by(auto simp add: entails_tassn_def)
    subgoal for d tr'
      apply(rule out_orig_assn.intros(2))
      using assms by(auto simp add: entails_tassn_def)
    done
  done

lemma out_tassm_assn_tran:
  assumes"\<And>t. t \<in> S \<Longrightarrow> P t \<Longrightarrow>\<^sub>t Q t"
  shows "out_tassm_assn ch v s S P \<Longrightarrow>\<^sub>t out_tassm_assn ch v s S Q"
  unfolding entails_tassn_def
  apply auto
  subgoal for tr
    apply(cases rule: out_tassm_assn.cases[of ch v s S P tr])
        apply auto
    subgoal for tr'
      apply(rule out_tassm_assn.intros(1))
      using assms by(auto simp add: entails_tassn_def)
    subgoal for d tr'
      apply(rule out_tassm_assn.intros(2))
      using assms by(auto simp add: entails_tassn_def)
    subgoal for w tr'
      apply(rule out_tassm_assn.intros(3))
      using assms by(auto simp add: entails_tassn_def)
    subgoal for d w tr'
      apply(rule out_tassm_assn.intros(4))
      using assms by(auto simp add: entails_tassn_def)
    done
  done

lemma out_0assm_assn_tran:
  assumes"P \<Longrightarrow>\<^sub>t Q "
  shows "out_0assm_assn ch v P \<Longrightarrow>\<^sub>t out_0assm_assn ch v Q"
  unfolding entails_tassn_def
  apply auto
  subgoal for tr
    apply(cases rule: out_0assm_assn.cases[of ch v P tr])
        apply auto
    subgoal for tr'
      apply(rule out_0assm_assn.intros(1))
      using assms by(auto simp add: entails_tassn_def)
    subgoal for d p a b tr'
      apply(rule out_0assm_assn.intros(2))
      using assms by(auto simp add: entails_tassn_def)
    done
  done

lemma out_0assm_rdy_assn_tran:
  assumes"P \<Longrightarrow>\<^sub>t Q "
  shows "out_0assm_rdy_assn ch v rdy P \<Longrightarrow>\<^sub>t out_0assm_rdy_assn ch v rdy Q"
  unfolding entails_tassn_def
  apply auto
  subgoal for tr
    apply(cases rule: out_0assm_rdy_assn.cases[of ch v rdy P tr])
        apply auto
    subgoal for tr'
      apply(rule out_0assm_rdy_assn.intros(1))
      using assms by(auto simp add: entails_tassn_def)
    subgoal for d p tr'
      apply(rule out_0assm_rdy_assn.intros(2))
      using assms by(auto simp add: entails_tassn_def)
    done
  done


inductive in_orig_assn :: "cname \<Rightarrow> real \<Rightarrow> 'a gstate \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "P tr \<Longrightarrow> (in_orig_assn ch v s P) (InBlock ch v # tr)"
| "P tr \<Longrightarrow> d > 0 \<Longrightarrow> (in_orig_assn ch v s P) (WaitBlk d (\<lambda>\<tau>. s) ({}, {ch}) # InBlock ch v # tr)"

(* Input v on channel ch is ready during a time within the set S,
   followed by trace satisfying P. *)
inductive in_guar_assn :: "cname \<Rightarrow> real \<Rightarrow> 'a gstate \<Rightarrow> real set \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "P tr \<Longrightarrow> 0 \<in> S \<Longrightarrow> (in_guar_assn ch v s S P) (InBlock ch v # tr)"
| "P tr \<Longrightarrow> 0 \<in> S \<Longrightarrow> d2 > 0 \<Longrightarrow> (in_guar_assn ch v s S P)
      (WaitBlk d2 (\<lambda>\<tau>. s) ({}, {ch}) # InBlock ch v # tr)"
| "P tr \<Longrightarrow> d1 \<in> S \<Longrightarrow> (in_guar_assn ch v s S P)
      (WaitBlk d1 (\<lambda>\<tau>. s) ({}, {}) # InBlock ch v # tr)"
| "P tr \<Longrightarrow> d1 \<in> S \<Longrightarrow> d2 > 0 \<Longrightarrow> (in_guar_assn ch v s S P)
      (WaitBlk d1 (\<lambda>\<tau>. s) ({}, {}) # WaitBlk d2 (\<lambda>\<tau>. s) ({}, {ch}) # InBlock ch v # tr)"

(* Input v on channel ch, assuming the environment will provide the corresponding output
   in the time given by S, if so the input value is v and the ensuring trace satisfies P. *)
inductive in_tassm_assn :: "cname \<Rightarrow> real \<Rightarrow> 'a gstate \<Rightarrow> real set \<Rightarrow> (real \<Rightarrow> 'a tassn) \<Rightarrow> 'a tassn" where
  "P 0 tr \<Longrightarrow> 0 \<in> S \<Longrightarrow> (in_tassm_assn ch v s S P) (InBlock ch v # tr)"
| "P d tr \<Longrightarrow> d \<in> S \<Longrightarrow> d > 0 \<Longrightarrow> (in_tassm_assn ch v s S P)
      (WaitBlk d (\<lambda>\<tau>. s) ({}, {ch}) # InBlock ch v # tr)"
| "0 \<notin> S \<Longrightarrow> (in_tassm_assn ch v s S P) (InBlock ch w # tr)"
| "d \<notin> S \<Longrightarrow> d > 0 \<Longrightarrow> (in_tassm_assn ch v s S P)
      (WaitBlk d (\<lambda>\<tau>. s) ({}, {ch}) # InBlock ch w # tr)"



inductive in_vassm_assn :: "cname \<Rightarrow> (real set) \<Rightarrow> 'a gstate \<Rightarrow> (real \<Rightarrow> 'a tassn) \<Rightarrow> 'a tassn" where
  "P v tr \<Longrightarrow> v \<in> V \<Longrightarrow> (in_vassm_assn ch V s P) (InBlock ch v # tr)"
| "P v tr \<Longrightarrow> v \<in> V \<Longrightarrow> (d::real)> 0 \<Longrightarrow> (in_vassm_assn ch V s P)
      (WaitBlk d (\<lambda>\<tau>. s) ({}, {ch}) # InBlock ch v # tr)"
| "w \<notin> V \<Longrightarrow> (in_vassm_assn ch V s P) (InBlock ch w # tr)"
| "w \<notin> V \<Longrightarrow> (d::real) > 0 \<Longrightarrow> (in_vassm_assn ch V s P)
      (WaitBlk d (\<lambda>\<tau>. s) ({}, {ch}) # InBlock ch w # tr)"


inductive in_assms_assn :: "cname \<Rightarrow> real set \<Rightarrow> 'a gstate \<Rightarrow> real set \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> 'a tassn)\<Rightarrow> 'a tassn" where
  "v \<in> V \<Longrightarrow> 0 \<in> S \<Longrightarrow> (P v 0) tr \<Longrightarrow> (in_assms_assn ch V s S P) (InBlock ch v # tr)"
| "v \<in> V \<Longrightarrow> d \<in> S \<Longrightarrow> d > 0 \<Longrightarrow> (P v d) tr \<Longrightarrow> (in_assms_assn ch V s S P)
      (WaitBlk d (\<lambda>\<tau>. s) ({}, {ch}) # InBlock ch v # tr)"
| "0 \<notin> S \<or> w \<notin> V \<Longrightarrow> (in_assms_assn ch V s S P) (InBlock ch w # tr)"
| "d \<notin> S \<or> w \<notin> V \<Longrightarrow> d > 0 \<Longrightarrow> (in_assms_assn ch V s S P)
      (WaitBlk d (\<lambda>\<tau>. s) ({}, {ch}) # InBlock ch w # tr)"


inductive in_0assm_assn :: "cname \<Rightarrow> real \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "P tr \<Longrightarrow> (in_0assm_assn ch v P) (InBlock ch v # tr)"
| "d > 0 \<Longrightarrow> ch \<in> snd rdy \<Longrightarrow> (in_0assm_assn ch v P) (WaitBlk d p rdy # tr)"

inductive in_0assm_rdy_assn :: "cname \<Rightarrow> real \<Rightarrow> rdy_info \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "P tr \<Longrightarrow> (in_0assm_rdy_assn ch v rdy P) (InBlock ch v # tr)"
| "d > 0 \<Longrightarrow> ch \<in> snd rdy \<Longrightarrow> (in_0assm_rdy_assn ch v rdy P) (WaitBlk d p rdy # tr)"

inductive in_0orig_vassm_assn :: "cname \<Rightarrow> real set \<Rightarrow>(real \<Rightarrow> 'a tassn) \<Rightarrow> 'a tassn" where
  "P v tr \<Longrightarrow> v \<in> V \<Longrightarrow> (in_0orig_vassm_assn ch V P) (InBlock ch v # tr)"
| "v \<notin> V \<Longrightarrow> (in_0orig_vassm_assn ch V P) (InBlock ch v # tr)"

lemma in_0assm_assn_tran:
  assumes"P \<Longrightarrow>\<^sub>t Q "
  shows "in_0assm_assn ch v P \<Longrightarrow>\<^sub>t in_0assm_assn ch v Q"
  unfolding entails_tassn_def
  apply auto
  subgoal for tr
    apply(cases rule: in_0assm_assn.cases[of ch v P tr])
        apply auto
    subgoal for tr'
      apply(rule in_0assm_assn.intros(1))
      using assms by(auto simp add: entails_tassn_def)
    subgoal for d p a b tr'
      apply(rule in_0assm_assn.intros(2))
      using assms by(auto simp add: entails_tassn_def)
    done
  done

lemma in_0assm_rdy_assn_tran:
  assumes"P \<Longrightarrow>\<^sub>t Q "
  shows "in_0assm_rdy_assn ch v rdy P \<Longrightarrow>\<^sub>t in_0assm_rdy_assn ch v rdy Q"
  unfolding entails_tassn_def
  apply auto
  subgoal for tr
    apply(cases rule: in_0assm_rdy_assn.cases[of ch v rdy P tr])
        apply auto
    subgoal for tr'
      apply(rule in_0assm_rdy_assn.intros(1))
      using assms by(auto simp add: entails_tassn_def)
    subgoal for d p tr'
      apply(rule in_0assm_rdy_assn.intros(2))
      using assms by(auto simp add: entails_tassn_def)
    done
  done


lemma in_0orig_vassm_assn_tran:
  assumes"\<And> v. v \<in> V \<Longrightarrow> P v \<Longrightarrow>\<^sub>t Q v"
  shows "in_0orig_vassm_assn ch V P \<Longrightarrow>\<^sub>t in_0orig_vassm_assn ch V Q"
  unfolding entails_tassn_def
  apply auto
  subgoal for tr
    apply(cases rule: in_0orig_vassm_assn.cases[of ch V P tr])
        apply auto
    subgoal for tr'
      apply(rule in_0orig_vassm_assn.intros(1))
      using assms by(auto simp add: entails_tassn_def)
    subgoal for v tr'
      apply(rule in_0orig_vassm_assn.intros(2))
      using assms by(auto simp add: entails_tassn_def)
    done
  done

(* Communication of value v on channel ch during time within a set S,
   followed by trace satisfying P. *)
inductive io_guar_assn :: "cname \<Rightarrow> real \<Rightarrow> 'a gstate \<Rightarrow> real set \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "P tr \<Longrightarrow> 0 \<in> S \<Longrightarrow> (io_guar_assn ch v s S P) (IOBlock ch v # tr)"
| "P tr \<Longrightarrow> d \<in> S \<Longrightarrow> d > 0 \<Longrightarrow> (io_guar_assn ch v s S P)
      (WaitBlk d (\<lambda>\<tau>. s) ({}, {ch}) # IOBlock ch v # tr)"

inductive io_orig_assn :: "cname \<Rightarrow> real \<Rightarrow>  'a tassn \<Rightarrow> 'a tassn" where
  "P tr \<Longrightarrow> (io_orig_assn ch v P) (IOBlock ch v # tr)"


inductive wait_orig_assn :: "real \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "P tr \<Longrightarrow> d = 0 \<Longrightarrow> (wait_orig_assn d p rdy P) tr"
| "P tr \<Longrightarrow> d > 0 \<Longrightarrow> (wait_orig_assn d p rdy P) (WaitBlk d p rdy # tr)"

inductive wait_guar_assn :: "real set \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "P tr \<Longrightarrow> 0 \<in> S \<Longrightarrow> (wait_guar_assn S p rdy P) tr"
| "P tr \<Longrightarrow> d \<in> S \<Longrightarrow> d > 0 \<Longrightarrow> (wait_guar_assn S p rdy P) (WaitBlk d p rdy # tr)"

inductive wait_guar'_assn :: "real set \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> (real \<Rightarrow> 'a tassn) \<Rightarrow> 'a tassn" where
  "P 0 tr \<Longrightarrow> 0 \<in> S \<Longrightarrow> (wait_guar'_assn S p rdy P) tr"
| "P d tr \<Longrightarrow> d \<in> S \<Longrightarrow> d > 0 \<Longrightarrow> (wait_guar'_assn S p rdy P) (WaitBlk d p rdy # tr)"

lemma wait_orig_to_guard:
"wait_orig_assn v p rdy = wait_guar_assn {v} p rdy"
  apply(rule ext)
  subgoal for P
    apply(rule ext)
    subgoal for tr
      apply auto
      subgoal
        apply(cases rule:wait_orig_assn.cases[of v p rdy P tr])
          apply auto
        subgoal apply(rule wait_guar_assn.intros(1)) by auto
        subgoal for tr' apply(rule wait_guar_assn.intros(2)) by auto
        done
      subgoal
        apply(cases rule:wait_guar_assn.cases[of "{v}" p rdy P tr])
          apply auto
        subgoal apply(rule wait_orig_assn.intros(1)) by auto
        subgoal apply(rule wait_orig_assn.intros(2)) by auto
        done
      done
    done
  done

lemma wait_orig_to_guard':
"wait_orig_assn v p rdy P = wait_guar'_assn {v} p rdy (\<lambda>_ . P)"
  apply(rule ext)
   subgoal for tr
      apply auto
      subgoal
        apply(cases rule:wait_orig_assn.cases[of v p rdy P tr])
          apply auto
        subgoal apply(rule wait_guar'_assn.intros(1)) by auto
        subgoal for tr' apply(rule wait_guar'_assn.intros(2)) by auto
        done
      subgoal
        apply(cases rule:wait_guar'_assn.cases[of "{v}" p rdy "(\<lambda>_. P)" tr])
          apply auto
        subgoal apply(rule wait_orig_assn.intros(1)) by auto
        subgoal apply(rule wait_orig_assn.intros(2)) by auto
        done
      done
    done


lemma out_guar_equal_g1:
  "out_guar_assn ch v s S P tr \<Longrightarrow> wait_guar_assn S (\<lambda>_.s) ({},{}) (out_orig_assn ch v s P) tr"
  apply (cases rule: out_guar_assn.cases[of ch v s S P tr])
  subgoal by auto
  subgoal for tr'
    apply(rule wait_guar_assn.intros(1))
    apply auto
    apply(rule out_orig_assn.intros(1)) by auto
  subgoal for tr' d2
    apply(rule wait_guar_assn.intros(1))
     apply auto
    apply(rule out_orig_assn.intros(2)) by auto
  subgoal for tr' d1
    apply auto
    apply(rule wait_guar_assn.intros(2))
      apply auto
    apply(rule out_orig_assn.intros(1)) by auto
  subgoal for tr' d1 d2
    apply auto
    apply(rule wait_guar_assn.intros(2))
      apply auto
    apply(rule out_orig_assn.intros(2)) by auto
  done

lemma out_guar_equal_g2:
  "wait_guar_assn S (\<lambda>_.s) ({},{}) (out_orig_assn ch v s P) tr \<Longrightarrow> out_guar_assn ch v s S P tr"
  apply(cases rule:wait_guar_assn.cases[of S "(\<lambda>_.s)" "({}, {})""(out_orig_assn ch v s P)"" tr"])
  subgoal by auto
  subgoal
    apply(cases rule:out_orig_assn.cases[of ch v s P tr])
    subgoal by auto
    subgoal for tr'
      apply auto
      apply(rule out_guar_assn.intros(1)) by auto
    subgoal for tr' d2
      apply auto
      apply(rule out_guar_assn.intros(2)) by auto 
    done
  subgoal for tr' d1
    apply(cases rule:out_orig_assn.cases[of ch v s P tr'])
    subgoal by auto
    subgoal for tr''
      apply auto
      apply(rule out_guar_assn.intros(3)) by auto
    subgoal for tr'' d2
      apply auto
      apply(rule out_guar_assn.intros(4)) by auto
    done
  done

lemma out_guar_equal:
  "out_guar_assn ch v s S P = wait_guar_assn S (\<lambda>_.s) ({},{}) (out_orig_assn ch v s P)"
  apply(rule ext)
  subgoal for tr
    using out_guar_equal_g1 out_guar_equal_g2 by auto
  done

lemma wait_orig_assn_tran:
  assumes"P \<Longrightarrow>\<^sub>t Q "
  shows "wait_orig_assn s p rdy P \<Longrightarrow>\<^sub>t wait_orig_assn s p rdy Q"
  unfolding entails_tassn_def
  apply auto
  subgoal for tr
    apply(cases rule: wait_orig_assn.cases[of s p rdy P tr])
      apply auto
    subgoal
      apply(rule wait_orig_assn.intros(1))
      using assms 
      by(auto simp add:entails_tassn_def)
    subgoal for tr'
      apply(rule wait_orig_assn.intros(2))
      using assms
      by(auto simp add:entails_tassn_def)
    done
  done




lemma wait_guar'_assn_tran:
  assumes"\<And>v. v \<in> s \<Longrightarrow> P v \<Longrightarrow>\<^sub>t Q v"
  shows "wait_guar'_assn s p rdy P \<Longrightarrow>\<^sub>t wait_guar'_assn s p rdy Q"
  unfolding entails_tassn_def
  apply auto
  subgoal for tr
    apply(cases rule: wait_guar'_assn.cases[of s p rdy P tr])
      apply auto
    subgoal
      apply(rule wait_guar'_assn.intros(1))
      using assms 
      by(auto simp add:entails_tassn_def)
    subgoal for d tr'
      apply(rule wait_guar'_assn.intros(2))
      using assms
      by(auto simp add:entails_tassn_def)
    done
  done


lemma combine_emp_wait_orig1:
  assumes "d<0"
  shows "combine_assn chs emp\<^sub>t (wait_orig_assn d p rdy P) \<Longrightarrow>\<^sub>t R"
  unfolding entails_tassn_def combine_assn_def
  using assms
  apply auto
  apply(elim wait_orig_assn.cases)
  by auto
                               
lemma combine_emp_wait_orig2:
  assumes "d=0"
  shows "combine_assn chs emp\<^sub>t (wait_orig_assn d p rdy P) \<Longrightarrow>\<^sub>t combine_assn chs emp\<^sub>t P"
  unfolding entails_tassn_def combine_assn_def
  using assms
  apply auto
  apply(elim wait_orig_assn.cases)
  by auto

lemma combine_emp_wait_orig3:
  assumes "d>0"
  shows "combine_assn chs emp\<^sub>t (wait_orig_assn d p rdy P) \<Longrightarrow>\<^sub>t R"
  unfolding entails_tassn_def combine_assn_def
  using assms
  apply auto
  apply(elim wait_orig_assn.cases)
   apply (auto simp add: emp_assn_def)
  by(auto elim: sync_elims)

lemma combine_emp_wait_orig4:
  "d \<noteq> 0 \<Longrightarrow> combine_assn chs emp\<^sub>t (wait_orig_assn d p rdy P)\<Longrightarrow>\<^sub>t G"  
apply(auto simp add: entails_tassn_def)
  subgoal for tr
    apply(auto simp add: combine_assn_def emp_assn_def)
    subgoal for tr2
      apply(cases rule: wait_orig_assn.cases[of d p rdy P tr2])
      by (auto elim!: sync_elims)
    done
  done

lemma combine_emp_wait_orig5:
  "combine_assn chs emp\<^sub>t (wait_orig_assn d p rdy P)\<Longrightarrow>\<^sub>t combine_assn chs emp\<^sub>t P"  
apply(auto simp add: entails_tassn_def)
  subgoal for tr
    apply(auto simp add: combine_assn_def emp_assn_def)
    subgoal for tr2
      apply(cases rule: wait_orig_assn.cases[of d p rdy P tr2])
      by (auto elim!: sync_elims)
    done
  done

lemma combine_wait_orig_emp5:
  "combine_assn chs (wait_orig_assn d p rdy P) emp\<^sub>t \<Longrightarrow>\<^sub>t combine_assn chs P emp\<^sub>t"  
apply(auto simp add: entails_tassn_def)
  subgoal for tr
    apply(auto simp add: combine_assn_def emp_assn_def)
    subgoal for tr2
      apply(cases rule: wait_orig_assn.cases[of d p rdy P tr2])
      by (auto elim!: sync_elims)
    done
  done

lemma combine_io_orig_emp:
  "combine_assn chs (io_orig_assn ch v P) emp\<^sub>t \<Longrightarrow>\<^sub>t io_orig_assn ch v (combine_assn chs P emp\<^sub>t)"  
apply(auto simp add: entails_tassn_def)
  subgoal for tr
    apply(auto simp add: combine_assn_def emp_assn_def)
    subgoal for tr1
      apply(cases rule: io_orig_assn.cases[of ch v P tr1])
       apply (auto elim!: sync_elims)
      apply(rule io_orig_assn.intros)
      apply auto
    done
  done
  done

lemma io_orig_assn_tran:
  assumes"P \<Longrightarrow>\<^sub>t Q "
  shows "io_orig_assn ch v P \<Longrightarrow>\<^sub>t io_orig_assn ch v Q"
  unfolding entails_tassn_def
  apply auto
  subgoal for tr
    apply(cases rule: io_orig_assn.cases[of ch v P tr])
      apply auto
    subgoal
      apply(rule io_orig_assn.intros(1))
      using assms 
      by(auto simp add:entails_tassn_def)
    done
  done




lemma combine_out_guar_in_tassm1':
  "ch \<in> chs \<Longrightarrow>
   S1 \<subseteq> S2 \<Longrightarrow>
   combine_assn chs (out_guar_assn ch v s1 S1 P1) (in_tassm_assn ch v s2 S2 (\<lambda>t. P2)) tr \<Longrightarrow>
   io_guar_assn ch v (ParState s1 s2) S1 (combine_assn chs P1 P2) tr"
  unfolding combine_assn_def
  apply clarify subgoal for tr1 tr2
    apply (cases rule: out_guar_assn.cases[of ch v s1 S1 P1 tr1])
    subgoal by auto
    subgoal for tr1'
      apply (cases rule: in_tassm_assn.cases[of ch v s2 S2 "(\<lambda>t. P2)" tr2])
      subgoal by auto
      subgoal for tr2' by (auto elim!: combine_blocks_pairE intro: io_guar_assn.intros)
      subgoal for tr2' d1 by (auto elim!: sync_elims)
      subgoal for w tr2' by auto
      subgoal for d1 w tr2' by (auto elim!: sync_elims)
      done
    subgoal for tr1' d1
      apply (cases rule: in_tassm_assn.cases[of ch v s2 S2 "(\<lambda>t. P2)" tr2])
      by (auto elim!: sync_elims)
    subgoal for tr1' d1
      apply (cases rule: in_tassm_assn.cases[of ch v s2 S2 "(\<lambda>t. P2)" tr2])
      subgoal by auto
      subgoal for tr2' by (auto elim!: sync_elims)
      subgoal for d2 tr2'
        apply (cases "d1 < d2")
        subgoal apply auto apply (elim combine_blocks_waitE3)
          by (auto elim!: sync_elims)
        apply (cases "d2 < d1")
        subgoal apply auto apply (elim combine_blocks_waitE4)
          by (auto elim!: sync_elims)
        apply auto apply (elim combine_blocks_waitE2)
        subgoal by auto
        subgoal for tr'
          apply (elim combine_blocks_pairE)
            apply auto apply (rule io_guar_assn.intros)
          by auto
        done
      subgoal for w tr2' by (auto elim!: sync_elims)
      subgoal for d2 w tr2'
        apply (cases "d1 < d2")
        subgoal apply auto apply (elim combine_blocks_waitE3)
          by (auto elim!: sync_elims)
        apply (cases "d2 < d1")
        subgoal apply auto apply (elim combine_blocks_waitE4)
          by (auto elim!: sync_elims)
        by auto
      done
    subgoal for tr1' d1 d2
      apply (cases rule: in_tassm_assn.cases[of ch v s2 S2 "(\<lambda>t. P2)" tr2])
      subgoal by auto
      subgoal for tr2' by (auto elim!: sync_elims)
      subgoal for d tr2' 
        apply (cases "d1 < d")
        subgoal apply auto 
          apply (rule combine_blocks_waitE3
                            [of chs d1 "(\<lambda>\<tau>. s1)"" ({}, {})" 
                                "WaitBlk d2 (\<lambda>\<tau>. s1) ({ch}, {}) # OutBlock ch v # tr1'"
                                d "(\<lambda>\<tau>. s2)""({}, {ch})" "InBlock ch v # tr2'" tr])
          by (auto elim!: sync_elims)
        apply (cases "d < d1")
        subgoal apply auto apply (elim combine_blocks_waitE4)
          by (auto elim!: sync_elims)
        apply auto
        apply (elim combine_blocks_waitE2)
        subgoal by auto
        subgoal for tr' by (auto elim!: sync_elims)
        done
      subgoal for w tr2' by (auto elim!: sync_elims)
      subgoal for d w tr2'
        apply (cases "d1 < d")
        subgoal apply auto 
          apply (rule combine_blocks_waitE3
                            [of chs d1 "(\<lambda>\<tau>. s1)"" ({}, {})" 
                                "WaitBlk d2 (\<lambda>\<tau>. s1) ({ch}, {}) # OutBlock ch v # tr1'"
                                d "(\<lambda>\<tau>. s2)""({}, {ch})" "InBlock ch w # tr2'" tr])
          by (auto elim!: sync_elims)
        apply (cases "d < d1")
        subgoal apply auto apply (elim combine_blocks_waitE4)
          by (auto elim!: sync_elims)
        by auto
      done
    done
  done


lemma combine_in_orig_out_orig1':
  "ch \<in> chs \<Longrightarrow>
   combine_assn chs (in_orig_assn ch v s1 P1) (out_orig_assn ch v s2 P2) tr \<Longrightarrow>
   io_orig_assn ch v (combine_assn chs P1 P2) tr"
  apply(auto simp add:combine_assn_def)
  subgoal for tr1 tr2
    apply(cases rule: in_orig_assn.cases[of ch v s1 P1 tr1])
      apply auto
    subgoal for tr1'
      apply(cases rule: out_orig_assn.cases[of ch v s2 P2 tr2])
        apply auto
      subgoal for tr2'
        apply(elim combine_blocks_pairE)
          apply auto
        subgoal for tr'
          apply(rule io_orig_assn.intros)
          by auto
        done
      subgoal for tr2' d2
        by (auto elim!: sync_elims)
      done
    subgoal for tr1' d1
      apply(cases rule: out_orig_assn.cases[of ch v s2 P2 tr2])
        apply auto
      subgoal for tr2'
        by (auto elim!: sync_elims)
      subgoal for tr2' d2
        by (auto elim!: sync_elims)
      done
    done
  done


lemma combine_in_orig_out_orig1:
  "ch \<in> chs \<Longrightarrow>
   combine_assn chs (in_orig_assn ch v s1 P1) (out_orig_assn ch v s2 P2) \<Longrightarrow>\<^sub>t
   io_orig_assn ch v (combine_assn chs P1 P2) "
  apply(auto simp add:entails_tassn_def)
  subgoal for tr
    using combine_in_orig_out_orig1'  by blast
  done


lemma combine_in_vassm_out_orig1':
"ch \<in> chs \<Longrightarrow>
    v \<in> V \<Longrightarrow>
   combine_assn chs (in_vassm_assn ch V s1 P1) (out_orig_assn ch v s2 P2) tr \<Longrightarrow>
   io_orig_assn ch v (combine_assn chs (P1 v) P2) tr"
  apply(auto simp add:combine_assn_def)
  subgoal for tr1 tr2
    apply(cases rule: in_vassm_assn.cases[of ch V s1 P1 tr1])
        apply auto
    subgoal for v' tr1'
      apply(cases rule: out_orig_assn.cases[of ch v s2 P2 tr2])
        apply auto
      subgoal for tr2'
        apply(elim combine_blocks_pairE)
          apply auto
        apply(rule io_orig_assn.intros)
        by auto
      subgoal for d2 tr2'
        by (auto elim!: sync_elims)
      done
    subgoal for d1 tr1' v'
      apply(cases rule: out_orig_assn.cases[of ch v s2 P2 tr2])
        apply auto
      subgoal for tr2'
        by (auto elim!: sync_elims)
      subgoal for tr2' d2
        by (auto elim!: sync_elims)
      done
    subgoal for w tr1'
      apply(cases rule: out_orig_assn.cases[of ch v s2 P2 tr2])
        apply auto
      subgoal for tr2'
        apply(elim combine_blocks_pairE)
        by auto
      subgoal for tr2' d2
        by (auto elim!: sync_elims)
      done
    subgoal for w d1 tr1'
      apply(cases rule: out_orig_assn.cases[of ch v s2 P2 tr2])
        apply auto
      subgoal for tr2'
        by (auto elim!: sync_elims)
      subgoal for tr2' d2
        by (auto elim!: sync_elims)
      done
    done
  done

lemma combine_in_vassm_out_orig1:
"ch \<in> chs \<Longrightarrow>
    v \<in> V \<Longrightarrow>
   combine_assn chs (in_vassm_assn ch V s1 P1) (out_orig_assn ch v s2 P2) \<Longrightarrow>\<^sub>t
   io_orig_assn ch v (combine_assn chs (P1 v) P2) "
  apply(auto simp add:entails_tassn_def)
  using combine_in_vassm_out_orig1' by blast









inductive waitout_orig_assn :: "real \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> cname \<Rightarrow> 'a g_exp \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "P tr \<Longrightarrow> d = 0 \<Longrightarrow> (waitout_orig_assn d p rdy ch e P) (OutBlock ch (e(p d)) # tr)"
| "P tr \<Longrightarrow> d > 0 \<Longrightarrow> (waitout_orig_assn d p rdy ch e P) (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # OutBlock ch (e(p d)) # tr)"


inductive waitout_guar_assn :: "real set \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> cname \<Rightarrow> 'a g_exp \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "P tr \<Longrightarrow> d = 0 \<Longrightarrow> d \<in> S \<Longrightarrow> (waitout_guar_assn S p rdy ch e P) (OutBlock ch (e(p d)) # tr)"
| "P tr \<Longrightarrow> d > 0 \<Longrightarrow> d \<in> S \<Longrightarrow> (waitout_guar_assn S p rdy ch e P) (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # OutBlock ch (e(p d)) # tr)"


inductive waitout_assm_assn :: "real set \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> cname \<Rightarrow> 'a g_exp \<Rightarrow> 'a tassn \<Rightarrow> 'a tassn" where
  "P tr \<Longrightarrow> 0 \<in> S \<Longrightarrow> (waitout_assm_assn S p rdy ch e P) (OutBlock ch (e(p 0)) # tr)"
| "P tr \<Longrightarrow> d \<in> S \<Longrightarrow> d > 0 \<Longrightarrow> (waitout_assm_assn S p rdy ch e P)
      (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # OutBlock ch (e(p d)) # tr)"
| "0 \<notin> S \<Longrightarrow> (waitout_assm_assn S p rdy ch e P) (OutBlock ch w # tr)"
| "d \<notin> S \<Longrightarrow> d > 0 \<Longrightarrow> (waitout_assm_assn S p rdy ch e P)
      (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # OutBlock ch w # tr)"

inductive waitin_assms'_assn :: "real set \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> cname \<Rightarrow> real set \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> 'a tassn) \<Rightarrow> 'a tassn" where
  "v \<in> V \<Longrightarrow> 0 \<in> S \<Longrightarrow> (P v 0) tr \<Longrightarrow> (waitin_assms'_assn S p rdy ch V P) (InBlock ch v # tr)"
| "v \<in> V \<Longrightarrow> d \<in> S \<Longrightarrow> d > 0 \<Longrightarrow> (P v d) tr \<Longrightarrow> (waitin_assms'_assn S p rdy ch V P)
      (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # InBlock ch v # tr)"
| "0 \<notin> S \<or> w \<notin> V \<Longrightarrow> (waitin_assms'_assn S p rdy ch V P) (InBlock ch w # tr)"
| "d \<notin> S \<or> w \<notin> V \<Longrightarrow> d > 0 \<Longrightarrow> (waitin_assms'_assn S p rdy ch V P)
      (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # InBlock ch w # tr)"

inductive waitin_assms'_inv_assn :: "real set \<Rightarrow> ('a gstate \<Rightarrow> bool) \<Rightarrow> rdy_info \<Rightarrow> cname \<Rightarrow> real set \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> 'a tassn) \<Rightarrow> 'a tassn" where
  "v \<in> V \<Longrightarrow> 0 \<in> S \<Longrightarrow> (P v 0) tr \<Longrightarrow> (waitin_assms'_inv_assn S Inv rdy ch V P) (InBlock ch v # tr)"
| "v \<in> V \<Longrightarrow> d \<in> S \<Longrightarrow> d > 0 \<Longrightarrow> (P v d) tr \<Longrightarrow> \<forall> t\<in>{0..<d}. Inv (p t) \<Longrightarrow>
     (waitin_assms'_inv_assn S Inv rdy ch V P) (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # InBlock ch v # tr)"
| "0 \<notin> S \<or> w \<notin> V \<Longrightarrow> (waitin_assms'_inv_assn S Inv rdy ch V P) (InBlock ch w # tr)"
| "d \<notin> S \<or> w \<notin> V \<Longrightarrow> d > 0 \<Longrightarrow> (waitin_assms'_inv_assn S Inv rdy ch V P)
      (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # InBlock ch w # tr)"

inductive waitin_tguar'_vassm'_assn :: "real set \<Rightarrow> (real \<Rightarrow> 'a gstate) \<Rightarrow> rdy_info \<Rightarrow> cname \<Rightarrow> real set \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> 'a tassn) \<Rightarrow> 'a tassn" where
  "0 \<in> S \<Longrightarrow> v \<in> V \<Longrightarrow> (P v 0) tr \<Longrightarrow> (waitin_tguar'_vassm'_assn S p rdy ch V P) (InBlock ch v # tr)"
| "d \<in> S \<Longrightarrow> d > 0 \<Longrightarrow> v \<in> V \<Longrightarrow> (P v d) tr \<Longrightarrow> (waitin_tguar'_vassm'_assn S p rdy ch V P)
      (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # InBlock ch v # tr)"
| "0 \<in> S \<Longrightarrow> w \<notin> V \<Longrightarrow> (waitin_tguar'_vassm'_assn S p rdy ch V P) (InBlock ch w # tr)"
| "d \<in> S \<Longrightarrow> d > 0 \<Longrightarrow> w \<notin> V \<Longrightarrow> (waitin_tguar'_vassm'_assn S p rdy ch V P)
      (WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy # InBlock ch w # tr)"

lemma waitin_assms'_assn_tran:
  assumes"\<And> v d. v \<in> V \<and> d \<in> S \<Longrightarrow> P v d \<Longrightarrow>\<^sub>t Q v d"
  shows "waitin_assms'_assn S p rdy ch V P \<Longrightarrow>\<^sub>t waitin_assms'_assn S p rdy ch V Q"
  unfolding entails_tassn_def
  apply auto
  subgoal for tr
    apply(cases rule: waitin_assms'_assn.cases[of S p rdy ch V P tr])
      apply auto
    subgoal
      apply(rule waitin_assms'_assn.intros(1))
      using assms 
      by(auto simp add:entails_tassn_def)
    subgoal for d tr'
      apply(rule waitin_assms'_assn.intros(2))
      using assms
      by(auto simp add:entails_tassn_def)
    subgoal for w tr'
      apply(rule waitin_assms'_assn.intros(3))
      using assms
      by(auto simp add:entails_tassn_def)
    subgoal for w tr'
      apply(rule waitin_assms'_assn.intros(3))
      using assms
      by(auto simp add:entails_tassn_def)
    subgoal for d w tr'
      apply(rule waitin_assms'_assn.intros(4))
      using assms
      by(auto simp add:entails_tassn_def)
    subgoal for d w tr'
      apply(rule waitin_assms'_assn.intros(4))
      using assms
      by(auto simp add:entails_tassn_def)
    done
  done

lemma waitin_tguar'_vassm'_assn_tran:
  assumes"\<And> v d. v \<in> V \<and> d \<in> S \<Longrightarrow> P v d \<Longrightarrow>\<^sub>t Q v d"
  shows "waitin_tguar'_vassm'_assn S p rdy ch V P \<Longrightarrow>\<^sub>t waitin_tguar'_vassm'_assn S p rdy ch V Q"
  unfolding entails_tassn_def
  apply auto
  subgoal for tr
    apply(cases rule: waitin_tguar'_vassm'_assn.cases[of S p rdy ch V P tr])
      apply auto
    subgoal
      apply(rule waitin_tguar'_vassm'_assn.intros(1))
      using assms 
      by(auto simp add:entails_tassn_def)
    subgoal for d v tr'
      apply(rule waitin_tguar'_vassm'_assn.intros(2))
      using assms
      by(auto simp add:entails_tassn_def)
    subgoal for w tr'
      apply(rule waitin_tguar'_vassm'_assn.intros(3))
      using assms
      by(auto simp add:entails_tassn_def)
    subgoal for d w tr'
      apply(rule waitin_tguar'_vassm'_assn.intros(4))
      using assms
      by(auto simp add:entails_tassn_def)
    done
  done

definition wait_set_minus :: "real set \<Rightarrow> real set \<Rightarrow> real set" where
"wait_set_minus S1 S2 = {x. \<forall> y \<in> S2 \<inter> {0..}. \<exists> z \<in> S1 \<inter> {0..}. x = z-y}"

lemma exist_domain[simp]:
  assumes "\<exists> x. x \<in> S \<and> p x"
  shows "\<exists> x\<in> S. p x"
  using assms
  by auto

lemma combine_waitout_assm_wait_guar1':
assumes "ch \<in> chs "
    and "compat_rdy rdy1 rdy2"
  shows "combine_assn chs (waitout_assm_assn S1 p rdy1 ch e P) (wait_guar_assn S2 q rdy2 Q) tr \<Longrightarrow>
   wait_guar'_assn S2 (\<lambda>t. ParState (p t) (q t)) (merge_rdy rdy1 rdy2) 
        (\<lambda>d. combine_assn chs (waitout_assm_assn (wait_set_minus S1 S2) (\<lambda>t. p(t+d)) rdy1 ch e P) Q) tr"
  unfolding combine_assn_def
  apply clarify subgoal for tr1 tr2
    apply(cases rule: waitout_assm_assn.cases[of S1 p rdy1 ch e P tr1])
        apply auto
    subgoal for tr1' 
      apply(cases rule: wait_guar_assn.cases[of S2 q rdy2 Q tr2])
        apply auto
      subgoal
        apply(rule wait_guar'_assn.intros(1))
         apply auto
        apply(rule exI[where x="tr1"])
        apply auto
        using waitout_assm_assn.intros(1) 
          using waitout_assm_assn.intros(3)
          by (smt (verit, best))
      subgoal for tr2' d
        using assms by (auto elim!: sync_elims)
      done
    subgoal for tr1' d1
      apply(cases rule: wait_guar_assn.cases[of S2 q rdy2 Q tr2])
        apply auto
      subgoal
        apply(rule wait_guar'_assn.intros(1))
         apply auto
        apply(rule exI[where x="tr1"])
        apply auto
        using waitout_assm_assn.intros(2) 
          using waitout_assm_assn.intros(4)
          by (smt (verit, best))
      subgoal for tr2' d2
        apply(cases "d2>d1")
        subgoal
          apply(elim combine_blocks_waitE3)
          using assms
          by (auto elim!: sync_elims)
        apply(cases "d2=d1")
        subgoal
          apply auto
          apply(elim combine_blocks_waitE2)
          using assms apply auto
          apply(rule wait_guar'_assn.intros(2))
            apply auto
          subgoal for tr'
            apply(rule exI[where x="(OutBlock ch (e (p d1)) # tr1')"])
            apply auto
            using waitout_assm_assn.intros(1) 
            using waitout_assm_assn.intros(3) 
              by (smt (verit, best))
            done
        apply(elim combine_blocks_waitE4)
        using assms
           apply auto
        subgoal for tr'
          apply(rule wait_guar'_assn.intros(2))
            apply auto
          apply(rule exI[where x="(WaitBlk ((d1 - d2)) (\<lambda>t. p (t + d2)) rdy1 # OutBlock ch (e (p d1)) # tr1')"])
          apply auto
          using waitout_assm_assn.intros(2) 
          using waitout_assm_assn.intros(4)
          by (smt (verit, best))
        done
      done
    subgoal for w tr1'
      apply(cases rule: wait_guar_assn.cases[of S2 q rdy2 Q tr2])
        apply auto
      subgoal
        apply(rule wait_guar'_assn.intros(1))
         apply auto
        apply(rule exI[where x="(OutBlock ch w # tr1')"])
        apply auto
        apply(rule waitout_assm_assn.intros(3))
        by(auto simp add:wait_set_minus_def)
      subgoal for tr2' d2
        using assms
        by (auto elim!: sync_elims)
      done
    subgoal for d1 w tr1'
      apply(cases rule: wait_guar_assn.cases[of S2 q rdy2 Q tr2])
        apply auto
      subgoal
        apply(rule wait_guar'_assn.intros(1))
         apply auto
        apply(rule exI[where x="(WaitBlk d1 p rdy1 # OutBlock ch w # tr1')"])
        apply auto
        apply(rule waitout_assm_assn.intros(4))
         apply(auto simp add:wait_set_minus_def)
        apply(rule exist_domain)
        by auto
      subgoal for tr2' d2
        apply(cases "d2>d1")
        subgoal
          apply(elim combine_blocks_waitE3)
          using assms
          by (auto elim!: sync_elims)
        apply(cases "d2=d1")
        subgoal
          apply auto
          apply(elim combine_blocks_waitE2)
          using assms apply auto
          apply(rule wait_guar'_assn.intros(2))
            apply auto
          subgoal for tr'
            apply(rule exI[where x="(OutBlock ch w # tr1')"])
            apply auto
            apply(rule waitout_assm_assn.intros(3))
            by(auto simp add:wait_set_minus_def)
            done
          apply(elim combine_blocks_waitE4)
          using assms
             apply auto
          subgoal for tr'
            apply(rule wait_guar'_assn.intros(2))
              apply auto
            apply(rule exI[where x="(WaitBlk ((d1 - d2)) (\<lambda>t. p (t + d2)) rdy1 # OutBlock ch w # tr1')"])
            apply auto
            apply(rule waitout_assm_assn.intros(4))
             apply(simp add:wait_set_minus_def)
             apply(rule exist_domain)
            by auto
          done
        done
      done
    done

lemma combine_waitout_assm_wait_guar1:
assumes "ch \<in> chs "
    and "compat_rdy rdy1 rdy2"
  shows "combine_assn chs (waitout_assm_assn S1 p rdy1 ch e P) (wait_guar_assn S2 q rdy2 Q) \<Longrightarrow>\<^sub>t
   wait_guar'_assn S2 (\<lambda>t. ParState (p t) (q t)) (merge_rdy rdy1 rdy2) 
        (\<lambda>d. combine_assn chs (waitout_assm_assn (wait_set_minus S1 S2) (\<lambda>t. p(t+d)) rdy1 ch e P) Q) "       
  unfolding  entails_tassn_def
  apply auto
  using combine_waitout_assm_wait_guar1' assms by blast



lemma combine_waitout_assm_in_orig1':
  assumes "ch \<in> chs "
    and "0 \<in> S1"
    and "ch \<in> fst rdy1"
  shows "combine_assn chs (waitout_assm_assn S1 p rdy1 ch e P) (in_orig_assn ch r s Q) tr \<Longrightarrow>
   io_orig_assn ch r (combine_assn chs P Q) tr"
  unfolding combine_assn_def
  apply auto
  subgoal for tr1 tr2
    apply(cases rule: waitout_assm_assn.cases[of S1 p rdy1 ch e P tr1])
        apply auto
    subgoal for tr1'
      apply(cases rule:in_orig_assn.cases[of ch r s Q tr2])
        apply auto
      subgoal for tr2'
        apply(elim combine_blocks_pairE)
        using assms apply auto
        apply(rule io_orig_assn.intros)
        by auto
      subgoal for d2 tr2'
        using assms
        by (auto elim!: sync_elims)
      done
    subgoal for tr1' d1
      apply(cases rule:in_orig_assn.cases[of ch r s Q tr2])
        apply auto
      subgoal for tr2'
        using assms
        by (auto elim!: sync_elims)
      subgoal for tr2' d2
        using assms
        apply (auto elim!: sync_elims) 
        apply (cases rdy1) 
        by auto
      done
    subgoal for w tr1'
      apply(cases rule:in_orig_assn.cases[of ch r s Q tr2])
        apply auto
      subgoal for tr2'
        using assms by auto
      subgoal for tr2' d2
        using assms by auto
      done
    subgoal for d1 w tr1'
      apply(cases rule:in_orig_assn.cases[of ch r s Q tr2])
        apply auto
      subgoal for tr2'
        apply (auto elim!: sync_elims)
        using assms by auto
      subgoal for tr2' d2
        apply (auto elim!: sync_elims) 
        apply (cases rdy1) 
        using assms
        by auto
      done
    done
  done


lemma combine_waitout_assm_in_orig1:
  assumes "ch \<in> chs "
    and "0 \<in> S1"
    and "ch \<in> fst rdy1"
  shows "combine_assn chs (waitout_assm_assn S1 p rdy1 ch e P) (in_orig_assn ch r s Q) \<Longrightarrow>\<^sub>t
   io_orig_assn ch r (combine_assn chs P Q)"
  apply(auto simp add: entails_tassn_def)
  using combine_waitout_assm_in_orig1' assms by blast


lemma combine_waitout_assm_emp1:
  "ch \<in> chs \<Longrightarrow> combine_assn chs (waitout_assm_assn S p rdy ch e P) emp\<^sub>t \<Longrightarrow>\<^sub>t G"
  apply(auto simp add: entails_tassn_def)
  subgoal for tr
    apply(auto simp add: combine_assn_def emp_assn_def)
    subgoal for tr1 
      apply(cases rule: waitout_assm_assn.cases[of S p rdy ch e P tr1])
      by (auto elim!: sync_elims)
    done
  done

lemma combine_waitin_assm'_out_orig1':
  assumes "ch \<in> chs "
    and "0 \<in> S1"
    and "ch \<in> snd rdy1"
    and "r \<in> V"
  shows "combine_assn chs (waitin_assms'_assn S1 p rdy1 ch V P) (out_orig_assn ch r s Q) tr \<Longrightarrow>
   io_orig_assn ch r (combine_assn chs (P r 0)Q) tr"
  unfolding combine_assn_def
  apply auto
  subgoal for tr1 tr2
    apply(cases rule: waitin_assms'_assn.cases[of S1 p rdy1 ch V P tr1])
        apply auto
    subgoal for v tr1'
      apply(cases rule:out_orig_assn.cases[of ch r s Q tr2])
        apply auto
      subgoal for tr2'
        apply(elim combine_blocks_pairE)
        using assms apply auto
        apply(rule io_orig_assn.intros)
        by auto
      subgoal for d2 tr2'
        using assms
        by (auto elim!: sync_elims)
      done
    subgoal for v1 d1 tr1' 
      apply(cases rule:out_orig_assn.cases[of ch r s Q tr2])
        apply auto
      subgoal for tr2'
        using assms
        by (auto elim!: sync_elims)
      subgoal for tr2' d2
        using assms
        apply (auto elim!: sync_elims) 
        apply (cases rdy1) 
        by auto
      done
    subgoal for w tr1'
      apply(cases rule:out_orig_assn.cases[of ch r s Q tr2])
        apply auto
      subgoal for tr2'
        using assms by auto
      subgoal for tr2' d2
        using assms by auto
      done
    subgoal for w tr1'
      apply(cases rule:out_orig_assn.cases[of ch r s Q tr2])
        apply auto
      subgoal for tr2'
        apply (elim combine_blocks_pairE)
        using assms
        by auto
      subgoal for tr2' d2
        apply (auto elim!: sync_elims) 
        apply (cases rdy1) 
        using assms
        by auto
      done
    subgoal for d1 w tr1'
      apply(cases rule:out_orig_assn.cases[of ch r s Q tr2])
        apply auto
      subgoal for tr2'
        apply (auto elim!: sync_elims)
        using assms
        by auto
      subgoal for tr2' d2
        apply (auto elim!: sync_elims) 
        apply (cases rdy1) 
        using assms
        by auto
      done
    subgoal for d1 w tr1'
      apply(cases rule:out_orig_assn.cases[of ch r s Q tr2])
        apply auto
      subgoal for tr2'
        apply (auto elim!: sync_elims)
        using assms
        by auto
      subgoal for tr2' d2
        apply (auto elim!: sync_elims) 
        apply (cases rdy1) 
        using assms
        by auto
    done
  done
  done


lemma combine_waitin_assm'_out_orig1:
  assumes "ch \<in> chs "
    and "0 \<in> S1"
    and "ch \<in> snd rdy1"
    and "r \<in> V"
  shows "combine_assn chs (waitin_assms'_assn S1 p rdy1 ch V P) (out_orig_assn ch r s Q) \<Longrightarrow>\<^sub>t 
   io_orig_assn ch r (combine_assn chs (P r 0)Q) "
  apply(auto simp add: entails_tassn_def)
  using combine_waitin_assm'_out_orig1' assms
  by blast


lemma combine_waitin_assm'_inv_out_orig1':
  assumes "ch \<in> chs "
    and "0 \<in> S1"
    and "ch \<in> snd rdy1"
    and "r \<in> V"
  shows "combine_assn chs (waitin_assms'_inv_assn S1 Inv rdy1 ch V P) (out_orig_assn ch r s Q) tr \<Longrightarrow>
   io_orig_assn ch r (combine_assn chs (P r 0)Q) tr"
  unfolding combine_assn_def
  apply auto
  subgoal for tr1 tr2
    apply(cases rule: waitin_assms'_inv_assn.cases[of S1 Inv rdy1 ch V P tr1])
        apply auto
    subgoal for v tr1'
      apply(cases rule:out_orig_assn.cases[of ch r s Q tr2])
        apply auto
      subgoal for tr2'
        apply(elim combine_blocks_pairE)
        using assms apply auto
        apply(rule io_orig_assn.intros)
        by auto
      subgoal for d2 tr2'
        using assms
        by (auto elim!: sync_elims)
      done
    subgoal for v1 d1 tr1' 
      apply(cases rule:out_orig_assn.cases[of ch r s Q tr2])
        apply auto
      subgoal for tr2'
        using assms
        by (auto elim!: sync_elims)
      subgoal for tr2' d2
        using assms
        apply (auto elim!: sync_elims) 
        apply (cases rdy1) 
        by auto
      done
    subgoal for w tr1'
      apply(cases rule:out_orig_assn.cases[of ch r s Q tr2])
        apply auto
      subgoal for tr2'
        using assms by auto
      subgoal for tr2' d2
        using assms by auto
      done
    subgoal for w tr1'
      apply(cases rule:out_orig_assn.cases[of ch r s Q tr2])
        apply auto
      subgoal for tr2'
        apply (elim combine_blocks_pairE)
        using assms
        by auto
      subgoal for tr2' d2
        apply (auto elim!: sync_elims) 
        apply (cases rdy1) 
        using assms
        by auto
      done
    subgoal for d1 w tr1'
      apply(cases rule:out_orig_assn.cases[of ch r s Q tr2])
        apply auto
      subgoal for tr2'
        apply (auto elim!: sync_elims)
        using assms
        by auto
      subgoal for tr2' d2
        apply (auto elim!: sync_elims) 
        apply (cases rdy1) 
        using assms
        by auto
      done
    subgoal for d1 w tr1'
      apply(cases rule:out_orig_assn.cases[of ch r s Q tr2])
        apply auto
      subgoal for tr2'
        apply (auto elim!: sync_elims)
        using assms
        by auto
      subgoal for tr2' d2
        apply (auto elim!: sync_elims) 
        apply (cases rdy1) 
        using assms
        by auto
    done
  done
  done


lemma combine_waitin_assm'_inv_out_orig1:
  assumes "ch \<in> chs "
    and "0 \<in> S1"
    and "ch \<in> snd rdy1"
    and "r \<in> V"
  shows "combine_assn chs (waitin_assms'_inv_assn S1 Inv rdy1 ch V P) (out_orig_assn ch r s Q) \<Longrightarrow>\<^sub>t 
   io_orig_assn ch r (combine_assn chs (P r 0)Q) "
  apply(auto simp add: entails_tassn_def)
  using assms combine_waitin_assm'_inv_out_orig1'
  by blast



lemma combine_out_tassm_wait_guar1':
assumes "ch \<in> chs "
    and "compat_rdy ({ch}, {}) rdy2"
  shows "combine_assn chs (out_tassm_assn ch v s S1 P) (wait_guar_assn S2 q rdy2 Q) tr \<Longrightarrow>
   wait_guar'_assn S2 (\<lambda>t. ParState s (q t)) (merge_rdy ({ch}, {}) rdy2) 
        (\<lambda>d. combine_assn chs (out_tassm_assn ch v s (wait_set_minus S1 S2) (\<lambda>t. P(d+t))) Q) tr"
  unfolding combine_assn_def
  apply clarify subgoal for tr1 tr2       
    apply(cases rule :out_tassm_assn.cases[of ch v s S1 P tr1])
        apply auto
    subgoal for tr1'
      apply(cases rule:wait_guar_assn.cases[of S2 q rdy2 Q tr2])
        apply auto
      subgoal
        apply(rule wait_guar'_assn.intros(1))
         apply auto
        apply(rule exI[where x= tr1])
        apply auto
        by (metis out_tassm_assn.intros(1) out_tassm_assn.intros(3))
      subgoal for d2 tr2'
        using assms
        by (auto elim!: sync_elims)
      done
    subgoal for d1 tr1'
      apply(cases rule:wait_guar_assn.cases[of S2 q rdy2 Q tr2])
        apply auto
      subgoal
        apply(rule wait_guar'_assn.intros(1))
         apply auto
        apply(rule exI[where x= tr1])
        by (metis out_tassm_assn.intros(2) out_tassm_assn.intros(4))
      subgoal for tr2' d2
        apply(cases "d1<d2")
        subgoal
         apply(elim combine_blocks_waitE3)
        using assms apply auto
        subgoal for tr'
          by (auto elim!: sync_elims)
        done
      apply(cases "d1=d2")
      subgoal
        apply auto
        apply(elim combine_blocks_waitE2)
        using assms apply auto
        subgoal for tr'
          apply(rule wait_guar'_assn.intros(2))
            apply auto
          apply(rule exI[where x="(OutBlock ch v # tr1')"])
          apply auto
          by (smt (verit, best) out_tassm_assn.intros(1) out_tassm_assn.intros(3))
        done
      apply auto
      apply(elim combine_blocks_waitE4)
      using assms
         apply auto
      subgoal for tr'
        apply(rule wait_guar'_assn.intros(2))
          apply auto
        apply(rule exI[where x="(WaitBlk ((d1 - d2)) (\<lambda>t. s) ({ch}, {}) # OutBlock ch v # tr1')"])
        apply auto
        apply(cases "(d1 - d2)\<in>wait_set_minus S1 S2")
         apply(rule out_tassm_assn.intros(2)) 
           apply auto
        apply(rule out_tassm_assn.intros(4))
        by auto
      done
    done
  subgoal for w tr1'
    apply(cases rule:wait_guar_assn.cases[of S2 q rdy2 Q tr2])
      apply auto
    subgoal
      apply(rule wait_guar'_assn.intros(1))
       apply auto
      apply(rule exI[where x="tr1"])
      apply auto
      apply(rule out_tassm_assn.intros(3))
      by(auto simp add:wait_set_minus_def)
    subgoal for d2 tr2'
      using assms
      by (auto elim!: sync_elims)
    done
  subgoal for d1 w tr1'
    apply(cases rule:wait_guar_assn.cases[of S2 q rdy2 Q tr2])
      apply auto
    subgoal
      apply(rule wait_guar'_assn.intros(1))
       apply auto
      apply(rule exI[where x="tr1"])
      apply auto
      apply(rule out_tassm_assn.intros(4))
       apply(auto simp add: wait_set_minus_def)
      apply(rule exist_domain)
      apply(rule exI[where x=0])
      by auto
    subgoal for tr2' d2
      apply(cases "d2>d1")
      subgoal
        apply(elim combine_blocks_waitE3)
        using assms
        by (auto elim!: sync_elims)
      apply(cases "d1=d2")
       apply auto
      subgoal
        apply(elim combine_blocks_waitE2)
        using assms apply auto
        subgoal for tr'
          apply(rule wait_guar'_assn.intros(2))
            apply auto
          apply(rule exI[where x="(OutBlock ch w # tr1')"])
          apply auto
          apply(rule out_tassm_assn.intros(3))
          by(auto simp add:wait_set_minus_def)
        done
      apply(elim combine_blocks_waitE4)
      using assms
         apply auto
      subgoal for tr'
        apply(rule wait_guar'_assn.intros(2))
          apply auto
        apply(rule exI[where x="(WaitBlk ((d1 - d2)) (\<lambda>t. s) ({ch}, {}) # OutBlock ch w # tr1')"])
        apply auto
        apply(rule out_tassm_assn.intros(4))
         apply(auto simp add:wait_set_minus_def)
        apply(rule exist_domain)
        apply(rule exI[where x=d2])
        by auto
      done
    done
  done
  done


lemma combine_out_tassm_wait_guar1:
assumes "ch \<in> chs "
    and "compat_rdy ({ch}, {}) rdy2"
  shows "combine_assn chs (out_tassm_assn ch v s S1 P) (wait_guar_assn S2 q rdy2 Q) \<Longrightarrow>\<^sub>t
   wait_guar'_assn S2 (\<lambda>t. ParState s (q t)) (merge_rdy ({ch}, {}) rdy2) 
        (\<lambda>d. combine_assn chs (out_tassm_assn ch v s (wait_set_minus S1 S2) (\<lambda>t. P(d+t))) Q) "
  unfolding entails_tassn_def
  using combine_out_tassm_wait_guar1' assms 
  by blast


lemma combine_in_tassm_wait_guar1':
assumes "ch \<in> chs "
    and "compat_rdy ({}, {ch}) rdy2"
  shows "combine_assn chs (in_tassm_assn ch v s S1 P) (wait_guar_assn S2 q rdy2 Q) tr \<Longrightarrow>
   wait_guar'_assn S2 (\<lambda>t. ParState s (q t)) (merge_rdy ({}, {ch}) rdy2) 
        (\<lambda>d. combine_assn chs (in_tassm_assn ch v s (wait_set_minus S1 S2) (\<lambda>t. P(d+t))) Q) tr"
  unfolding combine_assn_def
  apply clarify subgoal for tr1 tr2       
    apply(cases rule :in_tassm_assn.cases[of ch v s S1 P tr1])
        apply auto
    subgoal for tr1'
      apply(cases rule:wait_guar_assn.cases[of S2 q rdy2 Q tr2])
        apply auto
      subgoal
        apply(rule wait_guar'_assn.intros(1))
         apply auto
        apply(rule exI[where x= tr1])
        apply auto
        by (metis in_tassm_assn.intros(1) in_tassm_assn.intros(3))
      subgoal for d2 tr2'
        using assms
        by (auto elim!: sync_elims)
      done
    subgoal for d1 tr1'
      apply(cases rule:wait_guar_assn.cases[of S2 q rdy2 Q tr2])
        apply auto
      subgoal
        apply(rule wait_guar'_assn.intros(1))
         apply auto
        apply(rule exI[where x= tr1])
        by (metis in_tassm_assn.intros(2) in_tassm_assn.intros(4))
      subgoal for tr2' d2
        apply(cases "d1<d2")
        subgoal
         apply(elim combine_blocks_waitE3)
        using assms apply auto
        subgoal for tr'
          by (auto elim!: sync_elims)
        done
      apply(cases "d1=d2")
      subgoal
        apply auto
        apply(elim combine_blocks_waitE2)
        using assms apply auto
        subgoal for tr'
          apply(rule wait_guar'_assn.intros(2))
            apply auto
          apply(rule exI[where x="(InBlock ch v # tr1')"])
          apply auto
          by (smt (verit, best) in_tassm_assn.intros(1) in_tassm_assn.intros(3))
        done
      apply auto
      apply(elim combine_blocks_waitE4)
      using assms
         apply auto
      subgoal for tr'
        apply(rule wait_guar'_assn.intros(2))
          apply auto
        apply(rule exI[where x="(WaitBlk ((d1 - d2)) (\<lambda>t. s) ({}, {ch}) # InBlock ch v # tr1')"])
        apply auto
        apply(cases "(d1 - d2)\<in>wait_set_minus S1 S2")
         apply(rule in_tassm_assn.intros(2)) 
           apply auto
        apply(rule in_tassm_assn.intros(4))
        by auto
      done
    done
  subgoal for w tr1'
    apply(cases rule:wait_guar_assn.cases[of S2 q rdy2 Q tr2])
      apply auto
    subgoal
      apply(rule wait_guar'_assn.intros(1))
       apply auto
      apply(rule exI[where x="tr1"])
      apply auto
      apply(rule in_tassm_assn.intros(3))
      by(auto simp add:wait_set_minus_def)
    subgoal for d2 tr2'
      using assms
      by (auto elim!: sync_elims)
    done
  subgoal for d1 w tr1'
    apply(cases rule:wait_guar_assn.cases[of S2 q rdy2 Q tr2])
      apply auto
    subgoal
      apply(rule wait_guar'_assn.intros(1))
       apply auto
      apply(rule exI[where x="tr1"])
      apply auto
      apply(rule in_tassm_assn.intros(4))
       apply(auto simp add: wait_set_minus_def)
      apply(rule exist_domain)
      apply(rule exI[where x=0])
      by auto
    subgoal for tr2' d2
      apply(cases "d2>d1")
      subgoal
        apply(elim combine_blocks_waitE3)
        using assms
        by (auto elim!: sync_elims)
      apply(cases "d1=d2")
       apply auto
      subgoal
        apply(elim combine_blocks_waitE2)
        using assms apply auto
        subgoal for tr'
          apply(rule wait_guar'_assn.intros(2))
            apply auto
          apply(rule exI[where x="(InBlock ch w # tr1')"])
          apply auto
          apply(rule in_tassm_assn.intros(3))
          by(auto simp add:wait_set_minus_def)
        done
      apply(elim combine_blocks_waitE4)
      using assms
         apply auto
      subgoal for tr'
        apply(rule wait_guar'_assn.intros(2))
          apply auto
        apply(rule exI[where x="(WaitBlk ((d1 - d2)) (\<lambda>t. s) ({}, {ch}) # InBlock ch w # tr1')"])
        apply auto
        apply(rule in_tassm_assn.intros(4))
         apply(auto simp add:wait_set_minus_def)
        apply(rule exist_domain)
        apply(rule exI[where x=d2])
        by auto
      done
    done
  done
  done

    
lemma combine_in_tassm_wait_guar1:
assumes "ch \<in> chs "
    and "compat_rdy ({}, {ch}) rdy2"
  shows "combine_assn chs (in_tassm_assn ch v s S1 P) (wait_guar_assn S2 q rdy2 Q) \<Longrightarrow>\<^sub>t
   wait_guar'_assn S2 (\<lambda>t. ParState s (q t)) (merge_rdy ({}, {ch}) rdy2) 
        (\<lambda>d. combine_assn chs (in_tassm_assn ch v s (wait_set_minus S1 S2) (\<lambda>t. P(d+t))) Q) "
  unfolding entails_tassn_def
  using combine_in_tassm_wait_guar1' assms 
  by blast
        


lemma combine_in_vassm_wait_guar1':
assumes "ch \<in> chs "
    and "compat_rdy ({}, {ch}) rdy2"
  shows "combine_assn chs (in_vassm_assn ch V s P) (wait_guar_assn S2 q rdy2 Q) tr \<Longrightarrow>
   wait_guar_assn S2 (\<lambda>t. ParState s (q t)) (merge_rdy ({}, {ch}) rdy2) 
        (combine_assn chs (in_vassm_assn ch V s P) Q) tr"
  unfolding combine_assn_def    
  apply auto
  subgoal for tr1 tr2
    apply(cases rule:in_vassm_assn.cases[of ch V s P tr1])
        apply auto
    subgoal for v tr1'
      apply(cases rule:wait_guar_assn.cases[of S2 q rdy2 Q tr2])
        apply auto
      subgoal
        apply(rule wait_guar_assn.intros(1))
        by auto
      subgoal for tr2' d
        using assms
        by (auto elim!: sync_elims)
      done
    subgoal for v tr1' d1
      apply(cases rule:wait_guar_assn.cases[of S2 q rdy2 Q tr2])
        apply auto
      subgoal
        apply(rule wait_guar_assn.intros(1))
        by auto
      subgoal for tr2' d2
        apply(cases "d2>d1")
        subgoal
          apply(elim combine_blocks_waitE3)
          using assms apply auto
          subgoal for tr'
            by (auto elim!: sync_elims)
          done
        apply(cases "d2=d1")
        subgoal
          apply auto
          apply(elim combine_blocks_waitE2)
          using assms
           apply auto
          subgoal for tr'
            apply(rule wait_guar_assn.intros(2))
              apply auto
            apply(rule exI[where x="(InBlock ch v # tr1')"])
            apply auto
            apply(rule in_vassm_assn.intros(1))
            by auto
          done
        apply(elim combine_blocks_waitE4)
        using assms
           apply auto
        subgoal for tr'
          apply(rule wait_guar_assn.intros(2))
            apply auto
          apply(rule exI[where x="(WaitBlk ((d1 - d2)) (\<lambda>t. s) ({}, {ch}) # InBlock ch v # tr1')"])
          apply auto
          apply(rule in_vassm_assn.intros(2))
          by auto
        done
      done
    subgoal for w tr1'
      apply(cases rule:wait_guar_assn.cases[of S2 q rdy2 Q tr2])
        apply auto
      subgoal
        apply(rule wait_guar_assn.intros(1))
        by auto
      subgoal for tr2' d2
        using assms
        by (auto elim!: sync_elims)
      done
    subgoal for w d1 tr1'
      apply(cases rule:wait_guar_assn.cases[of S2 q rdy2 Q tr2])
        apply auto
      subgoal
        apply(rule wait_guar_assn.intros(1))
        by auto
      subgoal for tr2' d2
        apply(cases "d2>d1")
        subgoal
          apply(elim combine_blocks_waitE3)
          using assms 
             apply auto
          subgoal for tr'
            by (auto elim!: sync_elims)
          done
        apply(cases "d2=d1")
        subgoal
          apply auto
          apply(elim combine_blocks_waitE2)
          using assms 
           apply auto
          subgoal for tr'
            apply(rule wait_guar_assn.intros(2))
              apply auto
            apply(rule exI[where x="(InBlock ch w # tr1')"])
            apply auto
            apply(rule in_vassm_assn.intros(3))
            by auto
          done
        apply(elim combine_blocks_waitE4)
        using assms apply auto
        subgoal for tr'
          apply(rule wait_guar_assn.intros(2))
            apply auto
          apply(rule exI[where x="WaitBlk ((d1 - d2)) (\<lambda>t. s) ({}, {ch}) # InBlock ch w # tr1'"])
          apply auto
          apply(rule in_vassm_assn.intros(4))
          by auto
        done
      done
    done
  done
  

lemma combine_in_vassm_wait_guar1:
assumes "ch \<in> chs "
    and "compat_rdy ({}, {ch}) rdy2"
  shows "combine_assn chs (in_vassm_assn ch V s P) (wait_guar_assn S2 q rdy2 Q) \<Longrightarrow>\<^sub>t
   wait_guar_assn S2 (\<lambda>t. ParState s (q t)) (merge_rdy ({}, {ch}) rdy2) 
        (combine_assn chs (in_vassm_assn ch V s P) Q) "
  apply(auto simp add:entails_tassn_def)
  using assms combine_in_vassm_wait_guar1' by blast

lemma combine_in_vassm_wait_orig1':
assumes "ch \<in> chs "
    and "compat_rdy ({}, {ch}) rdy2"
  shows "combine_assn chs (in_vassm_assn ch V s P) (wait_orig_assn T q rdy2 Q) tr \<Longrightarrow>
   wait_orig_assn T (\<lambda>t. ParState s (q t)) (merge_rdy ({}, {ch}) rdy2) 
        (combine_assn chs (in_vassm_assn ch V s P) Q) tr"
  unfolding combine_assn_def    
  apply auto
  subgoal for tr1 tr2
    apply(cases rule:in_vassm_assn.cases[of ch V s P tr1])
        apply auto
    subgoal for v tr1'
      apply(cases rule:wait_orig_assn.cases[of T q rdy2 Q tr2])
        apply auto
      subgoal
        apply(rule wait_orig_assn.intros(1))
        by auto
      subgoal for tr2' 
        using assms
        by (auto elim!: sync_elims)
      done
    subgoal for v tr1' d1
      apply(cases rule:wait_orig_assn.cases[of T q rdy2 Q tr2])
        apply auto
      subgoal
        apply(rule wait_orig_assn.intros(1))
        by auto
      subgoal for tr2' 
        apply(cases "T>d1")
        subgoal
          apply(elim combine_blocks_waitE3)
          using assms apply auto
          subgoal for tr'
            by (auto elim!: sync_elims)
          done
        apply(cases "T=d1")
        subgoal
          apply auto
          apply(elim combine_blocks_waitE2)
          using assms
           apply auto
          subgoal for tr'
            apply(rule wait_orig_assn.intros(2))
              apply auto
            apply(rule exI[where x="(InBlock ch v # tr1')"])
            apply auto
            apply(rule in_vassm_assn.intros(1))
            by auto
          done
        apply(elim combine_blocks_waitE4)
        using assms
           apply auto
        subgoal for tr'
          apply(rule wait_orig_assn.intros(2))
            apply auto
          apply(rule exI[where x="(WaitBlk ((d1 - T)) (\<lambda>t. s) ({}, {ch}) # InBlock ch v # tr1')"])
          apply auto
          apply(rule in_vassm_assn.intros(2))
          by auto
        done
      done
    subgoal for w tr1'
      apply(cases rule:wait_orig_assn.cases[of T q rdy2 Q tr2])
        apply auto
      subgoal
        apply(rule wait_orig_assn.intros(1))
        by auto
      subgoal for tr2'
        using assms
        by (auto elim!: sync_elims)
      done
    subgoal for w d1 tr1'
      apply(cases rule:wait_orig_assn.cases[of T q rdy2 Q tr2])
        apply auto
      subgoal
        apply(rule wait_orig_assn.intros(1))
        by auto
      subgoal for tr2' 
        apply(cases "T>d1")
        subgoal
          apply(elim combine_blocks_waitE3)
          using assms 
             apply auto
          subgoal for tr'
            by (auto elim!: sync_elims)
          done
        apply(cases "T=d1")
        subgoal
          apply auto
          apply(elim combine_blocks_waitE2)
          using assms 
           apply auto
          subgoal for tr'
            apply(rule wait_orig_assn.intros(2))
              apply auto
            apply(rule exI[where x="(InBlock ch w # tr1')"])
            apply auto
            apply(rule in_vassm_assn.intros(3))
            by auto
          done
        apply(elim combine_blocks_waitE4)
        using assms apply auto
        subgoal for tr'
          apply(rule wait_orig_assn.intros(2))
            apply auto
          apply(rule exI[where x="WaitBlk ((d1 - T)) (\<lambda>t. s) ({}, {ch}) # InBlock ch w # tr1'"])
          apply auto
          apply(rule in_vassm_assn.intros(4))
          by auto
        done
      done
    done
  done
  
lemma combine_in_vassm_wait_orig1:
assumes "ch \<in> chs "
    and "compat_rdy ({}, {ch}) rdy2"
  shows "combine_assn chs (in_vassm_assn ch V s P) (wait_orig_assn T q rdy2 Q) \<Longrightarrow>\<^sub>t
   wait_orig_assn T (\<lambda>t. ParState s (q t)) (merge_rdy ({}, {ch}) rdy2) 
        (combine_assn chs (in_vassm_assn ch V s P) Q) "
  apply(auto simp add:entails_tassn_def)
  using assms combine_in_vassm_wait_orig1' by blast

lemma combine_emp_out_orig1:
"ch\<in>chs \<Longrightarrow> combine_assn chs emp\<^sub>t (out_orig_assn ch v s P) \<Longrightarrow>\<^sub>t R"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:out_orig_assn.cases[of ch v s P])
      apply auto
    by (auto elim!: sync_elims)
  done

lemma combine_in_vassm_emp1:
"ch\<in>chs \<Longrightarrow> combine_assn chs (in_vassm_assn ch V s P) emp\<^sub>t \<Longrightarrow>\<^sub>t R"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:in_vassm_assn.cases[of ch V s P])
      apply auto
    by (auto elim!: sync_elims)
  done
        
lemma combine_out_tassm_emp1:
"ch\<in>chs \<Longrightarrow> combine_assn chs (out_tassm_assn ch v s S P) emp\<^sub>t \<Longrightarrow>\<^sub>t R"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:out_tassm_assn.cases[of ch v s S P])
      apply auto
    by (auto elim!: sync_elims)
  done



lemma combine_out_tassm_emp2:
"ch\<notin>chs \<Longrightarrow> combine_assn chs (out_tassm_assn ch v s S P) emp\<^sub>t \<Longrightarrow>\<^sub>t (out_tassm_assn ch v t S (\<lambda> t. combine_assn chs (P t) emp\<^sub>t))"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:out_tassm_assn.cases[of ch v s S P])
      apply auto
       apply (auto elim!: sync_elims)
    subgoal for tr1' tr'
      apply(rule out_tassm_assn.intros(1))
      by auto
    subgoal for w tr1' tr'
      apply(rule out_tassm_assn.intros(3))
      by auto
    done
  done

lemma combine_out_0assm_emp1:
"ch\<in>chs \<Longrightarrow> combine_assn chs (out_0assm_assn ch v P) emp\<^sub>t \<Longrightarrow>\<^sub>t Q"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:out_0assm_assn.cases[of ch v P])
      apply auto
    by (auto elim!: sync_elims)
  done


lemma combine_out_0assm_emp2:
"ch\<notin>chs \<Longrightarrow> combine_assn chs (out_0assm_assn ch v P) emp\<^sub>t \<Longrightarrow>\<^sub>t (out_0assm_assn ch v (combine_assn chs P emp\<^sub>t))"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:out_0assm_assn.cases[of ch v P])
      apply auto
       apply (auto elim!: sync_elims)
    subgoal for tr1' tr'
      apply(rule out_0assm_assn.intros(1))
      by auto
    done
  done

lemma combine_out_0assm_rdy_emp2:
"ch\<notin>chs \<Longrightarrow> combine_assn chs (out_0assm_rdy_assn ch v rdy P) emp\<^sub>t \<Longrightarrow>\<^sub>t (out_0assm_rdy_assn ch v rdy' (combine_assn chs P emp\<^sub>t))"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:out_0assm_rdy_assn.cases[of ch v rdy P])
      apply auto
       apply (auto elim!: sync_elims)
    subgoal for tr1' tr'
      apply(rule out_0assm_rdy_assn.intros(1))
      by auto
    done
  done

lemma combine_out_0assm_emp3:
"combine_assn chs (out_0assm_assn ch v P) emp\<^sub>t \<Longrightarrow>\<^sub>t (out_0assm_assn ch v (combine_assn chs P emp\<^sub>t))"
  apply(cases "ch\<in>chs")
   apply(rule "combine_out_0assm_emp1")
   apply auto
  apply(rule "combine_out_0assm_emp2")
  by auto


lemma combine_emp_out_0assm1:
"ch\<in>chs \<Longrightarrow> combine_assn chs  emp\<^sub>t (out_0assm_assn ch v P) \<Longrightarrow>\<^sub>t Q"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:out_0assm_assn.cases[of ch v P])
      apply auto
    by (auto elim!: sync_elims)
  done


lemma combine_emp_out_0assm2:
"ch\<notin>chs \<Longrightarrow> combine_assn chs emp\<^sub>t (out_0assm_assn ch v P) \<Longrightarrow>\<^sub>t (out_0assm_assn ch v (combine_assn chs emp\<^sub>t P))"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:out_0assm_assn.cases[of ch v P])
      apply auto
       apply (auto elim!: sync_elims)
    subgoal for tr1' tr'
      apply(rule out_0assm_assn.intros(1))
      by auto
    done
  done

lemma combine_emp_out_0assm3:
"combine_assn chs emp\<^sub>t (out_0assm_assn ch v P) \<Longrightarrow>\<^sub>t (out_0assm_assn ch v (combine_assn chs emp\<^sub>t P))"
  apply(cases "ch\<in>chs")
   apply(rule "combine_emp_out_0assm1")
   apply auto
  apply(rule "combine_emp_out_0assm2")
  by auto


lemma combine_in_0assm_emp2:
"ch\<notin>chs \<Longrightarrow> combine_assn chs (in_0assm_assn ch v P) emp\<^sub>t \<Longrightarrow>\<^sub>t (in_0assm_assn ch v (combine_assn chs P emp\<^sub>t))"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:in_0assm_assn.cases[of ch v P])
      apply auto
       apply (auto elim!: sync_elims)
    subgoal for tr1' tr'
      apply(rule in_0assm_assn.intros(1))
      by auto
    done
  done

lemma combine_in_0assm_rdy_emp2:
"ch\<notin>chs \<Longrightarrow> combine_assn chs (in_0assm_rdy_assn ch v rdy P) emp\<^sub>t \<Longrightarrow>\<^sub>t (in_0assm_rdy_assn ch v rdy' (combine_assn chs P emp\<^sub>t))"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:in_0assm_rdy_assn.cases[of ch v rdy P])
      apply auto
       apply (auto elim!: sync_elims)
    subgoal for tr1' tr'
      apply(rule in_0assm_rdy_assn.intros(1))
      by auto
    done
  done

lemma combine_waitin_assms'_emp1:
"ch\<in>chs \<Longrightarrow> combine_assn chs (waitin_assms'_assn S p rdy ch V P) emp\<^sub>t \<Longrightarrow>\<^sub>t Q"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:waitin_assms'_assn.cases[of S p rdy ch V P tr1])
        by (auto elim!: sync_elims)
      done


lemma combine_waitin_assms'_emp2:
"ch\<notin>chs \<Longrightarrow> combine_assn chs (waitin_assms'_assn S p rdy ch V P) emp\<^sub>t \<Longrightarrow>\<^sub>t (waitin_assms'_assn S q rdy ch V (\<lambda> v t . combine_assn chs (P v t) emp\<^sub>t))"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:waitin_assms'_assn.cases[of S p rdy ch V P tr1])
        apply (auto elim!: sync_elims)
    subgoal for v tr1' tr'
      apply(rule waitin_assms'_assn.intros(1))
      by auto
    subgoal for w tr1' tr'
      apply(rule waitin_assms'_assn.intros(3))
      by auto
    subgoal for w tr1' tr'
      apply(rule waitin_assms'_assn.intros(3))
  by auto
  done
  done

lemma combine_emp_waitin_assms'1:
"ch\<in>chs \<Longrightarrow> combine_assn chs emp\<^sub>t (waitin_assms'_assn S p rdy ch V P) \<Longrightarrow>\<^sub>t Q"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:waitin_assms'_assn.cases[of S p rdy ch V P tr1])
        by (auto elim!: sync_elims)
  done


lemma combine_emp_waitin_assms'2:
"ch\<notin>chs \<Longrightarrow> combine_assn chs emp\<^sub>t (waitin_assms'_assn S p rdy ch V P) \<Longrightarrow>\<^sub>t (waitin_assms'_assn S q rdy ch V (\<lambda> v t . combine_assn chs emp\<^sub>t (P v t)))"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:waitin_assms'_assn.cases[of S p rdy ch V P tr1])
        apply (auto elim!: sync_elims)
    subgoal for v tr1' tr'
      apply(rule waitin_assms'_assn.intros(1))
      by auto
    subgoal for w tr1' tr'
      apply(rule waitin_assms'_assn.intros(3))
      by auto
    subgoal for w tr1' tr'
      apply(rule waitin_assms'_assn.intros(3))
  by auto
  done
  done

lemma combine_waitin_tguar'_vassm'_emp1:
"ch\<in>chs \<Longrightarrow> combine_assn chs (waitin_tguar'_vassm'_assn S p rdy ch V P) emp\<^sub>t \<Longrightarrow>\<^sub>t Q"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:waitin_tguar'_vassm'_assn.cases[of S p rdy ch V P tr1])
        apply (auto elim!: sync_elims)
  done
  done

lemma combine_waitin_tguar'_vassm'_emp2:
"ch\<notin>chs \<Longrightarrow> combine_assn chs (waitin_tguar'_vassm'_assn S p rdy ch V P) emp\<^sub>t \<Longrightarrow>\<^sub>t (waitin_tguar'_vassm'_assn S q rdy ch V (\<lambda> v t . combine_assn chs (P v t) emp\<^sub>t))"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:waitin_tguar'_vassm'_assn.cases[of S p rdy ch V P tr1])
        apply (auto elim!: sync_elims)
    subgoal for v tr1' tr'
      apply(rule waitin_tguar'_vassm'_assn.intros(1))
      by auto
    subgoal for w tr1' tr'
      apply(rule waitin_tguar'_vassm'_assn.intros(3))
      by auto
  done
  done


lemma combine_wait_orig_emp2:
"combine_assn chs (wait_orig_assn d p rdy P) emp\<^sub>t \<Longrightarrow>\<^sub>t (wait_orig_assn d q rdy (combine_assn chs P emp\<^sub>t))"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1
    apply(cases rule: wait_orig_assn.cases[of d p rdy P tr1])
      apply auto
     apply(rule wait_orig_assn.intros(1))
      apply auto
    by (auto elim!: sync_elims)
  done

lemma combine_wait_guar'_emp2:
"combine_assn chs (wait_guar'_assn S p rdy P) emp\<^sub>t \<Longrightarrow>\<^sub>t (wait_guar'_assn S q rdy (\<lambda> t. combine_assn chs (P t) emp\<^sub>t))"
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1
    apply(cases rule: wait_guar'_assn.cases[of S p rdy P tr1])
      apply auto
     apply(rule wait_guar'_assn.intros(1))
      apply auto
    by (auto elim!: sync_elims)
  done  


lemma combine_out_orig_emp2:
"ch\<notin>chs \<Longrightarrow> combine_assn chs (out_orig_assn ch v s P) emp\<^sub>t \<Longrightarrow>\<^sub>t out_orig_assn ch v s'(combine_assn chs P emp\<^sub>t) "
  apply(auto simp add:entails_tassn_def combine_assn_def emp_assn_def)
  subgoal for tr tr1 
    apply(cases rule:out_orig_assn.cases[of ch v s P])
      apply (auto elim!: sync_elims)
    apply(rule out_orig_assn.intros(1))
    by auto
  done

lemma combine_wait_orig_wait_orig2:
  assumes "compat_rdy rdy1 rdy2"
  shows "combine_assn chs (wait_orig_assn d p1 rdy1 P) (wait_orig_assn d p2 rdy2 Q) \<Longrightarrow>\<^sub>t
         wait_orig_assn d (\<lambda> t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) (combine_assn chs P Q)"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply (cases rule:wait_orig_assn.cases[of d p1 rdy1 P tr1])
      apply auto
    subgoal 
      apply (cases rule:wait_orig_assn.cases[of d p2 rdy2 Q tr2])
        apply auto
      apply(rule wait_orig_assn.intros(1))
      by auto
    subgoal for tr1'
      apply (cases rule:wait_orig_assn.cases[of d p2 rdy2 Q tr2])
        apply auto
      subgoal for tr2'
        apply(elim combine_blocks_waitE2)
        using assms apply auto
      apply(rule wait_orig_assn.intros(2))
        by auto
      done
    done
  done

lemma combine_wait_orig_wait_orig3:
  assumes "compat_rdy rdy1 rdy2"
    and "d1<d2"
  shows "combine_assn chs (wait_orig_assn d1 p1 rdy1 P) (wait_orig_assn d2 p2 rdy2 Q) \<Longrightarrow>\<^sub>t
         wait_orig_assn d1 (\<lambda> t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) (combine_assn chs P (wait_orig_assn (d2-d1) (\<lambda> t. p2(t+d1)) rdy2 Q))"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply (cases rule:wait_orig_assn.cases[of d1 p1 rdy1 P tr1])
      apply auto
    subgoal 
      apply (cases rule:wait_orig_assn.cases[of d2 p2 rdy2 Q tr2])
        apply auto
      subgoal
      apply(rule wait_orig_assn.intros(1))
        by auto
      subgoal for tr2'
        apply(rule wait_orig_assn.intros(1))
        by auto
      done
    subgoal for tr1'
      apply (cases rule:wait_orig_assn.cases[of d2 p2 rdy2 Q tr2])
      using assms
        apply auto
      subgoal for tr2'
        apply(elim combine_blocks_waitE3)
        using assms apply auto
        apply(rule wait_orig_assn.intros(2))
         apply auto
        apply(rule exI[where x="tr1'"])
        apply auto
        apply(rule exI[where x="(WaitBlk (d2 - d1) (\<lambda>t. p2 (t + d1)) rdy2 # tr2')"])
        apply auto
        apply(rule  wait_orig_assn.intros(2))
        by auto
      done
    done
  done


lemma combine_wait_orig_wait_orig5:
  assumes "compat_rdy rdy1 rdy2"
    and "d1\<le>d2"
  shows "combine_assn chs (wait_orig_assn d1 p1 rdy1 P) (wait_orig_assn d2 p2 rdy2 Q) \<Longrightarrow>\<^sub>t
         wait_orig_assn d1 (\<lambda> t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) (combine_assn chs P (wait_orig_assn (d2-d1) (\<lambda> t. p2(t+d1)) rdy2 Q))"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply (cases rule:wait_orig_assn.cases[of d1 p1 rdy1 P tr1])
      apply auto
    subgoal 
      apply (cases rule:wait_orig_assn.cases[of d2 p2 rdy2 Q tr2])
        apply auto
      subgoal
      apply(rule wait_orig_assn.intros(1))
        by auto
      subgoal for tr2'
        apply(rule wait_orig_assn.intros(1))
        by auto
      done
    subgoal for tr1'
      apply (cases rule:wait_orig_assn.cases[of d2 p2 rdy2 Q tr2])
      using assms
        apply auto
      subgoal for tr2'
        apply(cases "d1<d2")
        subgoal
        apply(elim combine_blocks_waitE3)
        using assms apply auto
        apply(rule wait_orig_assn.intros(2))
         apply auto
        apply(rule exI[where x="tr1'"])
        apply auto
        apply(rule exI[where x="(WaitBlk (d2 - d1) (\<lambda>t. p2 (t + d1)) rdy2 # tr2')"])
        apply auto
        apply(rule  wait_orig_assn.intros(2))
        by auto
      subgoal apply(cases "d1=d2")
         apply auto
        apply(elim combine_blocks_waitE2)
        using assms apply auto
      apply(rule wait_orig_assn.intros(2))
         apply auto
        apply(rule exI[where x="tr1'"])
        apply auto
        apply(rule exI[where x="tr2'"])
        apply auto
        apply(rule wait_orig_assn.intros(1))
        by auto
      done
    done
  done
  done


lemma combine_out_0assm_out_0assm2':
  assumes "ch1 \<in> chs"
     and  "ch2 \<notin> chs"
     shows  "combine_assn chs (out_0assm_assn ch1 v1 P) (out_0assm_assn ch2 v2 Q) \<Longrightarrow>\<^sub>t 
           out_0assm_assn ch2 v2 (combine_assn chs (out_0assm_assn ch1 v1 P) Q)"
  using assms unfolding combine_assn_def entails_tassn_def apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: out_0assm_assn.cases[of ch1 v1 P tr1])
    apply auto
    apply(cases rule: out_0assm_assn.cases[of ch2 v2 Q tr2])
  apply auto
  subgoal
    apply(elim combine_blocks_unpairE1')
    using assms apply auto
    apply(rule out_0assm_assn.intros(1))
    by auto
  subgoal by (auto elim!: sync_elims)
apply(cases rule: out_0assm_assn.cases[of ch2 v2 Q tr2])
  apply auto
  subgoal
    apply(elim combine_blocks_unpairE3')
    using assms apply auto
    apply(rule out_0assm_assn.intros(1))
    by auto
  subgoal for d a b p tra da aa ba pa traa
    apply(cases "compat_rdy (a, b) (aa, ba)")
    subgoal
      apply(cases "d>da")
      subgoal
       apply(elim combine_blocks_waitE4)
        using assms apply auto
        apply(rule out_0assm_assn.intros(2))
        by auto
      apply(cases "d<da")
      subgoal
       apply(elim combine_blocks_waitE3)
        using assms apply auto
        apply(rule out_0assm_assn.intros(2))
        by auto
      apply auto
      apply(elim combine_blocks_waitE2)
        using assms apply auto
        apply(rule out_0assm_assn.intros(2))
        by auto
      apply(elim combine_blocks_waitE1)
      by auto
    done
  done



lemma combine_wait_orig_out_0assm2:
  assumes "d>0"
      and "ch\<notin>chs"
    shows "combine_assn chs (wait_orig_assn d p rdy P)(out_0assm_assn ch v Q) \<Longrightarrow>\<^sub>t
          out_0assm_assn ch v (combine_assn chs (wait_orig_assn d p rdy P) Q)"
  unfolding entails_tassn_def combine_assn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule:wait_orig_assn.cases[of d p rdy P tr1])
    using assms apply auto
    subgoal for tr1'
      apply(cases rule:out_0assm_assn.cases[of ch v Q tr2])
        apply auto
      subgoal for tr2'
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          apply(rule out_0assm_assn.intros(1))
          by auto
        done
      subgoal for d' a b p' tr2'
        apply(cases "compat_rdy rdy (a,b)")
        subgoal
          apply(cases "d<d'")
          subgoal
           apply(elim combine_blocks_waitE3)
               apply auto
            apply(rule out_0assm_assn.intros(2))
             apply auto
            apply(cases rdy)
            by auto
          apply(cases "d>d'")
          subgoal
           apply(elim combine_blocks_waitE4)
               apply auto
            apply(rule out_0assm_assn.intros(2))
             apply auto
            apply(cases rdy)
            by auto
          apply auto
          apply(elim combine_blocks_waitE2)
               apply auto
            apply(rule out_0assm_assn.intros(2))
             apply auto
            apply(cases rdy)
          by auto
        apply(elim combine_blocks_waitE1)
        by auto
      done
    done
  done
            
lemma combine_out_0assm_waitin_assm'1:
  assumes "ch \<in> chs"
      and "ch \<in> snd rdy"
      and "0 \<in> S \<and> v \<in> V"
    shows "combine_assn chs (out_0assm_assn ch v P)(waitin_assms'_assn S p rdy ch V Q) \<Longrightarrow>\<^sub>t
           io_orig_assn ch v (combine_assn chs P (Q v 0))"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: out_0assm_assn.cases[of ch v P tr1])
      apply auto
    subgoal for tr1'
     apply(cases rule: waitin_assms'_assn.cases[of S p rdy ch V Q tr2])
          apply simp
      subgoal for w tr2'
        apply auto
        apply (elim combine_blocks_pairE)
        using assms
          apply auto
        apply(rule io_orig_assn.intros)
        by auto
      subgoal for w d tr2'
        apply auto
        using assms
        by (auto elim!: sync_elims)
      subgoal for w tr2'
        apply simp
        using assms
        apply(elim combine_blocks_pairE)
        by auto
      subgoal for w d tr2'
        apply auto
        using assms
        by (auto elim!: sync_elims)
      done
    subgoal for d a b q tr1'
      apply(cases rule: waitin_assms'_assn.cases[of S p rdy ch V Q tr2])
          apply simp
      subgoal for w tr2'
        apply auto
        using assms
        by (auto elim!: sync_elims)
      subgoal for w t tr2'
        apply auto
        apply(elim combine_blocks_waitE1)
        apply(cases rdy)
        using assms by auto
      subgoal for w tr2'
        apply auto
        using assms
        by (auto elim!: sync_elims)
      subgoal for w t tr2'
        apply simp
        apply(elim combine_blocks_waitE1)
        apply(cases rdy)
        using assms by auto
      done
    done
  done


lemma combine_out_0assm_waitin_assm'2:
  assumes "ch \<in> chs \<and> ch \<in> snd rdy \<and> dh \<notin> chs \<and> 0 \<in> S"
    shows "combine_assn chs (out_0assm_assn ch w P)(waitin_assms'_assn S p rdy dh V Q) \<Longrightarrow>\<^sub>t
           in_0orig_vassm_assn dh V (\<lambda> v. combine_assn chs (out_0assm_assn ch w P) (Q v 0))"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: out_0assm_assn.cases[of ch w P tr1])
      apply auto
    subgoal for tr1'
      apply(cases rule: waitin_assms'_assn.cases[of S p rdy dh V Q tr2])
          apply simp
      subgoal for v tr2'
        apply auto
        apply(elim combine_blocks_unpairE1')
        using assms
          apply auto
        apply(rule in_0orig_vassm_assn.intros(1))
        by auto
      subgoal for v d tr2'
        using assms
        by (auto elim!: sync_elims)
      subgoal for v tr2'
        apply simp
        apply(elim combine_blocks_unpairE1')
        using assms apply simp
        using assms apply simp
        apply simp
        apply(rule in_0orig_vassm_assn.intros(2))
        using assms
        by auto
      subgoal for d v tr2'
        apply auto
        using assms
        by (auto elim!: sync_elims)
      done
    subgoal for d a b pp tr1'
      apply(cases rule: waitin_assms'_assn.cases[of S p rdy dh V Q tr2])
          apply simp
      subgoal for v tr2'
        apply auto
        apply(elim combine_blocks_unpairE3')
        using assms
          apply auto
        apply(rule in_0orig_vassm_assn.intros(1))
        by auto
      subgoal for v dd tr2'
        apply auto
        using assms
        apply(elim combine_blocks_waitE1)
        apply(cases rdy)
        by auto
      subgoal for v tr2'
        apply simp
        apply(elim combine_blocks_unpairE3')
        using assms apply auto
        apply(rule in_0orig_vassm_assn.intros(2))
        using assms
        by auto
      subgoal for dd v tr2'
        apply simp
        using assms
        apply(elim combine_blocks_waitE1)
        apply(cases rdy)
        by auto
      done
    done
  done


lemma combine_out_0assm_waitin_assm'3:
  assumes "ch \<in> chs \<and> ch \<in> snd rdy \<and> dh \<in> chs \<and> dh \<noteq> ch "
    shows "combine_assn chs (out_0assm_assn ch w P)(waitin_assms'_assn S p rdy dh V Q) \<Longrightarrow>\<^sub>t R"
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: out_0assm_assn.cases[of ch w P tr1])
      apply auto
    subgoal for tr1'
      apply(cases rule: waitin_assms'_assn.cases[of S p rdy dh V Q tr2])
          apply simp
      subgoal for v tr2'
        apply auto
        apply(elim combine_blocks_pairE)
        using assms
          by auto
      subgoal for v d tr2'
        using assms
        by (auto elim!: sync_elims)
      subgoal for v tr2'
        apply simp
        apply(elim combine_blocks_pairE)
        using assms
          by auto
      subgoal for d v tr2'
        apply auto
        using assms
        by (auto elim!: sync_elims)
      done
    subgoal for d a b pp tr1'
      apply(cases rule: waitin_assms'_assn.cases[of S p rdy dh V Q tr2])
          apply simp
      subgoal for v tr2'
        apply auto
        using assms
          by (auto elim!: sync_elims)
      subgoal for v dd tr2'
        apply auto
        using assms
        apply(elim combine_blocks_waitE1)
        apply(cases rdy)
        by auto
      subgoal for v tr2'
        apply simp
        using assms
        by (auto elim!: sync_elims)
      subgoal for dd v tr2'
        apply simp
        using assms
        apply(elim combine_blocks_waitE1)
        apply(cases rdy)
        by auto
      done
    done
  done





lemma combine_waitin_tguar'_vassm'_out_0assm1:
  assumes "ch\<in>chs \<and> ch \<in> snd rdy \<and> v \<in> V"
  shows "combine_assn chs (waitin_tguar'_vassm'_assn S p rdy ch V P) (out_0assm_assn ch v Q) \<Longrightarrow>\<^sub>t
         io_orig_assn ch v (combine_assn chs (P v 0) Q)" 
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: waitin_tguar'_vassm'_assn.cases[of S p rdy ch V P tr1])
        apply auto
    subgoal
      apply(cases rule:out_0assm_assn.cases[of ch v Q tr2])
        apply auto
      subgoal
        apply(elim combine_blocks_pairE)
        using assms
          apply auto
        apply(rule io_orig_assn.intros(1))
        by auto
      subgoal
        using assms
        by (auto elim!: sync_elims)
      done
    subgoal
      apply(cases rule:out_0assm_assn.cases[of ch v Q tr2])
        apply auto
      subgoal
        using assms
        by (auto elim!: sync_elims)
      subgoal
        using assms
        apply(cases rdy)
        by (auto elim!: sync_elims)
      done
    subgoal
      apply(cases rule:out_0assm_assn.cases[of ch v Q tr2])
        apply auto
      subgoal
        apply(elim combine_blocks_pairE)
        using assms
         by auto
      subgoal
        using assms
        by (auto elim!: sync_elims)
      done
    subgoal
      apply(cases rule:out_0assm_assn.cases[of ch v Q tr2])
        apply auto
      subgoal
        using assms
        by (auto elim!: sync_elims)
      subgoal
        using assms
        apply(cases rdy)
        by (auto elim!: sync_elims)
      done
    done
  done
        



lemma combine_waitin_tguar'_vassm'_out_0assm2:
  assumes "dh\<notin>chs \<and> ch\<in>chs"
  shows "combine_assn chs (waitin_tguar'_vassm'_assn S p rdy ch V P) (out_0assm_assn dh v Q) \<Longrightarrow>\<^sub>t
         out_0assm_assn dh v (combine_assn chs (waitin_tguar'_vassm'_assn S p rdy ch V P) Q)" 
  unfolding combine_assn_def entails_tassn_def
  apply auto
  subgoal for tr tr1 tr2
    apply(cases rule: waitin_tguar'_vassm'_assn.cases[of S p rdy ch V P tr1])
        apply auto
    subgoal for w tr1'
      apply(cases rule: out_0assm_assn.cases[of dh v Q tr2])
        apply auto
      subgoal for tr2'
        apply(elim combine_blocks_unpairE1')
        using assms apply auto
        apply(rule out_0assm_assn.intros(1))
        by auto
      subgoal using assms
        by (auto elim!: sync_elims)
      done
    subgoal for d w tr1'
      apply(cases rule: out_0assm_assn.cases[of dh v Q tr2])
        apply auto
      subgoal for tr2'
        apply(elim combine_blocks_unpairE3')
        using assms 
         apply auto
        apply(rule out_0assm_assn.intros(1))
        by auto
      subgoal for d' a b p' tr2'
        apply(cases "\<not> compat_rdy rdy (a,b)")
        subgoal by (auto elim!: sync_elims)
        apply(cases "d>d'")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply auto
          apply(rule out_0assm_assn.intros(2))
          apply auto
          apply(cases rdy)
          by auto
        apply(cases "d<d'")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply auto
          apply(rule out_0assm_assn.intros(2))
          apply auto
          apply(cases rdy)
          by auto
        apply auto
        apply(elim combine_blocks_waitE2)
             apply auto
          apply(rule out_0assm_assn.intros(2))
          apply auto
          apply(cases rdy)
        by auto
      done
    subgoal for w tr1'
      apply(cases rule: out_0assm_assn.cases[of dh v Q tr2])
        apply auto
      subgoal 
        apply(elim combine_blocks_unpairE1')
        using assms apply auto
        apply(rule out_0assm_assn.intros(1))
        by auto
      subgoal using assms
        by (auto elim!: sync_elims)
      done
    subgoal for d w tr1'
      apply(cases rule: out_0assm_assn.cases[of dh v Q tr2])
        apply auto
      subgoal for tr2'
        apply(elim combine_blocks_unpairE3')
        using assms 
         apply auto
        apply(rule out_0assm_assn.intros(1))
        by auto
      subgoal for d' a b p' tr2'
        apply(cases "\<not> compat_rdy rdy (a,b)")
        subgoal by (auto elim!: sync_elims)
        apply(cases "d>d'")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply auto
          apply(rule out_0assm_assn.intros(2))
          apply auto
          apply(cases rdy)
          by auto
        apply(cases "d<d'")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply auto
          apply(rule out_0assm_assn.intros(2))
          apply auto
          apply(cases rdy)
          by auto
        apply auto
        apply(elim combine_blocks_waitE2)
             apply auto
          apply(rule out_0assm_assn.intros(2))
          apply auto
          apply(cases rdy)
        by auto
      done
    done
  done
          


end