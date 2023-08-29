theory BigStepContParallel
  imports BigStepContinuous BigStepParallel
begin

subsection \<open>Interrupt specification for global states\<close>

datatype 'a comm_specg2 =
  InSpecg2 cname "real \<Rightarrow> real \<Rightarrow> 'a gassn2"
| OutSpecg2 cname "real \<Rightarrow> real \<Rightarrow> 'a gassn2"

text \<open>Mapping from specification on single state to specification
  on general states.
\<close>
fun comm_spec_gassn_of :: "pname \<Rightarrow> 'a comm_spec2 \<Rightarrow> 'a comm_specg2" where
  "comm_spec_gassn_of pn (InSpec2 ch Q) = InSpecg2 ch (\<lambda>d v. single_assn pn (Q d v))"
| "comm_spec_gassn_of pn (OutSpec2 ch Q) = OutSpecg2 ch (\<lambda>d v. single_assn pn (Q d v))"

definition rdy_of_comm_specg2 :: "'a comm_specg2 list \<Rightarrow> rdy_info" where
  "rdy_of_comm_specg2 = rdy_info_of_list (\<lambda>specg.
     case specg of InSpecg2 ch P \<Rightarrow> ({}, {ch})
                 | OutSpecg2 ch P \<Rightarrow> ({ch}, {}))"

lemma rdy_of_comm_spec_gassn_of:
  "rdy_of_comm_spec2 specs = rdy_of_comm_specg2 (map (comm_spec_gassn_of pn) specs)"
  unfolding rdy_of_comm_spec2_def rdy_of_comm_specg2_def
  apply (rule rdy_info_of_list_cong)
  apply (rule rel_list_map)
  subgoal for spec2 apply (cases spec2) by auto
  done

inductive interrupt_sol_cg ::
      "('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate \<Rightarrow> bool) \<Rightarrow>
       pname \<Rightarrow> 'a eexp \<Rightarrow> (real \<Rightarrow> 'a gassn2) \<Rightarrow>
       'a comm_specg2 list \<Rightarrow> 'a gassn2" where
  "e (the (s0 pn)) > 0 \<Longrightarrow> P d s0 s tr \<Longrightarrow> d = e (the (s0 pn)) \<Longrightarrow>
   rdy = rdy_of_comm_specg2 specs \<Longrightarrow> \<forall>t\<in>{0..d}. I s0 t (p t) \<Longrightarrow>
   interrupt_sol_cg I pn e P specs s0 s (WaitBlkP d (\<lambda>\<tau>. p \<tau>) rdy # tr)"
| "\<not>e (the (s0 pn)) > 0 \<Longrightarrow> P 0 s0 s tr \<Longrightarrow>
   interrupt_sol_cg I pn e P specs s0 s tr"
| "i < length specs \<Longrightarrow> specs ! i = InSpecg2 ch Q \<Longrightarrow>
   Q 0 v s0 s tr \<Longrightarrow>
   interrupt_sol_cg I pn e P specs s0 s (InBlockP ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = InSpecg2 ch Q \<Longrightarrow>
   0 < d' \<Longrightarrow> d' \<le> e (the (s0 pn)) \<Longrightarrow> Q d' v s0 s tr \<Longrightarrow>
   rdy = rdy_of_comm_specg2 specs \<Longrightarrow> \<forall>t\<in>{0..d'}. I s0 t (p t) \<Longrightarrow>
   interrupt_sol_cg I pn e P specs s0 s (WaitBlkP d' (\<lambda>\<tau>. p \<tau>) rdy # InBlockP ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpecg2 ch Q \<Longrightarrow>
   Q 0 v s0 s tr \<Longrightarrow> interrupt_sol_cg I pn e P specs s0 s (OutBlockP ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpecg2 ch Q \<Longrightarrow>
   0 < d' \<Longrightarrow> d' \<le> e (the (s0 pn)) \<Longrightarrow> Q d' v s0 s tr \<Longrightarrow>
   rdy = rdy_of_comm_specg2 specs \<Longrightarrow> \<forall>t\<in>{0..d'}. I s0 t (p t) \<Longrightarrow>
   interrupt_sol_cg I pn e P specs s0 s (WaitBlkP d' (\<lambda>\<tau>. p \<tau>) rdy # OutBlockP ch v # tr)"

lemma single_assn_interrupt_sol [single_assn_simps]:
  "single_assn pn (interrupt_sol_c I e P specs) =
   interrupt_sol_cg (single_inv pn I) pn e (\<lambda>d. single_assn pn (P d))
                    (map (comm_spec_gassn_of pn) specs)"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases) apply auto
      subgoal for s0' s' tr'
        apply (elim interrupt_sol_c.cases) apply auto
        subgoal premises pre for tr'' a b p
          using pre(3) apply (elim ptrace_of_waitE) apply auto
          apply (rule interrupt_sol_cg.intros(1))
          using pre rdy_of_comm_spec_gassn_of
          by (auto intro: single_assn.intros single_inv.intros)
        subgoal
          apply (rule interrupt_sol_cg.intros(2))
          by (auto intro: single_assn.intros)
        subgoal for i ch Q v tr''
          apply (elim ptrace_of_commE) apply auto
          apply (rule interrupt_sol_cg.intros(3)[of i _ _ "(\<lambda>d v. single_assn pn (Q d v))"])
          by (auto intro: single_assn.intros)
        subgoal premises pre for i ch Q d v tr'' a b p'
          using pre(3) apply (elim ptrace_of_waitE ptrace_of_commE) apply auto
          apply (rule interrupt_sol_cg.intros(4)[of i _ _ "(\<lambda>d v. single_assn pn (Q d v))"])
          using pre rdy_of_comm_spec_gassn_of
          by (auto intro: single_assn.intros single_inv.intros)
        subgoal for i ch Q v tr''
          apply (elim ptrace_of_commE) apply auto
          apply (rule interrupt_sol_cg.intros(5)[of i _ _ "(\<lambda>d v. single_assn pn (Q d v))" ])
          by (auto intro: single_assn.intros)
        subgoal premises pre for i ch Q d v tr'' a b
          using pre(3) apply (elim ptrace_of_waitE ptrace_of_commE) apply auto
          apply (rule interrupt_sol_cg.intros(6)[of i _ _ "(\<lambda>d v. single_assn pn (Q d v))"])
          using pre rdy_of_comm_spec_gassn_of
          by (auto intro: single_assn.intros single_inv.intros)
        done
      done
    subgoal apply (elim interrupt_sol_cg.cases) apply auto
      subgoal for tr' a b p
        apply (elim single_assn.cases) apply auto
        subgoal for s0' s' tr''
          apply (elim single_inv_intervalE) subgoal for p''
            apply (rule single_assn.intros[where tr=
                  "WaitBlk (e s0') p'' (rdy_of_comm_specg2 (map (comm_spec_gassn_of pn) specs)) # tr''"])
             prefer 2 apply (auto intro!: ptrace_of.intros WaitBlkP_eqI)
            apply (rule interrupt_sol_c.intros(1))
               apply (auto intro: ptrace_of.intros)
            unfolding rdy_of_comm_spec_gassn_of[symmetric] by auto
          done
        done
      subgoal
        apply (elim single_assn.cases) apply auto
        subgoal for s0' s' tr''
          apply (rule single_assn.intros)
           apply (rule interrupt_sol_c.intros(2))
          by auto
        done
      subgoal for i ch Q v tr'
        apply (cases "specs ! i") apply auto
        apply (elim single_assn.cases) apply auto
        subgoal for Q' s0' s' tr''
          apply (rule single_assn.intros)
           apply (rule interrupt_sol_c.intros(3)[of i _ _ Q'])
          by (auto intro: ptrace_of.intros)
        done
      subgoal for i ch Q d v tr' a b p'
        apply (cases "specs ! i") apply auto
        apply (elim single_assn.cases) apply auto
        subgoal for Q' s0'' s' tr''
          apply (elim single_inv_intervalE) subgoal for p''
            apply (rule single_assn.intros[where tr=
                  "WaitBlk d p'' (rdy_of_comm_specg2 (map (comm_spec_gassn_of pn) specs)) #
                   InBlock ch v # tr''"])
             prefer 2 apply (auto intro!: ptrace_of.intros WaitBlkP_eqI)
            apply (rule interrupt_sol_c.intros(4)[of i _ _ Q']) apply auto
            unfolding rdy_of_comm_spec_gassn_of[symmetric] by auto
          done
        done
      subgoal for i ch e Q tr'
        apply (cases "specs ! i") apply auto
        apply (elim single_assn.cases) apply auto
        subgoal for Q' s0'' s' tr''
          apply (rule single_assn.intros)
           apply (rule interrupt_sol_c.intros(5)[of i _ _ Q'])
          by (auto intro: ptrace_of.intros)
        done
      subgoal for i ch Q d v tr' a b p'
        apply (cases "specs ! i") apply auto
        apply (elim single_assn.cases) apply auto
        subgoal for Q' s0'' s' tr''
          apply (elim single_inv_intervalE) subgoal for p''
            apply (rule single_assn.intros[where tr=
                  "WaitBlk d p'' (rdy_of_comm_specg2 (map (comm_spec_gassn_of pn) specs)) #
                   OutBlock ch v # tr''"])
             prefer 2 apply (auto intro!: ptrace_of.intros WaitBlkP_eqI)
            apply (rule interrupt_sol_c.intros(6)[of i _ _ Q']) apply auto
            unfolding rdy_of_comm_spec_gassn_of[symmetric] by auto
          done
        done
      done
    done
  done

inductive interrupt_solInf_cg :: "('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate \<Rightarrow> bool) \<Rightarrow> 'a comm_specg2 list \<Rightarrow> 'a gassn2" where
  "i < length specs \<Longrightarrow> specs ! i = InSpecg2 ch Q \<Longrightarrow>
   Q 0 v gs0 gs tr \<Longrightarrow> interrupt_solInf_cg I specs gs0 gs (InBlockP ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = InSpecg2 ch Q \<Longrightarrow>
   0 < d \<Longrightarrow> Q d v gs0 gs tr \<Longrightarrow>
   rdy = rdy_of_comm_specg2 specs \<Longrightarrow> (\<forall>t\<in>{0..d}. I gs0 t (p t)) \<Longrightarrow>
   interrupt_solInf_cg I specs gs0 gs (WaitBlkP d p rdy # InBlockP ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpecg2 ch Q \<Longrightarrow>
   Q 0 v gs0 gs tr \<Longrightarrow> interrupt_solInf_cg I specs gs0 gs (OutBlockP ch v # tr)"
| "i < length specs \<Longrightarrow> specs ! i = OutSpecg2 ch Q \<Longrightarrow>
   0 < d \<Longrightarrow> Q d v gs0 gs tr \<Longrightarrow>
   rdy = rdy_of_comm_specg2 specs \<Longrightarrow> (\<forall>t\<in>{0..d}. I gs0 t (p t)) \<Longrightarrow>
   interrupt_solInf_cg I specs gs0 gs (WaitBlkP d p rdy # OutBlockP ch v # tr)"

lemma single_assn_interrupt_solInf [single_assn_simps]:
  "single_assn pn (interrupt_solInf_c I specs) =
   interrupt_solInf_cg (single_inv pn I) (map (comm_spec_gassn_of pn) specs)"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr
    apply (rule iffI)
    subgoal apply (elim single_assn.cases) apply auto
      subgoal for s0' s' tr'
        apply (elim interrupt_solInf_c.cases) apply auto
        subgoal for i ch Q v tr''
          apply (elim ptrace_of_commE) apply auto
          apply (rule interrupt_solInf_cg.intros(1)[of i _ _ "(\<lambda>d v. single_assn pn (Q d v))"])
          by (auto intro: single_assn.intros)
        subgoal premises pre for i ch Q d v tr'' a b p'
          using pre(3) apply (elim ptrace_of_waitE ptrace_of_commE) apply auto
          apply (rule interrupt_solInf_cg.intros(2)[of i _ _ "(\<lambda>d v. single_assn pn (Q d v))"])
          using pre rdy_of_comm_spec_gassn_of
          by (auto intro: single_assn.intros single_inv.intros)
        subgoal for i ch Q v tr''
          apply (elim ptrace_of_commE) apply auto
          apply (rule interrupt_solInf_cg.intros(3)[of i _ _ "(\<lambda>d v. single_assn pn (Q d v))" ])
          by (auto intro: single_assn.intros)
        subgoal premises pre for i ch Q d v tr'' a b
          using pre(3) apply (elim ptrace_of_waitE ptrace_of_commE) apply auto
          apply (rule interrupt_solInf_cg.intros(4)[of i _ _ "(\<lambda>d v. single_assn pn (Q d v))"])
          using pre rdy_of_comm_spec_gassn_of
          by (auto intro: single_assn.intros single_inv.intros)
        done
      done
    subgoal apply (elim interrupt_solInf_cg.cases) apply auto
      subgoal for i ch Q v tr'
        apply (cases "specs ! i") apply auto
        apply (elim single_assn.cases) apply auto
        subgoal for Q' s0' s' tr''
          apply (rule single_assn.intros)
           apply (rule interrupt_solInf_c.intros(1)[of i _ _ Q'])
          by (auto intro: ptrace_of.intros)
        done
      subgoal for i ch Q d v tr' a b p'
        apply (cases "specs ! i") apply auto
        apply (elim single_assn.cases) apply auto
        subgoal for Q' s0'' s' tr''
          apply (elim single_inv_intervalE) subgoal for p''
            apply (rule single_assn.intros[where tr=
                  "WaitBlk d p'' (rdy_of_comm_specg2 (map (comm_spec_gassn_of pn) specs)) #
                   InBlock ch v # tr''"])
             prefer 2 apply (auto intro!: ptrace_of.intros WaitBlkP_eqI)
            apply (rule interrupt_solInf_c.intros(2)[of i _ _ Q']) apply auto
            unfolding rdy_of_comm_spec_gassn_of[symmetric] by auto
          done
        done
      subgoal for i ch e Q tr'
        apply (cases "specs ! i") apply auto
        apply (elim single_assn.cases) apply auto
        subgoal for Q' s0'' s' tr''
          apply (rule single_assn.intros)
           apply (rule interrupt_solInf_c.intros(3)[of i _ _ Q'])
          by (auto intro: ptrace_of.intros)
        done
      subgoal for i ch Q d v tr' a b p'
        apply (cases "specs ! i") apply auto
        apply (elim single_assn.cases) apply auto
        subgoal for Q' s0'' s' tr''
          apply (elim single_inv_intervalE) subgoal for p''
            apply (rule single_assn.intros[where tr=
                  "WaitBlk d p'' (rdy_of_comm_specg2 (map (comm_spec_gassn_of pn) specs)) #
                   OutBlock ch v # tr''"])
             prefer 2 apply (auto intro!: ptrace_of.intros WaitBlkP_eqI)
            apply (rule interrupt_solInf_c.intros(4)[of i _ _ Q']) apply auto
            unfolding rdy_of_comm_spec_gassn_of[symmetric] by auto
          done
        done
      done
    done
  done

text \<open>Delay specification by a given amount of time\<close>
fun spec_wait_of :: "real \<Rightarrow> ('a gstate \<Rightarrow> real \<Rightarrow> 'a gstate) \<Rightarrow> 'a comm_specg2 \<Rightarrow> 'a comm_specg2" where
  "spec_wait_of d p (InSpecg2 ch P) = InSpecg2 ch (\<lambda>d' v. P (d + d') v)"
| "spec_wait_of d p (OutSpecg2 ch P) = OutSpecg2 ch (\<lambda>d' v. P (d + d') v)"

fun ch_of_specg2 :: "'a comm_specg2 \<Rightarrow> cname" where
  "ch_of_specg2 (InSpecg2 ch P) = ch"
| "ch_of_specg2 (OutSpecg2 ch P) = ch"

lemma rdy_of_spec_wait_of [simp]:
  "rdy_of_comm_specg2 (map (spec_wait_of d p) specs) = rdy_of_comm_specg2 specs"
  unfolding rdy_of_comm_specg2_def apply (rule sym)
  apply (rule rdy_info_of_list_cong)
  apply (rule rel_list_map)
  subgoal for specg2 apply (cases specg2) by auto
  done

subsection \<open>Synchronization rules for interrupt\<close>

text \<open>The following two lemmas are temporary. More general results
  are needed for the general cases.
\<close>
lemma merge_rdy_comm_specg2_empty:
  assumes "\<And>i. i < length specs \<Longrightarrow> ch_of_specg2 (specs ! i) \<in> chs"
  shows "merge_rdy chs (rdy_of_comm_specg2 specs) ({}, {}) = ({}, {})"
  sorry

lemma not_compat_rdy_comm_specg2:
  assumes "i < length specs"
    and "specs ! i = InSpecg2 ch P"
  shows "\<not> compat_rdy (rdy_of_comm_specg2 specs) ({ch}, {})"
  sorry

lemma sync_gassn_interrupt_solInf_wait:
  assumes "pn2 \<in> pns2"
    and "pns1 \<inter> pns2 = {}"
    and "\<And>i. i < length specs \<Longrightarrow> ch_of_specg2 (specs ! i) \<in> chs"
  shows
  "sync_gassn chs pns1 pns2 (interrupt_solInf_cg I1 specs) (wait_cg I2 pn2 e Q) s0 \<Longrightarrow>\<^sub>g
   wait_cg (merge_inv I1 I2) pn2 e
    (\<lambda>d. sync_gassn chs pns1 pns2 (interrupt_solInf_cg (delay_inv d I1) (map (spec_wait_of d p) specs)) (Q d)) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim interrupt_solInf_cg.cases) apply auto
      subgoal for i ch Q' v tr'
        apply (elim wait_cg.cases) apply auto
        subgoal for tr''
          apply (elim combine_blocks_pairE2)
          using assms(3)[of i] by auto
        subgoal
          apply (rule wait_cg.intros(2))
          apply (subst merge_state_eval2)
          using assms apply auto
          apply (rule sync_gassn.intros) apply auto
          apply (rule interrupt_solInf_cg.intros(1)[of i _ _ Q'])
          by auto
        done
      subgoal for i ch Q' d' v tr' a b p'
        apply (elim wait_cg.cases) apply auto
        subgoal for tr''
          apply (cases rule: linorder_cases[of d' "e (the (s12 pn2))"])
          subgoal
            apply (elim combine_blocks_waitE3) apply auto
            apply (elim combine_blocks_pairE2)
            using assms(3)[of i] by auto
          subgoal apply auto
            apply (elim combine_blocks_waitE2) apply auto
            subgoal for tr'''
              apply (rule wait_cg.intros(1))
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
                apply (rule sync_gassn.intros) apply auto
                apply (rule interrupt_solInf_cg.intros(1)[of i _ _ "\<lambda>d' v. Q' (e (the (s12 pn2)) + d') v"])
                  apply (auto intro: merge_inv.intros)
              apply (rule merge_rdy_comm_specg2_empty) using assms(3) by auto
            done
          subgoal
            apply (elim combine_blocks_waitE4) apply auto
            subgoal for tr'''
              apply (rule wait_cg.intros(1))
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
               apply (rule sync_gassn.intros) apply auto
               apply (rule interrupt_solInf_cg.intros(2)[of i _ _ "\<lambda>d' v. Q' (e (the (s12 pn2)) + d') v"])
                    apply (auto intro: delay_inv.intros)
              subgoal apply (intro merge_inv.intros)
                using assms by auto
              apply (rule merge_rdy_comm_specg2_empty) using assms(3) by auto
            done
          done
        subgoal
          apply (rule wait_cg.intros(2))
          subgoal apply (subst merge_state_eval2)
            using assms(1,2) by auto
          apply (rule sync_gassn.intros) apply auto
          apply (rule interrupt_solInf_cg.intros(2)[of i _ _ Q'])
          by (auto intro: delay_inv.intros)
        done
      subgoal for i ch e Q' tr'
        apply (elim wait_cg.cases) apply auto
        subgoal for tr''
          apply (elim combine_blocks_pairE2)
          using assms(3)[of i] by auto
        subgoal
          apply (rule wait_cg.intros(2))
          apply (subst merge_state_eval2)
          using assms apply auto
          apply (rule sync_gassn.intros) apply auto
          apply (rule interrupt_solInf_cg.intros(3)[of i _ _ e Q'])
          by auto
        done
      subgoal for i ch Q' d' v tr' a b p'
        apply (elim wait_cg.cases) apply auto
        subgoal for tr''
          apply (cases rule: linorder_cases[of d' "e (the (s12 pn2))"])
          subgoal
            apply (elim combine_blocks_waitE3) apply auto
            apply (elim combine_blocks_pairE2)
            using assms(3)[of i] by auto
          subgoal apply auto
            apply (elim combine_blocks_waitE2) apply auto
            subgoal for tr'''
              apply (rule wait_cg.intros(1))
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
                apply (rule sync_gassn.intros) apply auto
                apply (rule interrupt_solInf_cg.intros(3)[of i _ _ "\<lambda>d' v. Q' (e (the (s12 pn2)) + d') v"])
                  apply (auto intro: merge_inv.intros)
              apply (rule merge_rdy_comm_specg2_empty) using assms(3) by auto
            done
          subgoal
            apply (elim combine_blocks_waitE4) apply auto
            subgoal for tr'''
              apply (rule wait_cg.intros(1))
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
              subgoal apply (subst merge_state_eval2)
                using assms(1,2) by auto
                apply (rule sync_gassn.intros) apply auto
                apply (rule interrupt_solInf_cg.intros(4)[of i _ _ "\<lambda>d' v. Q' (e (the (s12 pn2)) + d') v"])
                     apply (auto intro: delay_inv.intros)
              subgoal using assms by (auto intro: merge_inv.intros)
              apply (rule merge_rdy_comm_specg2_empty) using assms(3) by auto
            done
          done
        subgoal
          apply (rule wait_cg.intros(2))
          subgoal apply (subst merge_state_eval2)
            using assms(1,2) by auto
          apply (rule sync_gassn.intros) apply auto
          apply (rule interrupt_solInf_cg.intros(4)[of i _ _ Q'])
          by (auto intro: delay_inv.intros)
        done
      done
    done
  done

text \<open>Synchronization between interrupt and synchronized output
  Assume there is a corresponding input in the interrupt. Then
  the communication happens immediately.
\<close>
lemma sync_gassn_interrupt_solInf_out:
  assumes "pns1 \<inter> pns2 = {}"
    and "\<And>i. i < length specs \<Longrightarrow> ch_of_specg2 (specs ! i) \<in> chs"
    and "\<And>i j. i < length specs \<Longrightarrow> j < length specs \<Longrightarrow> i \<noteq> j \<Longrightarrow>
               ch_of_specg2 (specs ! i) \<noteq> ch_of_specg2 (specs ! j)"
    and "i < length specs"
    and "specs ! i = InSpecg2 ch P"
  shows
  "sync_gassn chs pns1 pns2 (interrupt_solInf_cg p specs)
                            (wait_out_cg I ch Q) s0 \<Longrightarrow>\<^sub>g
   (\<exists>\<^sub>gv. sync_gassn chs pns1 pns2 (P 0 v) (Q 0 v)) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim interrupt_solInf_cg.cases) apply auto
      subgoal for i' ch' Q' v tr'
        apply (elim wait_out_cg.cases) apply auto
        subgoal for v' tr''
          apply (cases "i = i'")
          subgoal using assms(4,5) apply auto
            apply (elim combine_blocks_pairE)
            using assms(2) apply fastforce
            using assms(2) apply fastforce
            unfolding exists_gassn_def apply (rule exI[where x=v])
            apply (rule sync_gassn.intros)
            using assms by (auto simp add: assms)
          subgoal
            apply (elim combine_blocks_pairE)
            using assms(2) apply fastforce
            apply (metis assms(2,4,5) ch_of_specg2.simps(1))
            by (metis assms(3,4,5) ch_of_specg2.simps(1))
          done
        subgoal for d tr''
          apply (elim combine_blocks_pairE2)
          using assms(2) by fastforce
        done
      subgoal for i ch' Q' d v tr' a b
        apply (elim wait_out_cg.cases) apply auto
        subgoal for tr''
          apply (elim combine_blocks_pairE2')
          by (metis assms(2,4,5) ch_of_specg2.simps(1))
        subgoal for d' tr''
          apply (elim combine_blocks_waitE1)
          apply (rule not_compat_rdy_comm_specg2) using assms(4,5) by auto
        done
      subgoal for i ch' e' Q' tr'
        apply (elim wait_out_cg.cases) apply auto
        subgoal for tr''
          apply (elim combine_blocks_pairE)
          using assms(2) apply fastforce
           apply (metis assms(2,4,5) ch_of_specg2.simps(1))
          by auto
        subgoal for d' tr''
          apply (elim combine_blocks_pairE2)
          using assms(2) by fastforce
        done
      subgoal for i ch' e' Q' d tr' a b
        apply (elim wait_out_cg.cases) apply auto
        subgoal for tr''
          apply (elim combine_blocks_pairE2')
          by (metis assms(2,4,5) ch_of_specg2.simps(1))
        subgoal for d' tr''
          apply (elim combine_blocks_waitE1)
          apply (rule not_compat_rdy_comm_specg2) using assms(4,5) by auto
        done
      done
    done
  done

lemma sync_gassn_interrupt_solInf_outv:
  assumes "pn2 \<in> pns2"
    and "pns1 \<inter> pns2 = {}"
    and "\<And>i. i < length specs \<Longrightarrow> ch_of_specg2 (specs ! i) \<in> chs"
    and "\<And>i j. i < length specs \<Longrightarrow> j < length specs \<Longrightarrow> i \<noteq> j \<Longrightarrow>
               ch_of_specg2 (specs ! i) \<noteq> ch_of_specg2 (specs ! j)"
    and "i < length specs"
    and "specs ! i = InSpecg2 ch P"
  shows
    "sync_gassn chs pns1 pns2 (interrupt_solInf_cg p specs)
                              (wait_out_cgv I ch pns2 pn2 e Q) s0 \<Longrightarrow>\<^sub>g
     sync_gassn chs pns1 pns2 (P 0 (e (the (s0 pn2)))) (Q 0) s0"
  unfolding wait_out_cgv_def
  apply (rule entails_g_trans)
   apply (rule sync_gassn_interrupt_solInf_out) using assms apply auto
  apply (rule exists_gassn_elim)
  subgoal for v
    apply (rule sync_gassn_conj_pure_right)
     apply (simp add: restrict_state_def)
    by (rule entails_g_triv)
  done

subsection \<open>Invariant assertions\<close>

text \<open>Basic assertion for invariants: wait for the specified amount of time,
  while all states in the path satisfy the given invariant, then the remaining
  trace satisfy the following assertion.
\<close>
inductive wait_inv_cg :: "('a gstate \<Rightarrow> bool) \<Rightarrow> 'a gassn2 \<Rightarrow> 'a gassn2" where
  "d > 0 \<Longrightarrow> rdy = ({}, {}) \<Longrightarrow> \<forall>t\<in>{0..d}. I (p t) \<Longrightarrow> P gs0 gs tr \<Longrightarrow>
   wait_inv_cg I P gs0 gs (WaitBlkP d (\<lambda>t. p t) rdy # tr)"

lemma wait_inv_cg_updg:
  "wait_inv_cg I P (updg s0 pn var x) \<Longrightarrow>\<^sub>g wait_inv_cg I (\<lambda>s. P (updg s pn var x)) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim wait_inv_cg.cases) apply auto
    subgoal for p tr'
      apply (rule wait_inv_cg.intros) by auto
    done
  done

lemma wait_inv_cgI:
  assumes "e (the (gs0 pn)) = d"
    and "d > 0"
    and "\<forall>t\<in>{0..d}. \<forall>gs. I gs0 t gs \<longrightarrow> J gs"
  shows "wait_cg I pn e P gs0 \<Longrightarrow>\<^sub>g wait_inv_cg J (P d) gs0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim wait_cg.cases) apply auto
    using assms by (auto intro!: wait_inv_cg.intros)
  done

lemma wait_inv_cg_mono:
  assumes "P1 s0 \<Longrightarrow>\<^sub>g P2 s0"
  shows "wait_inv_cg I P1 s0 \<Longrightarrow>\<^sub>g wait_inv_cg I P2 s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim wait_inv_cg.cases) apply auto
    apply (rule wait_inv_cg.intros) apply auto
    using assms unfolding entails_g_def by auto
  done

subsection \<open>Simplification of interrupt assertions\<close>

lemma interrupt_solInf_cg_out:
  "interrupt_solInf_cg I [OutSpecg2 ch P] = wait_out_cg I ch P"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr apply (rule iffI)
    subgoal apply (elim interrupt_solInf_cg.cases) apply auto
      subgoal for v tr'
        by (intro wait_out_cg.intros(1)) 
      subgoal for d v tr' a b p
        unfolding rdy_of_comm_specg2_def apply simp
        by (auto intro: wait_out_cg.intros(2))
      done
    subgoal apply (elim wait_out_cg.cases) apply auto
      subgoal for v tr'
        apply (intro interrupt_solInf_cg.intros(3)[of 0 _ _ P]) by auto
      subgoal for d v tr' p
        apply (intro interrupt_solInf_cg.intros(4)[of 0 _ _ P]) apply auto
        unfolding rdy_of_comm_specg2_def by auto
      done
    done
  done

lemma interrupt_solInf_cg_in:
  "interrupt_solInf_cg I [InSpecg2 ch P] = wait_in_cg I ch P"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr apply (rule iffI)
    subgoal apply (elim interrupt_solInf_cg.cases) apply auto
      subgoal for v tr'
        by (intro wait_in_cg.intros(1)) 
      subgoal for d v tr' a b p
        unfolding rdy_of_comm_specg2_def apply simp
        by (auto intro: wait_in_cg.intros(2))
      done
    subgoal apply (elim wait_in_cg.cases) apply auto
      subgoal for v tr'
        apply (intro interrupt_solInf_cg.intros(1)[of 0 _ _ P]) by auto
      subgoal for d v tr' p
        apply (intro interrupt_solInf_cg.intros(2)[of 0 _ _ P]) apply auto
        unfolding rdy_of_comm_specg2_def by auto
      done
    done
  done

lemma interrupt_sol_cg_wait:
  "interrupt_sol_cg I pn e P [] = wait_cg I pn e P"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr apply (rule iffI)
    subgoal apply (elim interrupt_sol_cg.cases) apply auto
      subgoal for tr' a b p
        unfolding rdy_of_comm_specg2_def apply simp
        by (auto intro: wait_cg.intros(1))
      subgoal
        by (auto intro: wait_cg.intros(2))
      done
    subgoal apply (elim wait_cg.cases) apply auto
      subgoal for tr' p
        apply (intro interrupt_sol_cg.intros(1))
        unfolding rdy_of_comm_specg2_def by auto
      subgoal
        by (auto intro: interrupt_sol_cg.intros(2))
      done
    done
  done

text \<open>wait_in_cg_alt is also a special case of interrupt_sol_cg\<close>

lemma interrupt_sol_cg_wait_in:
  "interrupt_sol_cg I pn e P [InSpecg2 ch Q] = wait_in_cg_alt I ch pn e Q P"
  apply (rule ext) apply (rule ext) apply (rule ext)
  subgoal for s0 s tr apply (rule iffI)
    subgoal apply (elim interrupt_sol_cg.cases) apply auto
      subgoal for tr' a b p
        unfolding rdy_of_comm_specg2_def apply simp
        by (auto intro: wait_in_cg_alt.intros(3))
      subgoal
        by (auto intro: wait_in_cg_alt.intros(4))
      subgoal for v tr'
        by (auto intro: wait_in_cg_alt.intros(1))
      subgoal for d v tr' a b p
        unfolding rdy_of_comm_specg2_def apply simp
        by (auto intro: wait_in_cg_alt.intros(2))
      done
    subgoal apply (elim wait_in_cg_alt.cases) apply auto
      subgoal for v tr'
        apply (intro interrupt_sol_cg.intros(3)[of 0 _ _ Q]) by auto
      subgoal for d v tr' p
        apply (intro interrupt_sol_cg.intros(4)[of 0 _ _ Q]) apply auto
        unfolding rdy_of_comm_specg2_def by auto
      subgoal for tr' p
        apply (intro interrupt_sol_cg.intros(1)) apply auto
        unfolding rdy_of_comm_specg2_def by auto
      subgoal
        apply (intro interrupt_sol_cg.intros(2)) by auto
      done
    done
  done

end
