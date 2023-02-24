theory DisConSemantics
  imports ContinuousSyntax
          DiscreteSemantics
begin

(*use fixed_point to solve ODE;
fixed_point t0 T x0 f X;
h is only to get x0*)
definition solveODE :: "timed_vars \<Rightarrow> block \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow>\<^sub>C vec)" where
  "solveODE h b t0 t = unique_on_bounded_closed.fixed_point t0
  {t0 -- t0+t} (state2vec (timedVar2State h t0)) (block2ODE b) UNIV"

lemma solveODE_eq : "\<forall>v. h1 v (t0) = h2 v (t0) 
\<Longrightarrow> solveODE h1 b t0 t = solveODE h2 b t0 t"
  subgoal premises pre
proof -
  have 1: "(state2vec (timedVar2State h1 t0 )) = (state2vec (timedVar2State h2 t0 ))"
    unfolding timedVar2State_def using pre by auto
  show ?thesis unfolding solveODE_def using 1 by auto
qed
  done

lemma solveODE_t0 : "\<exists>L. unique_on_bounded_closed (t0)
 {(t0) -- (t0+ t)} (state2vec (timedVar2State h t0 )) 
(block2ODE b) UNIV L \<Longrightarrow> (solveODE h b t0 t) t0 = (state2vec (timedVar2State h t0))"
  using unique_on_bounded_closed.fixed_point_iv unfolding solveODE_def by blast
  

(*checkODE only checks those outputs in the ODE block
because continuous blocks change those outputs values at time t0;
so we use the initial timed_vars h0 to get those original values*)
fun checkODE :: "block \<Rightarrow> timed_vars \<Rightarrow> timed_vars \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "checkODE b h h0 t0 t = (realstate2realvec (timedVar2timedState 
  (\<lambda>vv tt. (if vv \<in> set (get_outputs b) \<and> tt > t0 
  \<and> tt \<le> t0 + t then h vv tt else 
  (timedState2timedVar (realvec2realstate (solveODE h0 b t0 t)) vv tt))))
  solves_ode (block2ODE b)) {t0 -- t0 + t} UNIV"

lemma checkODE_eq : "\<forall>v \<in> set (get_outputs b). \<forall>t' \<le> t0 + t. h1 v t' = h2 v t' \<Longrightarrow>
checkODE b h1 h0 t0 t \<Longrightarrow> checkODE b h2 h0 t0 t"
  subgoal premises pre
proof -
  have 1: "(\<lambda>vv tt. (if vv \<in> set (get_outputs b) \<and> tt > t0 
  \<and> tt \<le> t0 + t then h1 vv tt else 
  (timedState2timedVar (realvec2realstate (solveODE h0 b t0 t)) vv tt))) = 
  (\<lambda>vv tt. (if vv \<in> set (get_outputs b) \<and> tt > t0 
  \<and> tt \<le> t0 + t then h2 vv tt else 
  (timedState2timedVar (realvec2realstate (solveODE h0 b t0 t)) vv tt)))"
    using pre(1) by fastforce
  have 2: "realstate2realvec (timedVar2timedState 
  (\<lambda>vv tt. (if vv \<in> set (get_outputs b) \<and> tt > t0 
  \<and> tt \<le> t0 + t then h1 vv tt else 
  (timedState2timedVar (realvec2realstate (solveODE h0 b t0 t)) vv tt)))) = 
  realstate2realvec (timedVar2timedState 
  (\<lambda>vv tt. (if vv \<in> set (get_outputs b) \<and> tt > t0 
  \<and> tt \<le> t0 + t then h2 vv tt else 
  (timedState2timedVar (realvec2realstate (solveODE h0 b t0 t)) vv tt))))"
    using 1 by presburger
  then show ?thesis using pre(2) unfolding checkODE.simps by presburger
qed
  done

lemma checkODE_eq2 : "\<forall>v. h1 v t0 = h2 v t0 \<Longrightarrow>
checkODE b h h1 t0 t \<Longrightarrow> checkODE b h h2 t0 t"
  subgoal premises pre
  proof -
    have 1: "solveODE h1 b t0 t = solveODE h2 b t0 t"
      using solveODE_eq pre(1) by presburger
    show ?thesis using pre(2) unfolding checkODE.simps using 1 by metis
  qed
  done

lemma checkODE_lemma : "\<exists>L. unique_on_bounded_closed (t0)
 {(t0) -- (t0+ t)} (state2vec (timedVar2State h0 t0 )) 
(block2ODE b) UNIV L \<Longrightarrow> checkODE b h1 h0 t0 t = True \<Longrightarrow> checkODE b h2 h0 t0 t = True 
\<Longrightarrow> \<forall>vv tt. vv \<in> set (get_outputs b) \<and> tt > t0 \<and> tt \<le> t0 + t \<longrightarrow> h1 vv tt = h2 vv tt"
  subgoal premises pre
  proof -
    have 1: "\<forall>tt. tt > t0 \<and> tt \<le> t0 + t \<longrightarrow> tt \<in> {t0 -- t0 + t}"
      by (simp add: Line_Segment.closed_segment_eq_real_ivl)
    have 2: "realstate2realvec
      (timedVar2timedState
        (\<lambda>vv tt.
            if vv \<in> set (get_outputs b) \<and> t0 < tt \<and> tt \<le> t0 + t then h1 vv tt
            else timedState2timedVar (realvec2realstate (apply_bcontfun (solveODE h0 b t0 t))) vv
                  tt)) t0 = 
  (state2vec (timedVar2State h0 t0)) "
    proof -
      have tmp1: "(\<lambda>v. (\<lambda>vv tt. (if vv \<in> set (get_outputs b) \<and> tt > t0 
  \<and> tt \<le> t0 + t then h1 vv tt else 
  (timedState2timedVar (realvec2realstate (solveODE h0 b t0 t)) vv tt))) v t0) = 
  (\<lambda>v. (\<lambda>vv tt. timedState2timedVar (realvec2realstate (solveODE h0 b t0 t)) vv tt) v t0)"
        by auto
      have tmp2: "realstate2realvec (timedVar2timedState 
  (\<lambda>vv tt. (if vv \<in> set (get_outputs b) \<and> tt > t0 
  \<and> tt \<le> t0 + t then h1 vv tt else 
  (timedState2timedVar (realvec2realstate (solveODE h0 b t0 t)) vv tt)))) t0 = state2vec 
  (\<lambda>v. (\<lambda>vv tt. timedState2timedVar (realvec2realstate (solveODE h0 b t0 t)) vv tt) v t0)"
        using trans_eq5 tmp1 by presburger
      have tmp3: "(solveODE h0 b t0 t) t0 = (state2vec (timedVar2State h0 t0))"
        using solveODE_t0 pre(1) by auto
      show ?thesis using tmp2 tmp3 by (smt (verit, ccfv_threshold) Cart_lambda_cong state2vec_def 
            timedVar_state_map4 trans_eq3 vec_lambda_beta)
    qed
    have 3: "realstate2realvec (timedVar2timedState 
  (\<lambda>vv tt. (if vv \<in> set (get_outputs b) \<and> tt > t0 
  \<and> tt \<le> t0 + t then h2 vv tt else 
  (timedState2timedVar (realvec2realstate (solveODE h0 b t0 t)) vv tt)))) t0 = 
  (state2vec (timedVar2State h0 t0)) "
    proof -
      have tmp1: "(\<lambda>v. (\<lambda>vv tt. (if vv \<in> set (get_outputs b) \<and> tt > t0 
  \<and> tt \<le> t0 + t then h2 vv tt else 
  (timedState2timedVar (realvec2realstate (solveODE h0 b t0 t)) vv tt))) v t0) = 
  (\<lambda>v. (\<lambda>vv tt. timedState2timedVar (realvec2realstate (solveODE h0 b t0 t)) vv tt) v t0)"
        by auto
      have tmp2: "realstate2realvec (timedVar2timedState 
  (\<lambda>vv tt. (if vv \<in> set (get_outputs b) \<and> tt > t0 
  \<and> tt \<le> t0 + t then h2 vv tt else 
  (timedState2timedVar (realvec2realstate (solveODE h0 b t0 t)) vv tt)))) t0 = state2vec 
  (\<lambda>v. (\<lambda>vv tt. timedState2timedVar (realvec2realstate (solveODE h0 b t0 t)) vv tt) v t0)"
        using trans_eq5 tmp1 by presburger
      have tmp3: "(solveODE h0 b t0 t) t0 = (state2vec (timedVar2State h0 t0))"
        using solveODE_t0 pre(1) by auto
      show ?thesis using tmp2 tmp3 by (smt (verit, ccfv_threshold) Cart_lambda_cong state2vec_def 
            timedVar_state_map4 trans_eq3 vec_lambda_beta)
    qed
    have 4: "\<forall>tt vv. tt > t0 \<and> tt \<le> t0 + t \<and> vv \<in> set (get_outputs b)
  \<longrightarrow> realstate2realvec (timedVar2timedState 
  (\<lambda>vv tt. (if vv \<in> set (get_outputs b) \<and> tt > t0 
  \<and> tt \<le> t0 + t then h1 vv tt else 
  (timedState2timedVar (realvec2realstate (solveODE h0 b t0 t)) vv tt)))) tt $ vv = h1 vv tt"
      unfolding realstate2realvec.simps timedVar2timedState_def
      using state2vec_def by force
    have 5: "\<forall>tt vv. tt > t0 \<and> tt \<le> t0 + t \<and> vv \<in> set (get_outputs b)
  \<longrightarrow> realstate2realvec (timedVar2timedState 
  (\<lambda>vv tt. (if vv \<in> set (get_outputs b) \<and> tt > t0 
  \<and> tt \<le> t0 + t then h2 vv tt else 
  (timedState2timedVar (realvec2realstate (solveODE h0 b t0 t)) vv tt)))) tt $ vv = h2 vv tt"
      unfolding realstate2realvec.simps timedVar2timedState_def
      using state2vec_def by force
    have 6: "\<forall>tt. tt > t0 \<and> tt \<le> t0 + t \<longrightarrow> realstate2realvec
     (timedVar2timedState
       (\<lambda>vv tt.
           if vv \<in> set (get_outputs b) \<and> t0 < tt \<and> tt \<le> t0 + t then h1 vv tt
           else timedState2timedVar (realvec2realstate (apply_bcontfun (solveODE h0 b t0 t))) vv tt)) tt = 
    apply_bcontfun (unique_on_bounded_closed.fixed_point t0 {(t0) -- (t0+ t)} 
  (state2vec (timedVar2State h0 (t0))) (block2ODE b) UNIV) tt"
    proof -
      have tmp1: "\<exists>L. unique_on_bounded_closed t0 {(t0) -- (t0+ t)} 
          (state2vec (timedVar2State h0 (t0))) (block2ODE b) UNIV L"
        using pre(1) by auto
      have tmp2: "(realstate2realvec
     (timedVar2timedState
       (\<lambda>vv tt.
           if vv \<in> set (get_outputs b) \<and> t0 < tt \<and> tt \<le> t0 + t then h1 vv tt
           else timedState2timedVar (realvec2realstate (apply_bcontfun (solveODE h0 b t0 t))) vv tt)) solves_ode (block2ODE b)) {(t0) -- (t0+ t)} UNIV"
        using pre(2) unfolding checkODE.simps by blast
      have tmp3: "realstate2realvec
     (timedVar2timedState
       (\<lambda>vv tt.
           if vv \<in> set (get_outputs b) \<and> t0 < tt \<and> tt \<le> t0 + t then h1 vv tt
           else timedState2timedVar (realvec2realstate (apply_bcontfun (solveODE h0 b t0 t))) vv tt)) t0 
      = (state2vec (timedVar2State h0 (t0)))"
        using 2 by blast
      show ?thesis using unique_on_bounded_closed.solves_ode_equals_fixed_point tmp1 tmp2 tmp3 1
        by blast
    qed
    have 7: "\<forall>tt. tt > t0 \<and> tt \<le> t0 + t \<longrightarrow> realstate2realvec
     (timedVar2timedState
       (\<lambda>vv tt.
           if vv \<in> set (get_outputs b) \<and> t0 < tt \<and> tt \<le> t0 + t then h2 vv tt
           else timedState2timedVar (realvec2realstate (apply_bcontfun (solveODE h0 b t0 t))) vv tt)) tt = 
    apply_bcontfun (unique_on_bounded_closed.fixed_point t0 {(t0) -- (t0+ t)} 
  (state2vec (timedVar2State h0 (t0))) (block2ODE b) UNIV) tt"
    proof -
      have tmp1: "\<exists>L. unique_on_bounded_closed t0 {(t0) -- (t0+ t)} 
          (state2vec (timedVar2State h0 (t0))) (block2ODE b) UNIV L"
        using pre(1) by auto
      have tmp2: "(realstate2realvec
     (timedVar2timedState
       (\<lambda>vv tt.
           if vv \<in> set (get_outputs b) \<and> t0 < tt \<and> tt \<le> t0 + t then h2 vv tt
           else timedState2timedVar (realvec2realstate (apply_bcontfun (solveODE h0 b t0 t))) vv tt)) 
        solves_ode (block2ODE b)) {(t0) -- (t0+ t)} UNIV"
        using pre(3) unfolding checkODE.simps by blast
      have tmp3: "realstate2realvec
     (timedVar2timedState
       (\<lambda>vv tt.
           if vv \<in> set (get_outputs b) \<and> t0 < tt \<and> tt \<le> t0 + t then h2 vv tt
           else timedState2timedVar (realvec2realstate (apply_bcontfun (solveODE h0 b t0 t))) vv tt)) t0 
      = (state2vec (timedVar2State h0 (t0)))"
        using 3 by blast
      show ?thesis using unique_on_bounded_closed.solves_ode_equals_fixed_point tmp1 tmp2 tmp3 1
        by blast
    qed
    show ?thesis using 4 5 6 7 by auto
  qed
  done



fun behavCalBlk :: "var list \<Rightarrow> var list \<Rightarrow> offset list \<Rightarrow> outupd list \<Rightarrow> real \<Rightarrow> real \<Rightarrow> behav" where
  "behavCalBlk il [] ol fl t0 t h = True" |
  "behavCalBlk il vl ol [] t0 t h = True" |
  "behavCalBlk il vl [] fl t0 t h = True" |
  "behavCalBlk il (v#vl) (d#ol) (f#fl) t0 t h = (\<forall>tt. tt < t0 + t \<and> tt > t0 
\<longrightarrow> (if 1 \<in> set (d#ol) then True else ((h v tt = f (map (\<lambda> a. h a tt) il))
\<and> behavCalBlk il vl ol fl t0 t h)))"


lemma behavCalBlk_eq1 : "\<forall>x \<in> set il \<union> set vl. \<forall>tt. h1 x tt = h2 x tt
\<Longrightarrow> behavCalBlk il vl ol fl t0 t h1 \<Longrightarrow> behavCalBlk il vl ol fl t0 t h2"
proof(induction vl arbitrary:ol fl)
  case Nil
  then show ?case by simp
next
  case (Cons v vl)
  then show ?case
  proof(cases "fl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have 1: "fl = hd fl # tl fl"
      using False by simp
    then show ?thesis
    proof(cases "ol = []")
      case True
      then show ?thesis using 1 by (metis behavCalBlk.simps(3))
    next
      case False
      have 2: "ol = hd ol # tl ol"
        using False by simp
      then show ?thesis
      proof(cases "1 \<in> set ol")
        case True
        then show ?thesis using behavCalBlk.simps(4)
          using behavCalBlk.elims(3) by force
      next
        case False
        have 3: "behavCalBlk il vl (tl ol) (tl fl) t0 t h2"
        proof -
          have tmp1: "\<forall>x\<in>set il \<union> set vl. \<forall>tt. h1 x tt = h2 x tt"
            using Cons(2) by simp
          have tmp2: "behavCalBlk il vl (tl ol) (tl fl) t0 t h1"
            using Cons(3) behavCalBlk.simps(4)[of il v vl "hd ol" "tl ol"
            "hd fl" "tl fl" t0 t h1] 1 2 False
            by (smt (verit, ccfv_threshold) behavCalBlk.elims(3))
          show ?thesis using Cons(1) tmp1 tmp2 by simp
        qed
        have 4: "\<forall>tt. tt < t0 + t \<and> t0 < tt \<longrightarrow> h1 v tt = h2 v tt"
          using Cons(2) by simp
        have 5: "\<forall>tt. tt < t0 + t \<and> t0 < tt \<longrightarrow> hd fl (map (\<lambda>a. h1 a tt) il) = 
                hd fl (map (\<lambda>a. h2 a tt) il)"
          using Cons(2) apply simp by (smt (verit, ccfv_threshold) Un_iff map_eq_conv)
        have 6: "\<forall>tt. tt < t0 + t \<and> t0 < tt \<longrightarrow> 
                h1 v tt = hd fl (map (\<lambda>a. h1 a tt) il)"
          using Cons(3) behavCalBlk.simps(4)[of il v vl "hd ol" "tl ol"
            "hd fl" "tl fl" t0 t h1] 1 2 False 
            by (smt (verit, ccfv_threshold) behavCalBlk.elims(3))
        then show ?thesis using behavCalBlk.simps(4)[of il v vl "hd ol" "tl ol"
            "hd fl" "tl fl" t0 t h2] 1 2 3 4 5 by force
      qed
    qed
  qed
qed

lemma behavCalBlk_eq2 : "\<forall>x \<in> set il \<union> set vl. \<forall>tt < t0 + t. h1 x tt = h2 x tt
\<Longrightarrow> behavCalBlk il vl ol fl t0 t h1 \<Longrightarrow> behavCalBlk il vl ol fl t0 t h2"
proof(induction vl arbitrary:ol fl)
  case Nil
  then show ?case by simp
next
  case (Cons v vl)
  then show ?case
  proof(cases "fl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have 1: "fl = hd fl # tl fl"
      using False by simp
    then show ?thesis
    proof(cases "ol = []")
      case True
      then show ?thesis using 1 by (metis behavCalBlk.simps(3))
    next
      case False
      have 2: "ol = hd ol # tl ol"
        using False by simp
      then show ?thesis
      proof(cases "1 \<in> set ol")
        case True
        then show ?thesis using behavCalBlk.simps(4)
          using behavCalBlk.elims(3) by force
      next
        case False
        have 3: "behavCalBlk il vl (tl ol) (tl fl) t0 t h2"
        proof -
          have tmp1: "\<forall>x\<in>set il \<union> set vl. \<forall>tt < t0 + t. h1 x tt = h2 x tt"
            using Cons(2) by simp
          have tmp2: "behavCalBlk il vl (tl ol) (tl fl) t0 t h1"
            using Cons(3) behavCalBlk.simps(4)[of il v vl "hd ol" "tl ol"
            "hd fl" "tl fl" t0 t h1] 1 2 False
            by (smt (verit, ccfv_threshold) behavCalBlk.elims(3))
          show ?thesis using Cons(1) tmp1 tmp2 by simp
        qed
        have 4: "\<forall>tt. tt < t0 + t \<and> t0 < tt \<longrightarrow> h1 v tt = h2 v tt"
          using Cons(2) by simp
        have 5: "\<forall>tt. tt < t0 + t \<and> t0 < tt \<longrightarrow> hd fl (map (\<lambda>a. h1 a tt) il) = 
                hd fl (map (\<lambda>a. h2 a tt) il)"
          using Cons(2) apply simp by (smt (verit, ccfv_threshold) Un_iff map_eq_conv)
        have 6: "\<forall>tt. tt < t0 + t \<and> t0 < tt \<longrightarrow> 
                h1 v tt = hd fl (map (\<lambda>a. h1 a tt) il)"
          using Cons(3) behavCalBlk.simps(4)[of il v vl "hd ol" "tl ol"
            "hd fl" "tl fl" t0 t h1] 1 2 False 
            by (smt (verit, ccfv_threshold) behavCalBlk.elims(3))
        then show ?thesis using behavCalBlk.simps(4)[of il v vl "hd ol" "tl ol"
            "hd fl" "tl fl" t0 t h2] 1 2 3 4 5 by force
      qed
    qed
  qed
qed

lemma behavCalBlk_lemma1 : "Available' (Block il vl ol T fl) \<Longrightarrow> set ol = {0} \<Longrightarrow> 
behavCalBlk il vl ol fl t0 t h1 = True \<Longrightarrow>
behavCalBlk il vl ol fl t0 t h2 = True \<Longrightarrow>
\<forall>v \<in> set il. \<forall>t' < t0 + t. h1 v t' = h2 v t' \<Longrightarrow>
\<forall> t'::real. (t' < t0 + t \<and> t' > t0) \<longrightarrow> (\<forall> v \<in> set vl. h1 v t' = h2 v t')"
proof(induction vl arbitrary:ol fl)
  case Nil
  then show ?case by simp
next
  case (Cons v vl)
  then show ?case 
  proof(cases "fl = []")
    case True
    then show ?thesis using Cons(2) unfolding Available'_def by simp
  next
    case False
    have 1: "fl = hd fl # tl fl"
      using False by simp
    then show ?thesis
    proof(cases "ol = []")
      case True
      then show ?thesis using 1 using Cons(2) unfolding Available'_def by simp
    next
      case False
      have 2: "ol = hd ol # tl ol"
        using False by simp
      have 3: "\<forall>t'. t' < t0 + t \<and> t0 < t' \<longrightarrow>  h1 v t' = h2 v t'"
      proof -
        have tmp1: "1 \<notin> set (hd ol # tl ol)"
          using 2 Cons(3) by simp
        have tmp2: "\<forall>tt. tt < t0 + t \<and> t0 < tt \<longrightarrow> hd fl (map (\<lambda>a. h1 a tt) il)
            = hd fl (map (\<lambda>a. h2 a tt) il)"
          using Cons(6) by (smt (verit, best) map_eq_conv)
        show ?thesis using Cons(4,5) tmp1 tmp2 1 2 using behavCalBlk.simps(4)[of il v vl "hd ol" "tl ol"
            "hd fl" "tl fl" t0 t h1] behavCalBlk.simps(4)[of il v vl "hd ol" "tl ol"
            "hd fl" "tl fl" t0 t h2] by force
      qed
      have 4: "\<forall>t'. t' < t0 + t \<and> t0 < t' \<longrightarrow> (\<forall>v\<in>set vl. h1 v t' = h2 v t')"
      proof(cases "vl = []")
        case True
        then show ?thesis by simp
      next
        case False
        have tmp1: "Available' (Block il vl (tl ol) T (tl fl))"
        proof -
            have tmp: "({0} = set (tl ol) \<or> {1} = set (tl ol) \<or> tl ol = [])"
            proof(cases "set ol = {}")
              case True
              then show ?thesis by simp
            next
              case False
              note F = False
              then show ?thesis
              proof(cases "set ol = {0}")
                case True
                then show ?thesis by (metis "2" False insert_absorb insert_eq_iff 
                      list.set_intros(1) list.simps(15) set_empty singletonD)
              next
                case False
                have tmp: "set ol = {1}"
                  using Cons(2) F False unfolding Available'_def by simp
                then show ?thesis by (metis "2" set_empty set_subset_Cons subset_singletonD)
              qed
            qed
            then show ?thesis using Cons(2) False unfolding Available'_def apply simp by (metis
                  Cons.prems(2) One_nat_def Suc_less_eq diff_Suc_1 empty_iff insert_iff 
                  nth_Cons_Suc old.nat.distinct(1))
          qed
          have tmp2: "behavCalBlk il vl (tl ol) (tl fl) t0 t h1 = True"
            using Cons(4) 1 2 using behavCalBlk.simps(4)[of il v vl "hd ol" "tl ol"
            "hd fl" "tl fl" t0 t h1] Cons.prems(2) behavCalBlk.elims(3)
            by (metis equals0D insert_iff less_or_eq_imp_le not_one_le_zero)
          have tmp3: "behavCalBlk il vl (tl ol) (tl fl) t0 t h2 = True"
            using Cons(5) 1 2 using behavCalBlk.simps(4)[of il v vl "hd ol" "tl ol"
            "hd fl" "tl fl" t0 t h2] Cons.prems(2) behavCalBlk.elims(3)
            by (metis equals0D insert_iff less_or_eq_imp_le not_one_le_zero)
          then show ?thesis
          proof(cases "tl ol = []")
            case True
            then show ?thesis using False Cons
              using Available'_def length_0_conv tmp1 by auto
          next
            case False
            have tmp4: "set (tl ol) = {0}"
              using False Cons(3) 2 by (metis set_empty2 set_subset_Cons subset_singletonD)
            then show ?thesis using tmp1 tmp2 tmp3 Cons(1,6) by presburger
          qed
      qed
      then show ?thesis using 3 by auto
    qed
  qed
qed



fun behavCalBlks :: "block list \<Rightarrow> real \<Rightarrow> real \<Rightarrow> behav" where
  "behavCalBlks [] t0 t h = True" |
  "behavCalBlks (b#bl) t0 t h = (behavCalBlk (get_inputs b) (get_outputs b) 
  (get_offsets b) (get_outupd b) t0 t h \<and> behavCalBlks bl t0 t h)"

lemma behavCalBlks_last: "behavCalBlks (b#bl) t0 t h \<Longrightarrow>
behavCalBlks (bl@[b]) t0 t h"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  have 1: "behavCalBlks ((a # bl) @ [b]) t0 t h = 
    behavCalBlks (a # bl @ [b]) t0 t h"
    by simp
  then show ?case using Cons unfolding behavCalBlks.simps by blast
qed

lemma behavCalBlks_rev: "behavCalBlks bl t0 t h \<Longrightarrow>
behavCalBlks (rev bl) t0 t h"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  have 1: "behavCalBlks (rev (a # bl)) t0 t h = 
    behavCalBlks (rev bl @ [a]) t0 t h"
    by simp
  have 2: "behavCalBlks (a#(rev bl)) t0 t h "
    using Cons unfolding behavCalBlks.simps by auto
  then show ?case using 1 behavCalBlks_last by blast
qed

(*continuous diag has two parts: computational blocks and integrator blocks;
the behav check computational blocks and integrator blocks separately*)
fun behavConDiag :: "block list \<Rightarrow> real \<Rightarrow> real \<Rightarrow> timed_vars \<Rightarrow> timed_vars \<Rightarrow> bool" where
  "behavConDiag bl t0 t h h0 = (checkODE (updateIntegBlks bl (findIntegBlks bl)) h h0 t0 t 
  \<and> behavCalBlks (getCalBlks bl) t0 t h)"

lemma behavConDiag_rev: "wf2 bl \<Longrightarrow> behavConDiag bl t0 t h h0 \<Longrightarrow> 
behavConDiag (rev bl) t0 t h h0"
  subgoal premises pre
  proof -
    have 1: "(updateIntegBlks bl (findIntegBlks bl)) = 
      (updateIntegBlks (rev bl) (findIntegBlks (rev bl)))"
    proof -
    have tmp1: "wf2 (rev bl)"
      using pre(1) wf2_rev by simp
    have tmp2: "\<forall>bl. wf2 bl \<longrightarrow> wf2 (findIntegBlks bl)"
      apply clarify subgoal for bl
      proof(induction bl)
            case Nil
            then show ?case by simp
          next
            case (Cons a bl)
            then show ?case
            proof(cases "set (get_offsets a) = {0}")
              case True
              then show ?thesis unfolding getCalBlks.simps using Cons
                by (simp add: wf2_lemma)
            next
              case False
              have tmp1: "\<forall>j. j < (length bl) \<and> j \<ge> 0 \<longrightarrow> a \<noteq> (nth bl j) "
                using Cons(2) unfolding wf2_def Unique_def
                by (metis wf2_def Cons.prems Unique_k list.set_intros(1) remove_hd)
              have tmp2: "\<forall>j. j < (length (findIntegBlks bl)) \<and> j \<ge> 0 
                \<longrightarrow> a \<noteq> (nth (findIntegBlks bl) j)"
                using tmp1 findIntegBlksSubset3
                by (metis in_set_conv_nth less_eq_nat.simps(1) subset_code(1))
              have tmp3: "Unique (a # findIntegBlks bl)"
                using Cons Unique_add unfolding wf2_def tmp2 
                by (metis wf2_def wf2_lemma tmp2)
              have tmp4: "Graph (set (a # findIntegBlks bl))"
              proof -
                have tmp1: "set (a # findIntegBlks bl) \<subseteq> set (a#bl)"
                  using findIntegBlksSubset3 by auto
                show ?thesis using tmp1 Cons(2) unfolding wf2_def
                  by (meson Graph_def subsetD)
              qed
              have tmp5: "Ball (set (a # findIntegBlks bl)) Available' "
              proof -
                have tmp1: "set (a # findIntegBlks bl) \<subseteq> set (a#bl)"
                  using findIntegBlksSubset3 by auto
                show ?thesis using tmp1 Cons(2) unfolding wf2_def by blast
              qed
              show ?thesis using False unfolding 
                  findIntegBlks.simps wf2_def apply simp using tmp3 tmp4 tmp5
                by (metis wf2_def wf2_lemma list.set_intros(1) list.simps(15))
            qed
          qed
          done
      then show ?thesis using updateIntegBlksPerm pre(1) findIntegBlksPerm using tmp1
        by (metis perm_rev)
    qed
  have 2: "checkODE (updateIntegBlks (rev bl) (findIntegBlks (rev bl))) h h0 t0 t"
    using pre(2) 1 unfolding behavConDiag.simps by metis
  show ?thesis using pre unfolding behavConDiag.simps 
    using 2 behavCalBlks_rev getCalBlks_rev by presburger
qed
  done

lemma behavCalBlks_eq1 : "\<forall>x \<in> Inputs bl \<union> (Outputs bl). \<forall>tt. h1 x tt = h2 x tt
\<Longrightarrow> behavCalBlks bl t0 t h1 \<Longrightarrow> behavCalBlks bl t0 t h2"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  have 1: "behavCalBlks bl t0 t h2"
  proof -
    have tmp1: "\<forall>x\<in>Inputs bl \<union> Outputs bl. \<forall>tt. h1 x tt = h2 x tt"
      using Cons(2) using Inputs.simps(2) Outputs.simps(2) by blast
    have tmp2: "behavCalBlks bl t0 t h1"
      using Cons(3) unfolding behavCalBlks.simps by simp
    show ?thesis using tmp1 tmp2 Cons(1) by simp
  qed
  have 2: "behavCalBlk (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) t0 t h2"
    using behavCalBlk_eq1 Cons(1,3) unfolding behavCalBlks.simps
    using Cons.prems(1) Inputs.simps(2) Outputs.simps(2) by blast
  then show ?case unfolding behavCalBlks.simps using 1 by auto
qed

lemma behavCalBlks_eq2 : "\<forall>x \<in> Inputs bl \<union> (Outputs bl). 
\<forall>tt < t0 + t. h1 x tt = h2 x tt
\<Longrightarrow> behavCalBlks bl t0 t h1 \<Longrightarrow> behavCalBlks bl t0 t h2"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  have 1: "behavCalBlks bl t0 t h2"
  proof -
    have tmp1: "\<forall>x\<in>Inputs bl \<union> Outputs bl. \<forall>tt < t0 + t. h1 x tt = h2 x tt"
      using Cons(2) using Inputs.simps(2) Outputs.simps(2) by blast
    have tmp2: "behavCalBlks bl t0 t h1"
      using Cons(3) unfolding behavCalBlks.simps by simp
    show ?thesis using tmp1 tmp2 Cons(1) by simp
  qed
  have 2: "behavCalBlk (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) t0 t h2"
    using behavCalBlk_eq2 Cons(1,3) unfolding behavCalBlks.simps
    using Cons.prems(1) Inputs.simps(2) Outputs.simps(2) by blast
  then show ?case unfolding behavCalBlks.simps using 1 by auto
qed

lemma behavConDiag_eq : "\<forall>x \<in> (Outputs (getCalBlks bl)). 
\<forall>tt < t0 + t. h1 x tt = h2 x tt \<Longrightarrow>
\<forall>x \<in> (Outputs (findIntegBlks bl)). \<forall>tt \<le> t0 + t. h1 x tt = h2 x tt 
\<Longrightarrow> \<forall>x \<in> (Inputs bl). \<forall>tt < t0 + t. h1 x tt = h2 x tt \<Longrightarrow> wf2 bl
\<Longrightarrow> behavConDiag bl t0 t h1 h0 \<Longrightarrow> behavConDiag bl t0 t h2 h0"
  subgoal premises pre
  proof -
    have 1: "behavCalBlks (getCalBlks bl) t0 t h2"
    proof -
      have tmp1: "Inputs (getCalBlks bl) \<subseteq> (Inputs bl)"
        using getCalBlksSubset3 by auto
      then show ?thesis using behavCalBlks_eq2 pre unfolding behavConDiag.simps
        by (metis (no_types, lifting) Un_iff subset_Un_eq)
    qed
    have 2: "checkODE (updateIntegBlks bl (findIntegBlks bl)) h2 h0 t0 t"
    proof -
      have tmp: "set (get_outputs (updateIntegBlks bl (findIntegBlks bl))) = Outputs (findIntegBlks bl)"
      proof -
        have tmp1: "wf2 (findIntegBlks bl)"
          using findIntegBlkswf pre(4) by simp
        have tmp2: "\<forall>b\<in>set bl. set (get_offsets b) = {1} \<longrightarrow> set (get_outputs b) \<subseteq> Outputs (findIntegBlks bl)"
        proof(induction bl)
          case Nil
          then show ?case by simp
        next
          case (Cons a bl)
          then show ?case
          proof(cases "set (get_offsets a) = {1}")
            case True
            then show ?thesis unfolding findIntegBlks.simps using Cons by auto
          next
            case False
            then show ?thesis unfolding findIntegBlks.simps using Cons by auto
          qed
        qed
        have tmp3: "\<forall>c\<in>set (findIntegBlks bl). set (get_offsets c) = {1}"
        proof(induction bl)
          case Nil
          then show ?case by simp
        next
          case (Cons a bl)
          then show ?case
          proof(cases "set (get_offsets a) = {1}")
            case True
            then show ?thesis unfolding findIntegBlks.simps using Cons by auto
          next
            case False
            then show ?thesis unfolding findIntegBlks.simps using Cons by auto
          qed
        qed
        show ?thesis using updateIntegBlksSubset2 tmp1 tmp2 tmp3 pre(4) 
            findIntegBlksSubset3 by presburger
      qed
      then show ?thesis using checkODE_eq findIntegBlksSubset pre(2,5) 
        unfolding behavConDiag.simps by presburger
    qed
  show ?thesis unfolding behavConDiag.simps using 1 2 by simp
qed
  done

lemma behavConDiag_eq2: "\<forall>v. h1 v t0 = h2 v t0 \<Longrightarrow> behavConDiag bl t0 t h h1 \<Longrightarrow>
behavConDiag bl t0 t h h2"
  unfolding behavConDiag.simps using checkODE_eq2 by presburger


fun exeCalBlk :: "var list \<Rightarrow> var list \<Rightarrow> offset list \<Rightarrow> outupd list \<Rightarrow> timed_vars 
\<Rightarrow> real \<Rightarrow> real \<Rightarrow> timed_vars" where
  "exeCalBlk il [] ol fl h t0 t = h" |
  "exeCalBlk il vl ol [] h t0 t = h" |
  "exeCalBlk il vl [] fl h t0 t = h" |
  "exeCalBlk il (v#vl) (d#ol) (f#fl) h t0 t = (if 1 \<in> set (d#ol) then 
  h else exeCalBlk il vl ol fl (\<lambda> vv tt. 
  (if vv = v \<and> tt < t0 + t \<and> tt > t0 then f (map (\<lambda> a. h a tt) il) else h vv tt)) t0 t)"

fun exeCalBlk_attime :: "var list \<Rightarrow> var list \<Rightarrow> offset list \<Rightarrow> outupd list \<Rightarrow> timed_vars 
\<Rightarrow> real \<Rightarrow> timed_vars" where
  "exeCalBlk_attime il [] ol fl h t = h" |
  "exeCalBlk_attime il vl ol [] h t = h" |
  "exeCalBlk_attime il vl [] fl h t = h" |
  "exeCalBlk_attime il (v#vl) (d#ol) (f#fl) h t = (if 1 \<in> set (d#ol) then 
  h else exeCalBlk_attime il vl ol fl (\<lambda> vv tt. 
  (if vv = v \<and> tt = t then f (map (\<lambda> a. h a tt) il) else h vv tt)) t)"

lemma exeCalBlk_lemma1 : "\<forall>x. x \<notin> set vl \<longrightarrow> (\<forall>tt. 
exeCalBlk il vl ol fl h t0 t x tt = h x tt)"
proof(induction fl arbitrary:vl ol h)
  case Nil
  then show ?case
  proof(cases "vl = []")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis by (metis exeCalBlk.simps(2) neq_Nil_conv)
  qed
next
  case (Cons f fl)
  then show ?case
  proof(cases "vl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have 1: "vl = hd vl#(tl vl)"
      using False by simp
    then show ?thesis
    proof(cases "ol = []")
      case True
      then show ?thesis using 1 by (metis exeCalBlk.simps(3))
    next
      case False
      have 2: "ol = hd ol#(tl ol)"
        using False by simp
      then show ?thesis 
      proof(cases "hd ol = 1")
        case True
        then show ?thesis using exeCalBlk.simps(4)[of il "hd vl" "tl vl"
            "hd ol" "tl ol" f fl h t0 t] Cons
          using "1" "2" by auto
      next
        case False
        have 3: "\<forall>x. x \<notin> set vl \<longrightarrow>
        (\<forall>tt. exeCalBlk il (tl vl) (tl ol) fl
               (\<lambda>vv tt. if vv = hd vl \<and> tt < t0 + t \<and> t0 < tt 
                  then f (map (\<lambda>a. h a tt) il) else h vv tt)
               t0 t x tt = (\<lambda>vv tt. if vv = hd vl \<and> tt < t0 + t \<and> t0 < tt 
                  then f (map (\<lambda>a. h a tt) il)
                   else h vv tt) x tt)"
          using Cons[of "tl vl" "tl ol"]
          by (smt (verit, ccfv_threshold) "1" list.set_intros(2))
        then show ?thesis using exeCalBlk.simps(4)[of il "hd vl" "tl vl"
            "hd ol" "tl ol" f fl h t0 t] 1 2 apply simp using Cons[of "tl vl" "tl ol"]
          by (metis list.set_intros(1))
      qed
    qed
  qed
qed

lemma exeCalBlk_lemma2: "Available' (Block il vl ol st fl) \<Longrightarrow>
  \<forall>x \<in> set il \<union> set vl . \<forall>tt. h1 x tt = h2 x tt \<Longrightarrow>
  \<forall>xx \<in> set vl. \<forall>tt. 
  (exeCalBlk il vl ol fl h1 t0 t) xx tt =
  (exeCalBlk il vl ol fl h2 t0 t) xx tt "
proof(induction vl arbitrary:fl ol h1 h2)
  case Nil
  then show ?case by simp
next
  case (Cons v vl)
  then show ?case
  proof(cases "fl = []")
    case True
    then show ?thesis using Cons(2) by (simp add: Cons.prems(2))
  next
    case False
    have 1: "fl = hd fl #tl fl"
      using False by simp
    then show ?thesis
    proof(cases "ol = []")
      case True
      then show ?thesis using Cons(2) by (simp add: Available'_def)
    next
      case False
      have 2: "ol = hd ol # tl ol"
        using False by simp
      then show ?thesis
      proof(cases "1 \<in> set ol")
        case True
        then show ?thesis using 1 2 Cons(2)
          by (metis Cons.prems(2) Un_iff exeCalBlk.simps(4))
      next
        case False
        have 3: "\<forall>xx\<in>set vl. \<forall>tt. 
            exeCalBlk il vl (tl ol) (tl fl) (\<lambda>vv tt.
               if vv = v \<and> tt < t0 + t \<and> t0 < tt then hd fl (map (\<lambda>a. h1 a tt) il)
               else h1 vv tt) t0 t xx tt =
            exeCalBlk il vl (tl ol) (tl fl) (\<lambda>vv tt.
               if vv = v \<and> tt < t0 + t \<and> t0 < tt then hd fl (map (\<lambda>a. h2 a tt) il)
               else h2 vv tt) t0 t xx tt"
        proof -
          have tmp1: "Available' (Block il vl (tl ol) st (tl fl))"
          proof -
            have tmp: "({0} = set (tl ol) \<or> {1} = set (tl ol) \<or> tl ol = [])"
            proof(cases "set ol = {}")
              case True
              then show ?thesis by simp
            next
              case False
              note F = False
              then show ?thesis
              proof(cases "set ol = {0}")
                case True
                then show ?thesis by (metis "2" False insert_absorb insert_eq_iff 
                      list.set_intros(1) list.simps(15) set_empty singletonD)
              next
                case False
                have tmp: "set ol = {1}"
                  using Cons(2) F False unfolding Available'_def by simp
                then show ?thesis by (metis "2" set_empty set_subset_Cons subset_singletonD)
              qed
            qed
            then show ?thesis using Cons(2) unfolding Available'_def apply simp by (metis False 
                  One_nat_def diff_Suc_1 diff_Suc_Suc nth_Cons_Suc zero_less_diff)
          qed
          have tmp2: "v \<notin> set vl"
            using Cons(2) unfolding Available'_def by (metis Suc_eq_plus1 bot_nat_0.extremum 
                get_outputs.simps in_set_conv_nth le_imp_less_Suc length_tl less_diff_conv 
                list.sel(3) nth_Cons_0 nth_tl)
          have tmp3: "v \<notin> set il"
            using Cons(2) unfolding Available'_def using False by simp
          have tmp4: "\<forall>x\<in>set il \<union> set vl. \<forall>tt. (\<lambda>vv tt.
               if vv = v \<and> tt < t0 + t \<and> t0 < tt then hd fl (map (\<lambda>a. h1 a tt) il)
               else h1 vv tt) x tt = (\<lambda>vv tt.
               if vv = v \<and> tt < t0 + t \<and> t0 < tt then hd fl (map (\<lambda>a. h2 a tt) il)
               else h2 vv tt) x tt"
            using Cons(3) tmp2 tmp3 by auto
          show ?thesis using Cons(1) tmp4 tmp1 by presburger
        qed
        have 4: "\<forall>xx\<in>set vl. \<forall>tt. 
            exeCalBlk il (v # vl) ol fl h1 t0 t xx tt =
            exeCalBlk il (v # vl) ol fl h2 t0 t xx tt"
          using Cons(3) exeCalBlk.simps(4)[of il v vl
            "hd ol" "tl ol" "hd fl" "tl fl" h1 t0 t] exeCalBlk.simps(4)[of il v vl
            "hd ol" "tl ol" "hd fl" "tl fl" h2 t0 t] 1 2 3 False by force
        have 5: "\<forall>tt. exeCalBlk il (v # vl) ol fl h1 t0 t v tt =
            exeCalBlk il (v # vl) ol fl h2 t0 t v tt"
        proof -
          have tmp1: "\<forall>tt. t0 < tt \<and> tt < t0 + t \<longrightarrow>
            hd fl (map (\<lambda>a. h2 a tt) il) = hd fl (map (\<lambda>a. h2 a tt) il)"
            using Cons(3) by blast
          have tmp2: "v \<notin> set vl"
            using Cons(2) unfolding Available'_def by (metis Suc_eq_plus1 bot_nat_0.extremum 
                get_outputs.simps in_set_conv_nth le_imp_less_Suc length_tl less_diff_conv 
                list.sel(3) nth_Cons_0 nth_tl)
          show ?thesis using 1 2 False exeCalBlk.simps(4)[of il v vl
            "hd ol" "tl ol" "hd fl" "tl fl" h1 t0 t] exeCalBlk.simps(4)[of il v vl
            "hd ol" "tl ol" "hd fl" "tl fl" h2 t0 t] exeCalBlk_lemma1 tmp1 tmp2
            by (smt (z3) Cons.prems(2) Un_iff list.set_intros(1) map_eq_conv)
        qed
        then show ?thesis using 4 5 by simp
      qed
    qed
  qed
qed

lemma exeCalBlk_lemma3 : "\<forall> tt. tt \<ge> t0 + t \<or> tt \<le> t0 \<longrightarrow> (\<forall>x. 
exeCalBlk il vl ol fl h t0 t x tt = h x tt)"
proof(induction fl arbitrary:vl ol h)
  case Nil
  then show ?case
  proof(cases "vl = []")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis by (metis exeCalBlk.simps(2) neq_Nil_conv)
  qed
next
  case (Cons f fl)
  then show ?case
  proof(cases "vl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have 1: "vl = hd vl#(tl vl)"
      using False by simp
    then show ?thesis
    proof(cases "ol = []")
      case True
      then show ?thesis using 1 by (metis exeCalBlk.simps(3))
    next
      case False
      have 2: "ol = hd ol#(tl ol)"
        using False by simp
      then show ?thesis 
      proof(cases "hd ol = 1")
        case True
        then show ?thesis using exeCalBlk.simps(4)[of il "hd vl" "tl vl"
            "hd ol" "tl ol" f fl h t0 t] Cons
          using "1" "2" by auto
      next
        case False
        have 3: "\<forall> tt. tt \<ge> t0 + t \<or> tt \<le> t0  \<longrightarrow>
        (\<forall>x. exeCalBlk il (tl vl) (tl ol) fl
               (\<lambda>vv tt. if vv = hd vl \<and> tt < t0 + t \<and> t0 < tt 
                  then f (map (\<lambda>a. h a tt) il) else h vv tt)
               t0 t x tt = (\<lambda>vv tt. if vv = hd vl \<and> tt < t0 + t \<and> t0 < tt 
                  then f (map (\<lambda>a. h a tt) il)
                   else h vv tt) x tt)"
          using Cons[of "tl vl" "tl ol"] by blast
        then show ?thesis using exeCalBlk.simps(4)[of il "hd vl" "tl vl"
            "hd ol" "tl ol" f fl h t0 t] 1 2 by simp     
      qed
    qed
  qed
qed

fun exeCalBlks :: "sorted_block_list \<Rightarrow> timed_vars \<Rightarrow> real \<Rightarrow> real \<Rightarrow> timed_vars" where
  "exeCalBlks [] h t0 t = h" |
  "exeCalBlks (b#bl) h t0 t  = exeCalBlk (get_inputs b) (get_outputs b) 
  (get_offsets b) (get_outupd b) (exeCalBlks bl h t0 t) t0 t"

fun exeCalBlks_attime :: "sorted_block_list \<Rightarrow> timed_vars \<Rightarrow> real \<Rightarrow> timed_vars" where
  "exeCalBlks_attime [] h t = h" |
  "exeCalBlks_attime (b#bl) h t  = exeCalBlk_attime (get_inputs b) (get_outputs b) 
  (get_offsets b) (get_outupd b) (exeCalBlks_attime bl h t) t"

lemma exeCalBlks_lemma1: "\<forall>x. x \<notin> Outputs bl \<longrightarrow> (\<forall>tt. 
exeCalBlks bl h t0 t x tt = h x tt)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case using exeCalBlk_lemma1 unfolding exeCalBlks.simps 
    by simp
qed

lemma exeCalBlks_lemma2: "\<forall> tt. tt \<ge> t0 + t \<or> tt \<le> t0 \<longrightarrow> (\<forall>x.
exeCalBlks bl h t0 t x tt = h x tt)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case using exeCalBlk_lemma3 unfolding exeCalBlks.simps 
    by simp
qed

(*first execute ODE and then the computational blocks.*)
fun exeContinuousDiag_interval :: "sorted_block_list \<Rightarrow> timed_vars \<Rightarrow> real \<Rightarrow> real \<Rightarrow> timed_vars" where
  "exeContinuousDiag_interval bl h t0 t  = exeCalBlks (getCalBlks bl) (\<lambda>vv tt. 
(updTimedVar (solveODE h (updateIntegBlks bl (findIntegBlks bl)) t0 t) (get_outputs (updateIntegBlks bl 
(findIntegBlks bl))) h t0 t vv tt)) t0 t"

function exeContinuousDiag_tilltime :: "sorted_block_list \<Rightarrow> timed_vars \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> timed_vars" where
  "exeContinuousDiag_tilltime bl h t te  = (if te \<le> 0 \<or> t \<le> 0 then h else exeContinuousDiag_interval
  bl (exeContinuousDiag_tilltime bl h t (te-t)) (te-t) t)"
  by pat_completeness auto
termination 
  apply (relation "measures[(\<lambda>(bl::ConBlk list, h::timed_vars, t::nat, te::nat). te)]", auto)
  done

lemma exeContinuousDiag_interval_lemma1 : "wf2 bl \<Longrightarrow> \<forall>x. x \<notin> Outputs bl \<longrightarrow> (\<forall>tt. 
(exeContinuousDiag_interval bl h t0 t) x tt = h x tt)"
  subgoal premises pre
proof -
  have 1: "\<forall>b \<in> set bl. set (get_offsets b) = {0} \<or> set (get_offsets b) = {1}"
      using pre unfolding wf2_def Available'_def Graph_def
      by (metis less_nat_zero_code list.size(3) set_empty2 )
  have 2: "Outputs bl = Outputs (getCalBlks bl) \<union> Outputs (findIntegBlks bl)"
    using 1 proof(induction bl)
      case Nil
      then show ?case by simp
    next
      case (Cons b bl)
      then show ?case unfolding getCalBlks.simps findIntegBlks.simps by (smt 
            (verit, best) One_nat_def Outputs.simps(2) Un_assoc Un_left_commute list.set_intros(1) 
            list.set_intros(2) old.nat.distinct(1) singleton_insert_inj_eq')
    qed
  have 3: "wf2 (findIntegBlks bl)"
    using findIntegBlkswf pre by simp
  have 4: "\<forall>b\<in>set bl. set (get_offsets b) = {1} \<longrightarrow> set (get_outputs b) \<subseteq> Outputs (findIntegBlks bl)"
  proof(induction bl)
    case Nil
    then show ?case by simp
  next
    case (Cons a bl)
    then show ?case
    proof(cases "set (get_offsets a) = {1}")
      case True
      then show ?thesis unfolding findIntegBlks.simps using Cons by auto
    next
      case False
      then show ?thesis unfolding findIntegBlks.simps using Cons by auto
    qed
  qed
  have 5: "\<forall>c\<in>set (findIntegBlks bl). set (get_offsets c) = {1}"
  proof(induction bl)
    case Nil
    then show ?case by simp
  next
    case (Cons a bl)
    then show ?case
    proof(cases "set (get_offsets a) = {1}")
      case True
      then show ?thesis unfolding findIntegBlks.simps using Cons by auto
    next
      case False
      then show ?thesis unfolding findIntegBlks.simps using Cons by auto
    qed
  qed
  have 6: "set (get_outputs (updateIntegBlks bl (findIntegBlks bl))) = Outputs (findIntegBlks bl)"
    using 3 4 5 pre updateIntegBlksSubset2 using findIntegBlksSubset3 by presburger
  show ?thesis unfolding exeContinuousDiag_interval.simps using 2 updTimedVar_eq1 6
        exeCalBlks_lemma1 by simp
qed
  done

lemma exeContinuousDiag_interval_lemma2 : "\<forall>tt. tt \<le> t0 \<or> tt > t0 + t \<longrightarrow> (\<forall>x. 
(exeContinuousDiag_interval bl h t0 t) x tt = h x tt)"
  unfolding exeContinuousDiag_interval.simps using exeCalBlks_lemma2 updTimedVar_eq1
  by simp

lemma exeContinuousDiag_interval_lemma3: "wf2 bl \<Longrightarrow> \<forall>x. x \<in> Outputs bl \<longrightarrow>  
(exeContinuousDiag_interval bl h t0 t) x t0 = h x t0"
  subgoal premises pre
proof -
  have 1: "Outputs (findIntegBlks bl) \<inter> Outputs (getCalBlks bl) = {}"
    using pre IntegInterComputationalBlocks by simp
  have 2: "\<forall>b \<in> set bl. set (get_offsets b) = {0} \<or> set (get_offsets b) = {1}"
      using pre(1) unfolding wf2_def Available'_def Graph_def
      by (metis less_nat_zero_code list.size(3) set_empty2)
  have 3: "Outputs bl = Outputs (getCalBlks bl) \<union> Outputs (findIntegBlks bl)"
    using 2 proof(induction bl)
      case Nil
      then show ?case by simp
    next
      case (Cons b bl)
      then show ?case unfolding getCalBlks.simps findIntegBlks.simps by (smt 
            (verit, best) One_nat_def Outputs.simps(2) Un_assoc Un_left_commute list.set_intros(1) 
            list.set_intros(2) old.nat.distinct(1) singleton_insert_inj_eq')
    qed
  show ?thesis unfolding exeContinuousDiag_interval.simps using updTimedVar_eq1 
      exeCalBlks_lemma1 exeCalBlks_lemma2 by simp
qed
  done

lemma exeCalBlks_eq1 : "wf2 (b#bl) \<Longrightarrow>
besorted2 (rev (b#bl)) \<Longrightarrow> \<forall>x \<in> Inputs bl \<union> (Outputs bl). \<forall>tt.
(exeCalBlks (b#bl) h t0 t) x tt = (exeCalBlks bl h t0 t) x tt"
  subgoal premises pre
proof -
  have 1: "set (get_outputs b) \<inter> Outputs bl = {}"
    using pre(1) 
  proof(induction bl)
    case Nil
    then show ?case by simp
  next
    case (Cons a bl)
    have tmp1: "wf2 (b # bl)"
    proof -
      have tmp1: "remove1 a (b#a#bl) = (b#bl)"
        using Cons(2) unfolding wf2_def Unique_def by simp
      have tmp2: "Unique (b#bl)"
        using Cons(2) unfolding wf2_def using Unique_remove by (metis remove1_idem tmp1)
      then show ?thesis using Cons(2) unfolding wf2_def Graph_def by auto
    qed
    have tmp2: "set (get_outputs b) \<inter> Outputs bl = {}"
      using Cons(1) tmp1 by simp
    then show ?case unfolding Outputs.simps using Cons(2) unfolding wf2_def Unique_def Graph_def
      by fastforce
  qed
  have 2: "Unique (b#bl)"
    using pre(1) unfolding wf2_def by simp
  have 3: "set (get_outputs b) \<inter> Inputs bl = {}"
    using pre(2) 2
  proof(induction bl)
    case Nil
    then show ?case by simp
  next
    case (Cons a bl)
    have tmp1: "Unique (b#bl)"
      using Cons(3) unfolding Unique_def
      by (smt (verit, ccfv_threshold) length_Cons lessI less_imp_le_nat less_trans_Suc 
          list.sel(3) nth_Cons' nth_tl order_le_less_trans)
    have tmp2: "remove1 a (rev (b # a # bl)) = rev (b#bl)"
      using Cons(3) unfolding Unique_def 
      by (metis Cons.prems(2) One_nat_def Unique_k Unique_lemma append.right_neutral 
          in_set_conv_nth less_one list.set_intros(1) not_less_eq order_le_less 
          remove1_append remove_hd rev.simps(2) set_rev)
    have tmp3: "besorted2 (rev (b # bl))"
      using Cons(2) besorted2_remove tmp1 tmp2 
      by (metis Cons.prems(2) Unique_rev)
    have tmp4: "set (get_outputs b) \<inter> Inputs bl = {}"
      using Cons(1) tmp1 tmp2 tmp3 by simp
    have tmp5: "besorted2 ((rev bl)@([a]@[b]))"
      using Cons(2) by simp
    have tmp6: "set (get_outputs b) \<inter> set (get_inputs a) = {}"
      using tmp5 besorted2_lemma[of "rev bl" "a" "b"] by simp
    then show ?case using Cons(2) tmp4 unfolding Inputs.simps by auto
  qed
  have 4: "set (get_outputs b) \<inter> (Inputs bl \<union> Outputs bl) = {}"
    using 1 3 by auto
  show ?thesis unfolding exeCalBlks.simps using 4  exeCalBlk_lemma1
    by blast
  qed
  done

(*unique_on_bounded_closed condition:
for all h has a L.*)
definition ODE_cond :: "block \<Rightarrow> timed_vars \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "ODE_cond b h t0 t = (\<exists>L. unique_on_bounded_closed (t0)
 {(t0) -- (t0+ t)} (state2vec (timedVar2State h t0 )) 
(block2ODE b) UNIV L)"

definition ODE_cond' :: "block \<Rightarrow> timed_vars \<Rightarrow> real \<Rightarrow> bool" where
  "ODE_cond' b h k = (\<forall>h t0 t. (\<exists>L. unique_on_bounded_closed (t0)
 {(t0) -- (t0+ t)} (state2vec (timedVar2State h t0 )) 
(block2ODE b) UNIV L))"


lemma existence_of_one_block: "Available' (Block il vl ol st fl) \<Longrightarrow>
  behavCalBlk il vl ol fl t0 t (exeCalBlk il vl ol fl h t0 t)"
proof(induction vl arbitrary: ol fl h)
  case Nil
  then show ?case by simp
next
  case (Cons v vl)
  then show ?case
  proof(cases "fl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have 1: "fl = hd fl # tl fl"
      using False by simp
    then show ?thesis
    proof(cases "ol = []")
      case True
      then show ?thesis using behavCalBlk.elims(3) by blast
    next
      case False
      have 2: "ol = hd ol # tl ol"
        using False by simp
      then show ?thesis 
      proof(cases "1 \<in> set ol")
        case True
        then show ?thesis using 1 2 by (metis behavCalBlk.simps(4))
      next
        case False
        have 3: "\<forall>t'. t' < t0 + t \<and> t0 < t' \<longrightarrow> 
        (exeCalBlk il (v # vl) ol fl h t0 t) v t' = hd fl (map (\<lambda>a. 
        (exeCalBlk il (v # vl) ol fl h t0 t) a t') il)"
        proof -
          have tmp1: "v \<notin> set vl"
            using Cons(2) unfolding Available'_def by (metis Suc_eq_plus1 bot_nat_0.extremum 
                get_outputs.simps in_set_conv_nth le_imp_less_Suc length_tl less_diff_conv 
                list.sel(3) nth_Cons_0 nth_tl)
          have tmp2: "set il \<inter> set (v#vl) = {}"
            using Cons(2) unfolding Available'_def using False by auto
          have tmp3: "\<forall>tt. (map (\<lambda>a. (exeCalBlk il (v # vl) ol fl h t0 t) a tt) il) = 
            (map (\<lambda>a. h a tt) il)"
            using exeCalBlk_lemma1 using 1 2 tmp2 False 
            by (meson disjoint_iff_not_equal list.map_cong0)
          then show ?thesis using exeCalBlk_lemma1 using tmp1 1 2 False
             using exeCalBlk.simps(4)[of il v vl "hd ol" "tl ol" "hd fl"
              "tl fl" h t0 t] by (smt (z3))
        qed
        have 4: "behavCalBlk il vl (tl ol) (tl fl) t0 t
                 (exeCalBlk il (v # vl) ol fl h t0 t)"
        proof -
          have tmp1: "Available' (Block il vl (tl ol) st (tl fl))"
          proof -
            have tmp: "({0} = set (tl ol) \<or> {1} = set (tl ol) \<or> tl ol = [])"
            proof(cases "set ol = {}")
              case True
              then show ?thesis by simp
            next
              case False
              note F = False
              then show ?thesis
              proof(cases "set ol = {0}")
                case True
                then show ?thesis by (metis "2" False insert_absorb insert_eq_iff 
                      list.set_intros(1) list.simps(15) set_empty singletonD)
              next
                case False
                have tmp: "set ol = {1}"
                  using Cons(2) F False unfolding Available'_def by simp
                then show ?thesis by (metis "2" set_empty set_subset_Cons subset_singletonD)
              qed
            qed
            then show ?thesis using Cons(2) unfolding Available'_def apply simp by (metis False 
                  One_nat_def diff_Suc_1 diff_Suc_Suc nth_Cons_Suc zero_less_diff)
          qed
          have tmp2: "behavCalBlk il vl (tl ol) (tl fl) t0 t
                 (exeCalBlk il vl (tl ol) (tl fl) h t0 t)"
            using tmp1 Cons(1) by presburger
          have tmp3: "\<forall>x\<in>set il \<union> set vl. \<forall>tt. (exeCalBlk il (v # vl) ol fl h t0 t) x tt 
            = (exeCalBlk il vl (tl ol) (tl fl) h t0 t) x tt"
          proof -
            have tmp3_1: "v \<notin> set vl"
              using Cons(2) unfolding Available'_def by (metis Suc_eq_plus1 bot_nat_0.extremum 
                  get_outputs.simps in_set_conv_nth le_imp_less_Suc length_tl less_diff_conv 
                  list.sel(3) nth_Cons_0 nth_tl)
            have tmp3_2: "\<forall>x\<in>set il \<union> set vl. \<forall>tt. (\<lambda>vv tt.
               if vv = v \<and> tt < t0 + t \<and> t0 < tt then hd fl (map (\<lambda>a. h a tt) il)
               else h vv tt) x tt = h x tt"
              using tmp3_1 using Available'_def Cons.prems False by force
            have tmp3_3: "\<forall>x\<in>set vl.
                \<forall>tt. exeCalBlk il (v # vl) ol fl h t0 t x tt =
                  exeCalBlk il vl (tl ol) (tl fl) h t0 t x tt"
              using exeCalBlk.simps(4)[of il v vl "hd ol" "tl ol" "hd fl"
              "tl fl" h t0 t] 1 2 False exeCalBlk_lemma2 tmp3_2 tmp1 by force
            have tmp3_4: "set il \<inter> set (v#vl) = {}"
              using Cons(2) False unfolding Available'_def by auto
            have tmp3_5: "\<forall>x\<in>set il.
                \<forall>tt. exeCalBlk il (v # vl) ol fl h t0 t x tt =
                  exeCalBlk il vl (tl ol) (tl fl) h t0 t x tt"
              using tmp3_4 exeCalBlk_lemma1 by (simp add: disjoint_iff)
            show ?thesis using tmp3_3 tmp3_5 by auto
          qed
          show ?thesis using behavCalBlk_eq1 tmp2 tmp3
            by (metis (no_types, opaque_lifting))
        qed
        then show ?thesis using exeCalBlk.simps(4)[of il v vl "hd ol" "tl ol" "hd fl"
              "tl fl" h t0 t] behavCalBlk.simps(4)[of il v vl "hd ol" "tl ol" "hd fl"
              "tl fl" t0 t "(exeCalBlk il (v # vl) ol fl h t0 t)"] Cons 1 2 3 False
          by simp
      qed
    qed
  qed
qed

lemma existence_of_calculational_blocks: 
shows "besorted2 (rev bl)  \<Longrightarrow> wf2 bl \<Longrightarrow> 
       behavCalBlks bl t0 t (exeCalBlks bl h t0 t)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  have 1: "behavCalBlks bl t0 t (exeCalBlks bl h t0 t)"
  proof -
    have tmp1: "besorted2 (rev bl)"
      using Cons(2) using besorted2.simps(2) besorted2_last by simp
    have tmp2: "wf2 bl"
      using Cons(3) wf2_lemma by simp
    show ?thesis using tmp1 tmp2 Cons(1,3) by simp
  qed
  have 2: "behavCalBlks bl t0 t (exeCalBlks (a # bl) h t0 t)"
  proof -
    have tmp1: "\<forall>x \<in> Inputs bl \<union> (Outputs bl). \<forall>tt.
(exeCalBlks (a#bl) h t0 t) x tt = (exeCalBlks bl h t0 t) x tt"
      using exeCalBlks_eq1 Cons(2,3) by presburger
    then show ?thesis using behavCalBlks_eq1 by (metis "1")
  qed
  have 3: "behavCalBlk (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) t0 t
        (exeCalBlks (a # bl) h t0 t)"
  proof -
    have tmp1: "Available' (Block (get_inputs a) (get_outputs a) (get_offsets a) 
      (get_sample_time a) (get_outupd a))"
      using Cons(3) unfolding wf2_def by (simp add: Available'_def)
    then show ?thesis unfolding exeCalBlks.simps 
       using existence_of_one_block by presburger
  qed
  then show ?case unfolding behavCalBlks.simps using 2 by simp
qed

lemma existence_of_continuous_diag_base: 
shows "cl = (getCalBlks bl) \<Longrightarrow> besorted2 (rev cl)  \<Longrightarrow> wf2 bl \<Longrightarrow> 
       ODE_cond (updateIntegBlks bl (findIntegBlks bl)) h t0 t = True \<Longrightarrow>
       behavConDiag bl t0 t (exeContinuousDiag_interval bl h t0 t) h"
  subgoal premises pre 
  proof -
    have 1: "besorted2 (rev cl)"
      using pre(2) by simp
    have 2: "wf2 cl"
    proof -
      have tmp1: "set cl \<subseteq> set bl"
        using pre(1)
      proof(induction bl arbitrary:cl)
        case Nil
        then show ?case by simp
      next
        case (Cons b bl)
        then show ?case unfolding getCalBlks.simps 
        proof(cases "set (get_offsets b) = {0}")
          case True
          then show ?thesis using Cons(1)[of "getCalBlks bl"] Cons(2)
            unfolding getCalBlks.simps by auto
        next
          case False
          then show ?thesis using Cons(1)[of "getCalBlks bl"] Cons(2)
            unfolding getCalBlks.simps by auto
        qed
      qed
      have tmp2: "(\<forall>i j. i < j \<and> j < length bl \<and> 0 \<le> i \<longrightarrow> bl ! i \<noteq> bl ! j)"
        using pre(3) unfolding wf2_def Unique_def by simp
      have tmp3: "Unique cl"
        using pre(1) tmp2 unfolding Unique_def
      proof(induction bl arbitrary:cl)
        case Nil
        then show ?case by simp
      next
        case (Cons b bl)
        then show ?case unfolding getCalBlks.simps
        proof(cases "set (get_offsets b) = {0}")
          case True
          have tmp1: "\<forall>i j. i < j \<and> j < length (getCalBlks bl) \<and> 0 \<le> i 
            \<longrightarrow> getCalBlks bl ! i \<noteq> getCalBlks bl ! j"
            using Cons(1,3) by (metis Unique_def Unique_lemma)
          have tmp2: "\<exists>c. c \<in> set (getCalBlks bl) \<and> c = b \<Longrightarrow> 
      \<forall>i j. i < j \<and> j < length (b # bl) \<and> 0 \<le> i \<longrightarrow> (b # bl) ! i \<noteq> (b # bl) ! j \<Longrightarrow> False"
            apply clarify subgoal premises pre for c
          proof -
            have tmp2_1: "\<forall>c. c \<in> set (getCalBlks bl) \<longrightarrow> c \<in> set bl"
              apply clarify subgoal for c
            proof(induction bl)
              case Nil
              then show ?case by simp
            next
              case (Cons d dl)
              then show ?case unfolding getCalBlks.simps
                by (smt (verit, best) list.set_intros(1) list.set_intros(2) set_ConsD)
            qed
            done
          have tmp2_2 : "b \<in> set bl"
            using tmp2_1 pre(2) by simp 
          show ?thesis using tmp2_2 pre(1) by (metis Suc_leI bot_nat_0.extremum in_set_conv_nth 
                le_imp_less_Suc length_Cons nth_Cons_0 nth_Cons_Suc)
          qed
          done
        have tmp3: "\<forall>i. i < length (getCalBlks bl) \<and> 0 \<le> i \<longrightarrow> 
              (getCalBlks bl) ! i \<noteq> b"
          using tmp2 Cons(3) using nth_mem by blast
        then show ?thesis using Cons(2) True unfolding getCalBlks.simps apply simp
            using tmp1 using less_Suc_eq_0_disj by fastforce
        next
          case False
          then show ?thesis using Cons unfolding getCalBlks.simps
            by (metis Unique_def Unique_lemma)
        qed
      qed
      have tmp4: "Graph (set cl)"
        using pre(3) tmp1 unfolding wf2_def Graph_def by (meson subsetD)
      show ?thesis using pre(3) tmp1 tmp3 tmp4 unfolding wf2_def by blast
    qed
    have 3: "behavCalBlks (getCalBlks bl) t0 t
     (exeCalBlks (getCalBlks bl)
       (updTimedVar (apply_bcontfun (solveODE h (updateIntegBlks bl (findIntegBlks bl)) t0 t))
         (get_outputs (updateIntegBlks bl (findIntegBlks bl))) h t0 t)
       t0 t)"
      using existence_of_calculational_blocks 1 2 pre(1) by force
    have 4: "checkODE (updateIntegBlks bl (findIntegBlks bl))
     (exeCalBlks (getCalBlks bl)
       (updTimedVar (apply_bcontfun (solveODE h (updateIntegBlks bl (findIntegBlks bl)) t0 t))
         (get_outputs (updateIntegBlks bl (findIntegBlks bl))) h t0 t)
       t0 t) h
     t0 t"
    proof -
      have tmp1: "((apply_bcontfun (solveODE h (updateIntegBlks bl (findIntegBlks bl)) t0 t))
        solves_ode (block2ODE (updateIntegBlks bl (findIntegBlks bl)))) 
        {(t0) -- (t0+ t)} UNIV"
        using pre(4) unfolding solveODE_def ODE_cond_def
        using unique_on_bounded_closed.fixed_point_solution by blast
      have tmp3: "\<forall>vv tt. vv \<in> set (get_outputs (updateIntegBlks bl (findIntegBlks bl))) \<and>
      t0 < tt \<and> tt \<le> t0 + t \<longrightarrow> exeCalBlks (getCalBlks bl)
      (updTimedVar (apply_bcontfun (solveODE h (updateIntegBlks bl (findIntegBlks bl)) t0 t))
      (get_outputs (updateIntegBlks bl (findIntegBlks bl))) h t0 t) t0 t vv tt = 
      apply_bcontfun (solveODE h (updateIntegBlks bl (findIntegBlks bl)) t0 t) tt $ vv"
      proof -
        have tmp1: "set (get_outputs (updateIntegBlks bl (findIntegBlks bl))) 
          \<subseteq> Outputs (findIntegBlks bl)"
        proof -
          have tmp1: "\<forall>b\<in>set bl. set (get_offsets b) = {1} \<longrightarrow> 
            set (get_outputs b) \<subseteq> Outputs (findIntegBlks bl)"
          proof(induction bl)
            case Nil
            then show ?case by simp
          next
            case (Cons a bl)
            then show ?case
            proof(cases "set (get_offsets a) = {1}")
              case True
              then show ?thesis using Cons unfolding findIntegBlks.simps by auto
            next
              case False
              then show ?thesis using Cons unfolding findIntegBlks.simps by simp
            qed
          qed
          have tmp2: "\<forall>c\<in>set (findIntegBlks bl). set (get_offsets c) = {1}"
          proof(induction bl)
            case Nil
            then show ?case by simp
          next
            case (Cons a bl)
            then show ?case
            proof(cases "set (get_offsets a) = {1}")
              case True
              then show ?thesis using Cons unfolding findIntegBlks.simps by auto
            next
              case False
              then show ?thesis using Cons unfolding findIntegBlks.simps by simp
            qed
          qed
          have tmp3: "set (findIntegBlks bl) \<subseteq> set bl"
          proof(induction bl)
            case Nil
            then show ?case by simp
          next
            case (Cons a bl)
            then show ?case
            proof(cases "set (get_offsets a) = {1}")
              case True
              then show ?thesis using Cons unfolding findIntegBlks.simps by auto
            next
              case False
              then show ?thesis using Cons unfolding findIntegBlks.simps by auto
            qed
          qed
          have tmp4: "wf2 (findIntegBlks bl)"
            using pre(3)
          proof(induction bl)
            case Nil
            then show ?case by simp
          next
            case (Cons a bl)
            then show ?case
            proof(cases "set (get_offsets a) = {0}")
              case True
              then show ?thesis unfolding getCalBlks.simps using Cons
                by (simp add: wf2_lemma)
            next
              case False
              have tmp1: "\<forall>j. j < (length bl) \<and> j \<ge> 0 \<longrightarrow> a \<noteq> (nth bl j) "
                using Cons(2) unfolding wf2_def Unique_def
                by (metis wf2_def Cons.prems Unique_k list.set_intros(1) remove_hd)
              have tmp2: "\<forall>j. j < (length (findIntegBlks bl)) \<and> j \<ge> 0 
                \<longrightarrow> a \<noteq> (nth (findIntegBlks bl) j)"
                using tmp1 findIntegBlksSubset3
                by (metis in_set_conv_nth less_eq_nat.simps(1) subset_code(1))
              have tmp3: "Unique (a # findIntegBlks bl)"
                using Cons Unique_add unfolding wf2_def tmp2 
                by (metis wf2_def wf2_lemma tmp2)
              have tmp4: "Graph (set (a # findIntegBlks bl))"
              proof -
                have tmp1: "set (a # findIntegBlks bl) \<subseteq> set (a#bl)"
                  using findIntegBlksSubset3 by auto
                show ?thesis using tmp1 Cons(2) unfolding wf2_def
                  by (meson Graph_def subsetD)
              qed
              have tmp5: "Ball (set (a # findIntegBlks bl)) Available' "
              proof -
                have tmp1: "set (a # findIntegBlks bl) \<subseteq> set (a#bl)"
                  using findIntegBlksSubset3 by auto
                show ?thesis using tmp1 Cons(2) unfolding wf2_def by blast
              qed
              show ?thesis using False unfolding 
                  findIntegBlks.simps wf2_def apply simp using tmp3 tmp4 tmp5
                by (metis wf2_def wf2_lemma list.set_intros(1) list.simps(15))
            qed
          qed
          show ?thesis using tmp1 tmp2 tmp3 tmp4 pre(3) updateIntegBlksSubset by presburger
        qed
        have tmp2: "Outputs (findIntegBlks bl) \<inter> Outputs (getCalBlks bl) = {}"
          using IntegInterComputationalBlocks pre(3) by presburger
        show ?thesis using exeCalBlks_lemma1 updTimedVar_eq2 
          by (smt (verit, del_insts) Int_iff empty_iff subsetD tmp1 tmp2)
      qed
      have tmp4: "(realstate2realvec (timedVar2timedState (\<lambda>vv tt.
            if vv \<in> set (get_outputs (updateIntegBlks bl (findIntegBlks bl))) \<and>
               t0 < tt \<and> tt \<le> t0 + t
            then exeCalBlks (getCalBlks bl) (updTimedVar
                    (apply_bcontfun (solveODE h (updateIntegBlks bl (findIntegBlks bl)) t0 t))
                    (get_outputs (updateIntegBlks bl (findIntegBlks bl))) h t0 t) t0 t vv tt
            else timedState2timedVar (realvec2realstate (apply_bcontfun (solveODE h
            (updateIntegBlks bl (findIntegBlks bl)) t0 t))) vv tt))) = 
            (apply_bcontfun (solveODE h (updateIntegBlks bl (findIntegBlks bl)) t0 t))"
      proof -
        have tmp4_2: "\<forall>vv' tt'.  (\<lambda>vv tt.
           if vv \<in> set (get_outputs (updateIntegBlks bl (findIntegBlks bl))) \<and>
        t0 < tt \<and> tt \<le> t0 + t then exeCalBlks (getCalBlks bl)
        (updTimedVar (apply_bcontfun (solveODE h (updateIntegBlks bl (findIntegBlks bl)) t0 t))
        (get_outputs (updateIntegBlks bl (findIntegBlks bl))) h t0 t) t0 t vv tt
         else timedState2timedVar (realvec2realstate (apply_bcontfun (solveODE h
        (updateIntegBlks bl (findIntegBlks bl)) t0 t))) vv tt) vv' tt' =
        apply_bcontfun (solveODE h (updateIntegBlks bl (findIntegBlks bl)) t0 t) tt' $ vv'"
          apply clarify subgoal for vv' tt'
        proof(cases "vv' \<in> set (get_outputs (updateIntegBlks bl (findIntegBlks bl))) \<and>
        t0 < tt' \<and> tt' \<le> t0 + t")
          case True
          then show ?thesis using tmp3 by presburger
        next
          case False
          have tmp1: "vv' \<notin> set (get_outputs (updateIntegBlks bl (findIntegBlks bl))) \<or>
               t0 \<ge> tt' \<or> tt' \<ge> t0 + t"
            using False by linarith
          then show ?thesis using  False apply simp by (metis realstate2realvec.simps 
                state2vec_def timedVar2timedState_def timedVar_state_map4 vec_lambda_beta)
        qed      
        done
        show ?thesis using tmp4_2 trans_eq4 vec_eq by (simp add: ext)
      qed
      show ?thesis unfolding checkODE.simps using tmp1 tmp3 tmp4 by presburger
    qed
  show ?thesis unfolding behavConDiag.simps exeContinuousDiag_interval.simps using 3 4 
    using pre(1) by force
qed
  done

lemma existence_of_continuous_diag: 
shows "cl = (getCalBlks bl) \<Longrightarrow> sortDiag (rev cl) = rev cl  \<Longrightarrow> wf2 bl \<Longrightarrow> 
       ODE_cond (updateIntegBlks bl (findIntegBlks bl)) h t0 t = True \<Longrightarrow>
       behavConDiag bl t0 t (exeContinuousDiag_interval bl h t0 t) h"
  subgoal premises pre 
    using pre(1,2,3) sort_is_sorted2 existence_of_continuous_diag_base pre(4) by presburger
  done


lemma behavCalBlks_unique: "behavCalBlks bl t0 t h1 = True \<Longrightarrow> 
distinct bl \<Longrightarrow> bl <~~> bl' \<Longrightarrow> besorted2 bl \<Longrightarrow> wf2 bl \<Longrightarrow> besorted2 bl' \<Longrightarrow>
behavCalBlks bl' t0 t h2 = True \<Longrightarrow> 
(\<forall> v \<in> Outputs bl. \<forall>t \<le> t0. h1 v t = h2 v t) \<Longrightarrow> 
\<forall>v \<in> Inputs bl - Outputs bl. \<forall>t' < t0 + t. h1 v t' = h2 v t' \<Longrightarrow>
\<forall>b \<in> set bl. (set (get_offsets b)) = {0} \<Longrightarrow>
\<forall> t'::real. (t' < t0 + t \<and> t' > t0) \<longrightarrow> (\<forall> v \<in> Outputs bl. h1 v t' = h2 v t')"
proof(induction bl arbitrary: bl')
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  note C1 = Cons
  have 1: "bl <~~> bl' \<Longrightarrow> Inputs bl = Inputs bl' \<and> Outputs bl = Outputs bl'"
  proof(induction bl arbitrary: bl')
    case Nil
    then show ?case by simp
  next
    case (Cons a bl)
    have tmp1: "Inputs bl = Inputs (remove1 a bl') \<and> Outputs bl = Outputs (remove1 a bl')"
      using perm_remove_perm Cons by (metis remove_hd)
    have tmp2: "a \<in> set bl'"
      using Cons(2) prem_seteq by (metis list.set_intros(1))
    have tmp3: "a \<in> set bl' \<Longrightarrow> Inputs bl' = Inputs (remove1 a bl') \<union> set (get_inputs a)"
    proof(induction bl')
      case Nil
      then show ?case by simp 
    next
      case (Cons b bl')
      then show ?case
      proof(cases "a = b")
        case True
        then show ?thesis by fastforce
      next
        case False
        have tmp1: "a \<in> set bl'"
          using Cons(2) False by simp
        then show ?thesis using Cons by auto
      qed
    qed
    have tmp4: "a \<in> set bl' \<Longrightarrow> Outputs bl' = Outputs (remove1 a bl') \<union> set (get_outputs a)"
    proof(induction bl')
      case Nil
      then show ?case by simp 
    next
      case (Cons b bl')
      then show ?case
      proof(cases "a = b")
        case True
        then show ?thesis by fastforce
      next
        case False
        have tmp1: "a \<in> set bl'"
          using Cons(2) False by simp
        then show ?thesis using Cons by auto
      qed
    qed
    then show ?case using tmp1 tmp2 tmp3 by (simp add: sup_commute)
  qed
  have 2: "\<forall>t'. t' < t0 + t \<and> t0 < t' \<longrightarrow> (\<forall>v\<in>set (get_outputs a). h1 v t' = h2 v t')"
  proof -
    have tmp1: "Available' (Block (get_inputs a) (get_outputs a) (get_offsets a) (get_sample_time a)
       (get_outupd a))"
      using Cons(6) unfolding wf2_def by (simp add: Available'_def)
    have tmp2: "set (get_offsets a) = {0}"
      using Cons(11) by auto
    have tmp3: "behavCalBlk (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a)
       t0 t h1  = True"
      using Cons(2) unfolding behavCalBlk.simps by simp
    have tmp4: "a \<in> set bl'"
        using Cons(4) by (simp add: prem_seteq)
    have tmp5: "behavCalBlk (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a)
       t0 t h2  = True"
      using Cons(8) tmp4 apply simp
    proof(induction bl')
      case Nil
      then show ?case by simp
    next
      case (Cons b bl')
      then show ?case
      proof(cases "a = b")
        case True
        then show ?thesis using Cons unfolding behavCalBlks.simps by simp
      next
        case False
        then show ?thesis using Cons unfolding behavCalBlks.simps by simp
      qed
    qed
    have tmp6: "\<forall>v\<in>set (get_inputs a). \<forall>t' < t0 + t. h1 v t' = h2 v t'"
    proof -
      have tmp1: "set (get_inputs a) \<inter> set (get_outputs a) = {}"
        using Cons(6,11) unfolding wf2_def Available'_def by (simp add: inf_sup_aci(1))
      have tmp2: "set (get_inputs a) \<inter> Outputs bl = {}"
        using Cons(5,6)
      proof(induction bl)
        case Nil
        then show ?case by simp
      next
        case (Cons b bl)
        have tmp1: "remove1 b (a # b # bl) = (a # bl)"
          using Cons(3) unfolding wf2_def Unique_def by simp
        have tmp2: "wf2 (b # bl)"
        proof -
          have tmp: "Unique (a#bl)"
            using Cons(3) unfolding wf2_def using Unique_remove by (metis remove1_idem tmp1)
          then show ?thesis using Cons(3) unfolding wf2_def Graph_def
            by (metis Unique_lemma list.set_intros(2))
        qed
        then show ?case using Cons(1,2) tmp1 besorted2_remove by (smt (verit, best) wf2_def 
              Cons.prems(2) Graph_Permutation Graph_lemma Outputs.simps(2) Un_iff Unique_remove 
              besorted2.simps(2) disjoint_iff_not_equal list.set_intros(1) list.set_intros(2) 
              notin_set_remove1 perm.swap)
      qed
      then show ?thesis using Cons(5,10) tmp1 unfolding besorted2.simps by auto
    qed
    show ?thesis using behavCalBlk_lemma1 tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 by simp
  qed
  have 3: "\<forall>t'. t' < t0 + t \<and> t0 < t' \<longrightarrow> (\<forall>v\<in>Outputs bl. h1 v t' = h2 v t')"
  proof -
    have tmp1: "behavCalBlks bl t0 t h1 = True"
      using Cons(2) unfolding behavCalBlks.simps by auto
    have tmp2: "distinct bl"
      using Cons(3) by auto
    have tmp3: "bl <~~> remove1 a bl'"
      using perm_remove_perm Cons(4) by (metis remove_hd)
    have tmp4: "besorted2 bl"
      using Cons(5) by auto
    have tmp5: "wf2 bl"
      using Cons(6) unfolding wf2_def Unique_def Graph_def
      by (simp add: nth_eq_iff_index_eq tmp2)
    have tmp6: "besorted2 (remove1 a bl')"
    proof -
      have tmp1: "distinct bl'"
        using Cons(3,4) distinct_perm by blast
      have tmp2: "a \<notin> set (remove1 a bl')"
        using tmp1 by simp
      have tmp3: "a \<in> set bl'"
        using Cons(4) by (simp add: prem_seteq)
      show ?thesis using Cons(4) Cons(7) besorted2_remove Unique'_def Unique_eq tmp1 by blast
    qed
    have tmp7: "behavCalBlks (remove1 a bl') t0 t h2 = True"
      using Cons(8) apply simp
    proof(induction bl')
      case Nil
      then show ?case by simp
    next
      case (Cons b bl')
      then show ?case
      proof(cases "a = b")
        case True
        then show ?thesis using Cons(2) by auto
      next
        case False
        then show ?thesis using Cons by auto
      qed
    qed
    have tmp8: "\<forall>v\<in>Outputs bl. \<forall>t \<le> t0. h1 v t = h2 v t"
      using Cons(9) by auto
    have tmp9: "\<forall>v\<in>Inputs bl - Outputs bl. \<forall>t' < t0 + t. h1 v t' = h2 v t'"
    proof -
      have tmp1: "\<forall>v\<in>Inputs bl - Outputs (a#bl). \<forall>t' < t0 + t. h1 v t' = h2 v t'"
        using Cons(10) by simp
      have tmp2: "\<forall>v\<in> set (get_outputs a). 
        (\<forall>t'. t' < t0 + t  \<longrightarrow> h1 v t' = h2 v t')"
        using Cons(9) 2 by (metis Outputs.simps(2) Un_iff linorder_not_less)
      show ?thesis using tmp1 tmp2 by auto
    qed
    have tmp10: "\<forall>b\<in>set bl. set (get_offsets b) = {0}"
      using Cons(11) by auto
    show ?thesis using Cons(1) tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 tmp7 tmp8 tmp9 tmp10 by blast
  qed
  then show ?case using 2 by auto
qed

lemma behavCalBlks_unique2: "behavCalBlks (rev bl) t0 t h1 = True \<Longrightarrow> 
distinct bl \<Longrightarrow> bl <~~> bl' \<Longrightarrow> besorted2 bl \<Longrightarrow> wf2 bl \<Longrightarrow> besorted2 bl' \<Longrightarrow>
behavCalBlks (rev bl') t0 t h2 = True \<Longrightarrow> 
(\<forall> v \<in> Outputs bl. \<forall>t \<le> t0. h1 v t = h2 v t) \<Longrightarrow> 
\<forall>v \<in> Inputs bl - Outputs bl. \<forall>t' < t0 + t. h1 v t' = h2 v t' \<Longrightarrow>
\<forall>b \<in> set bl. (set (get_offsets b)) = {0} \<Longrightarrow>
\<forall> t'::real. (t' < t0 + t \<and> t' > t0) \<longrightarrow> (\<forall> v \<in> Outputs bl. h1 v t' = h2 v t')"
  subgoal premises pre
    using behavCalBlks_unique[of bl t0 t h1 bl' h2] pre 
      behavCalBlks_rev by (metis (full_types) rev_rev_ident)
  done


lemma uniqueness_of_continuous_behav: "behavConDiag bl t0 t h1 h0 = True \<Longrightarrow> 
bl <~~> bl' \<Longrightarrow> besorted2 (getCalBlks bl) \<Longrightarrow> 
wf2 bl \<Longrightarrow> besorted2 (getCalBlks bl') \<Longrightarrow>
behavConDiag bl' t0 t h2 h0 = True \<Longrightarrow>  
\<forall>v \<in> Inputs bl - Outputs bl. \<forall>t' < t0 + t. h1 v t' = h2 v t' \<Longrightarrow>
ODE_cond (updateIntegBlks bl (findIntegBlks bl)) h0 t0 t = True \<Longrightarrow>
\<forall>v \<in> Outputs bl. \<forall>t' \<le> t0. h1 v t' = h2 v t' \<Longrightarrow>
\<forall> t'::real. (t' < t0 + t \<and> t' \<ge> t0) \<longrightarrow> (\<forall> v \<in> Outputs bl. h1 v t' = h2 v t')"
  subgoal premises pre
  proof -
    have 1: "\<forall>b \<in> set bl. set (get_offsets b) = {0} \<or> set (get_offsets b) = {1}"
      using pre(4) unfolding wf2_def Available'_def Graph_def
      by (metis less_nat_zero_code list.size(3) set_empty2)
    have 2: "Outputs bl = Outputs (getCalBlks bl) \<union> Outputs (findIntegBlks bl)"
    using 1 proof(induction bl)
      case Nil
      then show ?case by simp
    next
      case (Cons b bl)
      then show ?case unfolding getCalBlks.simps findIntegBlks.simps by (smt 
            (verit, best) One_nat_def Outputs.simps(2) Un_assoc Un_left_commute list.set_intros(1) 
            list.set_intros(2) old.nat.distinct(1) singleton_insert_inj_eq')
    qed
    have 3: "\<forall> t'::real. (t' \<le> t0 + t \<and> t' > t0) \<longrightarrow> 
      (\<forall> v \<in> Outputs (findIntegBlks bl). h1 v t' = h2 v t')"
    proof -
      have tmp1: "\<exists>L. unique_on_bounded_closed (t0) {t0--t0 + t}
           (state2vec (timedVar2State h0 (t0))) (block2ODE 
            (updateIntegBlks bl (findIntegBlks bl))) UNIV L"
        using pre(9) unfolding ODE_cond_def using ODE_cond_def pre(8) by presburger
      have tmp2: "wf2 (findIntegBlks bl)"
            using pre(4)
      proof(induction bl)
            case Nil
            then show ?case by simp
          next
            case (Cons a bl)
            then show ?case
            proof(cases "set (get_offsets a) = {0}")
              case True
              then show ?thesis unfolding getCalBlks.simps using Cons
                by (simp add: wf2_lemma)
            next
              case False
              have tmp1: "\<forall>j. j < (length bl) \<and> j \<ge> 0 \<longrightarrow> a \<noteq> (nth bl j) "
                using Cons(2) unfolding wf2_def Unique_def
                by (metis wf2_def Cons.prems Unique_k list.set_intros(1) remove_hd)
              have tmp2: "\<forall>j. j < (length (findIntegBlks bl)) \<and> j \<ge> 0 
                \<longrightarrow> a \<noteq> (nth (findIntegBlks bl) j)"
                using tmp1 findIntegBlksSubset3
                by (metis in_set_conv_nth less_eq_nat.simps(1) subset_code(1))
              have tmp3: "Unique (a # findIntegBlks bl)"
                using Cons Unique_add unfolding wf2_def tmp2 
                by (metis wf2_def wf2_lemma tmp2)
              have tmp4: "Graph (set (a # findIntegBlks bl))"
              proof -
                have tmp1: "set (a # findIntegBlks bl) \<subseteq> set (a#bl)"
                  using findIntegBlksSubset3 by auto
                show ?thesis using tmp1 Cons(2) unfolding wf2_def
                  by (meson Graph_def subsetD)
              qed
              have tmp5: "Ball (set (a # findIntegBlks bl)) Available' "
              proof -
                have tmp1: "set (a # findIntegBlks bl) \<subseteq> set (a#bl)"
                  using findIntegBlksSubset3 by auto
                show ?thesis using tmp1 Cons(2) unfolding wf2_def by blast
              qed
              show ?thesis using False unfolding 
                  findIntegBlks.simps wf2_def apply simp using tmp3 tmp4 tmp5
                by (metis wf2_def wf2_lemma list.set_intros(1) list.simps(15))
            qed
      qed
      have tmp3: "set (findIntegBlks bl) \<subseteq> set bl"
        using findIntegBlksSubset3 by simp
      have tmp4: "\<forall>c\<in>set (findIntegBlks bl). set (get_offsets c) = {1}"
      proof(induction bl)
        case Nil
        then show ?case by simp
      next
        case (Cons b bl)
        then show ?case unfolding findIntegBlks.simps by simp
      qed
      have tmp5: "\<forall>b\<in>set bl. set (get_offsets b) = {1} \<longrightarrow> 
      set (get_outputs b) \<subseteq> Outputs (findIntegBlks bl)"
        apply clarify subgoal for b x
        proof(induction bl)
          case Nil
          then show ?case by simp
        next
          case (Cons a bl)
          then show ?case
          proof(cases "b = a")
            case True
            then show ?thesis unfolding findIntegBlks.simps using Cons by simp
          next
            case False
            then show ?thesis unfolding findIntegBlks.simps using Cons by simp
          qed
        qed
        done
      have tmp6: "set (get_outputs (updateIntegBlks bl (findIntegBlks bl))) = 
        Outputs (findIntegBlks bl)"
        using updateIntegBlksSubset2 tmp2 pre(4) tmp3 tmp4 tmp5 by presburger
      have tmp7: "checkODE (updateIntegBlks bl (findIntegBlks bl)) h1 h0 t0 t = True"
        using pre(1) unfolding behavConDiag.simps by auto
      have tmp8: "checkODE (updateIntegBlks bl' (findIntegBlks bl')) h2 h0 t0 t = True"
        using pre(6) unfolding behavConDiag.simps by auto
      have tmp9: "(updateIntegBlks bl (findIntegBlks bl)) =
        (updateIntegBlks bl' (findIntegBlks bl'))"
        using updateIntegBlksPerm pre findIntegBlksPerm tmp2 by presburger
      show ?thesis using checkODE_lemma tmp1 tmp6 tmp7 tmp8 tmp9 by metis
    qed
    have 4: "\<forall> t'::real. (t' < t0 + t \<and> t' \<ge> t0) \<longrightarrow> 
      (\<forall> v \<in> Outputs (getCalBlks bl). h1 v t' = h2 v t')"
    proof -
      have tmp1: "behavCalBlks (getCalBlks bl) t0 t h1 = True"
        using pre(1) unfolding behavConDiag.simps by simp
      have tmp1': "distinct bl"
        using pre(4) unfolding wf2_def using Unique'_def Unique'_eq by blast
      have tmp2: "distinct (getCalBlks bl)"
        using tmp1'
      proof(induction bl)
        case Nil
        then show ?case by simp
      next
        case (Cons a bl)
        have tmp1: "distinct (getCalBlks bl)"
          using Cons by auto
        have tmp2: "a \<notin> set bl"
          using Cons(2) by simp
        then show ?case using tmp1 Cons(2) unfolding getCalBlks.simps
          using getCalBlksSubset2 by auto
      qed
      have tmp3: "(getCalBlks bl) <~~> (getCalBlks bl')"
        using pre(2) getCalBlksPerm by presburger
      have tmp4: "wf2 (getCalBlks bl)"
        using pre(4)
      proof(induction bl)
        case Nil
        then show ?case by simp
      next
        case (Cons a bl)
        then show ?case
        proof(cases "set (get_offsets a) = {1}")
          case True
          then show ?thesis unfolding getCalBlks.simps using Cons
            by (simp add: wf2_lemma)
        next
          case False
          have tmp1: "\<forall>j. j < (length bl) \<and> j \<ge> 0 \<longrightarrow> a \<noteq> (nth bl j) "
            using Cons(2) unfolding wf2_def Unique_def
            by (metis wf2_def Cons.prems Unique_k list.set_intros(1) remove_hd)
          have tmp2: "\<forall>j. j < (length (getCalBlks bl)) \<and> j \<ge> 0 
            \<longrightarrow> a \<noteq> (nth (getCalBlks bl) j)"
            using tmp1 getCalBlksSubset2 
            by (metis in_set_conv_nth less_eq_nat.simps(1) subset_code(1))
          have tmp3: "Unique (a # getCalBlks bl)"
            using Cons Unique_add unfolding wf2_def tmp2 
            by (metis wf2_def wf2_lemma tmp2)
          have tmp4: "Graph (set (a # getCalBlks bl))"
          proof -
            have tmp1: "set (a # getCalBlks bl) \<subseteq> set (a#bl)"
              using getCalBlksSubset2 by auto
            show ?thesis using tmp1 Cons(2) unfolding wf2_def
              by (meson Graph_def subsetD)
          qed
          have tmp5: "Ball (set (a # getCalBlks bl)) Available' "
          proof -
            have tmp1: "set (a # getCalBlks bl) \<subseteq> set (a#bl)"
              using getCalBlksSubset2 by auto
            show ?thesis using tmp1 Cons(2) unfolding wf2_def by blast
          qed
          show ?thesis using False unfolding 
              getCalBlks.simps wf2_def apply simp using tmp3 tmp4 tmp5
            by (metis wf2_def wf2_lemma list.set_intros(1) list.simps(15))
        qed
      qed
      have tmp5: "behavCalBlks (getCalBlks bl') t0 t h2 = True"
        using pre(6) unfolding behavConDiag.simps by auto
      have tmp6: "\<forall>v\<in>Outputs (getCalBlks bl). \<forall>t < t0. h1 v t = h2 v t"
        using pre(9) getCalBlksSubset by (simp add: "2")
      have tmp7: "\<forall>v\<in>Inputs (getCalBlks bl) - Outputs (getCalBlks bl). 
          \<forall>t'<t0 + t. h1 v t' = h2 v t'"
      proof -
        have tmp1: "\<forall>v\<in>Inputs (getCalBlks bl) - Outputs bl. \<forall>t' < t0+t. h1 v t' = h2 v t'"
          using 2 pre(7) getCalBlksSubset3 by blast
        have tmp2: "\<forall>t'. t' < t0 + t \<longrightarrow>
         (\<forall>v\<in>Outputs (findIntegBlks bl). h1 v t' = h2 v t')"
          using 3 pre(9) 2 findIntegBlksSubset by (meson in_mono linorder_not_le not_less_iff_gr_or_eq)
        show ?thesis using pre(8,9) 2 3 tmp1 tmp2 by blast
      qed
      have tmp8: "\<forall>b\<in>set (getCalBlks bl). set (get_offsets b) = {0}"
      proof(induction bl)
        case Nil
        then show ?case by simp
      next
        case (Cons a bl)
        then show ?case unfolding getCalBlks.simps by auto
      qed
      show ?thesis using behavCalBlks_unique pre(3,5) tmp1 tmp2 tmp3 tmp4 tmp5 tmp6
        tmp7 tmp8 by (smt (verit, ccfv_threshold) getCalBlksSubset in_mono pre(9))
    qed
    show ?thesis using 2 3 4 pre(9) by (metis Un_iff order_le_less)
  qed
  done

lemma uniqueness_of_continuous_behav2: "behavConDiag (rev bl) t0 t h1 h0 = True \<Longrightarrow> 
bl <~~> bl' \<Longrightarrow> besorted2 (getCalBlks bl) \<Longrightarrow> 
wf2 bl \<Longrightarrow> besorted2 (getCalBlks bl') \<Longrightarrow>
behavConDiag (rev bl') t0 t h2 h0 = True \<Longrightarrow>
\<forall>v \<in> Inputs bl - Outputs bl. \<forall>t' < t0 + t. h1 v t' = h2 v t' \<Longrightarrow>
ODE_cond (updateIntegBlks bl (findIntegBlks bl)) h0 t0 t = True \<Longrightarrow>
\<forall>v \<in> Outputs bl. \<forall>t' \<le> t0. h1 v t' = h2 v t' \<Longrightarrow>
\<forall> t'::real. (t' < t0 + t \<and> t' \<ge> t0) \<longrightarrow> (\<forall> v \<in> Outputs bl. h1 v t' = h2 v t')"
  subgoal premises pre
  proof -
    have 1: "wf2 bl'"
      using pre(2,4) wf2_rev wf2_lemma2 by blast
    have 2: "behavConDiag bl t0 t h1 h0 = True"
      using behavConDiag_rev pre(1,4) by (metis wf2_rev rev_rev_ident) 
    have 3: "behavConDiag bl' t0 t h2 h0 = True"
      using behavConDiag_rev pre(6) 1 by (metis wf2_rev rev_rev_ident)
    show ?thesis using 2 3 pre uniqueness_of_continuous_behav by presburger
  qed
  done

lemma uniqueness_of_continuous_diag' :
"bl <~~> bl' \<Longrightarrow> cl = (getCalBlks bl) \<Longrightarrow>
cl' = (getCalBlks bl') \<Longrightarrow> besorted2 cl \<Longrightarrow> wf2 bl \<Longrightarrow> besorted2 cl' \<Longrightarrow>
ODE_cond (updateIntegBlks bl (findIntegBlks bl)) h t0 t = True \<Longrightarrow>
\<forall>v \<in> Outputs bl. \<forall>tt. tt < t0 + t \<and> tt \<ge> t0 \<longrightarrow> 
(exeContinuousDiag_interval (rev bl) h t0 t) v tt = (exeContinuousDiag_interval (rev bl') h t0 t) v tt"
  subgoal premises pre
proof -
  have 1: "\<forall>bl. (getCalBlks (rev bl)) = rev (getCalBlks bl)"
    apply clarify subgoal for bl using getCalBlks_rev by simp
    done
  have 2: "(updateIntegBlks bl (findIntegBlks bl)) = (updateIntegBlks bl' (findIntegBlks bl'))"
  proof -
    have tmp: "wf2 (findIntegBlks bl)"
      using pre(5)
      proof(induction bl)
            case Nil
            then show ?case by simp
          next
            case (Cons a bl)
            then show ?case
            proof(cases "set (get_offsets a) = {0}")
              case True
              then show ?thesis unfolding getCalBlks.simps using Cons
                by (simp add: wf2_lemma)
            next
              case False
              have tmp1: "\<forall>j. j < (length bl) \<and> j \<ge> 0 \<longrightarrow> a \<noteq> (nth bl j) "
                using Cons(2) unfolding wf2_def Unique_def
                by (metis wf2_def Cons.prems Unique_k list.set_intros(1) remove_hd)
              have tmp2: "\<forall>j. j < (length (findIntegBlks bl)) \<and> j \<ge> 0 
                \<longrightarrow> a \<noteq> (nth (findIntegBlks bl) j)"
                using tmp1 findIntegBlksSubset3
                by (metis in_set_conv_nth less_eq_nat.simps(1) subset_code(1))
              have tmp3: "Unique (a # findIntegBlks bl)"
                using Cons Unique_add unfolding wf2_def tmp2 
                by (metis wf2_def wf2_lemma tmp2)
              have tmp4: "Graph (set (a # findIntegBlks bl))"
              proof -
                have tmp1: "set (a # findIntegBlks bl) \<subseteq> set (a#bl)"
                  using findIntegBlksSubset3 by auto
                show ?thesis using tmp1 Cons(2) unfolding wf2_def
                  by (meson Graph_def subsetD)
              qed
              have tmp5: "Ball (set (a # findIntegBlks bl)) Available' "
              proof -
                have tmp1: "set (a # findIntegBlks bl) \<subseteq> set (a#bl)"
                  using findIntegBlksSubset3 by auto
                show ?thesis using tmp1 Cons(2) unfolding wf2_def by blast
              qed
              show ?thesis using False unfolding 
                  findIntegBlks.simps wf2_def apply simp using tmp3 tmp4 tmp5
                by (metis wf2_def wf2_lemma list.set_intros(1) list.simps(15))
            qed
      qed
      then show ?thesis using updateIntegBlksPerm pre findIntegBlksPerm by presburger
    qed
  have 3: "behavConDiag (rev bl) t0 t (exeContinuousDiag_interval (rev bl) h t0 t) h"
    using existence_of_continuous_diag_base pre(1,3,4,5,7) 1 by (smt (verit, ccfv_SIG) wf2_lemma2
    findIntegBlkswf findIntegBlksPerm perm_rev pre(2) rev_rev_ident updateIntegBlksPerm)
  have 4: "behavConDiag bl t0 t (exeContinuousDiag_interval (rev bl) h t0 t) h"
    using 3 behavConDiag_rev pre(5) by (metis wf2_rev rev_rev_ident)
  have 5: "behavConDiag (rev bl') t0 t (exeContinuousDiag_interval (rev bl') h t0 t) h"
    using existence_of_continuous_diag_base pre(1,2,3,4,5,7) 1 2 by (smt (verit, ccfv_SIG) 
        wf2_lemma2 findIntegBlkswf findIntegBlksPerm perm_rev pre(6) rev_rev_ident 
        updateIntegBlksPerm)
  have 6: "behavConDiag bl' t0 t (exeContinuousDiag_interval (rev bl') h t0 t) h"
  proof -
    have tmp1: "wf2 (rev bl')"
      using pre(1,5) wf2_lemma2 wf2_rev by blast
    then show ?thesis using 5 behavConDiag_rev by (metis rev_rev_ident)
  qed
  have 7: "bl <~~> bl' \<Longrightarrow> Inputs bl = Inputs bl' \<and> Outputs bl = Outputs bl'"
  proof(induction bl arbitrary: bl')
    case Nil
    then show ?case by simp
  next
    case (Cons a bl)
    have tmp1: "Inputs bl = Inputs (remove1 a bl') \<and> Outputs bl = Outputs (remove1 a bl')"
      using perm_remove_perm Cons by (metis remove_hd)
    have tmp2: "a \<in> set bl'"
      using Cons(2) prem_seteq by (metis list.set_intros(1))
    have tmp3: "a \<in> set bl' \<Longrightarrow> Inputs bl' = Inputs (remove1 a bl') \<union> set (get_inputs a)"
    proof(induction bl')
      case Nil
      then show ?case by simp 
    next
      case (Cons b bl')
      then show ?case
      proof(cases "a = b")
        case True
        then show ?thesis by fastforce
      next
        case False
        have tmp1: "a \<in> set bl'"
          using Cons(2) False by simp
        then show ?thesis using Cons by auto
      qed
    qed
   have tmp4: "a \<in> set bl' \<Longrightarrow> Outputs bl' = Outputs (remove1 a bl') \<union> set (get_outputs a)"
    proof(induction bl')
      case Nil
      then show ?case by simp 
    next
      case (Cons b bl')
      then show ?case
      proof(cases "a = b")
        case True
        then show ?thesis by fastforce
      next
        case False
        have tmp1: "a \<in> set bl'"
          using Cons(2) False by simp
        then show ?thesis using Cons by auto
      qed
    qed
    then show ?case using tmp1 tmp2 tmp3 by (simp add: sup_commute)
  qed
  have 8: "\<forall>v t'. t' < t0 \<longrightarrow> (exeContinuousDiag_interval (rev bl) h t0 t) v t' = 
      (exeContinuousDiag_interval (rev bl') h t0 t) v t'"
    using exeContinuousDiag_interval_lemma2 by (simp add: exeCalBlks_lemma2)
  have 9: "\<forall>v\<in>Inputs bl - Outputs bl. \<forall>t. (exeContinuousDiag_interval (rev bl) h t0 t) v t 
      = (exeContinuousDiag_interval (rev bl') h t0 t) v t"
  proof -
    have tmp1: "wf2 (rev bl')"
      using pre(1,5) wf2_lemma2 wf2_rev by blast
    then show ?thesis using 7 pre(2,5) exeContinuousDiag_interval_lemma1 
      by (simp add: wf2_rev Outputs_rev pre(1))
  qed
  have 10: "\<forall>v\<in>Outputs bl. (exeContinuousDiag_interval (rev bl) h t0 t)
     v t0 = (exeContinuousDiag_interval (rev bl') h t0 t) v t0"
  proof -
    have tmp1: "wf2 (rev bl)"
      using pre(5) wf2_rev by blast
    have tmp2: "wf2 (rev bl')"
      using pre(1,5) wf2_lemma2 wf2_rev by blast
    then show ?thesis using exeContinuousDiag_interval_lemma3 tmp1
      "7" Outputs_rev pre(1) by presburger
  qed
  show ?thesis using uniqueness_of_continuous_behav[of bl t0 t "(exeContinuousDiag_interval 
      (rev bl) h t0 t)" h bl' "(exeContinuousDiag_interval (rev bl') h t0 t)"] 4 pre(1,2,3,4,5,6,7) 
        6 8 9 10 2 by (smt (z3) "7" DiffD2 Outputs_rev exeContinuousDiag_interval_lemma1 wf2_lemma2 wf2_rev)
qed
  done

lemma uniqueness_of_continuous_diag :
"bl <~~> bl' \<Longrightarrow> cl = (getCalBlks bl) \<Longrightarrow>
cl' = (getCalBlks bl') \<Longrightarrow> besorted2 cl \<Longrightarrow> wf2 bl \<Longrightarrow> besorted2 cl' \<Longrightarrow>
ODE_cond (updateIntegBlks bl (findIntegBlks bl)) h t0 t = True \<Longrightarrow>
\<forall>v tt. (exeContinuousDiag_interval (rev bl) h t0 t) v tt = 
(exeContinuousDiag_interval (rev bl') h t0 t) v tt"
  subgoal premises pre
  proof -
    have 1: "\<forall>v tt. v \<notin> (Outputs bl) \<longrightarrow> (exeContinuousDiag_interval (rev bl) h t0 t) v tt = 
      (exeContinuousDiag_interval (rev bl') h t0 t) v tt"
    proof -
      show ?thesis using exeContinuousDiag_interval_lemma1 pre(5) Outputs_perm Outputs_rev pre(1) 
          wf2_lemma2 wf2_rev by presburger
    qed
    have 2: "\<forall>v tt. tt \<le> t0 \<or> t0 + t < tt \<longrightarrow> (exeContinuousDiag_interval (rev bl) h t0 t) v tt = 
      (exeContinuousDiag_interval (rev bl') h t0 t) v tt"
    proof -
      show ?thesis using exeContinuousDiag_interval_lemma2 by presburger
    qed
    have 3: "\<forall>v \<in> Outputs bl. \<forall>tt. tt < t0 + t \<and> tt \<ge> t0 \<longrightarrow> (exeContinuousDiag_interval 
      (rev bl) h t0 t) v tt = (exeContinuousDiag_interval (rev bl') h t0 t) v tt"
      using uniqueness_of_continuous_diag' pre by presburger
    show ?thesis apply clarify subgoal for v tt
      proof(cases "v \<notin> (Outputs bl)")
        case True
        then show ?thesis using 1 by simp
      next
        case False
        note F1 = False
        then show ?thesis
        proof(cases "tt \<le> t0 \<or> t0 + t < tt")
          case True
          then show ?thesis using 2 by blast
        next
          case False
          then show ?thesis using F1 3 by (smt (z3) exeCalBlks_lemma2 exeContinuousDiag_interval.simps 
                findIntegBlksPerm findIntegBlkswf perm.trans perm_rev perm_sym pre(1) pre(5) 
                updateIntegBlksPerm)
        qed
      qed
      done
  qed
  done

fun behav_diag_interval :: "DisBlk list \<Rightarrow> ConBlk list \<Rightarrow> 
  timed_vars \<Rightarrow> timed_vars \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "behav_diag_interval bl cl h h0 t0 t = (behavConDiag cl t0 t h h0 \<and> behavDisDiag_attime 
(bl@(getCalBlks cl)) (nat (floor (t0+t))) h \<and> (\<forall>vv tt. tt > t0 \<and> 
tt < t0 + t \<and> vv \<in> Outputs bl \<longrightarrow> h vv tt = h vv t0))"

lemma behav_diag_interval_rev: "wf2 cl \<Longrightarrow> 
behav_diag_interval bl cl h h0 t0 t \<Longrightarrow> behav_diag_interval (rev bl) (rev cl) h h0 t0 t"
  subgoal premises pre
  proof -
    have 1: "behavConDiag (rev cl) t0 t h h0"
      using pre behavConDiag_rev unfolding behav_diag_interval.simps by presburger
    have 2: "(\<forall>vv tt. t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs (rev bl) \<longrightarrow> h vv tt = h vv t0)"
      using pre(2) Outputs_rev unfolding behav_diag_interval.simps by presburger
    have 3: "behavDisDiag_attime (rev bl@(getCalBlks (rev cl)))
     (nat \<lfloor>t0 + t\<rfloor>) h"
    proof -
      have tmp1: "getCalBlks (rev cl) = rev (getCalBlks cl)"
        using getCalBlks_rev by simp
      show ?thesis using behavDisDiag_attime_perm pre(2) tmp1 
        unfolding behav_diag_interval.simps
        by (metis behavDisDiag_attime_rev perm_append_swap rev_append)
    qed
  show ?thesis unfolding behav_diag_interval.simps using 1 2 3 by simp
qed
  done

(*DisBlk initialization; ConBlk; DisBlk*)
fun exe_diag_interval :: "DisBlk list \<Rightarrow> ConBlk list \<Rightarrow> 
  timed_vars \<Rightarrow> real \<Rightarrow> real \<Rightarrow> timed_vars" where
  "exe_diag_interval bl cl h t0 t =  (exeDisDiag_attime 
(rev (sortDiag (bl@((getCalBlks cl))))) (exeContinuousDiag_interval cl (exeDisDiag_interval bl h t0 t) 
  t0 t) (nat (floor (t0+t))))"

lemma exe_diag_interval_lemma1: "(nat (floor ((t0::real)+t))) > (t0::real) \<Longrightarrow> 
  \<forall>t' \<le> (t0::real) . \<forall>v. exe_diag_interval bl cl h (t0::real) t v t'= h v t'"
  unfolding exe_diag_interval.simps using exeDisDiag_attime_lemma2 
  exeContinuousDiag_interval_lemma2 by (simp add: exeCalBlks_lemma2)

lemma exe_diag_interval_lemma2: "(nat (floor (t0+t))) = t0 + t \<Longrightarrow> 
  \<forall>t' > t0 + t. \<forall>v. exe_diag_interval bl cl h t0 t v t'= h v t'"
  unfolding exe_diag_interval.simps using exeDisDiag_attime_lemma2 
  exeContinuousDiag_interval_lemma2 by simp

lemma exe_diag_interval_lemma3: "loop_free (bl @ getCalBlks cl) \<Longrightarrow> wf2 cl \<Longrightarrow>
  \<forall>t'. \<forall>v. v \<notin> Outputs bl \<union> Outputs cl \<longrightarrow> exe_diag_interval bl cl h t0 t v t'= h v t'"
  subgoal premises pre
  proof -
  have 1: "(rev (sortDiag (bl @ getCalBlks cl))) <~~> (bl @ getCalBlks cl)"
    using pre toposort_perm unfolding loop_free_def sortDiag_def
    by (metis append.right_neutral perm.trans perm_rev perm_sym)
  have 2: "Outputs (rev (sortDiag (bl @ getCalBlks cl))) \<subseteq> Outputs bl \<union> Outputs cl"
    using 1 Outputs_perm Outputs_Cons getCalBlksSubset by (metis Un_mono sup.idem sup_ge1)
  show ?thesis unfolding exeDisDiag_interval.simps exe_diag_interval.simps using exeDisDiag_attime_lemma
    exeContinuousDiag_interval_lemma1 pre(2) by (smt (verit) "2" UnI1 UnI2 subset_Un_eq)
qed
  done

fun behavContinuousDiag :: "block list \<Rightarrow> block list \<Rightarrow> real \<Rightarrow> real  \<Rightarrow> timed_vars \<Rightarrow> bool" where
  "behavContinuousDiag bl cl t0 t h = behavConDiag cl t0 t (exe_diag_interval bl cl h t0 t) h"

fun behavDisDiag_interval :: "block list \<Rightarrow> block list \<Rightarrow> real \<Rightarrow> real \<Rightarrow> behav" where
  "behavDisDiag_interval bl cl t0 t h = (\<forall>vv tt. tt > t0 \<and> tt < t0 + t \<and> vv \<in> Outputs bl \<longrightarrow> 
  (exe_diag_interval bl cl h t0 t) vv tt = h vv t0)"

lemma existence_of_diag_interval': 
"dl = (getCalBlks cl) \<Longrightarrow> el = (rev (sortDiag (bl@(getCalBlks cl)))) \<Longrightarrow>
besorted2 (rev dl)  \<Longrightarrow> wf2 cl \<Longrightarrow> t0 \<ge> 0 \<and> t > 0 \<Longrightarrow> 
loop_free (bl @ getCalBlks cl) \<Longrightarrow> wf1 el \<Longrightarrow> Outputs bl \<inter> Outputs cl = {} \<Longrightarrow>
\<forall>h. ODE_cond (updateIntegBlks cl (findIntegBlks cl)) h t0 t = True \<Longrightarrow>
(nat (floor (t0+t))) = (t0::real) + (t::real) \<Longrightarrow>

behavConDiag cl t0 t (exe_diag_interval bl cl h t0 t) h \<and> behavDisDiag_interval bl cl t0 t h \<and>
behavDisDiag_attime el (nat (floor (t0+t))) (exe_diag_interval bl cl h t0 t)"
  subgoal premises pre                             
  proof -
    have 0: "besorted (rev el)"
    proof -
      have tmp1: "(bl @ getCalBlks cl) <~~> (sortDiag (bl@(getCalBlks cl)))"
      proof -
        show ?thesis using pre(6) unfolding loop_free_def sortDiag_def using toposort_perm 
          by (metis self_append_conv)
      qed
      have tmp2: "Unique (bl @ getCalBlks cl)"
        using pre(2,7) Unique_perm Unique_rev tmp1 unfolding wf1_def wf0_def by (metis perm_sym rev_swap)
      have tmp3: "Graph (set (bl @ getCalBlks cl))"
        using pre(2,7) tmp1 unfolding wf1_def by (metis Graph_Permutation perm_sym set_rev)
      show ?thesis using pre(2) tmp2 tmp3 sort_is_sorted by simp
    qed
    have 1: "behavDisDiag_attime el (nat (floor (t0+t))) (exe_diag_interval bl cl h t0 t)"
    proof -
      have tmp1: "\<exists>k. t0 + t = Suc k"
        using pre(5) using gr0_implies_Suc pre(10)
        by (smt (verit, ccfv_threshold) of_nat_0_less_iff)
      have tmp2: "besorted (rev el)"
        using 0 by simp
      show ?thesis unfolding exe_diag_interval.simps using pre(7) tmp1 tmp2
          existence_discrete_diag_attime pre(10) unfolding wf1_def
        by (metis (no_types, lifting) of_nat_eq_iff pre(2))
    qed
    have 2: "(\<forall>vv tt. tt > t0 \<and> tt < t0 + t \<and> vv \<in> Outputs bl \<longrightarrow> 
    (exe_diag_interval bl cl h t0 t) vv tt = h vv t0)"
    proof -
      have tmp1: "\<forall>x. x \<in> Outputs bl \<longrightarrow> (\<forall>tt. 
                  (exeContinuousDiag_interval cl (\<lambda>vv tt.
                  if t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs bl then h vv (t0)
                  else h vv tt) t0 t) x tt = (\<lambda>vv tt.
                  if t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs bl then h vv (t0)
                  else h vv tt) x tt)"
        using exeContinuousDiag_interval_lemma1 pre(4,8) by blast
      then show ?thesis unfolding exe_diag_interval.simps using exeDisDiag_attime_lemma2
        by (simp add: pre(10))
    qed
    have 3: "behavConDiag cl t0 t (exe_diag_interval bl cl h t0 t) h"
    proof -
      have 1: "behavConDiag cl t0 t (exeContinuousDiag_interval cl
       (\<lambda>vv tt. if t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs bl then h vv (t0)
           else h vv tt) t0 t) h"
        using existence_of_continuous_diag_base pre(1,3,4,9) behavConDiag_eq2 by (smt (verit))
      have 2: "\<forall>x\<in>Inputs cl.
       \<forall>tt<t0 + t.
          exeContinuousDiag_interval cl
           (\<lambda>vv tt.
               if t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs bl then h vv (t0)
               else h vv tt)
           t0 t x tt =
          exeDisDiag_attime el
           (exeContinuousDiag_interval cl
             (\<lambda>vv tt.
                 if t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs bl then h vv (t0)
                 else h vv tt)
             t0 t)
           (nat (floor (t0+t))) x tt"
        using exeDisDiag_attime_lemma2 pre(10) by simp
      have 3: "set (bl @ getCalBlks cl) = set el"
      proof -
        have tmp1: "length (topological_sort (bl @ getCalBlks cl) (bl @ getCalBlks cl)
         []) = length ((bl @ getCalBlks cl))"
          using pre(6) unfolding loop_free_def sortDiag_def by simp
        have tmp2: "set (bl @ getCalBlks cl) = set (topological_sort (bl @ getCalBlks cl)
           (bl @ getCalBlks cl) [])"
          using sort_subset tmp1 by (metis append_self_conv)
        show ?thesis using tmp2 pre(2) by (simp add: sortDiag_def)
      qed
      have 4: "\<forall>x\<in>Outputs (findIntegBlks cl).
       \<forall>tt. exeContinuousDiag_interval cl
             (\<lambda>vv tt.
                 if t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs bl then h vv (t0)
                 else h vv tt)
             t0 t x tt =
            exeDisDiag_attime el
             (exeContinuousDiag_interval cl
               (\<lambda>vv tt.
                   if t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs bl then h vv (t0)
                   else h vv tt)
               t0 t)
             (nat (floor (t0+t))) x tt"
      proof -
        have tmp1: "Outputs (findIntegBlks cl) \<inter> Outputs (bl @ getCalBlks cl) = {}"
          using pre(4,8) IntegInterComputationalBlocks findIntegBlksSubset Outputs_Cons
          by blast
        have tmp2: "\<forall>x. x \<in> Outputs (findIntegBlks cl) \<longrightarrow> x \<notin> Outputs el"
          using 3 tmp1 Outputs_eq by blast
        show ?thesis using exeDisDiag_attime_lemma tmp1 tmp2 by simp
      qed
      have 5: "\<forall>x\<in>Outputs (getCalBlks cl).
       \<forall>tt < t0 + t. exeContinuousDiag_interval cl
             (\<lambda>vv tt.
                 if t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs bl then h vv (t0)
                 else h vv tt)
             t0 t x tt =
            exeDisDiag_attime el
             (exeContinuousDiag_interval cl
               (\<lambda>vv tt.
                   if t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs bl then h vv (t0)
                   else h vv tt)
               t0 t)
             (nat (floor (t0+t))) x tt"
        using exeDisDiag_attime_lemma2 by (simp add: pre(10))
      then show ?thesis unfolding exeDisDiag_interval.simps exe_diag_interval.simps using 1 2 4 pre(4) 
          behavConDiag_eq pre(2) by blast
    qed
    show ?thesis using 1 2 3 by fastforce
  qed
  done

lemma existence_of_diag_interval: 
"dl = (getCalBlks cl) \<Longrightarrow> el = (rev (sortDiag (bl@(getCalBlks cl)))) \<Longrightarrow>
sortDiag (rev dl) = rev dl  \<Longrightarrow> wf2 cl \<Longrightarrow> t0 \<ge> 0 \<and> t > 0 \<Longrightarrow> 
loop_free (bl @ getCalBlks cl) \<Longrightarrow> wf1 el \<Longrightarrow> Outputs bl \<inter> Outputs cl = {} \<Longrightarrow>
\<forall>h. ODE_cond (updateIntegBlks cl (findIntegBlks cl)) h t0 t = True \<Longrightarrow>
(nat (floor (t0+t))) = (t0::real) + (t::real) \<Longrightarrow>

behavConDiag cl t0 t (exe_diag_interval bl cl h t0 t) h \<and> behavDisDiag_interval bl cl t0 t h \<and>
behavDisDiag_attime el (nat (floor (t0+t))) (exe_diag_interval bl cl h t0 t)"
  subgoal premises pre
  proof -
    have 0: "besorted (rev el)"
    proof -
      have tmp1: "(bl @ getCalBlks cl) <~~> (sortDiag (bl@(getCalBlks cl)))"
      proof -
        show ?thesis using pre(6) unfolding loop_free_def sortDiag_def using toposort_perm 
          by (metis self_append_conv)
      qed
      have tmp2: "Unique (bl @ getCalBlks cl)"
        using pre(2,7) Unique_perm Unique_rev tmp1 unfolding wf1_def wf0_def by (metis perm_sym rev_swap)
      have tmp3: "Graph (set (bl @ getCalBlks cl))"
        using pre(2,7) tmp1 unfolding wf1_def by (metis Graph_Permutation perm_sym set_rev)
      show ?thesis using pre(2) tmp2 tmp3 sort_is_sorted by simp
    qed
    have 1: "behavDisDiag_attime el (nat (floor (t0+t))) (exe_diag_interval bl cl h t0 t)"
    proof -
      have tmp1: "\<exists>k. t0 + t = Suc k"
        using pre(5) using gr0_implies_Suc pre(10)
        by (smt (verit, ccfv_threshold) of_nat_0_less_iff)
      have tmp2: "besorted (rev el)"
        using 0 by simp
      show ?thesis unfolding exe_diag_interval.simps using pre(7) tmp1 tmp2
          existence_discrete_diag_attime pre(10) unfolding wf1_def
        by (metis (no_types, lifting) of_nat_eq_iff pre(2))
    qed
    have 2: "(\<forall>vv tt. tt > t0 \<and> tt < t0 + t \<and> vv \<in> Outputs bl \<longrightarrow> 
    (exe_diag_interval bl cl h t0 t) vv tt = h vv t0)"
    proof -
      have tmp1: "\<forall>x. x \<in> Outputs bl \<longrightarrow> (\<forall>tt. 
                  (exeContinuousDiag_interval cl (\<lambda>vv tt.
                  if t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs bl then h vv (t0)
                  else h vv tt) t0 t) x tt = (\<lambda>vv tt.
                  if t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs bl then h vv (t0)
                  else h vv tt) x tt)"
        using exeContinuousDiag_interval_lemma1 pre(4,8) by blast
      then show ?thesis unfolding exe_diag_interval.simps using exeDisDiag_attime_lemma2
        by (simp add: pre(10))
    qed
    have 3: "behavConDiag cl t0 t (exe_diag_interval bl cl h t0 t) h"
    proof -
      have 1: "behavConDiag cl t0 t (exeContinuousDiag_interval cl
       (\<lambda>vv tt. if t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs bl then h vv (t0)
           else h vv tt) t0 t) h"
        using existence_of_continuous_diag pre(1,3,4,9) behavConDiag_eq2 by (smt (verit))
      have 2: "\<forall>x\<in>Inputs cl.
       \<forall>tt<t0 + t.
          exeContinuousDiag_interval cl
           (\<lambda>vv tt.
               if t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs bl then h vv (t0)
               else h vv tt)
           t0 t x tt =
          exeDisDiag_attime el
           (exeContinuousDiag_interval cl
             (\<lambda>vv tt.
                 if t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs bl then h vv (t0)
                 else h vv tt)
             t0 t)
           (nat (floor (t0+t))) x tt"
        using exeDisDiag_attime_lemma2 pre(10) by simp
      have 3: "set (bl @ getCalBlks cl) = set el"
      proof -
        have tmp1: "length (topological_sort (bl @ getCalBlks cl) (bl @ getCalBlks cl)
         []) = length ((bl @ getCalBlks cl))"
          using pre(6) unfolding loop_free_def sortDiag_def by simp
        have tmp2: "set (bl @ getCalBlks cl) = set (topological_sort (bl @ getCalBlks cl)
           (bl @ getCalBlks cl) [])"
          using sort_subset tmp1 by (metis append_self_conv)
        show ?thesis using tmp2 pre(2) by (simp add: sortDiag_def)
      qed
      have 4: "\<forall>x\<in>Outputs (findIntegBlks cl).
       \<forall>tt. exeContinuousDiag_interval cl
             (\<lambda>vv tt.
                 if t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs bl then h vv (t0)
                 else h vv tt)
             t0 t x tt =
            exeDisDiag_attime el
             (exeContinuousDiag_interval cl
               (\<lambda>vv tt.
                   if t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs bl then h vv (t0)
                   else h vv tt)
               t0 t)
             (nat (floor (t0+t))) x tt"
      proof -
        have tmp1: "Outputs (findIntegBlks cl) \<inter> Outputs (bl @ getCalBlks cl) = {}"
          using pre(4,8) IntegInterComputationalBlocks findIntegBlksSubset Outputs_Cons
          by blast
        have tmp2: "\<forall>x. x \<in> Outputs (findIntegBlks cl) \<longrightarrow> x \<notin> Outputs el"
          using 3 tmp1 Outputs_eq by blast
        show ?thesis using exeDisDiag_attime_lemma tmp1 tmp2 by simp
      qed
      have 5: "\<forall>x\<in>Outputs (getCalBlks cl).
       \<forall>tt < t0 + t. exeContinuousDiag_interval cl
             (\<lambda>vv tt.
                 if t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs bl then h vv (t0)
                 else h vv tt)
             t0 t x tt =
            exeDisDiag_attime el
             (exeContinuousDiag_interval cl
               (\<lambda>vv tt.
                   if t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs bl then h vv (t0)
                   else h vv tt)
               t0 t)
             (nat (floor (t0+t))) x tt"
        using exeDisDiag_attime_lemma2 by (simp add: pre(10))
      then show ?thesis unfolding exeDisDiag_interval.simps exe_diag_interval.simps using 1 2 4 pre(4) 
          behavConDiag_eq pre(2) by blast
    qed
    show ?thesis using 1 2 3 by fastforce
  qed
  done

lemma uniqueness_of_diag_interval_behav: "behav_diag_interval bl cl h1 h0 t0 t = True \<Longrightarrow> 
cl <~~> cl' \<Longrightarrow> besorted2 (getCalBlks cl) \<Longrightarrow> 
wf2 cl \<Longrightarrow> besorted2 (getCalBlks cl') \<Longrightarrow>
behav_diag_interval bl' cl' h2 h0 t0 t = True \<Longrightarrow> 
(\<forall> v. \<forall>t'. t' < t0 \<or> t' > t0 + t \<longrightarrow> h1 v t' = h2 v t') \<Longrightarrow> 
\<forall>h. ODE_cond (updateIntegBlks cl (findIntegBlks cl)) h t0 t = True \<Longrightarrow>
\<forall>v \<in> Outputs cl. h1 v t0 = h2 v t0 \<Longrightarrow> Outputs bl \<inter> Outputs cl = {} \<Longrightarrow>
bl <~~> bl' \<Longrightarrow> wf1 (bl @ getCalBlks cl) \<Longrightarrow> (\<forall> v \<in> Outputs bl. h1 v t0 = h2 v t0) \<Longrightarrow> 
(nat (floor (t0+t))) = (t0::real) + (t::real) \<Longrightarrow> t0 \<ge> 0 \<and> t > 0 \<Longrightarrow>
loop_free ((rev bl) @ getCalBlks (rev cl)) \<Longrightarrow> 
loop_free ((rev bl') @ getCalBlks (rev cl'))
\<Longrightarrow> \<forall>v \<in> Inputs (bl@cl) - Outputs (bl@cl). \<forall>t::real. h1 v t = h2 v t \<Longrightarrow>

(\<forall> t'::real. (t' \<le> t0 + t \<and> t' \<ge> t0) \<longrightarrow> 
(\<forall> v \<in> Outputs cl. h1 v t' = h2 v t')) \<and> (\<forall> t'::real. (t' \<le> t0 + t \<and> t' \<ge> t0) \<longrightarrow> 
(\<forall> v \<in> Outputs bl. h1 v t' = h2 v t'))"
  subgoal premises pre
  proof - 
    have 0: "wf0 bl"
    proof -
      show ?thesis using pre(12) wf0_Cons unfolding wf1_def by auto
    qed
    have 1: "(rev (sortDiag ((rev bl)@(getCalBlks (rev cl))))) <~~> 
        (rev (sortDiag ((rev bl')@(getCalBlks (rev cl')))))"
    proof -
      have tmp1: "getCalBlks cl <~~> getCalBlks cl'"
        using pre(2) getCalBlksPerm by auto
      have tmp2: "bl@getCalBlks cl <~~> bl'@getCalBlks cl'"
        using pre(11) tmp1 by blast
      have tmp3: "((rev bl) @ getCalBlks (rev cl)) <~~>
        (sortDiag ((rev bl)@(getCalBlks (rev cl))))"
        using pre(16) unfolding loop_free_def sortDiag_def using toposort_perm 
        by (metis append.right_neutral)
      have tmp4: "((rev bl') @ getCalBlks (rev cl')) <~~>
        (sortDiag ((rev bl')@(getCalBlks (rev cl'))))"
        using pre(17) unfolding loop_free_def sortDiag_def using toposort_perm 
        by (metis append.right_neutral)
      show ?thesis using pre(11,12) tmp2 tmp3 tmp4 by (smt (verit, best) getCalBlksPerm 
            perm.trans perm_append1 perm_append2 perm_rev perm_sym pre(2))
    qed
    have 2: "Outputs cl = Outputs (getCalBlks cl) \<union> Outputs (findIntegBlks cl)"
    proof -
      have tmp: "\<forall>b \<in> set cl. set (get_offsets b) = {0} \<or> set (get_offsets b) = {1}"
      using pre(4) unfolding wf2_def Available'_def Graph_def
      by (metis less_nat_zero_code list.size(3) set_empty2)
      show ?thesis using tmp
      proof(induction cl)
        case Nil
        then show ?case by simp
      next
        case (Cons b cl)
        then show ?case unfolding getCalBlks.simps findIntegBlks.simps by (smt 
              (verit, best) One_nat_def Outputs.simps(2) Un_assoc Un_left_commute list.set_intros(1) 
              list.set_intros(2) old.nat.distinct(1) singleton_insert_inj_eq')
      qed
    qed
    have 3: "Inputs cl = Inputs (getCalBlks cl) \<union> Inputs (findIntegBlks cl)"
    proof -
      have tmp: "\<forall>b \<in> set cl. set (get_offsets b) = {0} \<or> set (get_offsets b) = {1}"
      using pre(4) unfolding wf2_def Available'_def Graph_def
      by (metis less_nat_zero_code list.size(3) set_empty2)
      show ?thesis using tmp
      proof(induction cl)
        case Nil
        then show ?case by simp
      next
        case (Cons b cl)
        then show ?case unfolding getCalBlks.simps findIntegBlks.simps by (smt 
              (verit, best) One_nat_def Inputs.simps(2) Un_assoc Un_left_commute list.set_intros(1) 
              list.set_intros(2) old.nat.distinct(1) singleton_insert_inj_eq')
      qed
    qed
    have 4: "besorted (sortDiag ((rev bl)@(getCalBlks (rev cl)))) \<and> 
        besorted (sortDiag ((rev bl')@(getCalBlks (rev cl'))))"
    proof -
      have tmp1: "((rev bl) @ getCalBlks (rev cl)) <~~>
        (sortDiag ((rev bl)@(getCalBlks (rev cl))))"
        using pre(16) unfolding loop_free_def sortDiag_def using toposort_perm 
        by (metis append.right_neutral)
      have tmp2: "Unique (bl @ getCalBlks cl)"
        using pre(11,12) tmp1 unfolding wf1_def wf0_def by (metis)
      have tmp3: "Graph (set (bl @ getCalBlks cl))"
        using pre(11,12) tmp1 unfolding wf1_def by blast
      have tmp4: "((rev bl') @ getCalBlks (rev cl')) <~~>
        (sortDiag ((rev bl')@(getCalBlks (rev cl'))))"
        using pre(17) unfolding loop_free_def sortDiag_def using toposort_perm 
        by (metis append.right_neutral)
      have tmp5: "Unique (bl' @ getCalBlks cl')"
        using pre(10,12) 1 Unique_perm unfolding wf1_def wf0_def 
        by (metis getCalBlksPerm perm_append1_eq perm_append2_eq pre(11) pre(2))
      have tmp6: "Graph (set (bl' @ getCalBlks cl'))"
        using pre(10,12) 1 tmp4 unfolding wf1_def by (metis Graph_Permutation getCalBlks_rev 
            perm_sym set_append set_rev tmp1)
      show ?thesis using pre(11,12) tmp2 tmp3 tmp5 tmp6 sort_is_sorted by (metis Graph_Permutation 
      Unique_Permutation Unique_rev getCalBlks_rev perm_append_swap rev_append set_rev)
    qed
    have 5: "bl <~~> bl' \<Longrightarrow> Inputs bl = Inputs bl' \<and> Outputs bl = Outputs bl'"
    proof(induction bl arbitrary: bl')
      case Nil
      then show ?case by simp
    next
      case (Cons a bl)
      have tmp1: "Inputs bl = Inputs (remove1 a bl') \<and> Outputs bl = Outputs (remove1 a bl')"
        using perm_remove_perm Cons by (metis remove_hd)
      have tmp2: "a \<in> set bl'"
        using Cons(2) prem_seteq by (metis list.set_intros(1))
      have tmp3: "a \<in> set bl' \<Longrightarrow> Inputs bl' = Inputs (remove1 a bl') \<union> set (get_inputs a)"
      proof(induction bl')
        case Nil
        then show ?case by simp 
      next
        case (Cons b bl')
        then show ?case
        proof(cases "a = b")
          case True
          then show ?thesis by fastforce
        next
          case False
          have tmp1: "a \<in> set bl'"
            using Cons(2) False by simp
          then show ?thesis using Cons by auto
        qed
      qed
      have tmp4: "a \<in> set bl' \<Longrightarrow> Outputs bl' = Outputs (remove1 a bl') \<union> set (get_outputs a)"
      proof(induction bl')
        case Nil
        then show ?case by simp 
      next
        case (Cons b bl')
        then show ?case
        proof(cases "a = b")
          case True
          then show ?thesis by fastforce
        next
          case False
          have tmp1: "a \<in> set bl'"
            using Cons(2) False by simp
          then show ?thesis using Cons by auto
        qed
      qed
      then show ?case using tmp1 tmp2 tmp3 by (simp add: sup_commute)
    qed
    have 6: "\<forall>v \<in> Outputs bl. (\<forall>t'. (t' < t0 + t \<and> t' > t0) \<longrightarrow> h1 v t' = h2 v t')"
    proof -
      have tmp1: "\<forall>v \<in> Outputs bl. (\<forall>t'. (t' < t0 + t \<and> t' > t0) 
      \<longrightarrow> h1 v t' = h1 v (t0))"
        using pre(1) unfolding behav_diag_interval.simps by auto
      have tmp2: "\<forall>v \<in> Outputs bl'. (\<forall>t'. (t' < t0 + t \<and> t' > t0) 
      \<longrightarrow> h2 v t' = h2 v (t0))"
        using pre(6) unfolding behav_diag_interval.simps by auto
      have tmp3: "Outputs bl = Outputs bl'"
        using 5 pre(11) by simp
      show ?thesis using tmp1 tmp2 tmp3 using pre(13) by simp
    qed
    have 7: "\<forall> t'::real. (t' \<le> t0 + t \<and> t' > t0) \<longrightarrow> 
      (\<forall> v \<in> Outputs (findIntegBlks cl). h1 v t' = h2 v t')"
    proof -
      have tmp1: "\<forall>h. \<exists>L. unique_on_bounded_closed (t0) {t0--t0 + t}
           (state2vec (timedVar2State h (t0))) (block2ODE 
            (updateIntegBlks cl (findIntegBlks cl))) UNIV L"
        using pre(8) unfolding ODE_cond_def by blast
      have tmp2: "wf2 (findIntegBlks cl)"
            using pre(4)
      proof(induction cl)
            case Nil
            then show ?case by simp
          next
            case (Cons a cl)
            then show ?case
            proof(cases "set (get_offsets a) = {0}")
              case True
              then show ?thesis unfolding getCalBlks.simps using Cons
                by (simp add: wf2_lemma)
            next
              case False
              have tmp1: "\<forall>j. j < (length cl) \<and> j \<ge> 0 \<longrightarrow> a \<noteq> (nth cl j) "
                using Cons(2) unfolding wf2_def Unique_def
                by (metis wf2_def Cons.prems Unique_k list.set_intros(1) remove_hd)
              have tmp2: "\<forall>j. j < (length (findIntegBlks cl)) \<and> j \<ge> 0 
                \<longrightarrow> a \<noteq> (nth (findIntegBlks cl) j)"
                using tmp1 findIntegBlksSubset3
                by (metis in_set_conv_nth less_eq_nat.simps(1) subset_code(1))
              have tmp3: "Unique (a # findIntegBlks cl)"
                using Cons Unique_add unfolding wf2_def tmp2 
                by (metis wf2_def wf2_lemma tmp2)
              have tmp4: "Graph (set (a # findIntegBlks cl))"
              proof -
                have tmp1: "set (a # findIntegBlks cl) \<subseteq> set (a#cl)"
                  using findIntegBlksSubset3 by auto
                show ?thesis using tmp1 Cons(2) unfolding wf2_def
                  by (meson Graph_def subsetD)
              qed
              have tmp5: "Ball (set (a # findIntegBlks cl)) Available' "
              proof -
                have tmp1: "set (a # findIntegBlks cl) \<subseteq> set (a#cl)"
                  using findIntegBlksSubset3 by auto
                show ?thesis using tmp1 Cons(2) unfolding wf2_def by blast
              qed
              show ?thesis using False unfolding 
                  findIntegBlks.simps wf2_def apply simp using tmp3 tmp4 tmp5
                by (metis wf2_def wf2_lemma list.set_intros(1) list.simps(15))
            qed
      qed
      have tmp3: "set (findIntegBlks cl) \<subseteq> set cl"
        using findIntegBlksSubset3 by simp
      have tmp4: "\<forall>c\<in>set (findIntegBlks cl). set (get_offsets c) = {1}"
      proof(induction cl)
        case Nil
        then show ?case by simp
      next
        case (Cons b cl)
        then show ?case unfolding findIntegBlks.simps by simp
      qed
      have tmp5: "\<forall>b\<in>set cl. set (get_offsets b) = {1} \<longrightarrow> 
      set (get_outputs b) \<subseteq> Outputs (findIntegBlks cl)"
        apply clarify subgoal for b x
        proof(induction cl)
          case Nil
          then show ?case by simp
        next
          case (Cons a cl)
          then show ?case
          proof(cases "b = a")
            case True
            then show ?thesis unfolding findIntegBlks.simps using Cons by simp
          next
            case False
            then show ?thesis unfolding findIntegBlks.simps using Cons by simp
          qed
        qed
        done
      have tmp6: "set (get_outputs (updateIntegBlks cl (findIntegBlks cl))) = 
        Outputs (findIntegBlks cl)"
        using updateIntegBlksSubset2 tmp2 pre(4) tmp3 tmp4 tmp5 by presburger
      have tmp7: "checkODE (updateIntegBlks cl (findIntegBlks cl)) h1 h0 t0 t = True"
        using pre(1) unfolding behavConDiag.simps by auto
      have tmp8: "checkODE (updateIntegBlks cl' (findIntegBlks cl')) h2 h0 t0 t = True"
        using pre(6) unfolding behavConDiag.simps by auto
      have tmp9: "(updateIntegBlks cl (findIntegBlks cl)) =
        (updateIntegBlks cl' (findIntegBlks cl'))"
        using updateIntegBlksPerm pre findIntegBlksPerm tmp2 by presburger
      show ?thesis using checkODE_lemma tmp1 tmp6 tmp7 tmp8 tmp9 by metis
    qed
    have 8: "\<forall> t'::real. (t' \<le> t0 + t \<and> t' \<ge> t0) \<longrightarrow> 
      (\<forall> v \<in> Outputs (findIntegBlks cl). h1 v t' = h2 v t')"
      using 7 pre(9) 2 order_less_le by blast
    have 9: "(\<forall> t'::real. (t' < t0 + t \<and> t' \<ge> t0) \<longrightarrow> 
      (\<forall> v \<in> Outputs (getCalBlks cl). h1 v t' = h2 v t'))"
    proof -
      have tmp1: "behavCalBlks (getCalBlks cl) t0 t h1 = True"
        using pre(1) unfolding behav_diag_interval.simps behavConDiag.simps by auto
      have tmp2: "distinct (getCalBlks cl)"
        using getCalBlks_distinct pre(4) unfolding wf2_def using Unique'_eq 
        Unique'_def by blast
      have tmp3: "behavCalBlks (getCalBlks cl') t0 t h2 = True"
        using pre(6) unfolding behav_diag_interval.simps behavConDiag.simps by auto
      have tmp4: "\<forall>v\<in>Outputs (getCalBlks cl). \<forall>t<t0. h1 v t = h2 v t"
        using pre(7) by simp
      have tmp5: "\<forall>v\<in>Inputs (getCalBlks cl) - Outputs (getCalBlks cl). 
        \<forall>t'< t0 + t. h1 v t' = h2 v t'"
      proof -
        have tmp1: "\<forall>v\<in>Inputs (getCalBlks cl) - Outputs (bl@cl). 
        \<forall>t'< t0 + t. h1 v t' = h2 v t'"
          using pre(18) 3 Inputs_Cons by blast
        have tmp2: "\<forall>v \<in> Outputs bl. \<forall>t'< t0 + t. h1 v t' = h2 v t'"
          using 6 pre(7,13) not_less_iff_gr_or_eq by blast
        have tmp3: "\<forall>v \<in> Outputs (findIntegBlks cl). \<forall>t'< t0 + t. h1 v t' = h2 v t'"
          using 7 pre(7,9) 2 by (meson "8" linorder_not_less)
        show ?thesis using tmp1 2 Outputs_Cons tmp2 tmp3 by blast
      qed
      have tmp6: "\<forall>b\<in>set (getCalBlks cl). set (get_offsets b) = {0}"
        apply clarify subgoal for b
        proof(induction cl)
          case Nil
          then show ?case by simp
        next
          case (Cons a cl)
          then show ?case
          proof(cases "set (get_offsets a) = {0}")
            case True
            then show ?thesis using Cons unfolding getCalBlks.simps by auto
          next
            case False
            then show ?thesis using Cons unfolding getCalBlks.simps by auto
          qed
        qed
        done
      have tmp7: "wf2 (getCalBlks cl)"
        using pre(4)
      proof(induction cl)
        case Nil
        then show ?case by simp
      next
        case (Cons a bl)
        then show ?case
        proof(cases "set (get_offsets a) = {1}")
          case True
          then show ?thesis unfolding getCalBlks.simps using Cons
            by (simp add: wf2_lemma)
        next
          case False
          have tmp1: "\<forall>j. j < (length bl) \<and> j \<ge> 0 \<longrightarrow> a \<noteq> (nth bl j) "
            using Cons(2) unfolding wf2_def Unique_def
            by (metis wf2_def Cons.prems Unique_k list.set_intros(1) remove_hd)
          have tmp2: "\<forall>j. j < (length (getCalBlks bl)) \<and> j \<ge> 0 
            \<longrightarrow> a \<noteq> (nth (getCalBlks bl) j)"
            using tmp1 getCalBlksSubset2 
            by (metis in_set_conv_nth less_eq_nat.simps(1) subset_code(1))
          have tmp3: "Unique (a # getCalBlks bl)"
            using Cons Unique_add unfolding wf2_def tmp2 
            by (metis wf2_def wf2_lemma tmp2)
          have tmp4: "Graph (set (a # getCalBlks bl))"
          proof -
            have tmp1: "set (a # getCalBlks bl) \<subseteq> set (a#bl)"
              using getCalBlksSubset2 by auto
            show ?thesis using tmp1 Cons(2) unfolding wf2_def
              by (meson Graph_def subsetD)
          qed
          have tmp5: "Ball (set (a # getCalBlks bl)) Available' "
          proof -
            have tmp1: "set (a # getCalBlks bl) \<subseteq> set (a#bl)"
              using getCalBlksSubset2 by auto
            show ?thesis using tmp1 Cons(2) unfolding wf2_def by blast
          qed
          show ?thesis using False unfolding 
              getCalBlks.simps wf2_def apply simp using tmp3 tmp4 tmp5
            by (metis wf2_def wf2_lemma list.set_intros(1) list.simps(15))
        qed
      qed
        show ?thesis using pre(2,3,5) tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 tmp7
          using behavCalBlks_unique by (smt (verit, ccfv_threshold) getCalBlksPerm 
              getCalBlksSubset in_mono pre(9))
       qed
    have 12: "\<forall>v\<in>Outputs (bl @ getCalBlks cl). h1 v (t0 + t) = h2 v (t0 + t)"
    proof(cases "sortDiag ((rev bl)@(getCalBlks (rev cl))) = []")
      case True
      have tmp1: "((rev bl) @ getCalBlks (rev cl)) <~~>
        (sortDiag ((rev bl)@(getCalBlks (rev cl))))"
        using pre(16) unfolding loop_free_def sortDiag_def using toposort_perm 
        by (metis append.right_neutral)
      then show ?thesis using Outputs_perm True by (simp add: getCalBlks_rev)
    next
      case False
      have tmp1: "((rev bl) @ getCalBlks (rev cl)) <~~>
        (sortDiag ((rev bl)@(getCalBlks (rev cl))))"
        using pre(16) unfolding loop_free_def sortDiag_def using toposort_perm 
        by (metis append.right_neutral)
      have tmp2: "((rev bl') @ getCalBlks (rev cl')) <~~>
        (sortDiag ((rev bl')@(getCalBlks (rev cl'))))"
        using pre(17) unfolding loop_free_def sortDiag_def using toposort_perm 
        by (metis append.right_neutral)
      have tmp3: "wf0 (sortDiag (rev bl @ getCalBlks (rev cl)))"
        using pre(12) tmp1 wf0_Permutation unfolding wf1_def by (metis getCalBlks_rev perm_append_swap 
            perm_rev rev_append rev_rev_ident)
      have tmp4: "behavDisDiag_attime (sortDiag (rev bl @ getCalBlks (rev cl))) 
          (nat (floor (t0+t))) h1 = True"
      proof -
        show ?thesis using pre(1) unfolding behav_diag_interval.simps 
          using behavDisDiag_attime_perm tmp1 
          by (metis getCalBlks_rev perm_append_swap perm_rev perm_sym rev_append)
      qed
      have tmp5: "behavDisDiag_attime (sortDiag (rev bl' @ getCalBlks (rev cl'))) 
        (nat \<lfloor>t0 + t\<rfloor>) h2 = True"
        using tmp2 pre(6) unfolding behav_diag_interval.simps 
        using behavDisDiag_attime_perm tmp2 by (meson wf2_lemma2 behav_diag_interval.elims(2) 
            behav_diag_interval_rev pre(2) pre(4) pre(6))
      have tmp6: "\<forall>v\<in>Outputs (sortDiag (rev bl @ getCalBlks (rev cl))). h1 v 0 = h2 v 0"
        using pre tmp1 Outputs_perm by (smt (verit, del_insts) "9" Outputs_Cons Outputs_rev Un_iff 
            getCalBlks_rev)
      have tmp7: "\<forall>v\<in>Inputs (sortDiag (rev bl @ getCalBlks (rev cl))) -
      Outputs (sortDiag (rev bl @ getCalBlks (rev cl))).
        \<forall>ta\<le>real (nat \<lfloor>t0 + t\<rfloor>). h1 v ta = h2 v ta"
        using pre tmp1 2 3 Outputs_perm by (smt (z3) "8" DiffD1 DiffD2 DiffI Inputs_Cons Inputs_eq 
            Inputs_rev Outputs_Cons Outputs_rev UnE UnI1 UnI2 append.right_neutral 
            getCalBlks_rev loop_free_def sortDiag_def sort_subset)
      have tmp8: "\<forall>ta<real (nat \<lfloor>t0 + t\<rfloor>).
        \<forall>v\<in>Outputs (sortDiag (rev bl @ getCalBlks (rev cl))). h1 v ta = h2 v ta"
        using pre tmp1 Outputs_perm 6 8 9 by (metis Outputs_Cons Outputs_rev Un_iff 
            getCalBlks_rev linorder_neqE_linordered_idom linorder_not_le)
      have tmp9: "\<forall>v\<in>Outputs (sortDiag (rev bl @ getCalBlks (rev cl))).
       h1 v (real (nat \<lfloor>t0 + t\<rfloor>)) = h2 v (real (nat \<lfloor>t0 + t\<rfloor>))"
        using blocklist_hebav_attime_lemma2[of "sortDiag (rev bl @ getCalBlks (rev cl))" 
            "nat (floor (t0+t))" h1 "sortDiag (rev bl' @ getCalBlks (rev cl'))" h2] False
        tmp3 tmp4 tmp5 tmp6 tmp7 tmp8 4 1 by (smt (verit, ccfv_SIG) perm.trans perm_rev perm_sym)
      show ?thesis using tmp9 tmp1 Outputs_perm by (metis Outputs_Cons Outputs_rev 
            getCalBlks_rev pre(14))
    qed
    have 13: "(\<forall>t'. t' \<le> t0 + t \<and> t0 \<le> t' \<longrightarrow> (\<forall>v\<in>Outputs bl. h1 v t' = h2 v t'))"
      using 6 12 pre(13) Outputs_Cons less_eq_real_def by auto
    have 14: "(\<forall>t'. t' \<le> t0 + t \<and> t0 \<le> t' \<longrightarrow> (\<forall>v\<in>Outputs cl. h1 v t' = h2 v t'))"
      using 2 7 9 12 pre(9) by (smt (verit, ccfv_threshold) Outputs_Cons Un_iff)
    show ?thesis using 13 14 by simp
  qed
  done

lemma uniqueness_of_diag_interval:
"cl <~~> cl' \<Longrightarrow> dl = getCalBlks cl \<Longrightarrow> dl' = (getCalBlks cl') 
\<Longrightarrow> besorted2 (rev dl) \<Longrightarrow> wf2 cl \<Longrightarrow> besorted2 (rev dl') \<Longrightarrow>
el = rev (sortDiag (bl @ getCalBlks cl)) \<Longrightarrow> 
el' = rev (sortDiag (bl' @ getCalBlks cl')) \<Longrightarrow> 
loop_free (bl @ getCalBlks cl) \<Longrightarrow> loop_free (bl' @ getCalBlks cl') \<Longrightarrow>
bl <~~> bl' \<Longrightarrow> wf1 el \<Longrightarrow> 
\<forall>h. ODE_cond (updateIntegBlks cl (findIntegBlks cl)) h t0 t = True \<Longrightarrow>
0 \<le> t0 \<and> 0 < t \<Longrightarrow> Outputs bl \<inter> Outputs cl = {} \<Longrightarrow> real (nat \<lfloor>t0 + t\<rfloor>) = t0 + t \<Longrightarrow>

(\<forall>vv t'::real. (t' \<le> t0 + t \<and> t' \<ge> t0) \<and> vv \<in> Outputs bl \<union> Outputs cl
\<longrightarrow> (exe_diag_interval bl cl h t0 t) vv t' =
(exe_diag_interval bl' cl' h t0 t) vv t')"
  subgoal premises pre
  proof -
    have 0: "el <~~> (bl @ getCalBlks cl)"
      using pre(7,9) toposort_perm unfolding loop_free_def sortDiag_def
      by (metis append.right_neutral perm.trans perm_rev perm_sym)
    have 1: "el' <~~> (bl' @ getCalBlks cl')"
      using pre(8,10) toposort_perm unfolding loop_free_def sortDiag_def
      by (metis append.right_neutral perm.trans perm_rev perm_sym)
    have 2: "wf0 bl"
    proof -
      have tmp1: "wf0 (rev el)"
        using pre(12) wf0_Permutation unfolding wf1_def by (metis perm_rev rev_swap)
      have tmp2: "(bl @ getCalBlks cl) <~~> (sortDiag (bl@((getCalBlks cl))))"
        using pre(9) unfolding loop_free_def sortDiag_def using toposort_perm 
        by (metis append.right_neutral)
      have tmp3: "wf0 (bl @ getCalBlks cl)"
        using tmp1 tmp2 pre(7) wf0_Permutation by (metis perm_sym rev_swap)
      show ?thesis using tmp3 wf0_Cons by auto
    qed
    have 3: "el <~~> el'"
    proof -
      have tmp1: "getCalBlks cl <~~> getCalBlks cl'"
        using pre(1) getCalBlksPerm by auto
      have tmp2: "bl@getCalBlks cl <~~> bl'@getCalBlks cl'"
        using pre(11) tmp1 by blast
      have tmp3: "(bl @ getCalBlks cl) <~~> (sortDiag (bl@((getCalBlks cl))))"
        using pre(9) unfolding loop_free_def sortDiag_def using toposort_perm 
        by (metis append.right_neutral)
      have tmp4: "(bl' @ getCalBlks cl') <~~> 
        (sortDiag (bl'@((getCalBlks cl'))))"
        using pre(10) unfolding loop_free_def sortDiag_def using toposort_perm 
        by (metis append.right_neutral)
      show ?thesis using pre(7,8) tmp2 tmp3 tmp4
        by (meson perm.trans perm_rev perm_sym)
    qed
    have 4: "Outputs cl = Outputs (getCalBlks cl) \<union> Outputs (findIntegBlks cl)"
    proof -
      have tmp: "\<forall>b \<in> set cl. set (get_offsets b) = {0} \<or> set (get_offsets b) = {1}"
      using pre(5) unfolding wf2_def Available'_def Graph_def
      by (metis less_nat_zero_code list.size(3) set_empty2)
      show ?thesis using tmp
      proof(induction cl)
        case Nil
        then show ?case by simp
      next
        case (Cons b cl)
        then show ?case unfolding getCalBlks.simps findIntegBlks.simps by (smt 
              (verit, best) One_nat_def Outputs.simps(2) Un_assoc Un_left_commute list.set_intros(1) 
              list.set_intros(2) old.nat.distinct(1) singleton_insert_inj_eq')
      qed
    qed
    have 5: "Inputs cl = Inputs (getCalBlks cl) \<union> Inputs (findIntegBlks cl)"
    proof -
      have tmp: "\<forall>b \<in> set cl. set (get_offsets b) = {0} \<or> set (get_offsets b) = {1}"
      using pre(5) unfolding wf2_def Available'_def Graph_def
      by (metis less_nat_zero_code list.size(3) set_empty2)
      show ?thesis using tmp
      proof(induction cl)
        case Nil
        then show ?case by simp
      next
        case (Cons b cl)
        then show ?case unfolding getCalBlks.simps findIntegBlks.simps by (smt 
              (verit, best) One_nat_def Inputs.simps(2) Un_assoc Un_left_commute list.set_intros(1) 
              list.set_intros(2) old.nat.distinct(1) singleton_insert_inj_eq')
      qed
    qed
    have 6: "besorted (rev el) \<and> besorted (rev el')"
    proof -
      have tmp1: "(bl @ getCalBlks cl) <~~> (sortDiag (bl@(getCalBlks cl)))"
      proof -
        show ?thesis using pre(9) unfolding loop_free_def sortDiag_def using toposort_perm 
          by (metis self_append_conv)
      qed
      have tmp2: "Unique (bl @ getCalBlks cl)"
        using pre(7,12) Unique_perm Unique_rev tmp1 unfolding wf1_def wf0_def by (metis perm_sym rev_swap)
      have tmp3: "Graph (set (bl @ getCalBlks cl))"
        using pre(7,12) tmp1 unfolding wf1_def by (metis Graph_Permutation perm_sym set_rev)
      have tmp4: "(bl' @ getCalBlks cl') <~~> 
          (sortDiag (bl'@(getCalBlks cl')))"
      proof -
        show ?thesis using pre(10) unfolding loop_free_def sortDiag_def using toposort_perm 
          by (metis self_append_conv)
      qed
      have tmp5: "Unique (bl' @ getCalBlks cl')"
        using pre(8,12) 3 Unique_perm unfolding wf1_def wf0_def
        by (metis perm_rev perm_sym tmp4)
      have tmp6: "Graph (set (bl' @ getCalBlks cl'))"
        using pre(8,12) 3 tmp4 unfolding wf1_def by (metis Graph_Permutation perm_sym set_rev)
      show ?thesis using pre(7,8) tmp2 tmp3 tmp5 tmp6 sort_is_sorted by simp
    qed
    have 7: "behav_diag_interval bl cl (exe_diag_interval bl cl h t0 t) h t0 t = True"
    proof -
      have tmp1: "behavConDiag cl t0 t (exe_diag_interval bl cl h t0 t) h \<and>
    behavDisDiag_interval bl cl t0 t h \<and>
    behavDisDiag_attime el (nat \<lfloor>t0 + t\<rfloor>) (exe_diag_interval bl cl h t0 t)"
        using existence_of_diag_interval'[of dl cl el bl t0 t h] pre
        by fastforce
    have tmp2: "behavDisDiag_attime (bl @ getCalBlks cl) (nat \<lfloor>t0 + t\<rfloor>)
      (exe_diag_interval bl cl h t0 t)"
      using tmp1 pre(7) 0 behavDisDiag_attime_perm by blast
    show ?thesis unfolding behav_diag_interval.simps using tmp1 tmp2 pre(7) 
          unfolding behavDisDiag_interval.simps using exe_diag_interval_lemma1 pre(16) by auto
    qed
    have 8: "behav_diag_interval (rev bl) (rev cl) (exe_diag_interval bl cl h t0 t) h t0 t = True"
      using 7 behav_diag_interval_rev pre(5) wf2_rev by blast
    have 9: "\<forall>bl bl'. bl <~~> bl' \<longrightarrow> Inputs bl = Inputs bl' \<and> Outputs bl = Outputs bl'"
      apply clarify subgoal for bl bl'
    proof(induction bl arbitrary: bl')
      case Nil
      then show ?case by simp
    next
      case (Cons a bl)
      have tmp1: "Inputs bl = Inputs (remove1 a bl') \<and> Outputs bl = Outputs (remove1 a bl')"
        using perm_remove_perm Cons by (metis remove_hd)
      have tmp2: "a \<in> set bl'"
        using Cons(2) prem_seteq by (metis list.set_intros(1))
      have tmp3: "a \<in> set bl' \<Longrightarrow> Inputs bl' = Inputs (remove1 a bl') \<union> set (get_inputs a)"
      proof(induction bl')
        case Nil
        then show ?case by simp 
      next
        case (Cons b bl')
        then show ?case
        proof(cases "a = b")
          case True
          then show ?thesis by fastforce
        next
          case False
          have tmp1: "a \<in> set bl'"
            using Cons(2) False by simp
          then show ?thesis using Cons by auto
        qed
      qed
     have tmp4: "a \<in> set bl' \<Longrightarrow> Outputs bl' = Outputs (remove1 a bl') \<union> set (get_outputs a)"
      proof(induction bl')
        case Nil
        then show ?case by simp 
      next
        case (Cons b bl')
        then show ?case
        proof(cases "a = b")
          case True
          then show ?thesis by fastforce
        next
          case False
          have tmp1: "a \<in> set bl'"
            using Cons(2) False by simp
          then show ?thesis using Cons by auto
        qed
      qed
      then show ?case using tmp1 tmp2 tmp3 by (simp add: sup_commute)
    qed
    done
    have 10: "behav_diag_interval bl' cl' (exe_diag_interval bl' cl' h t0 t) h t0 t = True"
    proof -
      have tmp1: "wf2 cl'"
        using pre(1,5) wf2_lemma2 by simp
      have tmp2: "Outputs bl' \<inter> Outputs cl' = {}"
        using pre(1,11,15) 9 by blast
      have tmp3: "(updateIntegBlks cl (findIntegBlks cl)) = (updateIntegBlks cl' (findIntegBlks cl'))"
      proof -
        have tmp: "wf2 (findIntegBlks cl)"
          using pre(5)
          proof(induction cl)
                case Nil
                then show ?case by simp
              next
                case (Cons a bl)
                then show ?case
                proof(cases "set (get_offsets a) = {0}")
                  case True
                  then show ?thesis unfolding getCalBlks.simps using Cons
                    by (simp add: wf2_lemma)
                next
                  case False
                  have tmp1: "\<forall>j. j < (length bl) \<and> j \<ge> 0 \<longrightarrow> a \<noteq> (nth bl j) "
                    using Cons(2) unfolding wf2_def Unique_def
                    by (metis wf2_def Cons.prems Unique_k list.set_intros(1) remove_hd)
                  have tmp2: "\<forall>j. j < (length (findIntegBlks bl)) \<and> j \<ge> 0 
                    \<longrightarrow> a \<noteq> (nth (findIntegBlks bl) j)"
                    using tmp1 findIntegBlksSubset3
                    by (metis in_set_conv_nth less_eq_nat.simps(1) subset_code(1))
                  have tmp3: "Unique (a # findIntegBlks bl)"
                    using Cons Unique_add unfolding wf2_def tmp2 
                    by (metis wf2_def wf2_lemma tmp2)
                  have tmp4: "Graph (set (a # findIntegBlks bl))"
                  proof -
                    have tmp1: "set (a # findIntegBlks bl) \<subseteq> set (a#bl)"
                      using findIntegBlksSubset3 by auto
                    show ?thesis using tmp1 Cons(2) unfolding wf2_def
                      by (meson Graph_def subsetD)
                  qed
                  have tmp5: "Ball (set (a # findIntegBlks bl)) Available' "
                  proof -
                    have tmp1: "set (a # findIntegBlks bl) \<subseteq> set (a#bl)"
                      using findIntegBlksSubset3 by auto
                    show ?thesis using tmp1 Cons(2) unfolding wf2_def by blast
                  qed
                  show ?thesis using False unfolding 
                      findIntegBlks.simps wf2_def apply simp using tmp3 tmp4 tmp5
                    by (metis wf2_def wf2_lemma list.set_intros(1) list.simps(15))
                qed
          qed
          then show ?thesis using updateIntegBlksPerm pre findIntegBlksPerm by presburger
        qed
        have tmp4: "\<forall>h. ODE_cond (updateIntegBlks cl' (findIntegBlks cl')) h t0 t = True"
          using pre(13) tmp3 by simp
        have tmp5: "behavConDiag cl' t0 t (exe_diag_interval bl' cl' h t0 t) h \<and>
        behavDisDiag_interval bl' cl' t0 t h \<and>
        behavDisDiag_attime el' (nat \<lfloor>t0 + t\<rfloor>) (exe_diag_interval bl' cl' h t0 t)"
          using tmp1 tmp2 tmp4 pre existence_of_diag_interval'[of dl' cl' el' bl' t0 t h] "3" 
            wf0_Permutation Graph_Permutation unfolding wf1_def by blast
        have tmp6:"behavDisDiag_attime (bl' @ getCalBlks cl') (nat \<lfloor>t0 + t\<rfloor>) 
          (exe_diag_interval bl' cl' h t0 t)"
          using tmp5 pre(8) 1 behavDisDiag_attime_perm by blast
        show ?thesis unfolding behav_diag_interval.simps using tmp5 tmp6 pre(8) 
          unfolding behavDisDiag_interval.simps using exe_diag_interval_lemma1 pre(16) by auto
      qed
    have 11: "behav_diag_interval (rev bl') (rev cl') (exe_diag_interval bl' cl' h t0 t) h t0 t = True"
      using 10 pre(5,11) wf2_lemma2 Outputs_perm behav_diag_interval_rev pre(1) by presburger
    have 12: "besorted2 (getCalBlks (rev cl))"
    proof -
      have tmp1: "\<forall>c. c \<in> set (getCalBlks cl) \<longrightarrow> set (get_offsets c) = {0}"
        apply clarify subgoal for c
        proof(induction cl)
          case Nil
          then show ?case by simp
        next
          case (Cons a cl)
          then show ?case
          proof(cases "set (get_offsets a) = {0}")
            case True
            then show ?thesis using Cons unfolding getCalBlks.simps by auto
          next
            case False
            then show ?thesis using Cons unfolding getCalBlks.simps by auto
          qed
        qed
        done
      have tmp2: "rev (getCalBlks cl) = getCalBlks (rev cl)"
        using getCalBlks_rev by simp
      show ?thesis using pre(2,4,5) tmp1  tmp2 by (metis)
    qed
    have 13: "besorted2 (getCalBlks (rev cl'))"
    proof -
      have tmp1: "\<forall>c. c \<in> set (getCalBlks cl') \<longrightarrow> set (get_offsets c) = {0}"
        apply clarify subgoal for c
        proof(induction cl')
          case Nil
          then show ?case by simp
        next
          case (Cons a cl)
          then show ?case
          proof(cases "set (get_offsets a) = {0}")
            case True
            then show ?thesis using Cons unfolding getCalBlks.simps by auto
          next
            case False
            then show ?thesis using Cons unfolding getCalBlks.simps by auto
          qed
        qed
        done
      have tmp2: "rev (getCalBlks cl') = getCalBlks (rev cl')"
        using getCalBlks_rev by simp
      show ?thesis using pre(3,5,6) tmp1 tmp2 wf2_lemma2 by (metis)
    qed
    have 14: "\<forall>v t'. t' < t0 \<or> t0 + t < t' \<longrightarrow> (exe_diag_interval bl cl h t0 t) v t' 
        = (exe_diag_interval bl' cl' h t0 t) v t'"
      unfolding exe_diag_interval.simps using exeContinuousDiag_interval_lemma2 exeDisDiag_attime_lemma2 
      using exeCalBlks_lemma2 exeContinuousDiag_interval.simps pre(14) pre(16) by auto
    have 15: "\<forall>v\<in>Outputs cl. (exe_diag_interval bl cl h t0 t) v t0 = 
        (exe_diag_interval bl' cl' h t0 t) v t0"
      unfolding exe_diag_interval.simps exeContinuousDiag_interval.simps using updTimedVar_eq1 
       exeCalBlks_lemma2 exeDisDiag_attime_lemma2 pre(14) pre(16) by auto
    have 16: "\<forall>v\<in>Outputs bl. (exe_diag_interval bl cl h t0 t) v t0 = 
        (exe_diag_interval bl' cl' h t0 t) v t0"
      unfolding exe_diag_interval.simps using exeDisDiag_attime_lemma2 pre(5,14,15,16)
      exeContinuousDiag_interval_lemma1 by (smt (z3) exe_diag_interval.simps exe_diag_interval_lemma1)
    have 17: "rev cl <~~> rev cl'"
      using pre(1) by (meson perm.trans perm_rev perm_sym)
    have 18: "wf2 (rev cl)"
      using pre(5) wf2_lemma2 wf2_rev by blast
    have 19: "(updateIntegBlks (rev cl) (findIntegBlks (rev cl))) = 
        (updateIntegBlks cl (findIntegBlks cl))"
      by (meson "18" findIntegBlkswf findIntegBlksPerm perm_rev updateIntegBlksPerm)
    have 20: "\<forall>h. ODE_cond (updateIntegBlks (rev cl) (findIntegBlks (rev cl))) h t0 t = True"
      using pre 19 by simp
    have 21: "wf0 (rev bl @ getCalBlks (rev cl))"
    proof -
      have tmp1: "wf0 (bl @ getCalBlks cl)"
        using pre(7,12) 0 wf0_Permutation unfolding wf1_def by presburger
      show ?thesis using tmp1 getCalBlks_rev wf0_Permutation 
        by (metis perm_append_swap perm_rev rev_append rev_rev_ident)
    qed
    have 22: "Graph (set (rev bl @ getCalBlks (rev cl)))"
      using pre(7, 12) 0 getCalBlks_rev Graph_Permutation unfolding wf1_def by fastforce
    have 23: "\<forall>v\<in>Outputs (rev bl).
       exe_diag_interval bl cl h t0 t v t0 = exe_diag_interval bl' cl' h t0 t v t0"
      using 16 Outputs_rev by blast
    have 24: "Outputs (rev bl) \<inter> Outputs (rev cl) = {}"
      using pre(15) Outputs_rev by simp
    have 25: "rev bl <~~> rev bl'"
      using pre(11) by (meson perm.trans perm_rev perm_sym)
    have 26: "\<forall>v\<in>Outputs (rev cl).
       exe_diag_interval bl cl h t0 t v t0 = exe_diag_interval bl' cl' h t0 t v t0"
      using 15 Outputs_rev findIntegBlks_rev by presburger
    show ?thesis using uniqueness_of_diag_interval_behav[of "rev bl" "rev cl" "(exe_diag_interval bl cl h t0 t)"
          h t0 t "rev cl'" "rev bl'" "(exe_diag_interval bl' cl' h t0 t)"] 1 3 8 17 12 18 13 11 14 26
          20 23 24 25 Outputs_rev findIntegBlks_rev 21 22 pre(9,10,14,16) unfolding wf1_def by (smt (z3) 
          "9" DiffD2 Outputs_Cons UnE exe_diag_interval_lemma3 pre(1) pre(5) rev_swap wf2_lemma2)
  qed
  done

fun DisBlks_init :: "DisBlk list \<Rightarrow> ConBlk list \<Rightarrow> timed_vars \<Rightarrow> timed_vars" where
  "DisBlks_init bl cl h = exeDisDiag_attime (rev (sortDiag (bl@((getCalBlks cl))))) h 0"

fun exe_diag_tilltime :: "DisBlk list \<Rightarrow> ConBlk list 
    \<Rightarrow> timed_vars \<Rightarrow> nat \<Rightarrow> timed_vars" where
  "exe_diag_tilltime bl cl h 0 = (DisBlks_init bl cl h)" |
  "exe_diag_tilltime bl cl h (Suc k) = exe_diag_interval bl cl (exe_diag_tilltime bl cl h k) k 1"

lemma exe_diag_tilltime_eq: "\<forall>t > real k. \<forall>v. exe_diag_tilltime bl cl h k v t = h v t"
proof(induction k)
  case 0
  then show ?case unfolding exe_diag_tilltime.simps DisBlks_init.simps 
    using exeDisDiag_attime_lemma2 by simp
next
  case (Suc k)
  have 1: "real (k + 1) = real (Suc k)"
    by simp
  have 2: "real (k + 1) > real k"
    by simp
  then show ?case unfolding exe_diag_tilltime.simps using 1 exe_diag_interval_lemma2[of k 1] Suc 
    by simp
qed

lemma exe_diag_tilltime_eq2: "loop_free (bl @ getCalBlks cl) \<Longrightarrow> wf2 cl \<Longrightarrow>
\<forall>t. \<forall>v. v \<notin> Outputs bl \<union> Outputs cl \<longrightarrow> exe_diag_tilltime bl cl h k v t = h v t"
proof(induction k)
  case 0
  have 1: "(rev (sortDiag (bl @ getCalBlks cl))) <~~> (bl @ getCalBlks cl)"
      using 0 toposort_perm unfolding loop_free_def sortDiag_def
      by (metis append.right_neutral perm.trans perm_rev perm_sym)
  have 2: "Outputs (rev (sortDiag (bl @ getCalBlks cl))) \<subseteq> Outputs bl \<union> Outputs cl"
    using 1 Outputs_perm Outputs_Cons getCalBlksSubset by (metis Un_mono sup.idem sup_ge1)
  then show ?case unfolding exe_diag_tilltime.simps DisBlks_init.simps 
    using exeDisDiag_attime_lemma by blast
next
  case (Suc k)
  then show ?case unfolding exe_diag_tilltime.simps using exe_diag_interval_lemma3
    by presburger 
qed

lemma exe_diag_tilltime_lemma: "besorted (sortDiag (bl@((getCalBlks cl)))) \<Longrightarrow> wf1 (rev (sortDiag (bl@((getCalBlks cl))))) \<Longrightarrow> 
behavDisDiag_attime (rev (sortDiag (bl@((getCalBlks cl)))))
   0 (exe_diag_tilltime bl cl h k)"
proof(induction k)
  case 0
  then show ?case unfolding exe_diag_tilltime.simps DisBlks_init.simps 
    using existence_discrete_diag_at0 by simp
next
  case (Suc k)
  then show ?case unfolding exe_diag_tilltime.simps using exe_diag_interval_lemma1[of k 1 bl cl 
        "(exe_diag_tilltime bl cl h k)"] blocklist_hebav_attime_lemma[of 0 
        "(exe_diag_tilltime bl cl h k)" "(exe_diag_interval bl cl (exe_diag_tilltime bl cl h k) 
        (real k) 1)" "(rev (sortDiag (bl @ getCalBlks cl)))"] by simp
qed

fun behavDisDiag_interval2 :: "block list \<Rightarrow> block list \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> behav" where
  "behavDisDiag_interval2 bl cl t0 t k h = (\<forall>vv tt. tt > t0 \<and> tt < t0 + t \<and> vv \<in> Outputs bl \<longrightarrow> 
  (exe_diag_tilltime bl cl h k) vv tt = (exe_diag_tilltime bl cl h (k-1)) vv t0)"

definition behavConDiag2 :: "block list \<Rightarrow> block list \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> timed_vars \<Rightarrow> bool" where
  "behavConDiag2 bl cl t0 t k h = behavConDiag cl t0 t (exe_diag_tilltime bl cl h k) 
  (exe_diag_tilltime bl cl h (k-1))"


lemma existence_of_diag: "
dl = (getCalBlks cl) \<Longrightarrow> el = (rev (sortDiag (bl@(getCalBlks cl)))) \<Longrightarrow>
besorted2 (rev dl)  \<Longrightarrow> wf2 cl \<Longrightarrow>
loop_free (bl @ getCalBlks cl) \<Longrightarrow> wf1 el \<Longrightarrow> Outputs bl \<inter> Outputs cl = {} \<Longrightarrow>
ODE_cond' (updateIntegBlks cl (findIntegBlks cl)) h k = True \<Longrightarrow>

\<forall>t::nat < k. behavConDiag2 bl cl t 1 k h \<and> 
behavDisDiag_interval2 bl cl t 1 k h \<and>
behavDisDiag_attime el (t+1) (exe_diag_tilltime bl cl h k) \<and>
behavDisDiag_attime el 0 (exe_diag_tilltime bl cl h k)"
  apply clarify subgoal for t
proof(induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have 0: "besorted (rev el)"
    proof -
      have tmp1: "(bl @ getCalBlks cl) <~~> (sortDiag (bl@(getCalBlks cl)))"
      proof -
        show ?thesis using Suc unfolding loop_free_def sortDiag_def using toposort_perm 
          by (metis self_append_conv)
      qed
      have tmp2: "Unique (bl @ getCalBlks cl)"
        using Suc Unique_perm Unique_rev tmp1 unfolding wf1_def wf0_def by (metis perm_sym rev_swap)
      have tmp3: "Graph (set (bl @ getCalBlks cl))"
        using Suc tmp1 unfolding wf1_def by (metis Graph_Permutation perm_sym set_rev)
      show ?thesis using Suc tmp2 tmp3 sort_is_sorted by simp
    qed
    have 00: "\<forall>h t0 t. ODE_cond (updateIntegBlks cl (findIntegBlks cl)) h t0 t = True"
      using Suc(8) unfolding ODE_cond_def ODE_cond'_def by simp
  then show ?case
  proof(cases "t = k")
    case True
    have 1: "behavConDiag cl (real t) 1 (exe_diag_interval bl cl (exe_diag_tilltime bl cl h k) (real k) 1)
     (exe_diag_tilltime bl cl h (Suc k - 1))"
      using Suc(2,3,4,5,6,7,8,9,10) True 00
      by (smt (verit, ccfv_threshold) add_diff_cancel_left' existence_of_diag_interval' 
          floor_of_nat nat_int of_nat_0_le_iff of_nat_1 of_nat_add plus_1_eq_Suc)
    have 2: "(\<forall>vv tt.
        real t < tt \<and> tt < real t + 1 \<and> vv \<in> Outputs bl \<longrightarrow>
        exe_diag_interval bl cl (exe_diag_tilltime bl cl h k) (real k) 1 vv tt =
        exe_diag_tilltime bl cl h (Suc k - 1) vv (real t))"
      using existence_of_diag_interval'[of dl cl el bl k 1 "(exe_diag_tilltime bl cl h k)"] 
        Suc(2,3,4,5,6,7,8,9,10) True 00 unfolding behavDisDiag_interval.simps by simp
    have 3: "behavDisDiag_attime (rev (sortDiag (bl @ getCalBlks cl))) (t + 1)
     (exe_diag_interval bl cl (exe_diag_tilltime bl cl h k) (real k) 1)"
      using existence_of_diag_interval'[of dl cl el bl k 1 "(exe_diag_tilltime bl cl h k)"] 
        Suc(2,3,4,5,6,7,8,9,10) True 00 unfolding behavDisDiag_interval.simps by (metis Suc_eq_plus1 
          add.commute floor_of_nat nat_int of_nat_0_le_iff of_nat_Suc zero_less_one)
    have 4: "behavDisDiag_attime el 0 (exe_diag_tilltime bl cl h (Suc k))"
      using exe_diag_tilltime_lemma 0 Suc(6) by (metis Suc.prems(1) rev_rev_ident)
    then show ?thesis using 4 unfolding behavDisDiag_interval2.simps exe_diag_tilltime.simps behavConDiag2_def
      using existence_of_diag_interval'[of dl cl el bl k 1 "(exe_diag_tilltime bl cl h k)"] 
      unfolding behavDisDiag_interval.simps using 1 2 3 using Suc.prems(1) by force
  next
    case False
    note F1 = False
    have 1: "t < k"
      using F1 Suc by auto
    then show ?thesis
    proof(cases "k = 0")
      case True
      then show ?thesis using 1 by simp
    next
      case False
      have 2: "behavConDiag cl (real t) 1 (exe_diag_tilltime bl cl h (Suc k)) (exe_diag_tilltime bl cl h k)"
      proof -
        have tmp0: "ODE_cond' (updateIntegBlks cl (findIntegBlks cl)) h (real k) = True"
          using 00 unfolding ODE_cond'_def ODE_cond_def by simp
        have tmp1: "behavConDiag cl (real t) 1 (exe_diag_tilltime bl cl h k) (exe_diag_tilltime bl cl h (k - 1))"
          using Suc 1 tmp0 unfolding behavConDiag2_def by simp
        have tmp2: "\<forall>t'\<le>real k. \<forall>v. exe_diag_interval bl cl (exe_diag_tilltime bl cl h k) 
            (real k) 1 v t' = (exe_diag_tilltime bl cl h k) v t'"
          using exe_diag_interval_lemma1[of k 1] by simp
        have tmp3: "t + 1 \<le> real k"
          using 1 by simp
        have tmp4: "behavConDiag cl (real t) 1 (exe_diag_interval bl cl (exe_diag_tilltime bl cl h k) (real k) 1)
     (exe_diag_tilltime bl cl h (k - 1))"
          using behavConDiag_eq[of cl t 1 "(exe_diag_tilltime bl cl h k)" 
              "(exe_diag_interval bl cl (exe_diag_tilltime bl cl h k) (real k) 1)" 
              "(exe_diag_tilltime bl cl h (k - 1))"]
          tmp1 tmp2 tmp3 getCalBlksSubset findIntegBlksSubset
          by (simp add: "1" Suc.prems nat_less_real_le)
        have tmp5: "\<forall>v. (exe_diag_tilltime bl cl h k) v t = (exe_diag_tilltime bl cl h (k - 1)) v t"
        proof -
          have tmp1: "k = Suc (k-1)"
            using False by simp
          show ?thesis using exe_diag_tilltime.simps(2)[of bl cl h "k-1"] 1
              exe_diag_interval_lemma1[of "k-1" 1 bl cl "(exe_diag_tilltime bl cl h (k - 1))"]
             by auto
        qed
        show ?thesis unfolding exe_diag_tilltime.simps using behavConDiag_eq2 tmp4 tmp5 
          by metis
      qed
      have 3: "behavDisDiag_interval2 bl cl (real t) 1 (Suc k) h"
      proof -
        have tmp0: "ODE_cond' (updateIntegBlks cl (findIntegBlks cl)) h (real k) = True"
          using 00 unfolding ODE_cond'_def ODE_cond_def by simp
        have tmp1: "behavDisDiag_interval2 bl cl (real t) 1 k h"
          using Suc F1 tmp0 by simp
        have tmp2: "t + 1 \<le> real k"
          using 1 by simp
        have tmp3: "\<forall>vv tt. real t < tt \<and> tt < real t + 1 \<and> vv \<in> Outputs bl \<longrightarrow>
           exe_diag_interval bl cl (exe_diag_tilltime bl cl h k) (real k) 1 vv tt =
           exe_diag_tilltime bl cl h (Suc k - 1) vv tt"
          using tmp1 unfolding behavDisDiag_interval2.simps exe_diag_tilltime.simps
          using exe_diag_interval_lemma1[of k 1 bl cl "(exe_diag_tilltime bl cl h k)"]
          tmp2 by auto
        have tmp4: "k = Suc (k-1)"
          using False by simp
        have tmp5: "\<forall>v. exe_diag_tilltime bl cl h (k - 1) v (real t) = 
           exe_diag_tilltime bl cl h k v (real t) "
        proof -
          have "Suc \<noteq> (+) 1 \<or> Suc (k - 1) = 1 + (k - 1)"
            by presburger
          then show ?thesis using tmp4 exe_diag_tilltime.simps(2)[of bl cl h "k-1"] exe_diag_interval_lemma1
            by (smt (z3) floor_of_nat nat_int of_nat_1 of_nat_Suc of_nat_add tmp2)
        qed
        show ?thesis using tmp1 tmp3 tmp5 unfolding behavDisDiag_interval2.simps exe_diag_tilltime.simps
          by auto
      qed
      have 4: "behavDisDiag_attime el (t + 1) (exe_diag_tilltime bl cl h (Suc k))"
      proof -
        have tmp0: "ODE_cond' (updateIntegBlks cl (findIntegBlks cl)) h (real k) = True"
          using 00 unfolding ODE_cond'_def ODE_cond_def by simp
        have tmp1: "behavDisDiag_attime el (t + 1) (exe_diag_tilltime bl cl h k)"
          using Suc F1 tmp0  by simp
        show ?thesis using tmp1 unfolding exe_diag_tilltime.simps
          using blocklist_hebav_attime_lemma[of "t+1" "(exe_diag_tilltime bl cl h k)"
             "(exe_diag_interval bl cl (exe_diag_tilltime bl cl h k) (real k) 1)"]
          exe_diag_interval_lemma1[of k 1 bl cl "(exe_diag_tilltime bl cl h k)"] 1 by auto
      qed
      have 5: "behavDisDiag_attime (rev (sortDiag (bl @ getCalBlks cl))) 
          0 (exe_diag_tilltime bl cl h (Suc k))"
        using exe_diag_tilltime_lemma 0 Suc(6) by (metis Suc.prems(1) rev_rev_ident)
      then show ?thesis using 2 3 4 Suc(2) unfolding behavConDiag2_def by simp
    qed
  qed
qed
  done

thm unique_on_closed_def

lemma uniqueness_of_diag': "cl <~~> cl' \<Longrightarrow> dl = getCalBlks cl \<Longrightarrow> dl' = (getCalBlks cl') 
\<Longrightarrow> besorted2 (rev dl) \<Longrightarrow> wf2 cl \<Longrightarrow> besorted2 (rev dl') \<Longrightarrow>
el = rev (sortDiag (bl @ getCalBlks cl)) \<Longrightarrow> 
el' = rev (sortDiag (bl' @ getCalBlks cl')) \<Longrightarrow> 
loop_free (bl @ getCalBlks cl) \<Longrightarrow> loop_free (bl' @ getCalBlks cl') \<Longrightarrow>
bl <~~> bl' \<Longrightarrow> wf1 el \<Longrightarrow> 
ODE_cond' (updateIntegBlks cl (findIntegBlks cl)) h k = True \<Longrightarrow>
Outputs bl \<inter> Outputs cl = {} \<Longrightarrow>

(\<forall>vv t'::real. (t' \<le> k) \<and> vv \<in> Outputs bl \<union> Outputs cl
\<longrightarrow> exe_diag_tilltime bl cl h k vv t' =
exe_diag_tilltime bl' cl' h k vv t')"
  subgoal premises pre
  proof -
    have 0: "el <~~> (bl @ getCalBlks cl)"
      using pre(7,9) toposort_perm unfolding loop_free_def sortDiag_def
      by (metis append.right_neutral perm.trans perm_rev perm_sym)
    have 1: "el' <~~> (bl' @ getCalBlks cl')"
      using pre(8,10) toposort_perm unfolding loop_free_def sortDiag_def
      by (metis append.right_neutral perm.trans perm_rev perm_sym)
    have 2: "wf0 bl"
    proof -
      have tmp1: "wf0 (rev el)"
        using pre(12) wf0_Permutation unfolding wf1_def by (metis perm_rev rev_swap)
      have tmp2: "(bl @ getCalBlks cl) <~~> (sortDiag (bl@((getCalBlks cl))))"
        using pre(9) unfolding loop_free_def sortDiag_def using toposort_perm 
        by (metis append.right_neutral)
      have tmp3: "wf0 (bl @ getCalBlks cl)"
        using tmp1 tmp2 pre(7) wf0_Permutation by (metis perm_sym rev_swap)
      show ?thesis using tmp3 wf0_Cons by auto
    qed
    have 3: "el <~~> el'"
    proof -
      have tmp1: "getCalBlks cl <~~> getCalBlks cl'"
        using pre(1) getCalBlksPerm by auto
      have tmp2: "bl@getCalBlks cl <~~> bl'@getCalBlks cl'"
        using pre(11) tmp1 by blast
      have tmp3: "(bl @ getCalBlks cl) <~~> (sortDiag (bl@((getCalBlks cl))))"
        using pre(9) unfolding loop_free_def sortDiag_def using toposort_perm 
        by (metis append.right_neutral)
      have tmp4: "(bl' @ getCalBlks cl') <~~> 
        (sortDiag (bl'@((getCalBlks cl'))))"
        using pre(10) unfolding loop_free_def sortDiag_def using toposort_perm 
        by (metis append.right_neutral)
      show ?thesis using pre(7,8) tmp2 tmp3 tmp4
        by (meson perm.trans perm_rev perm_sym)
    qed
    have 4: "Outputs cl = Outputs (getCalBlks cl) \<union> Outputs (findIntegBlks cl)"
    proof -
      have tmp: "\<forall>b \<in> set cl. set (get_offsets b) = {0} \<or> set (get_offsets b) = {1}"
      using pre(5) unfolding wf2_def Available'_def Graph_def
      by (metis less_nat_zero_code list.size(3) set_empty2)
      show ?thesis using tmp
      proof(induction cl)
        case Nil
        then show ?case by simp
      next
        case (Cons b cl)
        then show ?case unfolding getCalBlks.simps findIntegBlks.simps by (smt 
              (verit, best) One_nat_def Outputs.simps(2) Un_assoc Un_left_commute list.set_intros(1) 
              list.set_intros(2) old.nat.distinct(1) singleton_insert_inj_eq')
      qed
    qed
    have 5: "Inputs cl = Inputs (getCalBlks cl) \<union> Inputs (findIntegBlks cl)"
    proof -
      have tmp: "\<forall>b \<in> set cl. set (get_offsets b) = {0} \<or> set (get_offsets b) = {1}"
      using pre(5) unfolding wf2_def Available'_def Graph_def
      by (metis less_nat_zero_code list.size(3) set_empty2)
      show ?thesis using tmp
      proof(induction cl)
        case Nil
        then show ?case by simp
      next
        case (Cons b cl)
        then show ?case unfolding getCalBlks.simps findIntegBlks.simps by (smt 
              (verit, best) One_nat_def Inputs.simps(2) Un_assoc Un_left_commute list.set_intros(1) 
              list.set_intros(2) old.nat.distinct(1) singleton_insert_inj_eq')
      qed
    qed
    have 6: "besorted (rev el) \<and> besorted (rev el')"
    proof -
      have tmp1: "(bl @ getCalBlks cl) <~~> (sortDiag (bl@(getCalBlks cl)))"
      proof -
        show ?thesis using pre(9) unfolding loop_free_def sortDiag_def using toposort_perm 
          by (metis self_append_conv)
      qed
      have tmp2: "Unique (bl @ getCalBlks cl)"
        using pre(7,12) Unique_perm Unique_rev tmp1 unfolding wf1_def wf0_def by (metis perm_sym rev_swap)
      have tmp3: "Graph (set (bl @ getCalBlks cl))"
        using pre(7,12) tmp1 unfolding wf1_def by (metis Graph_Permutation perm_sym set_rev)
      have tmp4: "(bl' @ getCalBlks cl') <~~> 
          (sortDiag (bl'@(getCalBlks cl')))"
      proof -
        show ?thesis using pre(10) unfolding loop_free_def sortDiag_def using toposort_perm 
          by (metis self_append_conv)
      qed
      have tmp5: "Unique (bl' @ getCalBlks cl')"
        using pre(8,12) 3 Unique_perm unfolding wf1_def wf0_def
        by (metis perm_rev perm_sym tmp4)
      have tmp6: "Graph (set (bl' @ getCalBlks cl'))"
        using pre(8,12) 3 tmp4 unfolding wf1_def by (metis Graph_Permutation perm_sym set_rev)
      show ?thesis using pre(7,8) tmp2 tmp3 tmp5 tmp6 sort_is_sorted by simp
    qed
    show ?thesis
    proof(induction k)
      case 0
      then show ?case
      proof(cases "el = []")
        case True
        then show ?thesis unfolding exe_diag_tilltime.simps DisBlks_init.simps using pre(7,8)
        2 3 by auto
      next
        case False
        have tmp1: "wf0 (rev el)"
          using pre(12) wf0_Permutation unfolding wf1_def by (metis perm_rev rev_swap)
        have tmp2: "behavDisDiag_attime (rev el) 0 (exeDisDiag_attime el h 0) = True"
          using exe_diag_tilltime_lemma pre(7,12) 6 behavDisDiag_attime_rev 
            existence_discrete_diag_at0 by presburger
        have tmp3: "behavDisDiag_attime (rev el') 0 (exe_diag_tilltime bl' cl' h 0) = True"
          using exe_diag_tilltime_lemma pre(8,12) 3 6 unfolding wf1_def 
          by (metis Graph_Permutation behavDisDiag_attime_rev rev_rev_ident wf0_Permutation)
        have tmp4: "\<forall>v\<in>Inputs (rev el) - Outputs (rev el).
       \<forall>t\<le>real 0. exe_diag_tilltime bl cl h 0 v t = exe_diag_tilltime bl' cl' h 0 v t "
          unfolding exe_diag_tilltime.simps DisBlks_init.simps pre(7) using exeDisDiag_attime_lemma
          by (metis "3" DiffD2 Outputs_perm Outputs_rev pre(7) pre(8))
        have tmp5: "\<forall>t<real 0. \<forall>v\<in>Outputs (rev el). exe_diag_tilltime bl cl h 0 v t 
          = exe_diag_tilltime bl' cl' h 0 v t"
          unfolding exe_diag_tilltime.simps DisBlks_init.simps pre(7) using exeDisDiag_attime_lemma2
          by simp 
        have tmp6: "\<forall>v\<in>Outputs (rev el). exe_diag_tilltime bl cl h 0 v 0 
          = exe_diag_tilltime bl' cl' h 0 v 0"
          using blocklist_hebav_attime_lemma3[of "rev el" 
              "exe_diag_tilltime bl cl h 0" "rev el'" "exe_diag_tilltime bl' cl' h 0"] 
            tmp1 tmp2 tmp3 tmp4 tmp5 6 3 False by (smt (verit, best) behavDisDiag_attime_perm 
              exe_diag_tilltime_lemma perm.trans perm_rev pre(12) pre(7) rev_is_Nil_conv rev_swap)
        then show ?thesis unfolding exe_diag_tilltime.simps DisBlks_init.simps pre(7)
          using exeDisDiag_attime_lemma exeDisDiag_attime_lemma2 
          by (metis "3" Outputs_perm Outputs_rev of_nat_0 pre(7) pre(8))
      qed
    next
      case (Suc k)
      have 7: "\<forall>vv t'.
       t' \<le> real k \<and> vv \<in> Outputs bl \<union> Outputs cl \<longrightarrow>
       exe_diag_interval bl cl (exe_diag_tilltime bl cl h k) (real k) 1 vv t' =
       exe_diag_interval bl' cl' (exe_diag_tilltime bl' cl' h k) (real k) 1 vv t'"
      proof -
        have tmp1: "\<forall>vv t'.
        t' \<le> real k \<and> vv \<in> Outputs bl \<union> Outputs cl \<longrightarrow>
        exe_diag_interval bl cl (exe_diag_tilltime bl cl h k) (real k) 1 vv t' =
        exe_diag_tilltime bl cl h k vv t'"
          using exe_diag_interval_lemma1[of k 1 bl cl "(exe_diag_tilltime bl cl h k)"] by simp
        have tmp2: "\<forall>vv t'.
        t' \<le> real k \<and> vv \<in> Outputs bl \<union> Outputs cl \<longrightarrow>
        exe_diag_interval bl' cl' (exe_diag_tilltime bl' cl' h k) (real k) 1 vv t' =
        exe_diag_tilltime bl' cl' h k vv t'"
          using exe_diag_interval_lemma1[of k 1 bl' cl' "(exe_diag_tilltime bl' cl' h k)"] by simp
        show ?thesis using Suc tmp1 tmp2 by presburger
      qed
      have 8: "\<forall>vv t'. t' \<le> real k \<longrightarrow>
        exe_diag_tilltime bl cl h k vv t' = exe_diag_tilltime bl' cl' h k vv t'"
        using exe_diag_tilltime_eq2 pre(5,9) Suc
        by (metis Outputs_perm pre(1) pre(10) pre(11) wf2_lemma2)
      have 9: "\<forall>vv t'. exe_diag_tilltime bl cl h k vv t' = exe_diag_tilltime bl' cl' h k vv t'"
        using 8 exe_diag_tilltime_eq[of k bl cl h] exe_diag_tilltime_eq[of k bl' cl' h] 
        by (metis linorder_not_less)
      have 10: "exe_diag_tilltime bl cl h k = exe_diag_tilltime bl' cl' h k"
        using 9 by auto
      have 11: "\<forall>h. ODE_cond (updateIntegBlks cl (findIntegBlks cl)) h (real k) 1 = True"
        using pre(13) unfolding ODE_cond'_def ODE_cond_def by presburger
      have 12: "\<forall>vv t'.
       t' > real k \<and> t' \<le> real (Suc k) \<and> vv \<in> Outputs 
bl \<union> Outputs cl \<longrightarrow>
       exe_diag_interval bl cl (exe_diag_tilltime bl cl h k) (real k) 1 vv t' =
       exe_diag_interval bl' cl' (exe_diag_tilltime bl' cl' h k) (real k) 1 vv t'"
        using uniqueness_of_diag_interval[of cl cl' dl dl' el bl el' bl' k 1 
            "(exe_diag_tilltime bl cl h k)"] 10 pre 11 by simp
      then show ?case unfolding exe_diag_tilltime.simps using 7
        using linorder_not_less by blast
    qed
  qed
  done

lemma uniqueness_of_diag: "cl <~~> cl' \<Longrightarrow> dl = getCalBlks cl \<Longrightarrow> dl' = (getCalBlks cl') 
\<Longrightarrow> besorted2 (rev dl) \<Longrightarrow> wf2 cl \<Longrightarrow> besorted2 (rev dl') \<Longrightarrow>
el = rev (sortDiag (bl @ getCalBlks cl)) \<Longrightarrow> 
el' = rev (sortDiag (bl' @ getCalBlks cl')) \<Longrightarrow> 
loop_free (bl @ getCalBlks cl) \<Longrightarrow> loop_free (bl' @ getCalBlks cl') \<Longrightarrow>
bl <~~> bl' \<Longrightarrow> wf1 el \<Longrightarrow> 
ODE_cond' (updateIntegBlks cl (findIntegBlks cl)) h k = True \<Longrightarrow>
Outputs bl \<inter> Outputs cl = {} \<Longrightarrow>

(\<forall>vv t. exe_diag_tilltime bl cl h k vv t =
exe_diag_tilltime bl' cl' h k vv t)"
  subgoal premises pre
  proof -
    have 1: "(\<forall>vv t. vv \<notin> Outputs bl \<union> Outputs cl \<longrightarrow> exe_diag_tilltime bl cl h k vv t =
exe_diag_tilltime bl' cl' h k vv t)"
      using exe_diag_tilltime_eq2 pre Outputs_perm wf2_lemma2 by presburger
    have 2: "(\<forall>vv t. t > real k \<longrightarrow> exe_diag_tilltime bl cl h k vv t =
exe_diag_tilltime bl' cl' h k vv t)"
      using exe_diag_tilltime_eq pre Outputs_perm wf2_lemma2 by presburger
    have 3: "(\<forall>vv t'::real. (t' \<le> k) \<and> vv \<in> Outputs bl \<union> Outputs cl
  \<longrightarrow> exe_diag_tilltime bl cl h k vv t' = exe_diag_tilltime bl' cl' h k vv t')"
      using uniqueness_of_diag' pre by simp
    show ?thesis apply clarify subgoal for v t using 1 2 3
        using linorder_not_less by blast
      done
  qed
  done

text \<open>general subsystem\<close>
\<comment> \<open>discrete blocks, continuous blocks\<close>

datatype subsystem = Subsystem "DisBlk list" "ConBlk list" "subsystem list"


fun getDisBlks :: "subsystem \<Rightarrow> DisBlk list" where
  "getDisBlks (Subsystem a _ _) = a"

fun getConBlks :: "subsystem \<Rightarrow> ConBlk list" where
  "getConBlks (Subsystem _ b _) = b"

type_synonym subsystem_block = block
type_synonym subsystemMap = "subsystem_block \<Rightarrow> subsystem"

fun DivideInterval2 :: "real \<Rightarrow> real \<Rightarrow> real list \<Rightarrow> real list \<Rightarrow> real list" where
  "DivideInterval2 t0 t [] [] = []" |
  "DivideInterval2 t0 t [] (y#ys) = (if (y \<ge> t0 \<and> y \<le> t0 + t)
  then (y#(DivideInterval2 t0 t [] ys)) else (DivideInterval2 t0 t [] ys))" |
  "DivideInterval2 t0 t (x#xs) ys = (if (x \<ge> t0 \<and> x \<le> t0 + t)
  then (x#(DivideInterval2 t0 t xs ys)) else (DivideInterval2 t0 t xs ys))"

fun getBlockAttime :: "real \<Rightarrow> real \<Rightarrow> DisBlk list \<Rightarrow> DisBlk list" where
  "getBlockAttime t0 t [] = []" |
  "getBlockAttime t0 t (b#bl) = (if (\<exists> k::nat.  t0+t = (get_sample_time b)*k) then 
(b#(getBlockAttime t0 t bl)) else (getBlockAttime t0 t bl))"

\<comment> \<open>execute diag with subsystem\<close>
inductive exe_diag_with_subsystem_interval :: "DisBlk list \<Rightarrow> ConBlk list \<Rightarrow> 
  subsystem list \<Rightarrow> timed_vars \<Rightarrow> real \<Rightarrow> real \<Rightarrow> timed_vars \<Rightarrow> bool" where
  "exe_diag_with_subsystem_interval bl cl [] h t0 t (exe_diag_interval 
    (sortDiag bl) ((sortDiag (getCalBlks cl))@(findIntegBlks cl)) h t0 t)" |

  "exe_diag_with_subsystem_interval (bl@(getBlockAttime t0 t (getDisBlks sub)))
  (cl@(getConBlks sub)) (subs@c) h t0 t h1 \<Longrightarrow>
  exe_diag_with_subsystem_interval bl cl ((Subsystem a b c)#subs) h t0 t h1"
                                                                    

end
