theory Example
  imports DisConSemantics
begin


definition Gain::block where "Gain = Block ''x'' ''y'' [0] 1 [(\<lambda>s. (if length s = 1
  then (2*hd s) else 0))]"

definition UD1::block where "UD1 = Block ''y'' ''s'' [0] 1 [(\<lambda>s. (if length s = 1
  then (hd s) else 0))]"
definition UD2::block where "UD2 = Block ''s'' ''z'' [1] 1 [(\<lambda>s. (if length s = 1
  then (hd s) else 0))]"

definition Integ1::block where "Integ1 = Block ''z'' ''a'' [1] 0 [(\<lambda>s. (if length s = 1
  then (hd s) else 0))]"

definition Bias::block where "Bias = Block ''a'' ''b'' [0] 0 [(\<lambda>s. (if length s = 1
  then (hd s + 2::real) else 0))]"

definition Integ2::block where "Integ2 = Block ''b'' ''x'' [1] 0 [(\<lambda>s. (if length s = 1
  then (hd s) else 0))]"

definition h:: timed_vars where "h = (\<lambda>v t. 0)"

definition h':: timed_vars where "h' = (\<lambda>v t. (if t = 0 \<and> v = CHR ''b'' then 2 else 0))"

definition Bias'::block where "Bias' = Block ''a'' ''b'' [0] (-1) [(\<lambda>s. (if length s = 1
  then (hd s + 2::real) else 0))]"
\<comment> \<open>compute sample time of block "Bias'", and sample_time = 0 inherited by Ingteg1\<close>

term "exe_discrete_diag_tilltime [B2,B1] h 0 (CHR ''a'') 0"

lemma test0: "((\<lambda>x. k*x) has_vderiv_on (\<lambda>x. k)) T"
  by (auto simp: has_vderiv_on_def intro!: derivative_eq_intros)

lemma test0': "((\<lambda>x. 2*x*x) has_vderiv_on (\<lambda>x. 4*x)) T"
  by (auto simp: has_vderiv_on_def intro!: derivative_eq_intros) 

text \<open>Projection of has_vector_derivative onto components.\<close>
lemma has_vector_derivative_proj:
  assumes "(p has_vector_derivative q t) (at t within D)"
  shows "((\<lambda>t. p t $ i) has_vector_derivative q t $ i) (at t within D)"
  using assms unfolding has_vector_derivative_def has_derivative_def 
  apply (simp add: bounded_linear_scaleR_left)
  using tendsto_vec_nth by fastforce

lemma has_vderiv_on_proj:
  assumes "(p has_vderiv_on q) D"
  shows "((\<lambda>t. p t $ i) has_vderiv_on (\<lambda>t. q t $ i)) D"
  using assms unfolding has_vderiv_on_def 
  by (simp add: has_vector_derivative_proj)

lemma has_vector_derivative_projI:
  assumes "\<forall>i. ((\<lambda>t. p t $ i) has_vector_derivative q t $ i) (at t within D)"
  shows "(p has_vector_derivative q t) (at t within D)"
  using assms unfolding has_vector_derivative_def has_derivative_def
  apply (auto simp add: bounded_linear_scaleR_left)
  by (auto intro: vec_tendstoI)
                              

\<comment> \<open>combination check\<close>
lemma relatedBlocks_lemma1:"(getRelatedBlocks [Bias,Integ2] Integ2 []) = [Bias]"
proof- 
  have 1: "getOneRelatedBlock [Bias,Integ2] Integ2 [] = Some Bias"
    unfolding getOneRelatedBlock.simps Integ1_def Bias_def Integ2_def by force
  have 2: "(remove1 (the (Some Bias)) [Bias,Integ2] = [Integ2])"
    by simp
  have 3: "(getRelatedBlocks [Bias,Integ2] Integ2 []) = (getRelatedBlocks [Integ2] Integ2 [Bias])"
    using 1 2 by auto
  have 4: "getOneRelatedBlock [Integ2] Integ2 [Bias] = None"
    unfolding getOneRelatedBlock.simps Integ1_def Bias_def Integ2_def by force
  have 5: "(remove1 (the (Some Integ1)) [Integ1,Integ2] = [Integ2])"
    by simp
  have 6: "(getRelatedBlocks [Integ2] Integ2 [Bias]) = [Bias]"
    using 4 5 by auto
  show ?thesis using 3 6 by simp
qed

lemma relatedBlocks_lemma2:"(getRelatedBlocks [Integ1,Bias,Integ2] Integ1 []) = []"
proof- 
  have 1: "getOneRelatedBlock [Integ1,Bias,Integ2] Integ1 [] = None"
    unfolding getOneRelatedBlock.simps Integ1_def Bias_def Integ2_def by force
  show ?thesis using 1 by simp
qed

lemma outputs_sort_lemma1: "sort_by_outputs [Integ1, Integ2] = [Integ1, Integ2]"
proof -
  have 1: "get_first_block [Integ1, Integ2] = Integ1"
  proof -
    show ?thesis unfolding get_first_block.simps Integ1_def Integ2_def integer_of_char_def by simp
  qed
  show ?thesis unfolding sort_by_outputs.simps using 1 by auto
qed

lemma outputs_sort_lemma2: "sort_by_outputs [Integ1, Bias, Integ2] = [Integ1, Bias, Integ2]"
proof -
  have 1: "get_first_block [Integ1, Bias, Integ2] = Integ1"
    unfolding get_first_block.simps Integ1_def Integ2_def Bias_def integer_of_char_def by simp
  have 2: "remove1 Integ1 [Integ1, Bias, Integ2] = [Bias, Integ2]"
    by simp
  have 3: "sort_by_outputs [Bias, Integ2] = [Bias, Integ2]"
    unfolding sort_by_outputs.simps get_first_block.simps Integ2_def Bias_def integer_of_char_def by simp
  show ?thesis unfolding sort_by_outputs.simps using 1 3 by auto
qed

lemma combineOneBlock_lemma1: "combineOneBlock ''a'' ''b'' [0] [(\<lambda>s. (if length s = 1
  then (hd s + 2) else 0))] Integ2 = (Block ''a'' ''x'' [1] 0 (updateFunc [\<lambda>s. if length s = 1 
then hd s else 0] ''b'' CHR ''b''(\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))"
proof -
  have 1: "\<forall>b. get_sample_time b = 0 \<longrightarrow> combineOneBlock ''a'' [] [] [] b = b"
    by (metis (no_types, opaque_lifting) combineOneBlock.simps(1) get_sample_time.elims)
  have 2: "combineOneOutput ''a'' CHR ''b'' 0 (\<lambda>s. if length s = 1 then hd s + 2 else 0)
           (Block ''b'' ''x'' [1] 0 [(\<lambda>s. (if length s = 1 then (hd s) else 0))]) = 
  (Block ''a'' ''x'' [1] 0 (updateFunc [\<lambda>s. if length s = 1 then hd s else 0] ''b'' CHR ''b''
             (\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))"
  proof -
    have tmp1: "(combineInputs ''b'' ''a'' CHR ''b'') = ''a''"
      by simp
    show ?thesis unfolding combineOneOutput.simps by auto
  qed
  show ?thesis using combineOneBlock.simps(4)[of "''a''" "CHR ''b''" "[]" 0 "[]" "(\<lambda>s. (if length s = 1
  then (hd s + 2) else 0))" "[]"] 1 2 by (simp add: Integ2_def)
qed

value "(combineInputs2 ''a'' ''z'')"

lemma combineOneBlock_lemma2: "combineOneBlock ''a'' ''x'' [1] (updateFunc [\<lambda>s. if length s = 1 
then hd s else 0] ''b'' CHR ''b''(\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a'') Integ1  = 
Block ''za'' ''ax'' [1,1] 0
           (updateFunc2 [\<lambda>s. if length s = 1 then hd s else 0] ''a''
             (hd (updateFunc [\<lambda>s. if length s = 1 then hd s else 0] ''b'' CHR ''b''
                   (\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))
             ''z'')"
proof -
  have 1: "\<forall>b. get_sample_time b = 0 \<longrightarrow> combineOneBlock ''a'' [] [] [] b = b"
    by (metis (no_types, opaque_lifting) combineOneBlock.simps(1) get_sample_time.elims)
  have 2: "combineOneOutput2 ''a'' CHR ''x'' 1 (hd (updateFunc [\<lambda>s. if length s = 1 then hd s 
          else 0] ''b'' CHR ''b'' (\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))
             Integ1 = Block ''za'' ''ax'' [1,1] 0
           (updateFunc2 [\<lambda>s. if length s = 1 then hd s else 0] ''a''
             (hd (updateFunc [\<lambda>s. if length s = 1 then hd s else 0] ''b'' CHR ''b''
                   (\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))
             ''z'')"
  proof -
    have tmp1: "(combineInputs2 ''z'' ''a'') = ''za''"
      by simp
    show ?thesis unfolding Integ1_def combineOneOutput2.simps by simp
  qed
  show ?thesis using combineOneBlock.simps(4)[of "''a''" "CHR ''x''" "[]" 1 "[]" "hd 
    (updateFunc [\<lambda>s. if length s = 1 then hd s else 0] ''b'' CHR ''b''(\<lambda>s. if length s = 1 
    then hd s + 2 else 0) ''a'')" "[]"] 1 2 by (simp add: Integ1_def)
qed

lemma combineBlocks_lemma1: "combineBlocks (getRelatedBlocks [Bias,Integ2] Integ2 []) Integ2
  = (Block ''a'' ''x'' [1] 0 (updateFunc [\<lambda>s. if length s = 1 
then hd s else 0] ''b'' CHR ''b''(\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))"
proof -
  have 1: "combineBlocks [Bias] Integ2 = (Block ''a'' ''x'' [1] 0 (updateFunc [\<lambda>s. if length s = 1 
then hd s else 0] ''b'' CHR ''b''(\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))"
    unfolding combineBlocks.simps Bias_def Integ1_def using combineOneBlock_lemma1 
      get_inputs.simps get_offsets.simps get_outputs.simps     
      get_outupd.simps by presburger
  show ?thesis using 1 relatedBlocks_lemma1 by auto
qed

lemma combineBlocks_lemma2: "combineBlocks (getRelatedBlocks [Integ1,Bias,Integ2] Integ1 []) 
  Integ1 = Integ1"
  using relatedBlocks_lemma2 by auto

lemma combination_lemma: "combination [Integ1,Bias,Integ2] [Integ1, Integ2] = 
  [Integ1,(Block ''a'' ''x'' [1] 0 (updateFunc [\<lambda>s. if length s = 1 
then hd s else 0] ''b'' CHR ''b''(\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))]"
  unfolding combination.simps using combineBlocks_lemma1
  using combineBlocks_lemma2 by auto

lemma Combine_lemma: "Combine [Integ1,(Block ''a'' ''x'' [1] 0 (updateFunc [\<lambda>s. if length s = 1 
then hd s else 0] ''b'' CHR ''b''(\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))] = 
  Block ''za'' ''ax'' [1, 1] 0
   (updateFunc2 [\<lambda>s. if length s = 1 then hd s else 0] ''a''
     (hd (updateFunc [\<lambda>s. if length s = 1 then hd s else 0] ''b'' CHR ''b''
           (\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))
     ''z'')"
  unfolding Combine.simps combineBlocks.simps using combineOneBlock_lemma2 by simp

lemma updateIntegBlks_lemma: "updateIntegBlks [Integ1, Bias, Integ2] [Integ1, Integ2] =
  Block ''za'' ''ax'' [1, 1] 0
   (updateFunc2 [\<lambda>s. if length s = 1 then hd s else 0] ''a''
     (hd (updateFunc [\<lambda>s. if length s = 1 then hd s else 0] ''b'' CHR ''b''
           (\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))
     ''z'')"
  unfolding updateIntegBlks.simps using outputs_sort_lemma1 outputs_sort_lemma2
  combination_lemma Combine_lemma by auto


lemma getODE':"(block2ODE (Block ''a'' ''x'' [1] 0 (updateFunc [\<lambda>s. if length s = 1 
then hd s else 0] ''b'' CHR ''b''(\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))) =
(\<lambda>t v. (\<chi> x.(if x = CHR ''x'' then (v $ CHR ''a'' + 2) else 0)))"
proof -
  have 1: "getExps (updateFunc [\<lambda>s. if length s = 1 then hd s else 0] ''b'' CHR ''b''
                (\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a'') ''a'' = [\<lambda>s. s CHR ''a'' + 2]"
  proof -
    have tmp1: "\<forall>s. length (map s ''a'') = length (combineInputs ''b'' ''a'' CHR ''b'')"
      by simp
    have tmp2: "\<forall>s. (splitInputs ''b'' ''a'' CHR ''b'' (map s ''a'')
            (\<lambda>s. if length s = 1 then hd s + 2 else 0)) = [s CHR ''a'' + 2]"
      by simp
    have tmp3: "\<forall>s. length (splitInputs ''b'' ''a'' CHR ''b'' (map s ''a'')
                    (\<lambda>s. if length s = 1 then hd s + 2 else 0)) = 1"
      by simp
    show ?thesis  unfolding updateFunc.simps getExps.simps outupd2exp_def using tmp1 tmp2 tmp3 
      by force
  qed
  have 2: "exp2ODE ''x'' [\<lambda>s. s CHR ''a'' + 2] = 
      (\<lambda>s. if CHR ''x'' = s then \<lambda>st. st CHR ''a'' + 2 else zeroExp)"
    unfolding exp2ODE.simps by simp  
  have 3: "\<forall>v1. state2vec (\<lambda>x. (if CHR ''x'' = x then \<lambda>st. st CHR ''a'' + 2 else zeroExp) 
    (vec2state v1))
    = (\<chi> x. (if x = CHR ''x'' then v1 $ CHR ''a'' + 2 else 0))"
    apply clarify subgoal for v by (smt (verit, ccfv_SIG) Cart_lambda_cong 
          state2vec_def vec2state_def zeroExp_def)
    done
  show ?thesis unfolding block2ODE.simps using 1 2 apply simp subgoal premises pre
      using 3 by presburger done
qed

lemma combine1: "[\<lambda>xl. if length xl = length (combineInputs ''b'' ''a'' CHR ''b'')
               then if length
                        (splitInputs ''b'' ''a'' CHR ''b'' xl
                          (\<lambda>s. if length s = 1 then hd s + 2 else 0)) =
                       1
                    then hd (splitInputs ''b'' ''a'' CHR ''b'' xl
                              (\<lambda>s. if length s = 1 then hd s + 2 else 0))
                    else 0
               else 0] = [\<lambda>xl. (if length xl = 1 then hd xl + 2 else 0)]"
proof -
  have 1: "length (combineInputs ''b'' ''a'' CHR ''b'') = 1"
    by simp
  have 2: "\<forall>xl. length (splitInputs ''b'' ''a'' CHR ''b'' xl
                        (\<lambda>s. if length s = 1 then hd s + 2 else 0)) = 1"
    by simp
  have 3: "\<forall>xl. length xl = 1 \<longrightarrow> (splitInputs ''b'' ''a'' CHR ''b'' xl
           (\<lambda>s. if length s = 1 then hd s + 2 else 0)) = [hd xl + 2]"
    unfolding splitInputs.simps replaceInputs.simps by force
  show ?thesis using 1 2 3 by auto
qed

value "length (combineInputs2 ''a'' ''z'')"
lemma combine2: "updateFunc2 [\<lambda>s. if length s = 1 then hd s else 0] ''a''
                (\<lambda>xl. (if length xl = 1 then hd xl + 2 else 0))
                ''z'' = [\<lambda>s. if length s = 2 then hd s else 0,
\<lambda>s. if length s = 2 then last s + 2 else 0]"
proof -
  have 1: "reviseFun [\<lambda>s. if length s = 1 then hd s else 0] ''a'' ''z'' =
  [\<lambda>xl. if length xl = 2 then hd xl else 0]"
  proof -
    have tmp1: "\<forall>s. length s = 2 \<longrightarrow> length (splitInputs ''z'' ''a'' CHR '' '' s (\<lambda>x. 0)) = 1"
      by simp
    have tmp2: "\<forall>s. length s = 2 \<longrightarrow> hd (splitInputs ''z'' ''a'' CHR '' '' s (\<lambda>x. 0)) = hd s"
      apply clarify subgoal for s by simp
      done
    show ?thesis unfolding reviseFun.simps using tmp1 tmp2 by auto
  qed
  have 2: "[\<lambda>s. if length s = length (combineInputs2 ''z'' ''a'') then if 
          length (drop (length ''z'') s) = 1 then hd (drop (length ''z'') s) + 2 else 0 else 0]
  = [\<lambda>s. if length s = 2 then last s + 2 else 0]"
  proof -
    have tmp1: "\<forall>s. length s = 2 \<longrightarrow> hd (drop 1 s) = last s"
      apply clarify subgoal for s by (metis Suc_1 add_diff_cancel_left' hd_drop_conv_nth 
            last_conv_nth length_0_conv lessI nat.simps(3) plus_1_eq_Suc)
      done
    have tmp2: "length (combineInputs2 ''z'' ''a'') = 2"
      by simp
    have tmp3: "\<forall>s. length s = 2 \<longrightarrow> length (drop (length ''a'') s) = 1"
      by auto
    show ?thesis using tmp1 tmp2 tmp3 by (metis One_nat_def length_0_conv length_Cons)
  qed
  show ?thesis unfolding updateFunc2.simps using 1 2 by auto
qed


lemma getODE'_2 : "(block2ODE (Block ''za'' ''ax'' [1, 1] 0
   (updateFunc2 [\<lambda>s. if length s = 1 then hd s else 0] ''a''
     (hd (updateFunc [\<lambda>s. if length s = 1 then hd s else 0] ''b'' CHR ''b''
           (\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))
     ''z''))) =
(\<lambda>t v. (\<chi> x. (if x = CHR ''x'' then v $ CHR ''a'' + 2 else if 
      x = CHR ''a'' then v $ CHR ''z'' else 0)))"
proof -
  have 1: "(getExps
              (updateFunc2 [\<lambda>s. if length s = 1 then hd s else 0] ''a''
                (hd (updateFunc [\<lambda>s. if length s = 1 then hd s else 0] ''b'' CHR ''b''
                      (\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))
                ''z'')
              ''za'') = [\<lambda>s. s CHR ''z'', \<lambda>s. s CHR ''a''+2]"
  proof -
    have tmp1: "(updateFunc2 [\<lambda>s. if length s = 1 then hd s else 0] ''a''
                (hd (updateFunc [\<lambda>s. if length s = 1 then hd s else 0] ''b'' CHR ''b''
                      (\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))
                ''z'') = [\<lambda>s. if length s = 2 then hd s else 0,
\<lambda>s. if length s = 2 then last s + 2 else 0]"
      unfolding updateFunc.simps using combine1 combine2 by auto
    have tmp2: "\<forall>s. (if length (map s ''az'') = 2 then hd (map s ''az'') + 2 else 0)
        = (s CHR ''a'' + 2)"
      by auto
    have tmp3: "\<forall>s. (if length (map s ''az'') = 2 then last (map s ''az'') else 0)
        = (s CHR ''z'')"
      by auto
    have tmp4: "getExps [\<lambda>s. if length s = 2 then hd s else 0,
\<lambda>s. if length s = 2 then last s + 2 else 0] ''za'' = [\<lambda>s. s CHR ''z'', \<lambda>s. s CHR ''a''+2]"
      unfolding getExps.simps outupd2exp_def using tmp2 tmp3 by auto
    show ?thesis using tmp1 tmp4 by presburger
  qed
  have 2: "exp2ODE ''ax'' [\<lambda>s. s CHR ''z'', \<lambda>s. s CHR ''a'' + 2] = 
    (\<lambda>s. if CHR ''x'' = s then \<lambda>st. st CHR ''a'' + 2 else 
    if CHR ''a'' = s then \<lambda>s. s CHR ''z'' else zeroExp)"
    unfolding exp2ODE.simps by force
  have 3: "\<forall>v1. state2vec (\<lambda>x. (if CHR ''x'' = x then \<lambda>st. st CHR ''a'' + 2
               else if CHR ''a'' = x then \<lambda>s. s CHR ''z'' else zeroExp) (vec2state v1))
    = (\<chi> x. (if x = CHR ''x'' then v1 $ CHR ''a'' + 2 else if 
      x = CHR ''a'' then v1 $ CHR ''z'' else 0))"
    apply clarify subgoal for v by (smt (verit, ccfv_SIG) Cart_lambda_cong 
          state2vec_def vec2state_def zeroExp_def)
    done
  show ?thesis unfolding block2ODE.simps using 1 2 apply simp subgoal premises pre
      using 3 by presburger done
qed

lemma base1: "((\<lambda>x. \<chi> y. if y = CHR ''x'' then 2 * x else if y = CHR ''b'' then 2 else 0) has_vderiv_on
     (\<lambda>t. \<chi> x. if x = CHR ''x''
               then (\<chi> y. if y = CHR ''x'' then 2 * t else if y = CHR ''b'' then 2 else 0) $
                    CHR ''a'' +
                    2
               else if x = CHR ''a''
                    then (\<chi> y. if y = CHR ''x'' then 2 * t else if y = CHR ''b'' then 2 else 0) $
                         CHR ''z''
                    else 0))
     {0--1}"
  unfolding has_vderiv_on_def apply clarify subgoal premises pre for x
proof -
  have 1: "\<forall>i. ((\<lambda>t. (\<chi> y. if y = CHR ''x'' then 2 * t else if y = CHR ''b'' then 2 else 0) $
              i) has_vector_derivative
         (\<chi> xa. if xa = CHR ''x''
                then (\<chi> y. if y = CHR ''x'' then 2 * x else if y = CHR ''b'' then 2 else 0) $
                     CHR ''a'' +
                     2
                else if xa = CHR ''a''
                     then (\<chi> y. if y = CHR ''x'' then 2 * x else if y = CHR ''b'' then 2 else 0) $
                          CHR ''z''
                     else 0) $
         i)
         (at x within {0--1})"
    apply clarify subgoal for i
    proof(cases "i = CHR ''x''")
      case True
      then show ?thesis apply simp
        by (auto simp: has_vderiv_on_def intro!: derivative_eq_intros)
    next
      case False
      then show ?thesis by simp
    qed
    done
  show ?thesis 
    using has_vector_derivative_projI[of "(\<lambda>x. \<chi> y. if y = CHR ''x'' then 2 * x else if y = CHR ''b'' then 2 else 0)" 
        "(\<lambda>t. \<chi> x. if x = CHR ''x''
               then (\<chi> y. if y = CHR ''x'' then 2 * t else if y = CHR ''b'' then 2 else 0) $
                    CHR ''a'' +
                    2
               else if x = CHR ''a''
                    then (\<chi> y. if y = CHR ''x'' then 2 * t else if y = CHR ''b'' then 2 else 0) $
                         CHR ''z''
                    else 0)" x "{0--1}"] 1 pre by blast
  qed
  done

lemma base2: "(\<lambda>x. \<chi> y. if y = CHR ''x'' then 2 * x else if y = CHR ''b'' then 2 else 0) \<in> {0--1} \<rightarrow> UNIV"
  by simp

lemma base3: "((\<lambda>x. \<chi> y. if y = CHR ''x'' then 2 * x
               else if y = CHR ''b'' then 2
                    else if y = CHR ''y'' then 4 else if y = CHR ''s'' then 4 else 0) has_vderiv_on
     (\<lambda>t. \<chi> x. if x = CHR ''x''
               then (\<chi> y. if y = CHR ''x'' then 2 * t
                          else if y = CHR ''b'' then 2
                               else if y = CHR ''y'' then 4 else if y = CHR ''s'' then 4 else 0) $
                    CHR ''a'' +
                    2
               else if x = CHR ''a''
                    then (\<chi> y. if y = CHR ''x'' then 2 * t
                               else if y = CHR ''b'' then 2
                                    else if y = CHR ''y'' then 4
                                         else if y = CHR ''s'' then 4 else 0) $
                         CHR ''z''
                    else 0))
     {1--2}"
  unfolding has_vderiv_on_def apply clarify subgoal premises pre for x
proof -
  have 1: "\<forall>i. ((\<lambda>t. (\<chi> y. if y = CHR ''x'' then 2 * t
                    else if y = CHR ''b'' then 2
                         else if y = CHR ''y'' then 4 else if y = CHR ''s'' then 4 else 0) $
              i) has_vector_derivative
         (\<chi> xa. if xa = CHR ''x''
                then (\<chi> y. if y = CHR ''x'' then 2 * x
                           else if y = CHR ''b'' then 2
                                else if y = CHR ''y'' then 4 else if y = CHR ''s'' then 4 else 0) $
                     CHR ''a'' +
                     2
                else if xa = CHR ''a''
                     then (\<chi> y. if y = CHR ''x'' then 2 * x
                                else if y = CHR ''b'' then 2
                                     else if y = CHR ''y'' then 4
                                          else if y = CHR ''s'' then 4 else 0) $
                          CHR ''z''
                     else 0) $
         i)
         (at x within {1--2})"
    apply clarify subgoal for i
    proof(cases "i = CHR ''x''")
      case True
      then show ?thesis apply simp
        by (auto simp: has_vderiv_on_def intro!: derivative_eq_intros)
    next
      case False
      then show ?thesis by simp
    qed
    done
  show ?thesis 
    using has_vector_derivative_projI[of "(\<lambda>x. \<chi> y. if y = CHR ''x'' then 2 * x
               else if y = CHR ''b'' then 2
                    else if y = CHR ''y'' then 4 else if y = CHR ''s'' then 4 else 0)" 
              "(\<lambda>t. \<chi> x. if x = CHR ''x''
               then (\<chi> y. if y = CHR ''x'' then 2 * t
                          else if y = CHR ''b'' then 2
                               else if y = CHR ''y'' then 4 else if y = CHR ''s'' then 4 else 0) $
                    CHR ''a'' +
                    2
               else if x = CHR ''a''
                    then (\<chi> y. if y = CHR ''x'' then 2 * t
                               else if y = CHR ''b'' then 2
                                    else if y = CHR ''y'' then 4
                                         else if y = CHR ''s'' then 4 else 0) $
                         CHR ''z''
                    else 0)" x "{1--2}"] 1 pre by blast
  qed
  done

lemma base4: "(\<lambda>x. \<chi> y. if y = CHR ''x'' then 2 * x
              else if y = CHR ''b'' then 2
                   else if y = CHR ''y'' then 4 else if y = CHR ''s'' then 4 else 0)
    \<in> {1--2} \<rightarrow> UNIV"
  by simp

lemma base5: "((\<lambda>x. \<chi> y. if y = CHR ''x'' then 2 * x * x - 6 * x + 8
               else if y = CHR ''b'' then 2
                    else if y = CHR ''z'' then 4
                         else if y = CHR ''a'' then 4 * (x - 2)
                              else if y = CHR ''y'' then 8
                                   else if y = CHR ''s'' then 8 else 0) has_vderiv_on
     (\<lambda>t. \<chi> x. if x = CHR ''x''
               then (\<chi> y. if y = CHR ''x'' then 2 * t * t - 6 * t + 8
                          else if y = CHR ''b'' then 2
                               else if y = CHR ''z'' then 4
                                    else if y = CHR ''a'' then 4 * (t - 2)
                                         else if y = CHR ''y'' then 8
                                              else if y = CHR ''s'' then 8 else 0) $
                    CHR ''a'' +
                    2
               else if x = CHR ''a''
                    then (\<chi> y. if y = CHR ''x'' then 2 * t * t - 6 * t + 8
                               else if y = CHR ''b'' then 2
                                    else if y = CHR ''z'' then 4
                                         else if y = CHR ''a'' then 4 * (t - 2)
                                              else if y = CHR ''y'' then 8
else if y = CHR ''s'' then 8 else 0) $
                         CHR ''z''
                    else 0))
     {2--3}"
  unfolding has_vderiv_on_def apply clarify subgoal premises pre for x
proof -
  have 1: "\<forall>i. ((\<lambda>t. (\<chi> y. if y = CHR ''x'' then 2 * t * t - 6 * t + 8
                    else if y = CHR ''b'' then 2
                         else if y = CHR ''z'' then 4
                              else if y = CHR ''a'' then 4 * (t - 2)
                                   else if y = CHR ''y'' then 8
                                        else if y = CHR ''s'' then 8 else 0) $
              i) has_vector_derivative
         (\<chi> xa. if xa = CHR ''x''
                then (\<chi> y. if y = CHR ''x'' then 2 * x * x - 6 * x + 8
                           else if y = CHR ''b'' then 2
                                else if y = CHR ''z'' then 4
                                     else if y = CHR ''a'' then 4 * (x - 2)
                                          else if y = CHR ''y'' then 8
                                               else if y = CHR ''s'' then 8 else 0) $
                     CHR ''a'' +
                     2
                else if xa = CHR ''a''
                     then (\<chi> y. if y = CHR ''x'' then 2 * x * x - 6 * x + 8
                                else if y = CHR ''b'' then 2
                                     else if y = CHR ''z'' then 4
                                          else if y = CHR ''a'' then 4 * (x - 2)
                                               else if y = CHR ''y'' then 8
 else if y = CHR ''s'' then 8 else 0) $
                          CHR ''z''
                     else 0) $
         i)
         (at x within {2--3})"
    apply clarify subgoal for i
    proof(cases "i = CHR ''x''")
      case True
      then show ?thesis apply simp
        by (auto simp: has_vderiv_on_def intro!: derivative_eq_intros)
    next
      case False
      note F1 = False
      then show ?thesis
      proof(cases "i = CHR ''b''")
        case True
        then show ?thesis by simp
      next
        case False
        note F2 = False
        then show ?thesis
        proof(cases "i = CHR ''a''")
          case True
          then show ?thesis apply simp
            by (auto simp: has_vderiv_on_def intro!: derivative_eq_intros)
        next
          case False
          note F3 = False
          then show ?thesis
          proof(cases "i = CHR ''z''")
            case True
            then show ?thesis by simp
          next
            case False
            then show ?thesis using F1 F2 F3 by simp
          qed
        qed
      qed
    qed
    done
  show ?thesis 
    using has_vector_derivative_projI[of "(\<lambda>x. \<chi> y. if y = CHR ''x'' then 2 * x * x - 6 * x + 8
               else if y = CHR ''b'' then 2
                    else if y = CHR ''z'' then 4
                         else if y = CHR ''a'' then 4 * (x - 2)
                              else if y = CHR ''y'' then 8
                                   else if y = CHR ''s'' then 8 else 0)" 
            "(\<lambda>t. \<chi> x. if x = CHR ''x''
               then (\<chi> y. if y = CHR ''x'' then 2 * t * t - 6 * t + 8
                          else if y = CHR ''b'' then 2
                               else if y = CHR ''z'' then 4
                                    else if y = CHR ''a'' then 4 * (t - 2)
                                         else if y = CHR ''y'' then 8
                                              else if y = CHR ''s'' then 8 else 0) $
                    CHR ''a'' +
                    2
               else if x = CHR ''a''
                    then (\<chi> y. if y = CHR ''x'' then 2 * t * t - 6 * t + 8
                               else if y = CHR ''b'' then 2
                                    else if y = CHR ''z'' then 4
                                         else if y = CHR ''a'' then 4 * (t - 2)
                                              else if y = CHR ''y'' then 8
else if y = CHR ''s'' then 8 else 0) $
                         CHR ''z''
                    else 0)" x "{2--3}"] 1 pre by blast
  qed
  done

lemma base6: "(\<lambda>x. \<chi> y. if y = CHR ''x'' then 2 * x * x - 6 * x + 8
              else if y = CHR ''b'' then 2
                   else if y = CHR ''z'' then 4
                        else if y = CHR ''a'' then 4 * (x - 2)
                             else if y = CHR ''y'' then 8 else if y = CHR ''s'' then 8 else 0)
    \<in> {2--3} \<rightarrow> UNIV"
  by simp

definition h1:: timed_vars where "h1 = (\<lambda>v t. (if v = CHR ''b'' \<and> t \<ge> 0 \<and> t < 1 then 2 else 
if v = CHR ''x'' \<and> t \<ge> 0 \<and> t \<le> 1 then 2*t else h v t))"

\<comment> \<open>t \<in> {0--1}\<close>
lemma solves1: "((\<lambda>x. \<chi> y. if y = CHR ''x'' then 2 * x else 
if y = CHR ''b'' then 2 else 0) solves_ode 
  (\<lambda>t v. (\<chi> x.(if x = CHR ''x'' then v $ CHR ''a'' + 2 else 
  if x = CHR ''a'' then v $ CHR ''z'' else 0)))) {(0::real) -- (1::real)} UNIV"
  unfolding solves_ode_def using base1 base2 by auto

definition Vec0 :: "vec" where "Vec0 = (\<chi> x. (if x = CHR ''b'' then 2 else 0))"

lemma get_Vec0: "(state2vec (timedVar2State h' 0)) = Vec0"
  unfolding timedVar2State_def Vec0_def state2vec_def h'_def h_def by fastforce

lemma solves1_fixedpoint: "\<exists>L. unique_on_bounded_closed 0 {0--1} Vec0 
  (\<lambda>t v. (\<chi> x.(if x = CHR ''x'' then v $ CHR ''a'' + 2 else 
  if x = CHR ''a'' then v $ CHR ''z'' else 0))) UNIV L \<Longrightarrow>
\<forall>t \<in> {0 -- 1}. (\<lambda>x. \<chi> y. if y = CHR ''x'' then 2 * x else 
if y = CHR ''b'' then 2 else 0) t = 
(unique_on_bounded_closed.fixed_point 0 {0--1} Vec0 
(\<lambda>t v. (\<chi> x.(if x = CHR ''x'' then v $ CHR ''a'' + 2 else 
  if x = CHR ''a'' then v $ CHR ''z'' else 0))) UNIV) t"
  subgoal premises pre
proof -
  have 1: "(\<lambda>x. \<chi> y. if y = CHR ''x'' then 2 * x else 
if y = CHR ''b'' then 2 else 0) 0 = Vec0"
    unfolding Vec0_def by auto
  show ?thesis using solves1 unique_on_bounded_closed.solves_ode_equals_fixed_point 1 pre by blast
qed
  done

\<comment> \<open>t \<in> {1--2}\<close>
lemma solves2: "((\<lambda>x. \<chi> y. if y = CHR ''x'' then 2 * x else if y = CHR ''b'' then 2 
      else if y = CHR ''y'' then 4 else if y = CHR ''s'' then 4 else 0) solves_ode 
  (\<lambda>t v. (\<chi> x.(if x = CHR ''x'' then v $ CHR ''a'' + 2 else 
  if x = CHR ''a'' then v $ CHR ''z'' else 0)))) {(1::real) -- (2::real)} UNIV"
  unfolding solves_ode_def using base3 base4 by auto

definition h2::timed_vars where "h2 = (\<lambda>v t. if v = CHR ''b'' \<and> t = 1 then 2 else
(if v = CHR ''y'' \<and> t = 1 then 4 else (if v = CHR ''s'' \<and> t = 1 then 4 else h1 v t)))"

definition h2'::timed_vars where "h2' = (\<lambda>vv tt. if 1 < tt \<and> tt < 2 \<and> vv = CHR ''y'' then 4 else 
  if 1 < tt \<and> tt < 2 \<and> vv = CHR ''s'' then 4 else h2 vv tt)"

definition Vec1 :: "vec" where "Vec1 = (\<chi> x.(if x = CHR ''x'' then 2 else if x = CHR ''b'' then 2 
else if x = CHR ''y'' then 4 else if x = CHR ''s'' then 4 else 0))"

lemma get_Vec1: "(state2vec (timedVar2State h2 1)) = Vec1"
  unfolding timedVar2State_def h2_def h1_def Vec1_def state2vec_def h_def by fastforce

lemma solves2_fixedpoint: "\<exists>L. unique_on_bounded_closed 1 {1--2} Vec1 
  (\<lambda>t v. (\<chi> x.(if x = CHR ''x'' then v $ CHR ''a'' + 2 else 
  if x = CHR ''a'' then v $ CHR ''z'' else 0))) UNIV L \<Longrightarrow>
\<forall>t \<in> {1 -- 2}. (\<lambda>x. \<chi> y. if y = CHR ''x'' then 2 * x else if y = CHR ''b'' then 2 
      else if y = CHR ''y'' then 4 else if y = CHR ''s'' then 4 else 0) t = 
(unique_on_bounded_closed.fixed_point 1 {1--2} Vec1
(\<lambda>t v. (\<chi> x.(if x = CHR ''x'' then v $ CHR ''a'' + 2 else 
  if x = CHR ''a'' then v $ CHR ''z'' else 0))) UNIV) t"
  subgoal premises pre
proof -
  have 1: "(\<lambda>x. \<chi> y. if y = CHR ''x'' then 2 * x else if y = CHR ''b'' then 2 
      else if y = CHR ''y'' then 4 else if y = CHR ''s'' then 4 else 0) 1 = Vec1"
    unfolding Vec1_def by auto
  show ?thesis using solves2 unique_on_bounded_closed.solves_ode_equals_fixed_point 1 pre by blast
qed
  done

\<comment> \<open>t \<in> {2--3}\<close>
lemma solves3: "((\<lambda>x. (\<chi> y.(if y = CHR ''x'' then 2*x*x - 6*x + 8
  else if y = CHR ''b'' then 2 else if
  y = CHR ''z'' then 4 else if y = CHR ''a'' then 4*(x-2) 
  else if y = CHR ''y'' then 8 else if y = CHR ''s'' then 8 else 0)))  solves_ode 
  (\<lambda>t v. (\<chi> x.(if x = CHR ''x'' then v $ CHR ''a'' + 2 else
  if x = CHR ''a'' then v $ CHR ''z'' else 0)))) {(2::real) -- (3::real)} UNIV"
  unfolding solves_ode_def using base5 base6 by auto

definition h3:: timed_vars where "h3 = (\<lambda>v t. (if v = CHR ''b'' \<and> t > 1 \<and> t < 2 then 2 else 
(if v = CHR ''x'' \<and> t \<ge> 1 \<and> t \<le> 2 then 2*t else h2' v t)))"
definition h4::timed_vars where "h4 = (\<lambda>v t. if v = CHR ''b'' \<and> t = 2 then 2 else
(if v = CHR ''y'' \<and> t = 2 then 8 else (if v = CHR ''s'' \<and> t = 2 then 8 else 
if v = CHR ''z'' \<and> t = 2 then 4 else h3 v t)))"
definition h4'::timed_vars where "h4' = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t > 2 \<and> t < 3 then 8 else (if v = CHR ''s'' \<and> t > 2 \<and> t < 3 then 8 else 
if v = CHR ''z'' \<and> t > 2 \<and> t < 3 then 4 else h4 v t)))"

definition Vec2 :: "vec" where "Vec2 = (\<chi> x.(if x = CHR ''x'' then 4 else if x = CHR ''b'' then 2 
else if x = CHR ''z'' then 4 else if x = CHR ''y'' then 8 else if x = CHR ''s'' then 8 else 0))"

lemma getVec2: "(state2vec (timedVar2State h4 2)) = Vec2"
  unfolding Vec2_def h4_def h3_def h1_def h2'_def h2_def h_def timedVar2State_def state2vec_def by auto

lemma solves3_fixedpoint: "\<exists>L. unique_on_bounded_closed 2 {2--3} Vec2 
  (\<lambda>t v. (\<chi> x.(if x = CHR ''x'' then v $ CHR ''a'' + 2 else 
  if x = CHR ''a'' then v $ CHR ''z'' else 0))) UNIV L \<Longrightarrow>
\<forall>t \<in> {2 -- 3}. (\<lambda>x. (\<chi> y.(if y = CHR ''x'' then 2*x*x - 6*x + 8
  else if y = CHR ''b'' then 2 else if
  y = CHR ''z'' then 4 else if y = CHR ''a'' then 4*(x-2) 
  else if y = CHR ''y'' then 8 else if y = CHR ''s'' then 8 else 0))) t = 
(unique_on_bounded_closed.fixed_point 2 {2--3} Vec2
(\<lambda>t v. (\<chi> x.(if x = CHR ''x'' then v $ CHR ''a'' + 2 else 
  if x = CHR ''a'' then v $ CHR ''z'' else 0))) UNIV) t"
  subgoal premises pre
proof -
  have 1: "(\<lambda>x. (\<chi> y.(if y = CHR ''x'' then 2*x*x - 6*x + 8
  else if y = CHR ''b'' then 2 else if
  y = CHR ''z'' then 4 else if y = CHR ''a'' then 4*(x-2) 
  else if y = CHR ''y'' then 8 else if y = CHR ''s'' then 8 else 0))) 2 = Vec2"
    unfolding Vec2_def by auto
  show ?thesis using solves3 unique_on_bounded_closed.solves_ode_equals_fixed_point 1 pre by blast
qed
  done

value "(map (\<lambda>a. h1 a (real 1 - real 0)) ''x'')"

lemma exe1_0: "exeCalBlks [Bias] 
(\<lambda>v t. (if v = CHR ''x'' \<and> t \<ge> 0 \<and> t \<le> 1 then 2*t else h' v t)) 0 1 = (\<lambda>v t. (if 
v = CHR ''b'' \<and> t > 0 \<and> t < 1 then 2 else if v = CHR ''x'' \<and> t \<ge> 0 \<and> t \<le> 1 then 2*t else h' v t))"
proof -
  have 1: "\<forall>tt. length (map (\<lambda>a. if a = CHR ''x'' \<and> 0 \<le> tt \<and> tt \<le> 1 then 2 * tt
                           else if tt = 0 \<and> a = CHR ''b'' then 2 else 0) ''a'') = 1"
    by auto
  have 2: "\<forall>tt. hd (map (\<lambda>a. if a = CHR ''x'' \<and> 0 \<le> tt \<and> tt \<le> 1 then 2 * tt
                               else if tt = 0 \<and> a = CHR ''b'' then 2 else 0) ''a'') = (0::real)"
    by auto
  have 3: "\<forall>v t. (\<lambda>vv tt.
        if vv = CHR ''b'' \<and> tt < 1 \<and> 0 < tt
        then if length
                 (map (\<lambda>a. if a = CHR ''x'' \<and> 0 \<le> tt \<and> tt \<le> 1 then 2 * tt
                           else if tt = 0 \<and> a = CHR ''b'' then 2 else 0)
                   ''a'') =
                Suc 0
             then hd (map (\<lambda>a. if a = CHR ''x'' \<and> 0 \<le> tt \<and> tt \<le> 1 then 2 * tt
                               else if tt = 0 \<and> a = CHR ''b'' then 2 else 0)
                       ''a'') +
                  2::real
             else 0
        else if vv = CHR ''x'' \<and> 0 \<le> tt \<and> tt \<le> 1 then 2 * tt
             else if tt = 0 \<and> vv = CHR ''b'' then 2 else 0) v t = (\<lambda>v t. if v = CHR ''b'' \<and> 0 < t \<and> t < 1 then 2
           else if v = CHR ''x'' \<and> 0 \<le> t \<and> t \<le> 1 then 2 * t
                else if t = 0 \<and> v = CHR ''b'' then 2 else 0) v t"
    apply clarify subgoal for v t 
    proof(cases "v = CHR ''b'' \<and> t < 1 \<and> 0 < t")
      case True
      have tmp1: "(if v = CHR ''b'' \<and> 0 < t \<and> t < 1 then 2
     else if v = CHR ''x'' \<and> 0 \<le> t \<and> t \<le> 1 then 2 * t else 0) = 2"
        using True by auto
      have tmp2: "length (map (\<lambda>a. if a = CHR ''x'' \<and> 0 \<le> t \<and> t \<le> 1 then 2 * t else 0) ''a'') = 1"
        using 1 by auto
      have tmp3: "(if v = CHR ''b'' \<and> t < 1 \<and> 0 < t
     then if length
              (map (\<lambda>a. if a = CHR ''x'' \<and> 0 \<le> t \<and> t \<le> 1 then 2 * t
                        else if t = 0 \<and> a = CHR ''b'' then 2 else 0)
                ''a'') =
             Suc 0
          then hd (map (\<lambda>a. if a = CHR ''x'' \<and> 0 \<le> t \<and> t \<le> 1 then 2 * t
                            else if t = 0 \<and> a = CHR ''b'' then 2 else 0)
                    ''a'') +
               2::real
          else 0
     else if v = CHR ''x'' \<and> 0 \<le> t \<and> t \<le> 1 then 2 * t
          else if t = 0 \<and> v = CHR ''b'' then 2 else 0) = 2"
        using True by simp
      then show ?thesis using tmp3 by presburger
    next
      case False
      note F1 = False
      then show ?thesis by presburger
    qed
    done
  show ?thesis unfolding exeCalBlks.simps Bias_def h'_def h_def apply simp using 3 by auto
qed

value "sortDiag [Gain,UD1,UD2,Bias]"
lemma sort_lemma: "sortDiag [Gain,UD1,UD2,Bias] = [Gain,UD1,UD2,Bias]"
proof -
  have 1: "get_block_indegree Bias [Gain, UD1, UD2, Bias] = {}"
    unfolding get_block_indegree_def Bias_def Gain_def UD1_def UD2_def by auto
  have 2: "get_block_indegree UD2 [Gain, UD1, UD2, Bias] = {}"
    unfolding get_block_indegree_def Bias_def Gain_def UD1_def UD2_def by auto
  have 3: "get_block_indegree UD1 [Gain, UD1, UD2, Bias] = {CHR ''y''}"
    unfolding get_block_indegree_def Bias_def Gain_def UD1_def UD2_def by auto
  have 4: "get_block_indegree Gain [Gain, UD1, UD2, Bias] = {}"
    unfolding get_block_indegree_def Bias_def Gain_def UD1_def UD2_def by auto
  show ?thesis unfolding sortDiag_def using topological_sort.simps[of "[Gain,UD1,UD2,Bias]" 
      "[Gain,UD1,UD2,Bias]" "[]"] unfolding find_0indegree_blocks.simps using 1 2 3 4 apply simp
    unfolding Bias_def Gain_def UD1_def UD2_def by auto
qed

lemma exe0_1: "\<forall>v. exeDisDiag_attime [Gain] h 0 v 0 = h v 0"
  apply clarify subgoal for v
  proof -
    have 1: "(\<exists>k. 0 = get_sample_time Gain * k)"
    proof -
      have tmp1: "get_sample_time Gain = 1"
        using Gain_def get_sample_time.simps by (metis (no_types, lifting))
      have tmp2: "int 1 = get_sample_time Gain * 1"
        using tmp1 by simp
      show ?thesis using tmp2 by simp
    qed
    have 2: "(exeDisDiag_attime [] h 0) = h"
      using exeDisDiag_attime.simps(1)[of h 0] by simp
    have 3: "get_inputs Gain = ''x''"
      using Gain_def get_inputs.simps by (metis (no_types, lifting))
    have 4: "get_outputs Gain = ''y''"
      using Gain_def get_outputs.simps by (metis (no_types, lifting))
    have 5: "get_offsets Gain = [0]"
      using Gain_def get_offsets.simps by (metis (no_types, lifting))
    have 6: "get_outupd Gain = [\<lambda>s. if length s = 1 then 2 * hd s else 0]"
      using Gain_def get_outupd.simps by (metis (no_types, lifting))
    have 7: "\<forall>v t. outupd_exe_atst ''x'' ''y'' [0] [\<lambda>s. if length s = 1 then 2 * hd s else 0]
         h 0 v t = h v t"
    proof -
      have tmp1: "\<forall>h. outupd_exe_atst ''x'' [] [] [] h 0 = h"
        by auto
      have tmp2: "\<forall>v t. (\<lambda>vv tt.
       if tt = real 0 \<and> vv = CHR ''y''
       then if length (map (\<lambda>a. h a (real 0 - real 0)) ''x'') = 1
            then 2 * hd (map (\<lambda>a. h a (real 0 - real 0)) ''x'') else 0
       else h vv tt) v t = h v t"
        apply clarify subgoal for v t using h1_def h_def by (smt (verit, ccfv_SIG) One_nat_def 
              add.commute hd_map length_map list.sel(1) list.size(3) list.size(4) of_nat_0 
              of_nat_1 plus_1_eq_Suc)
        done
      show ?thesis using outupd_exe_atst.simps(4)[of "''x''" "CHR ''y''" "[]" 0 "[]" "
        \<lambda>s. if length s = 1 then 2 * hd s else 0" "[]" h 0] using tmp1 tmp2 by presburger
    qed
    show ?thesis using exeDisDiag_attime.simps(2)[of "Gain" "[]" h1 0] using 1 2 3 4 5 6 7
      by simp
  qed
  done

lemma exe0_2: "\<forall>v. exeDisDiag_attime [UD1, Gain] h 0 v 0 = h v 0"
  apply clarify subgoal for v
  proof -
    have 1: "(\<exists>k. 0 = get_sample_time UD1 * k)"
    proof -
      have tmp1: "get_sample_time UD1 = 1"
        using UD1_def get_sample_time.simps by (metis (no_types, lifting))
      have tmp2: "0 = get_sample_time UD1 * 0"
        using tmp1 by simp
      show ?thesis using tmp2 by simp
    qed
    have 2: "(exeDisDiag_attime [] h 0) = h"
      using exeDisDiag_attime.simps(1)[of h 0] by simp
    have 3: "get_inputs UD1 = ''y''"
      using UD1_def get_inputs.simps by (metis (no_types, lifting))
    have 4: "get_outputs UD1 = ''s''"
      using UD1_def get_outputs.simps by (metis (no_types, lifting))
    have 5: "get_offsets UD1 = [0]"
      using UD1_def get_offsets.simps by (metis (no_types, lifting))
    have 6: "get_outupd UD1 = [\<lambda>s. if length s = 1 then hd s else 0]"
      using UD1_def get_outupd.simps by (metis (no_types, lifting))
    have 7: "\<forall>v t. outupd_exe_atst ''y'' ''s'' [0] [\<lambda>s. if length s = 1 then hd s else 0]
         h 0 v t = h v t"
    proof -
      have tmp1: "\<forall>h. outupd_exe_atst ''y'' [] [] [] h 0 = h"
        by auto
      have tmp2: "\<forall>v t. (\<lambda>vv tt.
       if tt = real 0 \<and> vv = CHR ''s''
       then if length (map (\<lambda>a. h a (real 0 - real 0)) ''y'') = 1
            then hd (map (\<lambda>a. h a (real 0 - real 0)) ''y'') else 0
       else h vv tt) v t = h v t"
        apply clarify subgoal for v t using h1_def h_def by (smt (verit, ccfv_SIG) One_nat_def 
              add.commute hd_map length_map list.sel(1) list.size(3) list.size(4) of_nat_0 
              of_nat_1 plus_1_eq_Suc)
        done
      show ?thesis using outupd_exe_atst.simps(4)[of "''y''" "CHR ''s''" "[]" 0 "[]" "
        \<lambda>s. if length s = 1 then hd s else 0" "[]" "h"
            0] using tmp1 tmp2 by presburger
    qed
    show ?thesis using exeDisDiag_attime.simps(2)[of "UD1" "[Gain]" h 0] using 1 2 3 4 5 6 7
      exe0_1 by (smt (verit, best) hd_map int_ops(1) length_map list.distinct(1) 
          outupd_exe_atst.simps(1) outupd_exe_atst.simps(4))
  qed
  done


lemma exe0_3: "\<forall>v. exeDisDiag_attime [UD2, UD1, Gain] h 0 v 0 = h v 0"
  apply clarify subgoal for v
  proof -
    have 1: "(\<exists>k. int 0 = get_sample_time UD2 * k)"
    proof -
      have tmp1: "get_sample_time UD2 = 1"
        using UD2_def get_sample_time.simps by (metis (no_types, lifting))
      have tmp2: "int 1 = get_sample_time UD2 * 1"
        using tmp1 by simp
      show ?thesis using tmp2 by simp
    qed
    have 2: "(exeDisDiag_attime [] h 0) = h"
      using exeDisDiag_attime.simps(1)[of h1 1] by simp
    have 3: "get_inputs UD2 = ''s''"
      using UD2_def get_inputs.simps by (metis (no_types, lifting))
    have 4: "get_outputs UD2 = ''z''"
      using UD2_def get_outputs.simps by (metis (no_types, lifting))
    have 5: "get_offsets UD2 = [1]"
      using UD2_def get_offsets.simps by (metis (no_types, lifting))
    have 6: "get_outupd UD2 = [\<lambda>s. if length s = 1 then hd s else 0]"
      using UD2_def get_outupd.simps by (metis (no_types, lifting))
    have 7: "\<forall>v t. outupd_exe_atst ''s'' ''z'' [1] [\<lambda>s. if length s = 1 then hd s else 0] 
      h 0 v t = h v t"
    proof -
      have tmp1: "\<forall>h. outupd_exe_atst ''s'' [] [] [] h 0 = h"
        by auto
      have tmp2: "\<forall>v t. (\<lambda>vv tt.
       if tt = real 0 \<and> vv = CHR ''z''
       then if length (map (\<lambda>a. h a (real 0 - real 1)) ''s'') = 1
            then hd (map (\<lambda>a. h a (real 0 - real 1)) ''s'') else 0
       else h vv tt) v t = h v t"
        apply clarify subgoal for v t using h1_def h_def apply simp
          using char.inject by presburger
        done
      show ?thesis using outupd_exe_atst.simps(4)[of "''s''" "CHR ''z''" "[]" 1 "[]" "
        \<lambda>s. if length s = 1 then hd s else 0" "[]" h
            0] using tmp1 tmp2 by presburger
    qed
    show ?thesis using exeDisDiag_attime.simps(2)[of "UD2" "[UD1, Gain]" h 0] using 1 2 3 4 5 6 7
      exe0_2 by (smt (z3) One_nat_def exeDisDiag_attime_lemma2 hd_map length_map 
          list.distinct(1) outupd_exe_atst.simps(1) outupd_exe_atst.simps(4))
  qed
  done

lemma exe0_4: "exeDisDiag_attime [Bias, UD2, UD1, Gain] h 0 = h'"
  proof -
    have 1: "get_sample_time Bias = 0"
    proof -
      show ?thesis unfolding Bias_def by simp
    qed
    have 2: "(exeDisDiag_attime [] h 0) = h"
      using exeDisDiag_attime.simps(1)[of h1 1] by simp
    have 3: "get_inputs Bias = ''a''"
      using Bias_def get_inputs.simps by (metis (no_types, lifting))
    have 4: "get_outputs Bias = ''b''"
      using Bias_def get_outputs.simps by (metis (no_types, lifting))
    have 5: "get_offsets Bias = [0]"
      using Bias_def get_offsets.simps by (metis (no_types, lifting))
    have 6: "get_outupd Bias = [(\<lambda>s. (if length s = 1 then (hd s + 2::real) else 0))]"
      using Bias_def get_outupd.simps by (metis (no_types, lifting))
    have 7: "\<forall>v t. outupd_exe_atst ''a'' ''b'' [0] [(\<lambda>s. (if length s = 1 then (hd s + 2::real) else 0))]
 h 0 v t = h' v t"
    proof -
      have tmp1: "\<forall>h. outupd_exe_atst ''a'' [] [] [] h 0 = h"
        by auto
      have tmp2: "\<forall>v t. (\<lambda>vv tt.
       if tt = real 0 \<and> vv = CHR ''b''
       then if length (map (\<lambda>a. h a (real 0 - real 0)) ''a'') = 1
            then hd (map (\<lambda>a. h a (real 0 - real 0)) ''a'') + 2 else 0
       else h vv tt) 
      v t = h' v t"
        apply clarify subgoal for v t using h'_def h_def apply simp
          using char.inject by (smt (z3))
        done
      show ?thesis using outupd_exe_atst.simps(4)[of "''a''" "CHR ''b''" "[]" 0 "[]" "
        \<lambda>s. (if length s = 1 then (hd s + 2::real) else 0)" "[]" h 0] using tmp1 tmp2 by presburger
    qed
    have 8: "(exeDisDiag_attime [UD2, UD1, Gain] h 0) = h"
    proof -
      have tmp1: "\<forall>v t. (exeDisDiag_attime [UD2, UD1, Gain] h 0) v t = h v t"
        using exe0_3 exeDisDiag_attime_lemma2 by (metis of_nat_0)
      show ?thesis using tmp1 by blast
    qed
    have 9: "outupd_exe_atst ''a'' ''b'' [0] [(\<lambda>s. (if length s = 1 then (hd s + 2::real) else 0))]
      h 0 = h'"
      using 7 by presburger
    show ?thesis using exeDisDiag_attime.simps(2)[of "Bias" "[UD2, UD1, Gain]" h1 1] 
      using 1 2 3 4 5 6 8 9 by auto
  qed

lemma exe1_1: "\<forall>v. exeDisDiag_attime [Gain] h1 (Suc 0) v 1 = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 1 then 4 else h1 v t)) v 1"
  apply clarify subgoal for v
  proof -
    have 1: "(\<exists>k. int 1 = get_sample_time Gain * k)"
    proof -
      have tmp1: "get_sample_time Gain = 1"
        using Gain_def get_sample_time.simps by (metis (no_types, lifting))
      have tmp2: "int 1 = get_sample_time Gain * 1"
        using tmp1 by simp
      show ?thesis using tmp2 by simp
    qed
    have 2: "(exeDisDiag_attime [] h1 1) = h1"
      using exeDisDiag_attime.simps(1)[of h1 1] by simp
    have 3: "get_inputs Gain = ''x''"
      using Gain_def get_inputs.simps by (metis (no_types, lifting))
    have 4: "get_outputs Gain = ''y''"
      using Gain_def get_outputs.simps by (metis (no_types, lifting))
    have 5: "get_offsets Gain = [0]"
      using Gain_def get_offsets.simps by (metis (no_types, lifting))
    have 6: "get_outupd Gain = [\<lambda>s. if length s = 1 then 2 * hd s else 0]"
      using Gain_def get_outupd.simps by (metis (no_types, lifting))
    have 7: "\<forall>v t. outupd_exe_atst ''x'' ''y'' [0] [\<lambda>s. if length s = 1 then 2 * hd s else 0]
         h1 1 v t = (\<lambda>v t. (if v = CHR ''y'' \<and> t = 1 then 4 else h1 v t)) v t"
    proof -
      have tmp1: "\<forall>h. outupd_exe_atst ''x'' [] [] [] h 1 = h"
        by auto
      have tmp2: "\<forall>v t. (\<lambda>vv tt.
       if tt = real 1 \<and> vv = CHR ''y''
       then if length (map (\<lambda>a. h1 a (real 1 - real 0)) ''x'') = 1
            then 2 * hd (map (\<lambda>a. h1 a (real 1 - real 0)) ''x'') else 0
       else h1 vv tt) v t = (\<lambda>vv tt. (if vv = CHR ''y'' \<and> tt = 1 then 4 else h1 vv tt)) v t"
        apply clarify subgoal for v t using h1_def h_def by (smt (verit, ccfv_SIG) One_nat_def 
              add.commute hd_map length_map list.sel(1) list.size(3) list.size(4) of_nat_0 
              of_nat_1 plus_1_eq_Suc)
        done
      show ?thesis using outupd_exe_atst.simps(4)[of "''x''" "CHR ''y''" "[]" 0 "[]" "
        \<lambda>s. if length s = 1 then 2 * hd s else 0" "[]" h1 1] using tmp1 tmp2 by presburger
    qed
    show ?thesis using exeDisDiag_attime.simps(2)[of "Gain" "[]" h1 1] using 1 2 3 4 5 6 7
      using One_nat_def by presburger
  qed
  done

lemma exe1_2: "\<forall>v. exeDisDiag_attime [UD1, Gain] h1 (Suc 0) v 1 = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 1 then 4 else (if v = CHR ''s'' \<and> t = 1 then 4 else h1 v t))) v 1"
  apply clarify subgoal for v
  proof -
    have 1: "(\<exists>k. int 1 = get_sample_time UD1 * k)"
    proof -
      have tmp1: "get_sample_time UD1 = 1"
        using UD1_def get_sample_time.simps by (metis (no_types, lifting))
      have tmp2: "int 1 = get_sample_time UD1 * 1"
        using tmp1 by simp
      show ?thesis using tmp2 by simp
    qed
    have 2: "(exeDisDiag_attime [] h1 1) = h1"
      using exeDisDiag_attime.simps(1)[of h1 1] by simp
    have 3: "get_inputs UD1 = ''y''"
      using UD1_def get_inputs.simps by (metis (no_types, lifting))
    have 4: "get_outputs UD1 = ''s''"
      using UD1_def get_outputs.simps by (metis (no_types, lifting))
    have 5: "get_offsets UD1 = [0]"
      using UD1_def get_offsets.simps by (metis (no_types, lifting))
    have 6: "get_outupd UD1 = [\<lambda>s. if length s = 1 then hd s else 0]"
      using UD1_def get_outupd.simps by (metis (no_types, lifting))
    have 7: "\<forall>v t. outupd_exe_atst ''y'' ''s'' [0] [\<lambda>s. if length s = 1 then hd s else 0]
         (\<lambda>v t. (if v = CHR ''y'' \<and> t = 1 then 4 else h1 v t)) 1 v t = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 1 then 4 else (if v = CHR ''s'' \<and> t = 1 then 4 else h1 v t))) v t"
    proof -
      have tmp1: "\<forall>h. outupd_exe_atst ''y'' [] [] [] h 1 = h"
        by auto
      have tmp2: "\<forall>v t. (\<lambda>vv tt.
       if tt = real 1 \<and> vv = CHR ''s''
       then if length
                (map (\<lambda>a. if a = CHR ''y'' \<and> real 1 - real 0 = 1 then 4 else h1 a (real 1 - real 0))
                  ''y'') = 1
            then hd (map (\<lambda>a. if a = CHR ''y'' \<and> real 1 - real 0 = 1 then 4
                              else h1 a (real 1 - real 0))
                      ''y'') else 0
       else if vv = CHR ''y'' \<and> tt = 1 then 4 else h1 vv tt) v t = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 1 then 4 else (if v = CHR ''s'' \<and> t = 1 then 4 else h1 v t))) v t"
        apply clarify subgoal for v t using h1_def h_def by (smt (verit, ccfv_SIG) One_nat_def 
              add.commute hd_map length_map list.sel(1) list.size(3) list.size(4) of_nat_0 
              of_nat_1 plus_1_eq_Suc)
        done
      show ?thesis using outupd_exe_atst.simps(4)[of "''y''" "CHR ''s''" "[]" 0 "[]" "
        \<lambda>s. if length s = 1 then hd s else 0" "[]" "(\<lambda>v t. (if v = CHR ''y'' \<and> t = 1 then 4 else h1 v t))"
            1] using tmp1 tmp2 by presburger
    qed
    show ?thesis using exeDisDiag_attime.simps(2)[of "UD1" "[Gain]" h1 1] using 1 2 3 4 5 6 7
      exe1_1 by simp
  qed
  done


lemma exe1_3: "\<forall>v. exeDisDiag_attime [UD2, UD1, Gain] h1 (Suc 0) v 1 = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 1 then 4 else (if v = CHR ''s'' \<and> t = 1 then 4 else h1 v t))) v 1"
  apply clarify subgoal for v
  proof -
    have 1: "(\<exists>k. int 1 = get_sample_time UD2 * k)"
    proof -
      have tmp1: "get_sample_time UD2 = 1"
        using UD2_def get_sample_time.simps by (metis (no_types, lifting))
      have tmp2: "int 1 = get_sample_time UD2 * 1"
        using tmp1 by simp
      show ?thesis using tmp2 by simp
    qed
    have 2: "(exeDisDiag_attime [] h1 1) = h1"
      using exeDisDiag_attime.simps(1)[of h1 1] by simp
    have 3: "get_inputs UD2 = ''s''"
      using UD2_def get_inputs.simps by (metis (no_types, lifting))
    have 4: "get_outputs UD2 = ''z''"
      using UD2_def get_outputs.simps by (metis (no_types, lifting))
    have 5: "get_offsets UD2 = [1]"
      using UD2_def get_offsets.simps by (metis (no_types, lifting))
    have 6: "get_outupd UD2 = [\<lambda>s. if length s = 1 then hd s else 0]"
      using UD2_def get_outupd.simps by (metis (no_types, lifting))
    have 7: "\<forall>v t. outupd_exe_atst ''s'' ''z'' [1] [\<lambda>s. if length s = 1 then hd s else 0] (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 1 then 4 else (if v = CHR ''s'' \<and> t = 1 then 4 else h1 v t))) 1 v t 
= (\<lambda>v t. (if v = CHR ''y'' \<and> t = 1 then 4 else (if v = CHR ''s'' \<and> t = 1 then 4 else h1 v t))) v t"
    proof -
      have tmp1: "\<forall>h. outupd_exe_atst ''s'' [] [] [] h 1 = h"
        by auto
      have tmp2: "\<forall>v t. (\<lambda>vv tt.
       if tt = real 1 \<and> vv = CHR ''z''
       then if length (map (\<lambda>a. if a = CHR ''y'' \<and> real 1 - real 1 = 1 then 4
                          else if a = CHR ''s'' \<and> real 1 - real 1 = 1 then 4
                               else h1 a (real 1 - real 1)) ''s'') = 1
            then hd (map (\<lambda>a. if a = CHR ''y'' \<and> real 1 - real 1 = 1 then 4
                              else if a = CHR ''s'' \<and> real 1 - real 1 = 1 then 4
                                   else h1 a (real 1 - real 1)) ''s'') else 0
       else if vv = CHR ''y'' \<and> tt = 1 then 4 else if vv = CHR ''s'' \<and> tt = 1 then 4 else h1 vv tt) v t = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 1 then 4 else (if v = CHR ''s'' \<and> t = 1 then 4 else h1 v t))) v t"
        apply clarify subgoal for v t using h1_def h_def apply simp
          using char.inject by presburger
        done
      show ?thesis using outupd_exe_atst.simps(4)[of "''s''" "CHR ''z''" "[]" 1 "[]" "
        \<lambda>s. if length s = 1 then hd s else 0" "[]" "(\<lambda>v t. (if v = CHR ''y'' \<and> t = 1 
        then 4 else (if v = CHR ''s'' \<and> t = 1 then 4 else h1 v t)))"
            1] using tmp1 tmp2 by presburger
    qed
    show ?thesis using exeDisDiag_attime.simps(2)[of "UD2" "[UD1, Gain]" h1 1] using 1 2 3 4 5 6 7
      exe1_2 by (smt (z3) One_nat_def exeDisDiag_attime_lemma2 hd_map length_map 
          list.distinct(1) outupd_exe_atst.simps(1) outupd_exe_atst.simps(4))
  qed
  done

lemma exe1_4: "exeDisDiag_attime [Bias, UD2, UD1, Gain] h1 (Suc 0) = h2"
  proof -
    have 1: "get_sample_time Bias = 0"
    proof -
      show ?thesis unfolding Bias_def by simp
    qed
    have 2: "(exeDisDiag_attime [] h1 1) = h1"
      using exeDisDiag_attime.simps(1)[of h1 1] by simp
    have 3: "get_inputs Bias = ''a''"
      using Bias_def get_inputs.simps by (metis (no_types, lifting))
    have 4: "get_outputs Bias = ''b''"
      using Bias_def get_outputs.simps by (metis (no_types, lifting))
    have 5: "get_offsets Bias = [0]"
      using Bias_def get_offsets.simps by (metis (no_types, lifting))
    have 6: "get_outupd Bias = [(\<lambda>s. (if length s = 1 then (hd s + 2::real) else 0))]"
      using Bias_def get_outupd.simps by (metis (no_types, lifting))
    have 7: "\<forall>v t. outupd_exe_atst ''a'' ''b'' [0] [(\<lambda>s. (if length s = 1 then (hd s + 2::real) else 0))]
 (\<lambda>v t. (if v = CHR ''y'' \<and> t = 1 then 4 else (if v = CHR ''s'' \<and> t = 1 then 4 else h1 v t))) 1 v t 
= h2 v t"
    proof -
      have tmp1: "\<forall>h. outupd_exe_atst ''a'' [] [] [] h 1 = h"
        by auto
      have tmp2: "\<forall>v t. (\<lambda>vv tt.
         if tt = real 1 \<and> vv = CHR ''b''
         then if length
                  (map (\<lambda>a. if a = CHR ''y'' \<and> real 1 - real 0 = 1 then 4
                            else if a = CHR ''s'' \<and> real 1 - real 0 = 1 then 4
                                 else h1 a (real 1 - real 0))
                    ''a'') = 1
              then hd (map (\<lambda>a. if a = CHR ''y'' \<and> real 1 - real 0 = 1 then 4
                                else if a = CHR ''s'' \<and> real 1 - real 0 = 1 then 4
                                     else h1 a (real 1 - real 0))
                        ''a'') + 2
              else 0
         else if vv = CHR ''y'' \<and> tt = 1 then 4
              else if vv = CHR ''s'' \<and> tt = 1 then 4 else h1 vv tt) 
      v t = h2 v t"
        apply clarify subgoal for v t using h2_def h1_def h_def apply simp
          using char.inject by (smt (z3))
        done
      show ?thesis using outupd_exe_atst.simps(4)[of "''a''" "CHR ''b''" "[]" 0 "[]" "
        \<lambda>s. (if length s = 1 then (hd s + 2::real) else 0)" "[]" "(\<lambda>v t. (if v = CHR ''y'' \<and> t = 1 
        then 4 else (if v = CHR ''s'' \<and> t = 1 then 4 else h1 v t)))"
            1] using tmp1 tmp2 by presburger
    qed
    have 8: "(exeDisDiag_attime [UD2, UD1, Gain] h1 1) = 
    (\<lambda>v t. (if v = CHR ''y'' \<and> t = 1 then 4 else (if v = CHR ''s'' \<and> t = 1 then 4 else h1 v t)))"
      using exe1_3 exeDisDiag_attime_lemma2 by (metis 
          (no_types, opaque_lifting) One_nat_def of_nat_1)
    have 9: "outupd_exe_atst ''a'' ''b'' [0] [(\<lambda>s. (if length s = 1 then (hd s + 2::real) else 0))]
 (\<lambda>v t. (if v = CHR ''y'' \<and> t = 1 then 4 else (if v = CHR ''s'' \<and> t = 1 then 4 else h1 v t))) 1 = h2"
      using 7 by presburger
    show ?thesis using exeDisDiag_attime.simps(2)[of "Bias" "[UD2, UD1, Gain]" h1 1] 
      using 1 2 3 4 5 6 8 9 by auto
  qed

lemma exe_diag_interval1: "ODE_cond (Block ''za'' ''ax'' [1, 1] 0
   (updateFunc2 [\<lambda>s. if length s = 1 then hd s else 0] ''a''
     (hd (updateFunc [\<lambda>s. if length s = 1 then hd s else 0] ''b'' CHR ''b''
           (\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))
     ''z'')) h' 0 1 \<Longrightarrow>
  exe_diag_interval [Gain, UD1, UD2] [Integ1, Bias, Integ2] h' 0 1 = h2"
  subgoal premises pre
  proof -
    have 0: "\<exists>L. unique_on_bounded_closed 0 {0--1} Vec0 
  (\<lambda>t v. (\<chi> x.(if x = CHR ''x'' then v $ CHR ''a'' + 2 else 
  if x = CHR ''a'' then v $ CHR ''z'' else 0))) UNIV L"
      using pre(1) unfolding ODE_cond_def using get_Vec0 getODE'_2 by auto
  have 1: "(\<lambda>vv tt. if 0 < tt \<and> tt < 0 + 1 \<and> vv \<in> Outputs [Gain, UD1, UD2] then h' vv 0 else h' vv tt) = h'"
  proof -
    have tmp1: "Outputs [Gain, UD1, UD2] = {CHR ''y'', CHR ''s'', CHR ''z''}"
      unfolding Gain_def UD1_def UD2_def Outputs.simps by auto
    have tmp2: "\<forall>v t. (\<lambda>vv tt.
        if 0 < tt \<and> tt < 0 + 1 \<and> vv \<in> Outputs [Gain, UD1, UD2]
        then if 0 = 0 \<and> vv = CHR ''b'' then 2 else 0
        else if tt = 0 \<and> vv = CHR ''b'' then 2 else 0) v t=
    (\<lambda>v t. if t = 0 \<and> v = CHR ''b'' then 2 else 0) v t"
      using tmp1 by simp
    show ?thesis unfolding h'_def h_def using tmp2 by blast
  qed
  have 2: "exeContinuousDiag_interval [Integ1, Bias, Integ2] h' 0 1 = h1"
  proof -
    have tmp1: "findIntegBlks [Integ1, Bias, Integ2] = [Integ1, Integ2]"
      unfolding findIntegBlks.simps Integ1_def Bias_def Integ2_def by auto
    have tmp2: "(block2ODE (updateIntegBlks [Integ1, Bias, Integ2] 
    (findIntegBlks [Integ1, Bias, Integ2]))) = (\<lambda>t v. (\<chi> x. (if x = CHR ''x'' then v $ CHR ''a'' + 2 else if 
      x = CHR ''a'' then v $ CHR ''z'' else 0)))"
      using updateIntegBlks_lemma getODE'_2 tmp1 by auto
    have tmp3: "(state2vec (timedVar2State h' 0)) = Vec0"
      unfolding timedVar2State_def h'_def h_def Vec0_def state2vec_def by simp
    have tmp4: "\<forall>t \<in> {0 -- 1}. (apply_bcontfun
         (unique_on_bounded_closed.fixed_point 0 {0--0 + 1} (state2vec (timedVar2State h' 0))
           (block2ODE
             (updateIntegBlks [Integ1, Bias, Integ2] (findIntegBlks [Integ1, Bias, Integ2])))
           UNIV)) t = (\<lambda>x. \<chi> y. if y = CHR ''x'' then 2 * x else 
            if y = CHR ''b'' then 2 else 0) t "
      using tmp2 tmp3 solves1_fixedpoint 0 by auto
    have tmp5: "(get_outputs (updateIntegBlks [Integ1, Bias, Integ2] 
      (findIntegBlks [Integ1, Bias, Integ2]))) = ''ax''"
      using updateIntegBlks_lemma tmp1 by simp
    have tmp6: "\<forall>tt. tt > (0::real) \<and> tt \<le> (1::real) \<longrightarrow> tt \<in> {0::real -- 1::real}"
      unfolding closed_segment_def by force
    have tmp7: "\<forall>vv tt . updTimedVar
       (apply_bcontfun
         (unique_on_bounded_closed.fixed_point 0 {0--0 + 1} (state2vec (timedVar2State h' 0))
           (block2ODE
             (updateIntegBlks [Integ1, Bias, Integ2] (findIntegBlks [Integ1, Bias, Integ2])))
           UNIV)) ''ax'' h' 0 1 vv tt  = 
        (\<lambda>v t. (if v = CHR ''x'' \<and> t \<ge> 0 \<and> t \<le> 1 then 2*t else h' v t)) vv tt"
      apply clarify subgoal for vv tt 
      proof(cases "vv \<in> set ''ax'' \<and> tt > (0::real) \<and> tt \<le> (1::real)")
        case True
        have tmp1: "tt \<in> {0::real -- 1::real}"
          using True tmp6 by simp
        then show ?thesis using True updTimedVar_eq2[of "''ax''" 0 1
              "(\<lambda>x. \<chi> y. if y = CHR ''x'' then 2 * x else 
            if y = CHR ''b'' then 2 else 0)" h'] tmp4 unfolding h'_def h_def by auto
      next
        case False
        have tmp1: "vv \<notin> set ''ax'' \<or> tt \<le> 0 \<or> 1 < tt"
          using False by auto
        have tmp2: "updTimedVar
     (apply_bcontfun
       (unique_on_bounded_closed.fixed_point 0 {0--0 + 1} (state2vec (timedVar2State h' 0))
         (block2ODE
           (updateIntegBlks [Integ1, Bias, Integ2] (findIntegBlks [Integ1, Bias, Integ2])))
         UNIV))
     ''ax'' h' 0 1 (CHR ''x'') 0 = 0"
          using updTimedVar_eq1 unfolding h'_def h_def using tmp1 by force
        then show ?thesis
        proof(cases "tt = 0 \<and> vv = CHR ''x''")
          case True
          then show ?thesis using tmp2 by auto
        next
          case False
          note F1 = False
          have tmp: "\<not>(vv = CHR ''x'' \<and> 0 \<le> tt \<and> tt \<le> 1)"
            using False tmp1 by force
          then show ?thesis
          proof (cases "tt = 0 \<and> vv = CHR ''b''")
            case True
            then show ?thesis unfolding h'_def h_def by (smt (verit, ccfv_SIG) tmp updTimedVar_eq1)
          next
            case False
            then show ?thesis using tmp1 F1 False unfolding h'_def h_def
              by (smt (verit, ccfv_SIG) tmp updTimedVar_eq1)
          qed
        qed
      qed
      done
    have tmp8: "updTimedVar
       (apply_bcontfun
         (unique_on_bounded_closed.fixed_point 0 {0--0 + 1} (state2vec (timedVar2State h' 0))
           (block2ODE
             (updateIntegBlks [Integ1, Bias, Integ2] (findIntegBlks [Integ1, Bias, Integ2])))
           UNIV)) ''ax'' h' 0 1  = 
        (\<lambda>v t. (if v = CHR ''x'' \<and> t \<ge> 0 \<and> t \<le> 1 then 2*t else h' v t))"
      using tmp7 by presburger
    have tmp9: "getCalBlks [Integ1, Bias, Integ2] = [Bias]"
      unfolding getCalBlks.simps Integ1_def Bias_def Integ2_def by auto
    have tmp10: "exeCalBlks [Bias] (\<lambda>v t. if v = CHR ''x'' \<and> 0 \<le> t \<and> t \<le> 1 
    then 2 * t else h' v t) 0 1 = h1"
    proof -
      have tmp: "\<forall>v t. (\<lambda>v t. if v = CHR ''b'' \<and> 0 < t \<and> t < 1 then 2
         else if v = CHR ''x'' \<and> 0 \<le> t \<and> t \<le> 1 then 2 * t else h' v t) v t = h1 v t"
        unfolding h1_def h'_def h_def by simp
      show ?thesis using exe1_0 unfolding h1_def h'_def h_def using tmp using less_numeral_extra(3)
          linorder_not_le order.asym order_less_irrefl order_less_le real_scaleR_def 
          zero_neq_numeral by fastforce
    qed
    show ?thesis unfolding exeContinuousDiag_interval.simps solveODE_def using tmp5 tmp8 tmp9 tmp10 by auto
  qed
  have 3: "(rev (sortDiag ([Gain, UD1, UD2] @ getCalBlks [Integ1, Bias, Integ2]))) =
    [Bias, UD2, UD1, Gain]"
  proof -
    have tmp1: "getCalBlks [Integ1, Bias, Integ2] = [Bias]"
      unfolding getCalBlks.simps Integ1_def Bias_def Integ2_def by simp
    show ?thesis using sort_lemma tmp1 by auto
  qed
  show ?thesis unfolding exe_diag_interval.simps using 1 2 3 exe1_4 by auto
qed
  done

value "(\<lambda>vv tt.
       if tt = real 2 \<and> vv = CHR ''y''
       then if length (map (\<lambda>a. h3 a (real 2 - real 0)) ''x'') = 1
            then 2 * hd (map (\<lambda>a. h3 a (real 2 - real 0)) ''x'') else 0
       else h3 vv tt) (CHR ''y'') (real 2)"

lemma exe2_0: "exeCalBlks [Bias] (\<lambda>v t. (if v = CHR ''x'' \<and> t > 1 
        \<and> t \<le> 2 then 2*t else h2' v t)) 1 1 = h3"
proof -
  have 1: "\<forall>tt. length (map (\<lambda>a. if a = CHR ''x'' \<and> 1 < tt \<and> tt \<le> 2 then 2 * tt 
  else h2' a tt) ''a'') = 1"
    by auto
  have 2: "\<forall>tt. hd (map (\<lambda>a. if a = CHR ''x'' \<and> 1 < tt \<and> tt \<le> 2 then 2 * tt else h2' a tt)
                       ''a'') = (0::real)"
    unfolding h2'_def h2_def h1_def h_def by auto
  have 3: "\<forall>v t. (\<lambda>vv tt.
        if vv = CHR ''b'' \<and> tt < 2 \<and> 1 < tt
        then if length
                 (map (\<lambda>a. if a = CHR ''x'' \<and> 1 < tt \<and> tt \<le> 2 then 2 * tt else h2' a tt) ''a'') =
                Suc 0
             then hd (map (\<lambda>a. if a = CHR ''x'' \<and> 1 < tt \<and> tt \<le> 2 then 2 * tt else h2' a tt)
                       ''a'') + 2 else 0
        else if vv = CHR ''x'' \<and> 1 < tt \<and> tt \<le> 2 then 2 * tt else h2' vv tt) v t = h3 v t"
    apply clarify subgoal for v t 
    proof(cases "v = CHR ''b'' \<and> t < 2 \<and> 1 < t")
      case True
      have tmp1: "h3 v t = 2"
        using True unfolding h3_def h2'_def h2_def by auto
      have tmp2: "length (map (\<lambda>a. if a = CHR ''x'' \<and> 1 < t \<and> t \<le> 2 then 2 * t else h2' a t) ''a'') = 1"
        using 1 by auto
      have tmp3: "(if v = CHR ''b'' \<and> t < 2 \<and> 1 < t
          then if length (map (\<lambda>a. if a = CHR ''x'' \<and> 1 < t \<and> t \<le> 2 then 2 * t else h2' a t) ''a'') =
             Suc 0
          then hd (map (\<lambda>a. if a = CHR ''x'' \<and> 1 < t \<and> t \<le> 2 then 2 * t else h2' a t) ''a'') + 2
          else 0
          else if v = CHR ''x'' \<and> 1 < t \<and> t \<le> 2 then 2 * t else h2' v t) = 2"
        using True tmp2 2 by auto
      then show ?thesis using tmp1 tmp2 tmp3 by auto
    next
      case False
      note F1 = False
      then show ?thesis unfolding h3_def by (smt (z3) char.inject h1_def h2'_def h2_def)
    qed
    done
  show ?thesis unfolding exeCalBlks.simps Bias_def h_def apply simp using 3 by simp
qed

lemma exe2_1: "\<forall>v. exeDisDiag_attime [Gain] h3 (Suc 1) v 2 = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 2 then 8 else h3 v t)) v 2"
  apply clarify subgoal for v
  proof -
    have 1: "(\<exists>k. int 2 = get_sample_time Gain * k)"
    proof -
      have tmp1: "get_sample_time Gain = 1"
        using Gain_def get_sample_time.simps by (metis (no_types, lifting))
      have tmp2: "int 2 = get_sample_time Gain * 2"
        using tmp1 by simp
      show ?thesis using tmp2 by simp
    qed
    have 2: "(exeDisDiag_attime [] h3 2) = h3"
      using exeDisDiag_attime.simps(1)[of h3 2] by simp
    have 3: "get_inputs Gain = ''x''"
      using Gain_def get_inputs.simps by (metis (no_types, lifting))
    have 4: "get_outputs Gain = ''y''"
      using Gain_def get_outputs.simps by (metis (no_types, lifting))
    have 5: "get_offsets Gain = [0]"
      using Gain_def get_offsets.simps by (metis (no_types, lifting))
    have 6: "get_outupd Gain = [\<lambda>s. if length s = 1 then 2 * hd s else 0]"
      using Gain_def get_outupd.simps by (metis (no_types, lifting))
    have 7: "\<forall>v t. outupd_exe_atst ''x'' ''y'' [0] [\<lambda>s. if length s = 1 then 2 * hd s else 0]
         h3 2 v t = (\<lambda>v t. (if v = CHR ''y'' \<and> t = 2 then 8 else h3 v t)) v t"
    proof -
      have tmp1: "\<forall>h. outupd_exe_atst ''x'' [] [] [] h 1 = h"
        by auto
      have tmp2: "\<forall>v t. (\<lambda>vv tt.
       if tt = real 2 \<and> vv = CHR ''y''
       then if length (map (\<lambda>a. h3 a (real 2 - real 0)) ''x'') = 1
            then 2 * hd (map (\<lambda>a. h3 a (real 2 - real 0)) ''x'') else 0
       else h3 vv tt) v t = (\<lambda>vv tt. (if vv = CHR ''y'' \<and> tt = 2 then 8 else h3 vv tt)) v t"
        apply clarify subgoal for v t
        proof(cases "v = CHR ''y'' \<and> t = real 2")
          case True
          then show ?thesis unfolding h3_def h2_def h1_def h_def by force
        next
          case False
          then show ?thesis by auto
        qed
        done
      show ?thesis using outupd_exe_atst.simps(4)[of "''x''" "CHR ''y''" "[]" 0 "[]" "
        \<lambda>s. if length s = 1 then 2 * hd s else 0" "[]" h3 2] using tmp1 tmp2
        using outupd_exe_atst.simps(1) by presburger
    qed
    show ?thesis using exeDisDiag_attime.simps(2)[of "Gain" "[]" h3 2] using 1 2 3 4 5 6 7
      using One_nat_def Suc_1 by presburger
  qed
  done

lemma exe2_2: "\<forall>v. exeDisDiag_attime [UD1, Gain] h3 (Suc 1) v 2 = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 2 then 8 else (if v = CHR ''s'' \<and> t = 2 then 8 else h3 v t))) v 2"
  apply clarify subgoal for v
  proof -
    have 1: "(\<exists>k. int 2 = get_sample_time UD1 * k)"
    proof -
      have tmp1: "get_sample_time UD1 = 1"
        using UD1_def get_sample_time.simps by (metis (no_types, lifting))
      have tmp2: "int 2 = get_sample_time UD1 * 2"
        using tmp1 by simp
      show ?thesis using tmp2 by simp
    qed
    have 2: "(exeDisDiag_attime [] h3 2) = h3"
      using exeDisDiag_attime.simps(1)[of h3 2] by simp
    have 3: "get_inputs UD1 = ''y''"
      using UD1_def get_inputs.simps by (metis (no_types, lifting))
    have 4: "get_outputs UD1 = ''s''"
      using UD1_def get_outputs.simps by (metis (no_types, lifting))
    have 5: "get_offsets UD1 = [0]"
      using UD1_def get_offsets.simps by (metis (no_types, lifting))
    have 6: "get_outupd UD1 = [\<lambda>s. if length s = 1 then hd s else 0]"
      using UD1_def get_outupd.simps by (metis (no_types, lifting))
    have 7: "\<forall>v t. outupd_exe_atst ''y'' ''s'' [0] [\<lambda>s. if length s = 1 then hd s else 0]
         (\<lambda>v t. (if v = CHR ''y'' \<and> t = 2 then 8 else h3 v t)) 2 v t = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 2 then 8 else (if v = CHR ''s'' \<and> t = 2 then 8 else h3 v t))) v t"
    proof -
      have tmp1: "\<forall>h. outupd_exe_atst ''y'' [] [] [] h 2 = h"
        by auto
      have tmp2: "\<forall>v t. (\<lambda>vv tt.
       if tt = real 2 \<and> vv = CHR ''s''
       then if length
                (map (\<lambda>a. if a = CHR ''y'' \<and> real 2 - real 0 = 2 then 8 else h3 a (real 2 - real 0))
                  ''y'') = 1
            then hd (map (\<lambda>a. if a = CHR ''y'' \<and> real 2 - real 0 = 2 then 8
                              else h3 a (real 2 - real 0))
                      ''y'') else 0
       else if vv = CHR ''y'' \<and> tt = 2 then 8 else h3 vv tt) v t = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 2 then 8 else (if v = CHR ''s'' \<and> t = 2 then 8 else h3 v t))) v t"
        apply clarify subgoal for v t using h3_def h2_def h1_def h_def by simp
        done
      show ?thesis using outupd_exe_atst.simps(4)[of "''y''" "CHR ''s''" "[]" 0 "[]" "
        \<lambda>s. if length s = 1 then hd s else 0" "[]" "(\<lambda>v t. (if v = CHR ''y'' \<and> t = 2 then 8 else h3 v t))"
            2] using tmp1 tmp2 by presburger
    qed
    show ?thesis using exeDisDiag_attime.simps(2)[of "UD1" "[Gain]" h3 2] using 1 2 3 4 5 6 7
      exe2_1 by simp
  qed
  done

lemma exe2_3: "\<forall>v. exeDisDiag_attime [UD2, UD1, Gain] h3 2 v 2 = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 2 then 8 else (if v = CHR ''s'' \<and> t = 2 then 8 else 
if v = CHR ''z'' \<and> t = 2 then 4 else h3 v t))) v 2"
  apply clarify subgoal for v
  proof -
    have 1: "(\<exists>k. int 2 = get_sample_time UD2 * k)"
    proof -
      have tmp1: "get_sample_time UD2 = 1"
        using UD2_def get_sample_time.simps by (metis (no_types, lifting))
      have tmp2: "int 2 = get_sample_time UD2 * 2"
        using tmp1 by simp
      show ?thesis using tmp2 by simp
    qed
    have 2: "(exeDisDiag_attime [] h3 2) = h3"
      using exeDisDiag_attime.simps(1)[of h3 2] by simp
    have 3: "get_inputs UD2 = ''s''"
      using UD2_def get_inputs.simps by (metis (no_types, lifting))
    have 4: "get_outputs UD2 = ''z''"
      using UD2_def get_outputs.simps by (metis (no_types, lifting))
    have 5: "get_offsets UD2 = [1]"
      using UD2_def get_offsets.simps by (metis (no_types, lifting))
    have 6: "get_outupd UD2 = [\<lambda>s. if length s = 1 then hd s else 0]"
      using UD2_def get_outupd.simps by (metis (no_types, lifting))
    have 7: "\<forall>v t. outupd_exe_atst ''s'' ''z'' [1] [\<lambda>s. if length s = 1 then hd s else 0] (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 2 then 8 else (if v = CHR ''s'' \<and> t = 2 then 8 else h3 v t))) 2 v t 
= (\<lambda>v t. (if v = CHR ''y'' \<and> t = 2 then 8 else (if v = CHR ''s'' \<and> t = 2 then 8 else 
if v = CHR ''z'' \<and> t = 2 then 4 else h3 v t))) v t"
    proof -
      have tmp1: "\<forall>h. outupd_exe_atst ''s'' [] [] [] h 2 = h"
        by auto
      have tmp2: "\<forall>v t. (\<lambda>vv tt.
       if tt = real 2 \<and> vv = CHR ''z''
       then if length
                (map (\<lambda>a. if a = CHR ''y'' \<and> real 2 - real 1 = 2 then 8
                          else if a = CHR ''s'' \<and> real 2 - real 1 = 2 then 8
                               else h3 a (real 2 - real 1))
                  ''s'') =
               1
            then hd (map (\<lambda>a. if a = CHR ''y'' \<and> real 2 - real 1 = 2 then 8
                              else if a = CHR ''s'' \<and> real 2 - real 1 = 2 then 8
                                   else h3 a (real 2 - real 1))
                      ''s'')
            else 0
else if vv = CHR ''y'' \<and> tt = 2 then 8 else if vv = CHR ''s'' \<and> tt = 2 then 8 else h3 vv tt) v t = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 2 then 8 else (if v = CHR ''s'' \<and> t = 2 then 8 else 
if v = CHR ''z'' \<and> t = 2 then 4 else h3 v t))) v t"
        apply clarify subgoal for v t using h3_def h2'_def h2_def h1_def h_def apply simp
          using char.inject by presburger
        done
      show ?thesis using outupd_exe_atst.simps(4)[of "''s''" "CHR ''z''" "[]" 1 "[]" "
        \<lambda>s. if length s = 1 then hd s else 0" "[]" "(\<lambda>v t. (if v = CHR ''y'' \<and> t = 2 
        then 8 else (if v = CHR ''s'' \<and> t = 2 then 8 else h3 v t)))"
            2] using tmp1 tmp2 by presburger
    qed
    show ?thesis using exeDisDiag_attime.simps(2)[of "UD2" "[UD1, Gain]" h3 2] using 1 2 3 4 5 6 7
      exe2_2 by (smt (z3) Suc_1 exeDisDiag_attime_lemma2 hd_map length_map 
          list.distinct(1) outupd_exe_atst.simps(1) outupd_exe_atst.simps(4))
  qed
  done

lemma exe2_4: "exeDisDiag_attime [Bias, UD2, UD1, Gain] h3 2 = h4"
  proof -
    have 1: "get_sample_time Bias = 0"
    proof -
      show ?thesis unfolding Bias_def by simp
    qed
    have 2: "(exeDisDiag_attime [] h3 2) = h3"
      using exeDisDiag_attime.simps(1)[of h3 2] by simp
    have 3: "get_inputs Bias = ''a''"
      using Bias_def get_inputs.simps by (metis (no_types, lifting))
    have 4: "get_outputs Bias = ''b''"
      using Bias_def get_outputs.simps by (metis (no_types, lifting))
    have 5: "get_offsets Bias = [0]"
      using Bias_def get_offsets.simps by (metis (no_types, lifting))
    have 6: "get_outupd Bias = [(\<lambda>s. (if length s = 1 then (hd s + 2::real) else 0))]"
      using Bias_def get_outupd.simps by (metis (no_types, lifting))
    have 7: "\<forall>v t. outupd_exe_atst ''a'' ''b'' [0] [(\<lambda>s. (if length s = 1 then (hd s + 2::real) else 0))]
 (\<lambda>v t. (if v = CHR ''y'' \<and> t = 2 then 8 else (if v = CHR ''s'' \<and> t = 2 then 8 else 
if v = CHR ''z'' \<and> t = 2 then 4 else h3 v t))) 2 v t 
= h4 v t"
    proof -
      have tmp1: "\<forall>h. outupd_exe_atst ''a'' [] [] [] h 2 = h"
        by auto
      have tmp2: "\<forall>v t. (\<lambda>vv tt.
       if tt = real 2 \<and> vv = CHR ''b''
       then if length
                (map (\<lambda>a. if a = CHR ''y'' \<and> real 2 - real 0 = 2 then 8
                          else if a = CHR ''s'' \<and> real 2 - real 0 = 2 then 8
                               else if a = CHR ''z'' \<and> real 2 - real 0 = 2 then 4
                                    else h3 a (real 2 - real 0))
                  ''a'') =
               1
            then hd (map (\<lambda>a. if a = CHR ''y'' \<and> real 2 - real 0 = 2 then 8
                              else if a = CHR ''s'' \<and> real 2 - real 0 = 2 then 8
                                   else if a = CHR ''z'' \<and> real 2 - real 0 = 2 then 4
                                        else h3 a (real 2 - real 0))
                      ''a'') +
                 2
            else 0
       else if vv = CHR ''y'' \<and> tt = 2 then 8
            else if vv = CHR ''s'' \<and> tt = 2 then 8
                 else if vv = CHR ''z'' \<and> tt = 2 then 4 else h3 vv tt) 
      v t = h4 v t"
        apply clarify subgoal for v t using h4_def h3_def h2'_def h2_def h1_def h_def apply simp
          using char.inject by (smt (z3))
        done
      show ?thesis using outupd_exe_atst.simps(4)[of "''a''" "CHR ''b''" "[]" 0 "[]" "
        \<lambda>s. (if length s = 1 then (hd s + 2::real) else 0)" "[]" "(\<lambda>v t. (if v = CHR ''y'' 
        \<and> t = 2 then 8 else (if v = CHR ''s'' \<and> t = 2 then 8 else 
        if v = CHR ''z'' \<and> t = 2 then 4 else h3 v t)))" 2] using tmp1 tmp2 by presburger
    qed
    have 8: "exeDisDiag_attime [UD2, UD1, Gain] h3 2 = 
    (\<lambda>v t. (if v = CHR ''y'' \<and> t = 2 then 8 else (if v = CHR ''s'' \<and> t = 2 then 8 else 
      if v = CHR ''z'' \<and> t = 2 then 4 else h3 v t)))"
    proof -
      have tmp1: "\<forall>v t. exeDisDiag_attime [UD2, UD1, Gain] h3 2 v t = 
      (\<lambda>v t. (if v = CHR ''y'' \<and> t = 2 then 8 else (if v = CHR ''s'' \<and> t = 2 then 8 else 
      if v = CHR ''z'' \<and> t = 2 then 4 else h3 v t))) v t"
        apply clarify subgoal for v t
        proof(cases "t = real 2")
          case True
          then show ?thesis using exe2_3 by auto
        next
          case False
          then show ?thesis using exeDisDiag_attime_lemma2[of t 2 "[UD2, UD1, Gain]" h3 v]
            by auto
        qed
        done
      show ?thesis using tmp1 by presburger
    qed
    have 9: "outupd_exe_atst ''a'' ''b'' [0] [(\<lambda>s. (if length s = 1 then (hd s + 2::real) else 0))]
 (\<lambda>v t. (if v = CHR ''y'' \<and> t = 2 then 8 else (if v = CHR ''s'' \<and> t = 2 then 8 else 
    if v = CHR ''z'' \<and> t = 2 then 4 else h3 v t))) 2 = h4"
      using 7 by presburger
    have 10: "outupd_exe_atst (get_inputs Bias) (get_outputs Bias) (get_offsets Bias) (get_outupd Bias)
         (exeDisDiag_attime [UD2, UD1, Gain] h3 2) 2 = h4"
      using 1 2 3 4 5 6 8 9 by auto
    show ?thesis using exeDisDiag_attime.simps(2)[of "Bias" "[UD2, UD1, Gain]" h3 2] 
      using 1 10 by auto
  qed

lemma exe_diag_interval2: "ODE_cond (Block ''za'' ''ax'' [1, 1] 0
   (updateFunc2 [\<lambda>s. if length s = 1 then hd s else 0] ''a''
     (hd (updateFunc [\<lambda>s. if length s = 1 then hd s else 0] ''b'' CHR ''b''
           (\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))
     ''z'')) h2 1 1 \<Longrightarrow>
  exe_diag_interval [Gain, UD1, UD2] [Integ1, Bias, Integ2] h2 1 1 = h4"
  subgoal premises pre
  proof -
    have 0: "\<exists>L. unique_on_bounded_closed 1 {1--2} Vec1 
  (\<lambda>t v. (\<chi> x.(if x = CHR ''x'' then v $ CHR ''a'' + 2 else 
  if x = CHR ''a'' then v $ CHR ''z'' else 0))) UNIV L"
      using pre unfolding ODE_cond_def using get_Vec1 getODE'_2 by auto
  have 1: "(\<lambda>vv tt. if 1 < tt \<and> tt < 1 + 1 \<and> vv \<in> Outputs [Gain, UD1, UD2] then h2 vv 1 else h2 
  vv tt) = h2'"
  proof -
    have tmp1: "Outputs [Gain, UD1, UD2] = {CHR ''y'', CHR ''s'', CHR ''z''}"
      unfolding Gain_def UD1_def UD2_def Outputs.simps by auto
    have tmp2: "\<forall>v t. (\<lambda>vv tt. if 1 < tt \<and> tt < 1 + 1 \<and> vv \<in> Outputs [Gain, UD1, UD2] then h2 vv 1 else h2 
  vv tt) v t = h2' v t"
      apply clarify subgoal for v t
      proof(cases "1 < t \<and> t < 2 \<and> v = CHR ''y''")
        case True
        then show ?thesis using tmp1 unfolding h2'_def h2_def h1_def h_def by auto
      next
        case False
        then show ?thesis using tmp1 unfolding h2'_def h2_def h1_def h_def by auto
      qed
      done
    show ?thesis using tmp2 by presburger
  qed
  have 2: "exeContinuousDiag_interval [Integ1, Bias, Integ2] h2' 1 1 = h3"
  proof -
    have tmp1: "findIntegBlks [Integ1, Bias, Integ2] = [Integ1, Integ2]"
      unfolding findIntegBlks.simps Integ1_def Bias_def Integ2_def by auto
    have tmp2: "(block2ODE (updateIntegBlks [Integ1, Bias, Integ2] 
    (findIntegBlks [Integ1, Bias, Integ2]))) = (\<lambda>t v. (\<chi> x. (if x = CHR ''x'' then v $ CHR ''a'' + 2 else if 
      x = CHR ''a'' then v $ CHR ''z'' else 0)))"
      using updateIntegBlks_lemma getODE'_2 tmp1 by auto
    have tmp3: "(state2vec (timedVar2State h2' 1)) = Vec1"
      unfolding timedVar2State_def h2'_def h2_def h1_def h_def Vec1_def state2vec_def by fastforce
    have tmp4: "\<forall>t \<in> {1 -- 2}. (apply_bcontfun
         (unique_on_bounded_closed.fixed_point 1 {1--1 + 1} (state2vec (timedVar2State h2' 1))
           (block2ODE
             (updateIntegBlks [Integ1, Bias, Integ2] (findIntegBlks [Integ1, Bias, Integ2])))
           UNIV)) t = (\<lambda>x. \<chi> y. if y = CHR ''x'' then 2 * x else if y = CHR ''b'' then 2 
      else if y = CHR ''y'' then 4 else if y = CHR ''s'' then 4 else 0) t "
      using tmp2 tmp3 solves2_fixedpoint 0 by simp
    have tmp5: "(get_outputs (updateIntegBlks [Integ1, Bias, Integ2] 
      (findIntegBlks [Integ1, Bias, Integ2]))) = ''ax''"
      using updateIntegBlks_lemma tmp1 by simp
    have tmp7: "\<forall>vv tt . updTimedVar
       (apply_bcontfun
         (unique_on_bounded_closed.fixed_point 1 {1--1 + 1} (state2vec (timedVar2State h2' 1))
           (block2ODE
             (updateIntegBlks [Integ1, Bias, Integ2] (findIntegBlks [Integ1, Bias, Integ2])))
           UNIV)) ''ax'' h2' 1 1 vv tt  = 
        (\<lambda>v t. (if v = CHR ''x'' \<and> t > 1 \<and> t \<le> 2 then 2*t else h2' v t)) vv tt"
      apply clarify subgoal for vv tt 
      proof(cases "vv \<in> set ''ax'' \<and> tt > (1::real) \<and> tt \<le> (2::real)")
        case True
        have tmp1: "tt \<in> {1::real -- 2::real}"
          using True by (simp add: Line_Segment.closed_segment_eq_real_ivl)
        then show ?thesis using True updTimedVar_eq2 tmp4 unfolding h2'_def h2_def h1_def h_def
          using char.inject empty_iff set_ConsD set_empty vec_lambda_beta by auto
      next
        case False
        have tmp1: "vv \<notin> set ''ax'' \<or> tt \<le> 1 \<or> 2 < tt"
          using False by auto
        have tmp2: "updTimedVar
     (apply_bcontfun
       (unique_on_bounded_closed.fixed_point 1 {1--1 + 1} (state2vec (timedVar2State h2' 1))
         (block2ODE
           (updateIntegBlks [Integ1, Bias, Integ2] (findIntegBlks [Integ1, Bias, Integ2])))
         UNIV))
     ''ax'' h2' 1 1 vv tt = h2' vv tt"
          using updTimedVar_eq1[of "''ax''" 1 1 ] using tmp1 by fastforce
        then show ?thesis
        proof(cases "tt = 1 \<and> vv = CHR ''x''")
          case True
          then show ?thesis using tmp2 by auto
        next
          case False
          have tmp: "\<not>(vv = CHR ''x'' \<and> 1 \<le> tt \<and> tt \<le> 2)"
            using False tmp1 by force
          then show ?thesis using tmp2 unfolding h_def by auto
        qed
      qed
      done
    have tmp8: "updTimedVar
       (apply_bcontfun
         (unique_on_bounded_closed.fixed_point 1 {1--1 + 1} (state2vec (timedVar2State h2' 1))
           (block2ODE
             (updateIntegBlks [Integ1, Bias, Integ2] (findIntegBlks [Integ1, Bias, Integ2])))
           UNIV)) ''ax'' h2' 1 1  = (\<lambda>v t. (if v = CHR ''x'' \<and> t > 1 \<and> t \<le> 2 then 2*t else h2' v t))"
      using tmp7 by presburger
    have tmp9: "getCalBlks [Integ1, Bias, Integ2] = [Bias]"
      unfolding getCalBlks.simps Integ1_def Bias_def Integ2_def by auto
    have tmp10: "exeCalBlks [Bias] (\<lambda>v t. (if v = CHR ''x'' \<and> t > 1 
        \<and> t \<le> 2 then 2*t else h2' v t)) 1 1 = h3"
      using exe2_0 by simp
    show ?thesis unfolding exeContinuousDiag_interval.simps solveODE_def using tmp5 tmp8 tmp9 tmp10 by simp
  qed
  have 3: "(rev (sortDiag ([Gain, UD1, UD2] @ getCalBlks [Integ1, Bias, Integ2]))) =
    [Bias, UD2, UD1, Gain]"
  proof -
    have tmp1: "getCalBlks [Integ1, Bias, Integ2] = [Bias]"
      unfolding getCalBlks.simps Integ1_def Bias_def Integ2_def by simp
    show ?thesis using sort_lemma tmp1 by auto
  qed
  show ?thesis unfolding exe_diag_interval.simps using 1 2 3 exe2_4 by auto
qed
  done

definition h5:: timed_vars where "h5 = (\<lambda>v t. (if v = CHR ''a'' \<and> t > 2 \<and> t \<le> 3 then 4*(t-2) 
else (if v = CHR ''x'' \<and> t > 2 \<and> t \<le> 3 then 2*t*t - 6*t + 8 else h4' v t)))"

definition h6:: timed_vars where "h6 = (\<lambda>v t. (if v = CHR ''b'' \<and> t > 2 \<and> t < 3 then 4*(t-2)+2 
else h5 v t ))"

lemma exe3_continuous : "exeCalBlks [Bias] h5 2 1 = h6"
proof -
  have 1: "(exeCalBlks [] h5 2 1) = h5"
    by simp
  have 2: "get_inputs Bias = ''a''"
    using Bias_def get_inputs.simps by (metis (no_types, lifting))
  have 3: "get_outputs Bias = ''b''"
    using Bias_def get_outputs.simps by (metis (no_types, lifting))
  have 4: "get_offsets Bias = [0]"
    using Bias_def get_offsets.simps by (metis (no_types, lifting))
  have 5: "get_outupd Bias = [\<lambda>s. if length s = 1 then hd s + 2 else 0]"
    using Bias_def get_outupd.simps by (metis (no_types, lifting))
  have 6: "exeCalBlk ''a'' ''b'' [0] [\<lambda>s. if length s = 1 then hd s + 2 else 0]
   h5 2 1 = h6"
  proof -
    have tmp1: "\<forall>h. exeCalBlk ''a'' [] [] [] h 2 1 = h"
      by simp
    have tmp2: "\<forall>t::real. t \<ge> 2 \<and> t < 3 \<longrightarrow> (h5 (CHR ''a'') t + 2) = 4*(t-2)+2"
      apply clarify subgoal for t
        unfolding h5_def h4'_def h4_def h3_def h2'_def h2_def h1_def h_def by simp
      done
    have tmp3: "\<forall>t::real. t \<ge> 2 \<and> t < 3 \<longrightarrow> hd (map (\<lambda>a. h5 a t) ''a'') + 2 = (h5 (CHR ''a'') t + 2)"
      using tmp2 by simp
    have tmp4: "\<forall>v t. (\<lambda>vv tt.
             if vv = CHR ''b'' \<and> tt < 2 + 1 \<and> 2 < tt
             then if length (map (\<lambda>a. h5 a tt) ''a'') = 1 then hd (map (\<lambda>a. h5 a tt) ''a'') + 2
                  else 0
             else h5 vv tt) v t = h6 v t"
      apply clarify subgoal for v t
    proof(cases "v = CHR ''b'' \<and> t < 2 + 1 \<and> 2 < t")
      case True
      then show ?thesis using tmp2 tmp3 by (simp add: h6_def)
    next
      case False
      then show ?thesis apply simp unfolding h6_def by auto
    qed
    done
    show ?thesis using exeCalBlk.simps(4)[of "''a''" "CHR ''b''" "[]" 0 "[]"
          "\<lambda>s. if length s = 1 then hd s + 2 else 0" "[]" h5 2 1] tmp4 by force
  qed
  show ?thesis using exeCalBlks.simps(2)[of "Bias" "[]" h5 2 3]
    using "1" "2" "3" "4" "5" "6" by auto
qed

lemma exe3_1: "\<forall>v. exeDisDiag_attime [Bias] h6 (Suc 2) v 3 = (\<lambda>v t. 
(if v = CHR ''b'' \<and> t = 3 then 6 else h6 v t)) v 3"
  apply clarify subgoal for v
  proof -
    have 1: "(get_sample_time Bias = 0)"
    proof -
      show ?thesis using Bias_def get_sample_time.simps by (metis (no_types, lifting))
    qed
    have 2: "(exeDisDiag_attime [] h6 3) = h6"
      using exeDisDiag_attime.simps(1)[of h6 3] by simp
    have 3: "get_inputs Bias = ''a''"
      using Bias_def get_inputs.simps by (metis (no_types, lifting))
    have 4: "get_outputs Bias = ''b''"
      using Bias_def get_outputs.simps by (metis (no_types, lifting))
    have 5: "get_offsets Bias = [0]"
      using Bias_def get_offsets.simps by (metis (no_types, lifting))
    have 6: "get_outupd Bias = [\<lambda>s. if length s = 1 then hd s + 2 else 0]"
      using Bias_def get_outupd.simps by (metis (no_types, lifting))
    have 7: "\<forall>v t. outupd_exe_atst ''a'' ''b'' [0] [\<lambda>s. if length s = 1 then hd s + 2 else 0]
         h6 3 v t = (\<lambda>v t. (if v = CHR ''b'' \<and> t = 3 then 6 else h6 v t)) v t"
    proof -
      have tmp1: "\<forall>h. outupd_exe_atst ''a'' [] [] [] h 3 = h"
        by auto
      have tmp2: "\<forall>v t. (\<lambda>vv tt.
       if tt = real 3 \<and> vv = CHR ''b''
       then if length (map (\<lambda>a. h6 a (real 3 - real 0)) ''a'') = 1
            then hd (map (\<lambda>a. h6 a (real 3 - real 0)) ''a'') + 2 else 0
       else h6 vv tt) v t = (\<lambda>vv tt. (if vv = CHR ''b'' \<and> tt = 3 then 6 else h6 vv tt)) v t"
        apply clarify subgoal for v t
        proof(cases "v = CHR ''b'' \<and> t = real 3")
          case True
          then show ?thesis unfolding h6_def h5_def h4_def h3_def h2_def h1_def h_def by force
        next
          case False
          then show ?thesis by auto
        qed
        done
      show ?thesis using outupd_exe_atst.simps(4)[of "''a''" "CHR ''b''" "[]" 0 "[]" "
        \<lambda>s. if length s = 1 then hd s + 2 else 0" "[]" h6 3] using tmp1 tmp2
        using outupd_exe_atst.simps(1) by presburger
    qed
    show ?thesis using exeDisDiag_attime.simps(2)[of "Bias" "[]" h6 3] using 1 2 3 4 5 6 7
      using One_nat_def Suc_1 by (metis numeral_3_eq_3)
  qed
  done

lemma exe3_2: "\<forall>v. exeDisDiag_attime [Gain] h6 (Suc 2) v 3 = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 3 then 16 else h6 v t)) v 3"
  apply clarify subgoal for v
  proof -
    have 1: "(\<exists>k. int 3 = get_sample_time Gain * k)"
    proof -
      have tmp1: "get_sample_time Gain = 1"
        using Gain_def get_sample_time.simps by (metis (no_types, lifting))
      have tmp2: "int 3 = get_sample_time Gain * 3"
        using tmp1 by simp
      show ?thesis using tmp2 by simp
    qed
    have 2: "(exeDisDiag_attime [] h6 3) = h6"
      using exeDisDiag_attime.simps(1)[of h6 3] by simp
    have 3: "get_inputs Gain = ''x''"
      using Gain_def get_inputs.simps by (metis (no_types, lifting))
    have 4: "get_outputs Gain = ''y''"
      using Gain_def get_outputs.simps by (metis (no_types, lifting))
    have 5: "get_offsets Gain = [0]"
      using Gain_def get_offsets.simps by (metis (no_types, lifting))
    have 6: "get_outupd Gain = [\<lambda>s. if length s = 1 then 2 * hd s else 0]"
      using Gain_def get_outupd.simps by (metis (no_types, lifting))
    have 7: "\<forall>v t. outupd_exe_atst ''x'' ''y'' [0] [\<lambda>s. if length s = 1 then 2 * hd s else 0]
         h6 3 v t = (\<lambda>v t. (if v = CHR ''y'' \<and> t = 3 then 16 else h6 v t)) v t"
    proof -
      have tmp1: "\<forall>h. outupd_exe_atst ''x'' [] [] [] h 3 = h"
        by auto
      have tmp2: "\<forall>v t. (\<lambda>vv tt.
       if tt = real 3 \<and> vv = CHR ''y''
       then if length (map (\<lambda>a. h6 a (real 3 - real 0)) ''x'') = 1
            then 2 * hd (map (\<lambda>a. h6 a (real 3 - real 0)) ''x'') else 0
       else h6 vv tt) v t = (\<lambda>v t. (if v = CHR ''y'' \<and> t = 3 then 16 else h6 v t)) v t"
        apply clarify subgoal for v t
        proof(cases "v = CHR ''y'' \<and> t = real 3")
          case True
          then show ?thesis unfolding h6_def h5_def h4_def h3_def h2_def h1_def h_def by auto
        next
          case False
          then show ?thesis using of_nat_numeral by auto
        qed
        done
      show ?thesis using outupd_exe_atst.simps(4)[of "''x''" "CHR ''y''" "[]" 0 "[]" "
        \<lambda>s. if length s = 1 then 2 * hd s else 0" "[]" "h6" 3] using tmp1 tmp2 
          using outupd_exe_atst.simps(1) by presburger
    qed
    show ?thesis using exeDisDiag_attime.simps(2)[of "Gain" "[]" h6 3] using 1 2 3 4 5 6 7
      by simp
  qed
  done

lemma exe3_3: "\<forall>v. exeDisDiag_attime [UD1, Gain] h6 3 v 3 = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 3 then 16 else if v = CHR ''s'' \<and> t = 3 then 16 else h6 v t)) v 3"
  apply clarify subgoal for v
  proof -
    have 1: "(\<exists>k. int 3 = get_sample_time UD1 * k)"
    proof -
      have tmp1: "get_sample_time UD1 = 1"
        using UD1_def get_sample_time.simps by (metis (no_types, lifting))
      have tmp2: "int 3 = get_sample_time UD1 * 3"
        using tmp1 by simp
      show ?thesis using tmp2 by simp
    qed
    have 2: "(exeDisDiag_attime [] h6 3) = h6"
      using exeDisDiag_attime.simps(1)[of h6 3] by simp
    have 3: "get_inputs UD1 = ''y''"
      using UD1_def get_inputs.simps by (metis (no_types, lifting))
    have 4: "get_outputs UD1 = ''s''"
      using UD1_def get_outputs.simps by (metis (no_types, lifting))
    have 5: "get_offsets UD1 = [0]"
      using UD1_def get_offsets.simps by (metis (no_types, lifting))
    have 6: "get_outupd UD1 = [\<lambda>s. if length s = 1 then hd s else 0]"
      using UD1_def get_outupd.simps by (metis (no_types, lifting))
    have 7: "\<forall>v t. outupd_exe_atst ''y'' ''s'' [0] [\<lambda>s. if length s = 1 then hd s else 0]
         (\<lambda>v t. (if v = CHR ''y'' \<and> t = 3 then 16 else h6 v t)) 3 v t = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 3 then 16 else if v = CHR ''s'' \<and> t = 3 then 16 else h6 v t)) v t"
    proof -
      have tmp1: "\<forall>h. outupd_exe_atst ''y'' [] [] [] h 3 = h"
        by auto
      have tmp2: "\<forall>v t. (\<lambda>vv tt.
       if tt = real 3 \<and> vv = CHR ''s''
       then if length
                (map (\<lambda>a. if a = CHR ''y'' \<and> real 3 - real 0 = 3 then 16
                          else h6 a (real 3 - real 0))
                  ''y'') =
               1
            then hd (map (\<lambda>a. if a = CHR ''y'' \<and> real 3 - real 0 = 3 then 16
                              else h6 a (real 3 - real 0))
                      ''y'')
            else 0
       else if vv = CHR ''y'' \<and> tt = 3 then 16 else h6 vv tt) v t = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 3 then 16 else if v = CHR ''s'' \<and> t = 3 then 16 else h6 v t)) v t"
        apply clarify subgoal for v t by simp
        done
      show ?thesis using outupd_exe_atst.simps(4)[of "''y''" "CHR ''s''" "[]" 0 "[]" "
        \<lambda>s. if length s = 1 then hd s else 0" "[]" "(\<lambda>v t. (if v = CHR ''y'' \<and> t = 3 then 16 else 
          h6 v t))" 3] using tmp1 tmp2 by presburger
    qed
    show ?thesis using exeDisDiag_attime.simps(2)[of "UD1" "[Gain]" h3 2] using 1 2 3 4 5 6 7
      exe3_2 by simp
  qed
  done

lemma exe3_4: "\<forall>v. exeDisDiag_attime [UD2, UD1, Gain] h6 (Suc 2) v 3 = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 3 then 16 else if v = CHR ''s'' \<and> t = 3 then 16 else
 if v = CHR ''z'' \<and> t = 3 then 8 else h6 v t)) v 3"
  apply clarify subgoal for v
  proof -
    have 1: "(\<exists>k. int 3 = get_sample_time UD2 * k)"
    proof -
      have tmp1: "get_sample_time UD2 = 1"
        using UD2_def get_sample_time.simps by (metis (no_types, lifting))
      have tmp2: "int 3 = get_sample_time UD2 * 3"
        using tmp1 by simp
      show ?thesis using tmp2 by simp
    qed
    have 2: "(exeDisDiag_attime [] h6 3) = h6"
      using exeDisDiag_attime.simps(1)[of h6 3] by simp
    have 3: "get_inputs UD2 = ''s''"
      using UD2_def get_inputs.simps by (metis (no_types, lifting))
    have 4: "get_outputs UD2 = ''z''"
      using UD2_def get_outputs.simps by (metis (no_types, lifting))
    have 5: "get_offsets UD2 = [1]"
      using UD2_def get_offsets.simps by (metis (no_types, lifting))
    have 6: "get_outupd UD2 = [\<lambda>s. if length s = 1 then hd s else 0]"
      using UD2_def get_outupd.simps by (metis (no_types, lifting))
    have 7: "\<forall>v t. outupd_exe_atst ''s'' ''z'' [1] [\<lambda>s. if length s = 1 then hd s else 0] (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 3 then 16 else if v = CHR ''s'' \<and> t = 3 then 16 else
h6 v t)) 3 v t = (\<lambda>v t. (if v = CHR ''y'' \<and> t = 3 then 16 else if v = CHR ''s'' \<and> t = 3 
then 16 else if v = CHR ''z'' \<and> t = 3 then 8 else h6 v t)) v t"
    proof -
      have tmp1: "\<forall>h. outupd_exe_atst ''s'' [] [] [] h 3 = h"
        by auto
      have tmp2: "\<forall>v t. (\<lambda>vv tt.
       if tt = real 3 \<and> vv = CHR ''z''
       then if length
                (map (\<lambda>a. if a = CHR ''y'' \<and> real 3 - real 1 = 3 then 16
                          else if a = CHR ''s'' \<and> real 3 - real 1 = 3 then 16
                               else h6 a (real 3 - real 1))
                  ''s'') =
               1
            then hd (map (\<lambda>a. if a = CHR ''y'' \<and> real 3 - real 1 = 3 then 16
                              else if a = CHR ''s'' \<and> real 3 - real 1 = 3 then 16
                                   else h6 a (real 3 - real 1))
                      ''s'')
            else 0
       else if vv = CHR ''y'' \<and> tt = 3 then 16
            else if vv = CHR ''s'' \<and> tt = 3 then 16 else h6 vv tt) v t = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 3 then 16 else if v = CHR ''s'' \<and> t = 3 then 16 else
if v = CHR ''z'' \<and> t = 3 then 8 else h6 v t)) v t"
        apply clarify subgoal for v t unfolding h4'_def h4_def h5_def h6_def by simp
        done
      show ?thesis using outupd_exe_atst.simps(4)[of "''s''" "CHR ''z''" "[]" 1 "[]" "
        \<lambda>s. if length s = 1 then hd s else 0" "[]" "(\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 3 then 16 else if v = CHR ''s'' \<and> t = 3 then 16 else h6 v t))"
            3] using tmp1 tmp2 by presburger
    qed
    show ?thesis using exeDisDiag_attime.simps(2)[of "UD2" "[UD1, Gain]" h6 3] using 1 2 3 4 5 6 7
      exe3_3 by (smt (z3) One_nat_def Suc_1 char.inject exeDisDiag_attime_lemma2 hd_map 
     length_map list.distinct(1) numeral_3_eq_3 outupd_exe_atst.simps(1) outupd_exe_atst.simps(4))
  qed
  done

definition h7::timed_vars where "h7 = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 3 then 16 else if v = CHR ''s'' \<and> t = 3 then 16 else
if v = CHR ''b'' \<and> t = 3 then 6 else if v = CHR ''z'' \<and> t = 3 then 8 else h6 v t))"

lemma exe3_5: "exeDisDiag_attime [Bias, UD2, UD1, Gain] h6 3 = h7"
  proof -
    have 1: "get_sample_time Bias = 0"
    proof -
      show ?thesis unfolding Bias_def by simp
    qed
    have 2: "(exeDisDiag_attime [] h6 3) = h6"
      using exeDisDiag_attime.simps(1)[of h6 3] by simp
    have 3: "get_inputs Bias = ''a''"
      using Bias_def get_inputs.simps by (metis (no_types, lifting))
    have 4: "get_outputs Bias = ''b''"
      using Bias_def get_outputs.simps by (metis (no_types, lifting))
    have 5: "get_offsets Bias = [0]"
      using Bias_def get_offsets.simps by (metis (no_types, lifting))
    have 6: "get_outupd Bias = [(\<lambda>s. (if length s = 1 then (hd s + 2::real) else 0))]"
      using Bias_def get_outupd.simps by (metis (no_types, lifting))
    have 7: "\<forall>v t. outupd_exe_atst ''a'' ''b'' [0] [(\<lambda>s. (if length s = 1 then (hd s + 2::real) else 0))]
 (\<lambda>v t. (if v = CHR ''y'' \<and> t = 3 then 16 else if v = CHR ''s'' \<and> t = 3 then 16 else
 if v = CHR ''z'' \<and> t = 3 then 8 else h6 v t)) 3 v t 
= h7 v t"
    proof -
      have tmp1: "\<forall>h. outupd_exe_atst ''a'' [] [] [] h 3 = h"
        by auto
      have tmp2: "\<forall>v t. (\<lambda>vv tt.
       if tt = real 3 \<and> vv = CHR ''b''
       then if length
                (map (\<lambda>a. if a = CHR ''y'' \<and> real 3 - real 0 = 3 then 16
                          else if a = CHR ''s'' \<and> real 3 - real 0 = 3 then 16
                               else if a = CHR ''z'' \<and> real 3 - real 0 = 3 then 8
                                    else h6 a (real 3 - real 0))
                  ''a'') =
               1
            then hd (map (\<lambda>a. if a = CHR ''y'' \<and> real 3 - real 0 = 3 then 16
                              else if a = CHR ''s'' \<and> real 3 - real 0 = 3 then 16
                                   else if a = CHR ''z'' \<and> real 3 - real 0 = 3 then 8
                                        else h6 a (real 3 - real 0))
                      ''a'') +
                 2
            else 0
       else if vv = CHR ''y'' \<and> tt = 3 then 16
            else if vv = CHR ''s'' \<and> tt = 3 then 16
                 else if vv = CHR ''z'' \<and> tt = 3 then 8 else h6 vv tt) 
      v t = h7 v t"
        apply clarify subgoal for v t unfolding h7_def h6_def h5_def 
            h4_def h3_def h2'_def h2_def h1_def h_def by simp
        done
      show ?thesis using outupd_exe_atst.simps(4)[of "''a''" "CHR ''b''" "[]" 0 "[]" "
        \<lambda>s. (if length s = 1 then (hd s + 2::real) else 0)" "[]" "(\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 3 then 16 else if v = CHR ''s'' \<and> t = 3 then 16 else
 if v = CHR ''z'' \<and> t = 3 then 8 else h6 v t))" 3] using tmp1 tmp2 by presburger
    qed
    have 8: "exeDisDiag_attime [UD2, UD1, Gain] h6 (Suc 2) = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 3 then 16 else if v = CHR ''s'' \<and> t = 3 then 16 else
 if v = CHR ''z'' \<and> t = 3 then 8 else h6 v t))"
    proof -
      have tmp1: "\<forall>v t. exeDisDiag_attime [UD2, UD1, Gain] h6 (Suc 2) v t = (\<lambda>v t. 
(if v = CHR ''y'' \<and> t = 3 then 16 else if v = CHR ''s'' \<and> t = 3 then 16 else
 if v = CHR ''z'' \<and> t = 3 then 8 else h6 v t)) v t"
        apply clarify subgoal for v t
        proof(cases "t = real 3")
          case True
          then show ?thesis using exe3_4 by auto
        next
          case False
          then show ?thesis using exeDisDiag_attime_lemma2[of t 3 "[UD2, UD1, Gain]" h6 v]
            by auto
        qed
        done
      show ?thesis using tmp1 by presburger
    qed
    have 9: "outupd_exe_atst ''a'' ''b'' [0] [(\<lambda>s. (if length s = 1 then (hd s + 2::real) else 0))]
 (\<lambda>v t. (if v = CHR ''y'' \<and> t = 3 then 16 else if v = CHR ''s'' \<and> t = 3 then 16 else
 if v = CHR ''z'' \<and> t = 3 then 8 else h6 v t)) 3 = h7"
      using 7 by presburger
    have 10: "outupd_exe_atst (get_inputs Bias) (get_outputs Bias) (get_offsets Bias) (get_outupd Bias)
         (exeDisDiag_attime [UD2, UD1, Gain] h6 3) 3 = h7"
      using 1 2 3 4 5 6 8 9 by auto
    show ?thesis using exeDisDiag_attime.simps(2)[of "Bias" "[UD2, UD1, Gain]" h6 3] 
      using 1 10 by auto
  qed

  term "ODE_cond"

lemma exe_diag_interval3: "ODE_cond (Block ''za'' ''ax'' [1, 1] 0
   (updateFunc2 [\<lambda>s. if length s = 1 then hd s else 0] ''a''
     (hd (updateFunc [\<lambda>s. if length s = 1 then hd s else 0] ''b'' CHR ''b''
           (\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))
     ''z'')) h4 2 1 \<Longrightarrow>
  exe_diag_interval [Gain, UD1, UD2] [Integ1, Bias, Integ2] h4 2 1 = h7"
  subgoal premises pre
  proof -
    have 0: "\<exists>L. unique_on_bounded_closed 2 {2--3} Vec2
  (\<lambda>t v. (\<chi> x.(if x = CHR ''x'' then v $ CHR ''a'' + 2 else 
  if x = CHR ''a'' then v $ CHR ''z'' else 0))) UNIV L"
    proof -
      have tmp1: "(block2ODE
         (Block ''za'' ''ax'' [1, 1] 0
           (updateFunc2 [\<lambda>s. if length s = 1 then hd s else 0] ''a''
             (hd (updateFunc [\<lambda>s. if length s = 1 then hd s else 0] ''b'' CHR ''b'' (\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a'')) ''z'')))
        = (\<lambda>t v. (\<chi> x.(if x = CHR ''x'' then v $ CHR ''a'' + 2 else 
  if x = CHR ''a'' then v $ CHR ''z'' else 0)))"
        using getODE'_2 by force
      show ?thesis using pre(1) unfolding ODE_cond_def  using tmp1 getVec2 by auto
    qed
  have 1: "(\<lambda>vv tt. if 2 < tt \<and> tt < 2 + 1 \<and> vv \<in> Outputs [Gain, UD1, UD2] then h4 vv 2 else h4 
  vv tt) = h4'"
  proof -
    have tmp1: "Outputs [Gain, UD1, UD2] = {CHR ''y'', CHR ''s'', CHR ''z''}"
      unfolding Gain_def UD1_def UD2_def Outputs.simps by auto
    have tmp2: "\<forall>v t. (\<lambda>vv tt. if 2 < tt \<and> tt < 2 + 1 \<and> vv \<in> Outputs [Gain, UD1, UD2] then h4 vv 2 else h4 
  vv tt) v t = h4' v t"
      apply clarify subgoal for v t
      proof(cases "2 < t \<and> t < 3 \<and> v = CHR ''y''")
        case True
        then show ?thesis using tmp1 unfolding h4'_def h4_def h2'_def h2_def h1_def h_def by auto
      next
        case False
        then show ?thesis using tmp1 unfolding h4'_def h4_def h3_def h2'_def h2_def h1_def h_def by auto
      qed
      done
    show ?thesis using tmp2 by presburger
  qed
  have 2: "exeContinuousDiag_interval [Integ1, Bias, Integ2] h4' 2 1 = h6"
  proof -
    have tmp1: "findIntegBlks [Integ1, Bias, Integ2] = [Integ1, Integ2]"
      unfolding findIntegBlks.simps Integ1_def Bias_def Integ2_def by auto
    have tmp2: "(block2ODE (updateIntegBlks [Integ1, Bias, Integ2] 
    (findIntegBlks [Integ1, Bias, Integ2]))) = (\<lambda>t v. (\<chi> x. (if x = CHR ''x'' then v $ CHR ''a'' + 2 else if 
      x = CHR ''a'' then v $ CHR ''z'' else 0)))"
      using updateIntegBlks_lemma getODE'_2 tmp1 by auto
    have tmp3: "(state2vec (timedVar2State h4' 2)) = Vec2"
      unfolding timedVar2State_def h4'_def h4_def h3_def
       h2'_def h2_def h1_def h_def Vec2_def state2vec_def by fastforce
    have tmp4: "\<forall>t \<in> {2 -- 3}. (apply_bcontfun
         (unique_on_bounded_closed.fixed_point 2 {2--2 + 1} (state2vec (timedVar2State h4' 2))
           (block2ODE
             (updateIntegBlks [Integ1, Bias, Integ2] (findIntegBlks [Integ1, Bias, Integ2])))
           UNIV)) t = (\<lambda>x. (\<chi> y.(if y = CHR ''x'' then 2*x*x - 6*x + 8
  else if y = CHR ''b'' then 2 else if
  y = CHR ''z'' then 4 else if y = CHR ''a'' then 4*(x-2) 
  else if y = CHR ''y'' then 8 else if y = CHR ''s'' then 8 else 0))) t "
      using tmp2 tmp3 solves3_fixedpoint 0 by simp
    have tmp5: "(get_outputs (updateIntegBlks [Integ1, Bias, Integ2] 
      (findIntegBlks [Integ1, Bias, Integ2]))) = ''ax''"
      using updateIntegBlks_lemma tmp1 by simp
    have tmp7: "\<forall>vv tt . updTimedVar
       (apply_bcontfun
         (unique_on_bounded_closed.fixed_point 2 {2--2 + 1} (state2vec (timedVar2State h4' 2))
           (block2ODE
             (updateIntegBlks [Integ1, Bias, Integ2] (findIntegBlks [Integ1, Bias, Integ2])))
           UNIV)) ''ax'' h4' 2 1 vv tt  = h5 vv tt"
      apply clarify subgoal for vv tt 
      proof(cases "vv \<in> set ''ax'' \<and> tt > (2::real) \<and> tt \<le> (3::real)")
        case True
        have tmp1: "tt \<in> {2::real -- 3::real}"
          using True by (simp add: Line_Segment.closed_segment_eq_real_ivl)
        then show ?thesis using True updTimedVar_eq2 tmp4 unfolding h5_def apply simp
          by fastforce
      next
        case False
        have tmp1: "vv \<notin> set ''ax'' \<or> tt \<le> 2 \<or> 3 < tt"
          using False by auto
        have tmp2: "updTimedVar
     (apply_bcontfun
       (unique_on_bounded_closed.fixed_point 2 {2--2 + 1} (state2vec (timedVar2State h4' 2))
         (block2ODE
           (updateIntegBlks [Integ1, Bias, Integ2] (findIntegBlks [Integ1, Bias, Integ2])))
         UNIV))
     ''ax'' h4' 2 1 vv tt = h5 vv tt"
          unfolding h5_def using updTimedVar_eq1[of "''ax''" 2 1 ] using tmp1 by fastforce
        then show ?thesis
        proof(cases "tt = 2 \<and> vv = CHR ''x''")
          case True
          then show ?thesis using tmp2 by auto
        next
          case False
          have tmp: "\<not>(vv = CHR ''x'' \<and> 2 \<le> tt \<and> tt \<le> 3)"
            using False tmp1 by force
          then show ?thesis using tmp2 unfolding h_def by auto
        qed
      qed
      done
    have tmp8: "updTimedVar
       (apply_bcontfun
         (unique_on_bounded_closed.fixed_point 2 {2--2 + 1} (state2vec (timedVar2State h4' 2))
           (block2ODE
             (updateIntegBlks [Integ1, Bias, Integ2] (findIntegBlks [Integ1, Bias, Integ2])))
           UNIV)) ''ax'' h4' 2 1  = h5"
      using tmp7 by presburger
    have tmp9: "getCalBlks [Integ1, Bias, Integ2] = [Bias]"
      unfolding getCalBlks.simps Integ1_def Bias_def Integ2_def by auto
    have tmp10: "exeCalBlks [Bias] h5 2 1 = h6"
      using exe3_continuous by simp
    show ?thesis unfolding exeContinuousDiag_interval.simps solveODE_def using tmp5 tmp8 tmp9 tmp10 by simp
  qed
  have 3: "(rev (sortDiag ([Gain, UD1, UD2] @ getCalBlks [Integ1, Bias, Integ2]))) =
    [Bias, UD2, UD1, Gain]"
  proof -
    have tmp1: "getCalBlks [Integ1, Bias, Integ2] = [Bias]"
      unfolding getCalBlks.simps Integ1_def Bias_def Integ2_def by simp
    show ?thesis using sort_lemma tmp1 by auto
  qed
  show ?thesis unfolding exe_diag_interval.simps using 1 2 3 exe3_5 by auto
qed
  done

lemma exe_diag: "ODE_cond (Block ''za'' ''ax'' [1, 1] 0
   (updateFunc2 [\<lambda>s. if length s = 1 then hd s else 0] ''a''
     (hd (updateFunc [\<lambda>s. if length s = 1 then hd s else 0] ''b'' CHR ''b''
           (\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))
     ''z'')) h' 0 1 \<Longrightarrow> ODE_cond (Block ''za'' ''ax'' [1, 1] 0
   (updateFunc2 [\<lambda>s. if length s = 1 then hd s else 0] ''a''
     (hd (updateFunc [\<lambda>s. if length s = 1 then hd s else 0] ''b'' CHR ''b''
           (\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))
     ''z'')) h2 1 1 \<Longrightarrow> ODE_cond (Block ''za'' ''ax'' [1, 1] 0
   (updateFunc2 [\<lambda>s. if length s = 1 then hd s else 0] ''a''
     (hd (updateFunc [\<lambda>s. if length s = 1 then hd s else 0] ''b'' CHR ''b''
           (\<lambda>s. if length s = 1 then hd s + 2 else 0) ''a''))
     ''z'')) h4 2 1 \<Longrightarrow> exe_diag_tilltime [Gain,UD1,UD2] [Integ1,Bias,Integ2] h 3 = h7"
  subgoal premises pre
proof -
  have 0: "getCalBlks [Integ1, Bias, Integ2] = [Bias]"
    unfolding getCalBlks.simps Integ1_def Bias_def Integ2_def by simp
  have 1: "exe_diag_tilltime [Gain,UD1,UD2] [Integ1,Bias,Integ2] h 0 = h'"
    unfolding exe_diag_tilltime.simps DisBlks_init.simps using sort_lemma 0 exe0_4 by simp
  have 2: "exe_diag_interval [Gain,UD1,UD2] [Integ1,Bias,Integ2] h' 0 1 = h2"
    using exe_diag_interval1 pre(1) by simp
  have 3: "exe_diag_interval [Gain,UD1,UD2] [Integ1,Bias,Integ2] h2 1 1 = h4"
    using exe_diag_interval2 pre(2) by simp
  have 4: "exe_diag_interval [Gain,UD1,UD2] [Integ1,Bias,Integ2] h4 2 1 = h7"
    using exe_diag_interval3 pre(3) by simp
  have 5: "3 = Suc (Suc (Suc 0))"
    by simp
  have 6: "exe_diag_tilltime [Gain,UD1,UD2] [Integ1,Bias,Integ2] h (Suc (Suc (Suc 0))) = h7"
    unfolding exe_diag_tilltime.simps using 1 2 3 4 by (metis (mono_tags, opaque_lifting)  
        exe_diag_tilltime.simps(1) numeral_1_eq_Suc_0 numeral_2_eq_2 numeral_eq_one_iff 
        of_nat_0_eq_iff of_nat_numeral)
  show ?thesis using 5 6 by presburger
qed
  done
    

end