theory ExampleSimple
  imports BigStepParallel
begin


subsection \<open>Test of big-step semantics\<close>

text \<open>Send 1 immediately\<close>
lemma test1a: "big_step (Cm (''ch''[!](\<lambda>_. 1)))
  (\<lambda>_. 0) [OutBlock ''ch'' 1] (\<lambda>_. 0)"
  by (rule sendB1)

text \<open>Send x + 1 immediately\<close>
lemma test1b: "big_step (Cm (''ch''[!](\<lambda>s. s X + 1)))
  ((\<lambda>_. 0)(X := 1)) [OutBlock ''ch'' 2] ((\<lambda>_. 0)(X := 1))"
  apply (rule big_step_cong) apply (rule sendB1) by auto

text \<open>Send 1 after delay 2\<close>
lemma test1c: "big_step (Cm (''ch''[!](\<lambda>_. 1)))
  (\<lambda>_. 0) [WaitBlk 2 (\<lambda>_. State (\<lambda>_. 0)) ({''ch''}, {}),
           OutBlock ''ch'' 1] (\<lambda>_. 0)"
  by (rule sendB2, auto)

text \<open>Receive 1 immediately\<close>
lemma test2a: "big_step (Cm (''ch''[?]X))
  (\<lambda>_. 0) [InBlock ''ch'' 1] ((\<lambda>_. 0)(X := 1))"
  by (rule receiveB1)

text \<open>Receive 1 after delay 2\<close>
lemma test2b: "big_step (Cm (''ch''[?]X))
  (\<lambda>_. 0) [WaitBlk 2 (\<lambda>_. State (\<lambda>_. 0)) ({}, {''ch''}),
           InBlock ''ch'' 1] ((\<lambda>_. 0)(X := 1))"
  by (rule receiveB2, auto)

text \<open>Communication\<close>
lemma test3: "par_big_step (
  Parallel (Single (Cm (''ch''[!](\<lambda>_. 1)))) {''ch''}
           (Single (Cm (''ch''[?]X))))
  (ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0)))
    [IOBlock ''ch'' 1]
  (ParState (State (\<lambda>_. 0)) (State ((\<lambda>_. 0)(X := 1))))"
  apply (rule ParallelB)
    apply (rule SingleB[OF test1a])
   apply (rule SingleB[OF test2a])
  by (auto intro: combine_blocks.intros)

text \<open>Wait\<close>
lemma test4: "big_step (Wait (\<lambda>_. 2))
  (\<lambda>_. 0) [WaitBlk 2 (\<lambda>_. State (\<lambda>_. 0)) ({}, {})] (\<lambda>_. 0)"
  apply (rule waitB1) by auto

text \<open>Seq\<close>
lemma test5: "big_step (Wait (\<lambda>_. 2); Cm (''ch''[!](\<lambda>_. 1)))
  (\<lambda>_. 0) [WaitBlk 2 (\<lambda>_. State (\<lambda>_. 0)) ({}, {}), OutBlock ''ch'' 1] (\<lambda>_. 0)"
  apply (rule big_step_cong) apply (rule seqB[OF test4 test1a]) by auto

text \<open>Communication after delay 2\<close>
lemma test6: "par_big_step (
  Parallel (Single (Wait (\<lambda>_. 2); Cm (''ch''[!](\<lambda>_. 1)))) {''ch''}
           (Single (Cm (''ch''[?]X))))
  (ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0)))
    [WaitBlk 2 (\<lambda>_. ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0))) ({}, {''ch''}), IOBlock ''ch'' 1]
  (ParState (State (\<lambda>_. 0)) (State ((\<lambda>_. 0)(X := 1))))"
  apply (rule ParallelB)
    apply (rule SingleB[OF test5])
   apply (rule SingleB[OF test2b])
  by (auto intro!: combine_blocks.intros)

text \<open>Loop one time\<close>
lemma test7: "big_step (Rep (Assign X (\<lambda>s. s X + 1); Cm (''ch''[!](\<lambda>s. s X))))
  (\<lambda>_. 0) [OutBlock ''ch'' 1] ((\<lambda>_. 0)(X := 1))"
  apply (rule RepetitionB2)
    apply (rule seqB) apply (rule assignB) apply (rule sendB1)
  apply auto[1] apply (rule RepetitionB1)
  by auto

text \<open>Loop two times\<close>
lemma test8: "big_step (Rep (Assign X (\<lambda>s. s X + 1); Cm (''ch''[!](\<lambda>s. s X))))
  (\<lambda>_. 0) [OutBlock ''ch'' 1, OutBlock ''ch'' 2] ((\<lambda>_. 0)(X := 2))"
  apply (rule RepetitionB2)
    apply (rule seqB) apply (rule assignB) apply (rule sendB1)
   apply auto[1] apply (rule RepetitionB2)
     apply (rule seqB) apply (rule assignB) apply (rule sendB1)
    apply auto[1] apply (rule RepetitionB1)
  by auto

text \<open>External choice 1\<close>
lemma test9a: "big_step (EChoice [(''ch1''[!](\<lambda>_. 1), Wait (\<lambda>_. 1)),
                                  (''ch2''[!](\<lambda>_. 2), Wait (\<lambda>_. 2))])
  (\<lambda>_. 0) [OutBlock ''ch1'' 1, WaitBlk 1 (\<lambda>_. State (\<lambda>_. 0)) ({}, {})] (\<lambda>_. 0)"
  apply (rule EChoiceSendB1[where i=0])
  apply auto apply (rule waitB1) by auto

text \<open>External choice 2\<close>
lemma test9b: "big_step (EChoice [(''ch1''[!](\<lambda>_. 1), Wait (\<lambda>_. 1)),
                                  (''ch2''[!](\<lambda>_. 2), Wait (\<lambda>_. 2))])
  (\<lambda>_. 0) [OutBlock ''ch2'' 2, WaitBlk 2 (\<lambda>_. State (\<lambda>_. 0)) ({}, {})] (\<lambda>_. 0)"
  apply (rule EChoiceSendB1[where i=1])
  apply auto apply (rule waitB1) by auto

text \<open>Communication with external choice\<close>
lemma test10: "par_big_step (
  Parallel (Single (EChoice [(''ch1''[!](\<lambda>_. 1), Wait (\<lambda>_. 1)),
                             (''ch2''[!](\<lambda>_. 2), Wait (\<lambda>_. 2))])) {''ch1'', ''ch2''}
           (Single (Cm (''ch1''[?]X); Wait (\<lambda>_. 1))))
  (ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0)))
    [IOBlock ''ch1'' 1, WaitBlk 1 (\<lambda>_. ParState (State (\<lambda>_. 0)) (State ((\<lambda>_. 0)(X := 1)))) ({}, {})]
  (ParState (State (\<lambda>_. 0)) (State ((\<lambda>_. 0)(X := 1))))"
  apply (rule ParallelB)
    apply (rule SingleB[OF test9a])
   apply (rule SingleB)
   apply (rule seqB) apply (rule receiveB1) apply (rule waitB1)
  apply auto
  by (intro combine_blocks.intros, auto)

text \<open>ODE Example 1\<close>
lemma test11: "big_step (Cont (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 1))
  (\<lambda>_. 0) [WaitBlk 1 (\<lambda>t. State ((\<lambda>_. 0)(X := t))) ({}, {})] ((\<lambda>_. 0)(X := 1))"
  apply (rule ContB2)
  apply (auto simp add: ODEsol_def state2vec_def fun_upd_def has_vderiv_on_def)
  apply (rule has_vector_derivative_projI)
  by (auto intro!: derivative_intros)

text \<open>Interrupt examples\<close>

text \<open>Exit through boundary\<close>
lemma test_interrupt1:
  "big_step (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 2) [(''ch''[!](\<lambda>_. 1), Assign X (\<lambda>_. 0))])
    (\<lambda>_. 0) [WaitBlk 2 (\<lambda>t. State ((\<lambda>_. 0)(X := t))) ({''ch''}, {})] ((\<lambda>_. 0)(X := 2))"
  apply (rule InterruptB2)
  apply (auto simp add: ODEsol_def state2vec_def fun_upd_def has_vderiv_on_def)
  apply (rule has_vector_derivative_projI)
  by (auto intro!: derivative_intros)

text \<open>Immediate communication\<close>
lemma test_interrupt2:
  "big_step (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 2) [(''ch''[!](\<lambda>_. 1), Assign X (\<lambda>_. 3))])
    (\<lambda>_. 0) [OutBlock ''ch'' 1] ((\<lambda>_. 0)(X := 3))"
  apply (rule InterruptSendB1)
    apply (auto simp add: ODEsol_def state2vec_def fun_upd_def has_vderiv_on_def)
  apply (rule big_step_cong) apply (rule assignB) by auto

text \<open>Communication in the middle\<close>
lemma test_interrupt3:
  "big_step (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 2) [(''ch''[!](\<lambda>_. 1), Assign X (\<lambda>_. 3))])
    (\<lambda>_. 0) [WaitBlk 1 (\<lambda>t. State ((\<lambda>_. 0)(X := t))) ({''ch''}, {}),
             OutBlock ''ch'' 1] ((\<lambda>_. 0)(X := 3))"
  apply (rule InterruptSendB2)
  apply (auto simp add: ODEsol_def state2vec_def fun_upd_def has_vderiv_on_def)
  apply (rule has_vector_derivative_projI)
   apply (auto intro!: derivative_intros)
  apply (rule big_step_cong) apply (rule assignB) by auto

text \<open>Note with current definition, communication at the end is also possible\<close>
lemma test_interrupt4:
  "big_step (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>s. s X < 2) [(''ch''[!](\<lambda>_. 1), Assign X (\<lambda>_. 3))])
    (\<lambda>_. 0) [WaitBlk 2 (\<lambda>t. State ((\<lambda>_. 0)(X := t))) ({''ch''}, {}),
             OutBlock ''ch'' 1] ((\<lambda>_. 0)(X := 3))"
  apply (rule InterruptSendB2)
  apply (auto simp add: ODEsol_def state2vec_def fun_upd_def has_vderiv_on_def)
  apply (rule has_vector_derivative_projI)
  apply (auto intro!: derivative_intros)
  apply (rule big_step_cong) apply (rule assignB) by auto

subsection \<open>Difference between internal and external choice\<close>

text \<open>This example shows the difference between semantics of internal
and external choice. We begin with the process with internal choice,
  (ch1!1 \<squnion> ch2!2)*,
which can produce the trace (2,s,{ch2!})^(ch2!,2)^(ch1!,1).
\<close>
lemma test_internal:
  "big_step (Rep (IChoice (Cm (''ch1''[!](\<lambda>_. 1))) (Cm (''ch2''[!](\<lambda>_. 2)))))
    (\<lambda>_. 0) [WaitBlk 2 (\<lambda>_. State (\<lambda>_. 0)) ({''ch2''}, {}),
             OutBlock ''ch2'' 2,
             OutBlock ''ch1'' 1] (\<lambda>_. 0)"
  apply (rule RepetitionB2)
    apply (rule IChoiceB2)
    apply (rule sendB2[where d=2]) apply auto[1]
  apply (rule RepetitionB2)
  apply (rule IChoiceB1)
     apply (rule sendB1) apply (rule RepetitionB1)
  by auto

text \<open>For external choice, the process
  (ch1!1 \<rightarrow> skip $ ch2!2 \<rightarrow> skip)*
produces the trace (2,s,{ch1!,ch2!})^(ch2!,2)^(ch1!,1).
\<close>
lemma test_external:
  "big_step (Rep (EChoice [(''ch1''[!](\<lambda>_. 1), Skip), (''ch2''[!](\<lambda>_. 2), Skip)]))
    (\<lambda>_. 0) [WaitBlk 2 (\<lambda>_. State (\<lambda>_. 0)) ({''ch1'', ''ch2''}, {}),
             OutBlock ''ch2'' 2,
             OutBlock ''ch1'' 1] (\<lambda>_. 0)"
  apply (rule RepetitionB2)
    apply (rule EChoiceSendB2[where d=2 and i=1])
       apply auto apply (rule skipB)
  apply (rule RepetitionB2)
    apply (rule EChoiceSendB1[where i=0])
      apply auto apply (rule skipB)
  by (rule RepetitionB1)

text \<open>The other side is the process
  (wait 1; ch1?x) || (wait 2; ch2?x),
which can produce the trace (1,s,{})^(1,s,{ch1?})^(ch2?,2)^(ch1?,1).
\<close>
lemma test_internal_other:
  "par_big_step (Parallel (Single (Wait (\<lambda>_. 1); Cm (''ch1''[?]X))) {}
                          (Single (Wait (\<lambda>_. 2); Cm (''ch2''[?]X))))
    (ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0)))
    [WaitBlk 1 (\<lambda>_. ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0))) ({}, {}),
     WaitBlk 1 (\<lambda>_. ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0))) ({}, {''ch1''}),
     InBlock ''ch2'' 2,
     InBlock ''ch1'' 1]
    (ParState (State ((\<lambda>_. 0)(X := 1))) (State ((\<lambda>_. 0)(X := 2))))"
proof -
  have left: "big_step (Wait (\<lambda>_. 1); Cm (''ch1''[?]X)) (\<lambda>_. 0)
    [WaitBlk 1 (\<lambda>_. State (\<lambda>_. 0)) ({}, {}),
     WaitBlk 1 (\<lambda>_. State (\<lambda>_. 0)) ({}, {''ch1''}),
     InBlock ''ch1'' 1] ((\<lambda>_. 0)(X := 1))"
    apply (rule big_step_cong) apply (rule seqB) apply (rule waitB1)
    apply auto apply (rule receiveB2) by auto
  have right: "big_step (Wait (\<lambda>_. 2); Cm (''ch2''[?]X)) (\<lambda>_. 0)
    [WaitBlk 2 (\<lambda>_. State (\<lambda>_. 0)) ({}, {}),
     InBlock ''ch2'' 2] ((\<lambda>_. 0)(X := 2))"
    apply (rule big_step_cong) apply (rule seqB) apply (rule waitB1)
    apply auto by (rule receiveB1)
  show ?thesis
    apply (rule ParallelB)
      apply (rule SingleB[OF left])
     apply (rule SingleB[OF right])
    apply (rule combine_blocks_wait2) apply auto
    apply (rule combine_blocks_wait1) apply auto
     apply (rule combine_blocks_unpair2) apply auto
     apply (rule combine_blocks_unpair1) apply auto
    by (rule combine_blocks_empty)
qed

text \<open>The two sides can be synchronized, so the process
  (ch1!1 \<squnion> ch2!2)* || ((wait 1; ch1?x) || (wait 2; ch2?x))
can produce the trace (1,s,{ch2!})^(1,s,{ch1?,ch2!})^(ch2,2)^(ch1,1).

However, for the case of external choice, the two sides cannot be
synchronized, since the test of compat_rdy fails in the time interval (1,2).
\<close>
lemma test_internal_parallel:
  "par_big_step (Parallel
    (Single (Rep (IChoice (Cm (''ch1''[!](\<lambda>_. 1))) (Cm (''ch2''[!](\<lambda>_. 2)))))) {''ch1'', ''ch2''}
    (Parallel (Single (Wait (\<lambda>_. 1); Cm (''ch1''[?]X))) {}
              (Single (Wait (\<lambda>_. 2); Cm (''ch2''[?]X)))))
    (ParState (State (\<lambda>_. 0)) (ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0))))
    [WaitBlk 1 (\<lambda>_. ParState (State (\<lambda>_. 0)) (ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0)))) ({''ch2''}, {}),
     WaitBlk 1 (\<lambda>_. ParState (State (\<lambda>_. 0)) (ParState (State (\<lambda>_. 0)) (State (\<lambda>_. 0)))) ({''ch2''}, {''ch1''}),
     IOBlock ''ch2'' 2,
     IOBlock ''ch1'' 1]
    (ParState (State (\<lambda>_. 0))
              (ParState (State ((\<lambda>_. 0)(X := 1))) (State ((\<lambda>_. 0)(X := 2)))))"
  apply (rule ParallelB)
    apply (rule SingleB[OF test_internal])
  apply (rule test_internal_other)
  apply (rule combine_blocks_wait3) apply auto
  apply (rule combine_blocks_wait1) apply auto
  apply (rule combine_blocks_pair2) apply auto
  apply (rule combine_blocks_pair2) apply auto
  by (rule combine_blocks_empty)


subsection \<open>Tests for combine_blocks\<close>

lemma test_combine1:
  "combine_blocks {''ch''} [InBlock ''ch'' v] [OutBlock ''ch'' v] [IOBlock ''ch'' v]"
  by (intro combine_blocks.intros, auto)

lemma test_combine1_unique:
  "combine_blocks {''ch''} [InBlock ''ch'' v] [OutBlock ''ch'' v] blks \<Longrightarrow>
   blks = [IOBlock ''ch'' v]"
  by (auto elim: sync_elims)

lemma test_combine2:
  "combine_blocks {} [InBlock ''ch1'' v] [OutBlock ''ch2'' w] [InBlock ''ch1'' v, OutBlock ''ch2'' w]"
  by (intro combine_blocks.intros, auto)

lemma test_combine2_unique:
  "combine_blocks {} [InBlock ''ch1'' v] [OutBlock ''ch2'' w] blks \<Longrightarrow>
   blks = [InBlock ''ch1'' v, OutBlock ''ch2'' w] \<or>
   blks = [OutBlock ''ch2'' w, InBlock ''ch1'' v]"
  apply (elim combine_blocks_unpairE2) by (auto elim: sync_elims)

subsection \<open>Simple examples of proofs\<close>

text \<open>Send 1\<close>
lemma testHL1:
  "\<Turnstile> {\<lambda>s tr. Q s (tr @ [OutBlock ''ch'' 1]) \<and>
              (\<forall>d>0. Q s (tr @ [WaitBlk d (\<lambda>_. State s) ({''ch''}, {}), OutBlock ''ch'' 1]))}
        Cm (''ch''[!](\<lambda>_. 1))
      {Q}"
  by (rule Valid_send)

text \<open>This implies the strongest postcondition form\<close>
lemma testHL1':
  "\<Turnstile> {\<lambda>s t. s = st \<and> t = tr}
        Cm (''ch''[!](\<lambda>_. 1))
      {\<lambda>s t. s = st \<and>
           (t = tr @ [OutBlock ''ch'' 1] \<or>
             (\<exists>d>0. t = tr @ [WaitBlk d (\<lambda>_. State st) ({''ch''}, {}), OutBlock ''ch'' 1]))}"
  apply (rule Valid_weaken_pre)
   prefer 2
   apply (rule Valid_send)
  unfolding entails_def by auto

text \<open>Send 1, then send 2\<close>
lemma testHL2:
  "\<Turnstile> {\<lambda>s tr. (Q s ((tr @ [OutBlock ''ch'' 1]) @ [OutBlock ''ch'' 2]) \<and>
               (\<forall>d>0. Q s ((tr @ [OutBlock ''ch'' 1]) @ [WaitBlk d (\<lambda>_. State s) ({''ch''}, {}), OutBlock ''ch'' 2]))) \<and>
              (\<forall>d>0. Q s ((tr @ [WaitBlk d (\<lambda>_. State s) ({''ch''}, {}), OutBlock ''ch'' 1]) @ [OutBlock ''ch'' 2]) \<and>
               (\<forall>da>0. Q s ((tr @ [WaitBlk d (\<lambda>_. State s) ({''ch''}, {}), OutBlock ''ch'' 1]) @
                             [WaitBlk da (\<lambda>_. State s) ({''ch''}, {}), OutBlock ''ch'' 2])))}
        Cm (''ch''[!](\<lambda>_. 1)); Cm (''ch''[!](\<lambda>_. 2))
      {Q}"
  apply (rule Valid_seq)
    prefer 2 apply (rule Valid_send)
  by (rule Valid_send)

text \<open>Receive from ch\<close>
lemma testHL3:
  "\<Turnstile> {\<lambda>s tr.
        (\<forall>v. Q (s(X := v)) (tr @ [InBlock ''ch'' v])) \<and>
        (\<forall>d>0. \<forall>v. Q (s(X := v)) (tr @ [WaitBlk d (\<lambda>_. State s) ({}, {''ch''}), InBlock ''ch'' v]))}
       Cm (''ch''[?]X)
      {Q}"
  by (rule Valid_receive)

text \<open>Strongest postcondition form\<close>
lemma testHL3':
  "\<Turnstile> {\<lambda>s t. s = st \<and> t = tr}
       (Cm (''ch''[?]X))
      {\<lambda>s t. (\<exists>v. s = st(X := v) \<and>
              (t = tr @ [InBlock ''ch'' v]) \<or>
                 (\<exists>d>0. t = tr @ [WaitBlk d (\<lambda>_. State st) ({}, {''ch''}), InBlock ''ch'' v]))}"
  apply (rule Valid_weaken_pre)
   prefer 2
   apply (rule testHL3)
  unfolding entails_def by auto


subsection \<open>Simple examples redone\<close>

text \<open>Send 1\<close>
lemma testHL1s:
  "\<Turnstile> {\<lambda>s. Out\<^sub>t s ''ch'' (s X) @- P s}
       Cm (''ch''[!](\<lambda>s. s X))
      {P}"
  by (rule Valid_send')

text \<open>Strongest postcondition form\<close>
lemma testHL1s':
  "\<Turnstile> {\<lambda>s tr. s = st \<and> P tr}
       Cm (''ch''[!](\<lambda>s. s X))
      {\<lambda>s tr. s = st \<and> (P @\<^sub>t Out\<^sub>t st ''ch'' (st X)) tr}"
  by (rule Valid_send_sp)

text \<open>Send 1, then send 2\<close>
lemma testHL2s:
  "\<Turnstile> {\<lambda>s. Out\<^sub>t s ''ch'' (s X) @- Out\<^sub>t s ''ch'' (s Y) @- P s}
        Cm (''ch''[!](\<lambda>s. s X)); Cm (''ch''[!](\<lambda>s. s Y))
      {P}"
  apply (rule Valid_seq)
    prefer 2 apply (rule Valid_send')
  by (rule Valid_send')

text \<open>Strongest postcondition form\<close>
lemma testHL2s':
  "\<Turnstile> {\<lambda>s tr. s = st \<and> P tr}
        Cm (''ch''[!](\<lambda>s. s X)); Cm (''ch''[!](\<lambda>s. s Y))
      {\<lambda>s tr. s = st \<and> (P @\<^sub>t (Out\<^sub>t s ''ch'' (s X)) @\<^sub>t (Out\<^sub>t s ''ch'' (s Y))) tr}"
  apply (rule Valid_seq)
   apply (rule Valid_send_sp)
  apply (rule Valid_strengthen_post)
   prefer 2 apply (rule Valid_send_sp)
  by (auto simp add: entails_def join_assoc)

text \<open>Receive from ch\<close>
lemma testHL3s:
  "\<Turnstile> {\<lambda>s. \<forall>\<^sub>tv. In\<^sub>t s ''ch'' v @- P (s(X := v))}
        Cm (''ch''[?]X)
      {P}"
  by (rule Valid_receive')

text \<open>Strongest postcondition form\<close>
lemma testHL3s':
  "\<Turnstile> {\<lambda>s tr. s = st \<and> P tr}
       Cm (''ch''[?]X)
      {\<lambda>s tr. \<exists>v. s = st(X := v) \<and> (P @\<^sub>t In\<^sub>t st ''ch'' v) tr}"
  by (rule Valid_receive_sp)

text \<open>Receive two values in a row\<close>
lemma testHL3a:
  "\<Turnstile> {\<lambda>s. \<forall>\<^sub>tv. In\<^sub>t s ''ch'' v @- (\<forall>\<^sub>tw. In\<^sub>t (s(X := v)) ''ch'' w @- P (s(X := w)))}
        Cm (''ch''[?]X); Cm (''ch''[?]X)
      {P}"
  apply (rule Valid_weaken_pre) prefer 2
  apply (rule Valid_seq)
    prefer 2 apply (rule Valid_receive')
  apply (rule Valid_receive')
  by (auto simp add: entails_def)

text \<open>Strongest postcondition form\<close>
lemma testHL3a':
  "\<Turnstile> {\<lambda>s tr. s = st \<and> P tr}
        Cm (''ch''[?]X); Cm (''ch''[?]X)
      {\<lambda>s tr. \<exists>v w. s = st(X := w) \<and> (P @\<^sub>t In\<^sub>t st ''ch'' v @\<^sub>t In\<^sub>t (st(X := v)) ''ch'' w) tr}"
  apply (rule Valid_seq)
   apply (rule Valid_receive_sp)
  apply (rule Valid_ex_pre)
  subgoal for v apply (rule Valid_ex_post)
    apply (rule exI[where x=v])
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_receive_sp)
    by (auto simp add: entails_def join_assoc)
  done

text \<open>Communication\<close>
lemma testHL4s:
  "\<Turnstile>\<^sub>p
    {pair_assn (\<lambda>s. s = st1) (\<lambda>s. s = st2)}
      Parallel (Single (Cm (''ch''[!](\<lambda>s. s X)))) {''ch''}
               (Single (Cm (''ch''[?]X)))
    {left_gassn (sing_assn (\<lambda>s. s = st1)) \<and>\<^sub>g
     right_gassn (sing_assn (\<lambda>s. s = st2(X := st1 X))) \<and>\<^sub>g
     trace_gassn (IO\<^sub>t ''ch'' (st1 X))}"
  apply (rule ParValid_conseq')
    apply (rule ParValid_Parallel')
     apply (rule testHL1s')
    apply (rule testHL3s')
   apply auto[1]
  apply (auto simp add: sing_gassn_ex sing_gassn_split)
  apply (rule sync_gassn_ex_pre_right)
  subgoal for v
    unfolding sync_gassn_state_left sync_gassn_state_right
    apply (rule and_entails_gassn2[OF sync_gassn_traces])
    apply (rule and_entails_gassn2[OF entails_trace_gassn])
     apply (rule combine_assn_out_in') apply auto
    by (auto simp add: entails_gassn_def and_gassn_def conj_assn_def pure_assn_def trace_gassn_def)
  done

text \<open>Receive then send\<close>
lemma testHL5:
  "\<Turnstile> {\<lambda>s. \<forall>\<^sub>tv. In\<^sub>t s ''ch1'' v @- Out\<^sub>t (s(X := v)) ''ch2'' (v + 1) @- Q (s(X := v))}
        Cm (''ch1''[?]X); Cm (''ch2''[!](\<lambda>s. s X + 1))
      {Q}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_seq)
    prefer 2 apply (rule Valid_send')
   apply (rule Valid_receive')
  by auto

text \<open>Receive then send, strongest postcondition version\<close>
lemma testHL5sp:
  "\<Turnstile>
    {\<lambda>s tr. s = st \<and> P s tr}
      Cm (''ch1''[?]X); Cm (''ch2''[!](\<lambda>s. s X + 1))
    {\<lambda>s tr. \<exists>v. s = st(X := v) \<and> ((P st @\<^sub>t In\<^sub>t st ''ch1'' v) @\<^sub>t Out\<^sub>t (st(X := v)) ''ch2'' (v + 1)) tr}"
  apply (rule Valid_seq)
   apply (rule Valid_receive_sp)
  apply (rule Valid_ex_pre)
  subgoal for v
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_send_sp)
    by (auto simp add: entails_def)
  done

subsection \<open>Test for internal choice\<close>

text \<open>Contrast this with the case of internal choice\<close>
lemma ichoice_test1:
  "\<Turnstile>
    {\<lambda>s. (\<forall>\<^sub>tv. In\<^sub>t s ''ch1'' v @- Q (s(X := v))) \<and>\<^sub>t
         (\<forall>\<^sub>tv. In\<^sub>t s ''ch2'' v @- Q (s(X := v)))}
      IChoice (Cm (''ch1''[?]X)) (Cm (''ch2''[?]X))
    {Q}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_ichoice)
    apply (rule Valid_receive') apply (rule Valid_receive')
  unfolding entails_def conj_assn_def by auto

text \<open>Strongest postcondition form\<close>

lemma ichoice_test1':
  "\<Turnstile>
    {\<lambda>s tr. s = st \<and> P tr}
      IChoice (Cm (''ch1''[?]X)) (Cm (''ch2''[?]X))
    {\<lambda>s tr. (\<exists>v. s = st(X := v) \<and> (P @\<^sub>t In\<^sub>t st ''ch1'' v) tr) \<or>
            (\<exists>v. s = st(X := v) \<and> (P @\<^sub>t In\<^sub>t st ''ch2'' v) tr)}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule ichoice_test1)
  apply (auto simp add: entails_def conj_assn_def magic_wand_assn_def join_assn_def all_assn_def)
  subgoal for tr v tr'
    apply (rule exI[where x=v])
    apply auto
    apply (rule exI[where x=tr])
    by auto
  done

subsection \<open>Test for external choice\<close>

text \<open>Some special cases of EChoice\<close>

lemma InIn_lemma:
  assumes "Q ch1 var1 p1"
    and "Q ch2 var2 p2"
    and "i < length [(ch1[?]var1, p1), (ch2[?]var2, p2)]"
  shows "case [(ch1[?]var1, p1), (ch2[?]var2, p2)] ! i of
            (ch[!]e, p1) \<Rightarrow> P ch e p1
          | (ch[?]var, p1) \<Rightarrow> Q ch var p1"
proof -
  have "case comm of ch[!]e \<Rightarrow> P ch e p | ch[?]var \<Rightarrow> Q ch var p"
    if "i < Suc (Suc 0)"
       "[(ch1[?]var1, p1), (ch2[?]var2, p2)] ! i = (comm, p)" for comm p i
  proof -
    have "i = 0 \<or> i = 1"
      using that(1) by auto
    then show ?thesis
      apply (rule disjE)
      using that(2) assms by auto
  qed
  then show ?thesis
    using assms(3) by auto
qed

theorem Valid_echoice_InIn:
  assumes "\<Turnstile> {Q1} p1 {R}"
    and "\<Turnstile> {Q2} p2 {R}"
  shows "\<Turnstile>
    {\<lambda>s tr. (\<forall>v. Q1 (s(var1 := v)) (tr @ [InBlock ch1 v])) \<and>
            (\<forall>d>0. \<forall>v. Q1 (s(var1 := v)) (tr @ [WaitBlk d (\<lambda>_. State s) ({}, {ch1, ch2}), InBlock ch1 v])) \<and>
            (\<forall>v. Q2 (s(var2 := v)) (tr @ [InBlock ch2 v])) \<and>
            (\<forall>d>0. \<forall>v. Q2 (s(var2 := v)) (tr @ [WaitBlk d (\<lambda>_. State s) ({}, {ch1, ch2}), InBlock ch2 v]))}
      EChoice [(ch1[?]var1, p1), (ch2[?]var2, p2)]
    {R}"
  apply (rule Valid_echoice)
  apply (rule InIn_lemma)
  subgoal apply (rule exI[where x=Q1])
    by (auto simp add: assms entails_def)
  apply (rule exI[where x=Q2])
  by (auto simp add: assms entails_def)

theorem Valid_echoice_InIn':
  assumes "\<Turnstile> {Q1} p1 {R}"
    and "\<Turnstile> {Q2} p2 {R}"
  shows "\<Turnstile>
    {\<lambda>s. (\<forall>\<^sub>tv. ((Inrdy\<^sub>t s ch1 v ({}, {ch1, ch2})) @- Q1 (s(var1 := v)))) \<and>\<^sub>t
         (\<forall>\<^sub>tv. ((Inrdy\<^sub>t s ch2 v ({}, {ch1, ch2})) @- Q2 (s(var2 := v))))}
      EChoice [(ch1[?]var1, p1), (ch2[?]var2, p2)]
    {R}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_echoice_InIn[OF assms(1-2)])
  apply (auto simp add: entails_def magic_wand_assn_def conj_assn_def all_assn_def)
  by (auto simp add: inrdy_assn.intros)

theorem Valid_echoice_InIn_sp:
  assumes "\<And>v. \<Turnstile> {\<lambda>s tr. s = st(var1 := v) \<and> (P st @\<^sub>t Inrdy\<^sub>t st ch1 v ({}, {ch1, ch2})) tr} p1 {Q1 v}"
    and "\<And>v. \<Turnstile> {\<lambda>s tr. s = st(var2 := v) \<and> (P st @\<^sub>t Inrdy\<^sub>t st ch2 v ({}, {ch1, ch2})) tr} p2 {Q2 v}"
  shows
   "\<Turnstile> {\<lambda>s tr. s = st \<and> P s tr}
        EChoice [(ch1[?]var1, p1), (ch2[?]var2, p2)]
       {\<lambda>s tr. (\<exists>v. Q1 v s tr) \<or> (\<exists>v. Q2 v s tr)}"
  apply (rule Valid_echoice_sp)
  apply (rule InIn_lemma)
  using assms apply (auto simp add: Valid_def) by blast+

lemma echoice_test1:
  "\<Turnstile>
    {\<lambda>s. (\<forall>\<^sub>tv. ((Inrdy\<^sub>t s ''ch1'' v ({}, {''ch1'', ''ch2''})) @- Q (s(X := v)))) \<and>\<^sub>t
         (\<forall>\<^sub>tv. ((Inrdy\<^sub>t s ''ch2'' v ({}, {''ch1'', ''ch2''})) @- Q (s(X := v))))}
      EChoice [(''ch1''[?]X, Skip), (''ch2''[?]X, Skip)]
    {Q}"
  apply (rule Valid_echoice_InIn')
   apply (rule Valid_skip)
  by (rule Valid_skip)

text \<open>Strongest postcondition form\<close>
lemma testEChoice1:
  "\<Turnstile>
    {\<lambda>s tr. s = st \<and> P s tr}
      EChoice [(''ch1''[?]X, Y ::= (\<lambda>s. s Y + s X)), (''ch2''[?]X, Y ::= (\<lambda>s. s Y - s X))]
    {\<lambda>s tr. (\<exists>v. s = st(X := v, Y := st Y + v) \<and> (P st @\<^sub>t Inrdy\<^sub>t st ''ch1'' v ({}, {''ch1'', ''ch2''})) tr) \<or>
            (\<exists>v. s = st(X := v, Y := st Y - v) \<and> (P st @\<^sub>t Inrdy\<^sub>t st ''ch2'' v ({}, {''ch1'', ''ch2''})) tr)}"
  apply (rule Valid_strengthen_post)
  prefer 2
   apply (rule Valid_echoice_InIn_sp)
    apply (rule Valid_assign_sp)
   apply (rule Valid_assign_sp)
  by auto

datatype dir = CH1 | CH2

fun echoice_ex_inv :: "state \<Rightarrow> (dir \<times> real) list \<Rightarrow> tassn" where
  "echoice_ex_inv st [] = emp\<^sub>t"
| "echoice_ex_inv st ((CH1, v) # rest) =
    Inrdy\<^sub>t st ''ch1'' v ({}, {''ch1'', ''ch2''}) @\<^sub>t echoice_ex_inv (st(X := v, Y := st Y + v)) rest"
| "echoice_ex_inv st ((CH2, v) # rest) =
    Inrdy\<^sub>t st ''ch2'' v ({}, {''ch1'', ''ch2''}) @\<^sub>t echoice_ex_inv (st(X := v, Y := st Y - v)) rest"

fun last_echoice_ex :: "state \<Rightarrow> (dir \<times> real) list \<Rightarrow> state" where
  "last_echoice_ex st [] = st"
| "last_echoice_ex st ((CH1, v) # rest) = last_echoice_ex (st(X := v, Y := st Y + v)) rest"
| "last_echoice_ex st ((CH2, v) # rest) = last_echoice_ex (st(X := v, Y := st Y - v)) rest"

lemma echoice_ex_inv_snoc [simp]:
  "echoice_ex_inv st (ins @ [(CH1, v)]) =
    echoice_ex_inv st ins @\<^sub>t Inrdy\<^sub>t (last_echoice_ex st ins) ''ch1'' v ({}, {''ch1'', ''ch2''}) \<and>
   echoice_ex_inv st (ins @ [(CH2, v)]) =
    echoice_ex_inv st ins @\<^sub>t Inrdy\<^sub>t (last_echoice_ex st ins) ''ch2'' v ({}, {''ch1'', ''ch2''})"
  apply (induct ins arbitrary: st)
  subgoal by auto
  apply auto subgoal for dir v ins st
    apply (cases dir)
    by (auto simp add: join_assoc)
  subgoal for dir v ins st
    apply (cases dir)
    by (auto simp add: join_assoc)
  done

lemma last_echoice_ex_snoc [simp]:
  "last_echoice_ex st (ins @ [(CH1, v)]) = (last_echoice_ex st ins)(X := v, Y := last_echoice_ex st ins Y + v) \<and>
   last_echoice_ex st (ins @ [(CH2, v)]) = (last_echoice_ex st ins)(X := v, Y := last_echoice_ex st ins Y - v)"
  apply (induct ins arbitrary: st)
  apply auto
  by (metis (full_types) dir.exhaust last_echoice_ex.simps(2) last_echoice_ex.simps(3))+

lemma testEChoice:
  "\<Turnstile>
    {\<lambda>s tr. s = st \<and> tr = []}
      Rep (EChoice [(''ch1''[?]X, Y ::= (\<lambda>s. s Y + s X)),
                    (''ch2''[?]X, Y ::= (\<lambda>s. s Y - s X))])
    {\<lambda>s tr. \<exists>ins. s = last_echoice_ex st ins \<and> echoice_ex_inv st ins tr}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
   apply (rule Valid_ex_pre)
  subgoal for ins
    apply (rule Valid_strengthen_post)
    prefer 2
     apply (rule Valid_echoice_InIn_sp)
    apply (rule Valid_assign_sp)
     apply (rule Valid_assign_sp)
    apply (auto simp add: entails_def)
    subgoal for tr v
      apply (rule exI[where x="ins@[(CH1,v)]"])
      by auto
    subgoal for tr v
      apply (rule exI[where x="ins@[(CH2,v)]"])
      by auto
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by (auto simp add: emp_assn_def)


subsection \<open>Examples for loops\<close>

text \<open>First example simply counts up variable X.\<close>

fun count_up_inv :: "real \<Rightarrow> nat \<Rightarrow> tassn" where
  "count_up_inv a 0 = emp\<^sub>t"
| "count_up_inv a (Suc n) = Out\<^sub>t ((\<lambda>_. 0)(X := a + 1)) ''ch'' (a + 1) @\<^sub>t count_up_inv (a + 1) n"

lemma count_up_inv_Suc:
  "count_up_inv a (Suc n) = count_up_inv a n @\<^sub>t Out\<^sub>t ((\<lambda>_. 0)(X := a + real n + 1)) ''ch'' (a + real n + 1)"
  apply (induct n arbitrary: a)
   apply (auto simp add: join_assoc)
  by (smt join_assoc)

lemma testLoop1:
  "\<Turnstile>
    {\<lambda>s tr. s = ((\<lambda>_. 0)(X := a)) \<and> emp\<^sub>t tr}
      Rep (Assign X (\<lambda>s. s X + 1); Cm (''ch''[!](\<lambda>s. s X)))
    {\<lambda>s tr. \<exists>n. s = ((\<lambda>_. 0)(X := a + n)) \<and> count_up_inv a n tr}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
  apply (rule Valid_ex_pre)
  subgoal for n
    apply (rule Valid_seq)
    apply (rule Valid_assign_sp)
  apply (rule Valid_strengthen_post) prefer 2
     apply (rule Valid_send_sp)
    apply (auto simp add: entails_def)
    apply (rule exI[where x="Suc n"])
    by (auto simp add: count_up_inv_Suc simp del: count_up_inv.simps)    
  apply (auto simp add: entails_def)
  apply (rule exI[where x=0])
  by (auto simp add: emp_assn_def)

text \<open>In each iteration, increment by 1, output, then increment by 2.\<close>
fun count_up3_inv :: "nat \<Rightarrow> tassn" where
  "count_up3_inv 0 = emp\<^sub>t"
| "count_up3_inv (Suc n) = count_up3_inv n @\<^sub>t Out\<^sub>t ((\<lambda>_. 0)(X := 3 * real n + 1)) ''ch'' (3 * real n + 1)"

lemma testLoop2:
  "\<Turnstile>
    {\<lambda>s tr. s = ((\<lambda>_. 0)(X := 0)) \<and> emp\<^sub>t tr}
      Rep (Assign X (\<lambda>s. s X + 1); Cm (''ch''[!](\<lambda>s. s X)); Assign X (\<lambda>s. s X + 2))
    {\<lambda>s tr. \<exists>n. s = ((\<lambda>_. 0)(X := 3 * real n)) \<and> count_up3_inv n tr}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
   apply (rule Valid_ex_pre)
  subgoal for n
    apply (rule Valid_seq)
     apply (rule Valid_assign_sp)
    apply (rule Valid_seq)
     apply (rule Valid_send_sp)
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_assign_sp)
    apply (auto simp add: entails_def)
    apply (rule exI[where x="Suc n"])
    by auto
    apply (auto simp add: entails_def)
  apply (rule exI[where x=0])
  by (auto simp add: emp_assn_def)

text \<open>Example that repeatedly receives on X\<close>

text \<open>Here a is the starting value of X\<close>
fun receive_inv :: "real \<Rightarrow> real list \<Rightarrow> tassn" where
  "receive_inv a [] = emp\<^sub>t"
| "receive_inv a (x # xs) = In\<^sub>t ((\<lambda>_. 0)(Y := a)) ''ch'' x @\<^sub>t receive_inv x xs"

fun last_val :: "real \<Rightarrow> real list \<Rightarrow> real" where
  "last_val a [] = a"
| "last_val a (x # xs) = last_val x xs"

lemma receive_inv_snoc:
  "receive_inv a (xs @ [v]) = receive_inv a xs @\<^sub>t In\<^sub>t ((\<lambda>_. 0)(Y := last_val a xs)) ''ch'' v"
  apply (induct xs arbitrary: a)
  by (auto simp add: join_assoc)

lemma last_val_snoc [simp]:
  "last_val a (xs @ [v]) = v"
  by (induct xs arbitrary: a, auto)

lemma testLoop3:
  "\<Turnstile>
    {\<lambda>s tr. s = ((\<lambda>_. 0)(Y := a)) \<and> emp\<^sub>t tr}
      Rep (Cm (''ch''[?]Y))
    {\<lambda>s tr. \<exists>xs. s = ((\<lambda>_. 0)(Y := last_val a xs)) \<and> receive_inv a xs tr}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
  apply (rule Valid_ex_pre)
  subgoal for xs
    apply (rule Valid_strengthen_post)
     prefer 2 apply (rule Valid_receive_sp)
    apply (auto simp add: entails_def)
    subgoal for tr v
      apply (rule exI[where x="xs@[v]"])
      by (auto simp add: receive_inv_snoc)
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by (auto simp add: emp_assn_def)

text \<open>Example that repeated receives, and add the input values\<close>

text \<open>Here a is the starting value of X, b is the starting value of Y\<close>
fun receive_add_inv :: "real \<Rightarrow> real \<Rightarrow> real list \<Rightarrow> tassn" where
  "receive_add_inv a b [] = emp\<^sub>t"
| "receive_add_inv a b (x # xs) = In\<^sub>t ((\<lambda>_. 0)(X := a, Y := b)) ''ch'' x @\<^sub>t receive_add_inv (a + x) x xs"

fun last_add_val :: "real \<Rightarrow> real list \<Rightarrow> real" where
  "last_add_val a [] = a"
| "last_add_val a (x # xs) = last_add_val (a + x) xs"

lemma receive_add_inv_snoc:
  "receive_add_inv a b (xs @ [v]) = receive_add_inv a b xs @\<^sub>t In\<^sub>t ((\<lambda>_. 0)(X := last_add_val a xs, Y := last_val b xs)) ''ch'' v"
  apply (induct xs arbitrary: a b)
  by (auto simp add: join_assoc)

lemma last_add_val_snoc [simp]:
  "last_add_val a (xs @ [v]) = last_add_val a xs + v"
  by (induct xs arbitrary: a, auto)

lemma testLoop4:
  "\<Turnstile>
    {\<lambda>s tr. s = ((\<lambda>_. 0)(X := a, Y := b)) \<and> emp\<^sub>t tr}
     Rep (Cm (''ch''[?]Y); X ::= (\<lambda>s. s X + s Y))
    {\<lambda>s tr. \<exists>xs. s = ((\<lambda>_. 0)(X := last_add_val a xs, Y := last_val b xs)) \<and> receive_add_inv a b xs tr}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_rep)
  apply (rule Valid_ex_pre)
  subgoal for xs
    apply (rule Valid_seq)
     apply (rule Valid_receive_sp)
    apply (rule Valid_ex_pre)
    subgoal for v
      apply (rule Valid_strengthen_post)
       prefer 2
       apply (rule Valid_assign_sp)
    apply (auto simp add: entails_def)
    subgoal for tr
      apply (rule exI[where x="xs@[v]"])
      by (auto simp add: receive_add_inv_snoc)
    done
  done
  apply (auto simp add: entails_def)
  apply (rule exI[where x="[]"])
  by (auto simp add: emp_assn_def)

subsection \<open>Example of parallel\<close>

fun count_up_io_inv :: "real \<Rightarrow> nat \<Rightarrow> tassn" where
  "count_up_io_inv a 0 = emp\<^sub>t"
| "count_up_io_inv a (Suc n) = IO\<^sub>t ''ch'' (a + 1) @\<^sub>t count_up_io_inv (a + 1) n"

fun count_up_list :: "real \<Rightarrow> nat \<Rightarrow> real list" where
  "count_up_list a 0 = []"
| "count_up_list a (Suc n) = (a + 1) # count_up_list (a + 1) n"

lemma last_val_count_up_list [simp]:
  "last_val a (count_up_list a n) = a + n"
  apply (induction n arbitrary: a) by auto

lemma combine_count_up:
  "combine_assn {''ch''} (count_up_inv a n) (receive_inv b xs) \<Longrightarrow>\<^sub>t
   \<up>(xs = count_up_list a n) \<and>\<^sub>t count_up_io_inv a n"
proof (induction n arbitrary: a b xs)
  case 0
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis
      by (auto simp add: conj_assn_def pure_assn_def)
  next
    case (Cons x xs')
    then show ?thesis
      by (auto simp add: combine_assn_emp_in)
  qed
next
  case (Suc n)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis
      by (auto simp add: combine_assn_out_emp)
  next
    case (Cons x xs')
    then show ?thesis
      apply auto
      apply (rule entails_tassn_trans)
       apply (rule combine_assn_out_in)
       apply (auto simp add: entails_tassn_def)
      using Suc[of "a + 1" "a + 1" xs']
      unfolding entails_tassn_def conj_assn_def pure_assn_def join_assn_def
      by auto
  qed
qed

lemma testLoopPar:
  "\<Turnstile>\<^sub>p
    {pair_assn (\<lambda>s. s = ((\<lambda>_. 0)(X := a))) (\<lambda>s. s = ((\<lambda>_. 0)(Y := a)))}
      Parallel (Single (Rep (Assign X (\<lambda>s. s X + 1); Cm (''ch''[!](\<lambda>s. s X))))) {''ch''}
               (Single (Rep (Cm (''ch''[?]Y))))
    {\<exists>\<^sub>gn. left_gassn (sing_assn (\<lambda>s. s = ((\<lambda>_. 0)(X := a + n)))) \<and>\<^sub>g 
          right_gassn (sing_assn (\<lambda>s. s = ((\<lambda>_. 0)(Y := a + n)))) \<and>\<^sub>g
          trace_gassn (count_up_io_inv a n)}"
  apply (rule ParValid_conseq')
    apply (rule ParValid_Parallel')
     apply (rule testLoop1)
    apply (rule testLoop3)
   apply (auto simp add: sing_gassn_ex sing_gassn_split)
  apply (rule sync_gassn_ex_pre_left)
  apply (rule sync_gassn_ex_pre_right)
  subgoal for n xs
    unfolding sync_gassn_state_left sync_gassn_state_right
    apply (rule entails_ex_gassn)
    apply (rule exI[where x=n])
    apply (rule and_entails_gassn2[OF sync_gassn_traces])
    apply (rule and_entails_gassn2[OF entails_trace_gassn])
    apply (rule entails_tassn_trans)
     prefer 2 apply (rule combine_count_up)
    apply (rule combine_assn_mono)
    by (auto simp add: entails_tassn_def entails_gassn_def and_gassn_def conj_assn_def
                       trace_gassn_def pure_assn_def)
  done


end
