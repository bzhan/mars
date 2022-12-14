theory System_coon
  imports ext_Complementlemma
begin


datatype scheduler =
  sch (pool:"(int \<times> string) list")

definition data :: char where "data = CHR ''x''"
definition t :: char where "t = CHR ''t''"
definition cmd :: char where "cmd = CHR ''c''"

lemma vars_distinct[simp]:"data \<noteq> t" "data \<noteq> cmd" "t\<noteq>data" "t\<noteq>cmd" "cmd\<noteq>data" "cmd\<noteq>t"
  unfolding data_def t_def cmd_def by auto

definition databuffer1 :: "cname \<Rightarrow> cname => scheduler proc" where
  "databuffer1 ch1 ch2 = data ::= (\<lambda>_.0); 
Rep (EChoice[(ch1[?]data,Skip),(ch2[!](\<lambda>(a,s). s data),Skip)])"

definition coon0 :: "scheduler proc" where
"coon0 = databuffer1 ''outputs_bus0_img'' ''inputs_imgacpimp_img''"

datatype io =
   In real
|  Out

fun endio :: "real \<Rightarrow> io list \<Rightarrow> real" where
  "endio d [] = d"
| "endio d (In r # res) = endio r res"
| "endio d (Out # res) = endio d res"

lemma endio_snoc1:
"endio d (fcs @ [In v]) = v"
proof (induction fcs arbitrary: d)
  case Nil
  then show ?case 
    by auto
next
  case Con:(Cons a fcs)
  then show ?case 
    proof (cases a)
      case (In x1)
      then show ?thesis 
        using endio.simps(2)[of d x1 "fcs @ [io.In v]"]
        using Con[of x1] by auto
    next
      case Out
      then show ?thesis 
        using endio.simps(3)[of d "fcs @ [io.In v]"]
        using Con[of d] by auto
    qed
qed

lemma endio_snoc2:
"endio d (fcs @ [Out]) = endio d fcs"
proof (induction fcs arbitrary: d)
  case Nil
  then show ?case 
    by auto
next
  case Con:(Cons a fcs)
  then show ?case 
    proof (cases a)
      case (In x1)
      then show ?thesis 
        using endio.simps(2)[of d x1 "fcs @ [io.Out]"]
        using Con[of x1] by auto
    next
      case Out
      then show ?thesis 
        using endio.simps(3)[of d "fcs @ [io.Out]"]
        using Con[of d] by auto
    qed
qed



inductive db1 :: "cname \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> io list \<Rightarrow> scheduler tassn" where
  "db1 ch1 ch2 d [] []"
| "Inrdy\<^sub>t (sch [],(\<lambda>_.0)(data := d)) ch1 r ({ch2},{ch1}) tr1
   \<Longrightarrow> db1 ch1 ch2 r res tr2 \<Longrightarrow> db1 ch1 ch2 d (In r # res) (tr1 @ tr2)"
| "Outrdy\<^sub>t (sch [],(\<lambda>_.0)(data := d)) ch2 d ({ch2},{ch1}) tr1
   \<Longrightarrow> db1 ch1 ch2 d res tr2 \<Longrightarrow> db1 ch1 ch2 d (Out # res) (tr1 @ tr2)"

lemma db1_snoc1:
"db1 ch1 ch2 d fcs tr1 \<Longrightarrow> 
Inrdy\<^sub>t (sch [],(\<lambda>_.0)(data := endio d fcs)) ch1 r ({ch2},{ch1}) tr2 \<Longrightarrow> 
db1 ch1 ch2 d (fcs@[In r]) (tr1 @ tr2)"
proof (induct rule: db1.induct)
  case (1 ch1 ch2 d)
  then show ?case 
    using db1.intros(2)[of d ch1 r ch2 tr2 "[]" "[]"]
    using db1.intros(1) 
    by (metis append_Nil endio.simps(1) self_append_conv)
next
  case (2 d ch1 r' ch2 tr11 res tr12)
  then show ?case 
    using db1.intros(2)[of d ch1 r' ch2 tr11 "res @ [io.In r]" "(tr12 @ tr2)"]
    using endio.simps(2)[of d r' res] by auto
next
  case (3 d ch1 ch2 tr11 res tr12)
  then show ?case 
    using db1.intros(3)[of d ch1 ch2 tr11 "res @ [io.In r]" "(tr12 @ tr2)"]
    using endio.simps(3)[of d res] by auto
qed


lemma db1_snoc2:
"db1 ch1 ch2 d fcs tr1 \<Longrightarrow> 
Outrdy\<^sub>t (sch [],(\<lambda>_.0)(data := endio d fcs)) ch2 (endio d fcs) ({ch2},{ch1}) tr2 \<Longrightarrow> 
db1 ch1 ch2 d (fcs@[Out]) (tr1 @ tr2)"
proof (induct rule: db1.induct)
  case (1 ch1 ch2 d)
  then show ?case 
    using db1.intros(3)[of d ch1 ch2 tr2 "[]" "[]"]
    using db1.intros(1) 
    by (metis append_Nil db1.intros(3) endio.simps(1) self_append_conv)
next
  case (2 d ch1 r' ch2 tr11 res tr12)
  then show ?case 
    using db1.intros(2)[of d ch1 r' ch2 tr11 "res @ [io.Out]" "(tr12 @ tr2)"]
    using endio.simps(2)[of d r' res] by auto
next
  case (3 d ch1 ch2 tr11 res tr12)
  then show ?case 
    using db1.intros(3)[of d ch1 ch2 tr11 "res @ [io.Out]" "(tr12 @ tr2)"]
    using endio.simps(3)[of d res] by auto
qed

lemma databuffer1_prop:
"\<Turnstile>{\<lambda>(a,s) t. (a,s) = (sch [],\<lambda>_ . 0) \<and> emp\<^sub>t t}
databuffer1 ch1 ch2 
{\<lambda>(a,s) t. \<exists> list. (a,s) = (sch [],(\<lambda>_ . 0)(data := endio 0 list)) \<and> db1 ch1 ch2 0 list t}"
  unfolding databuffer1_def
  apply(rule Valid_seq)
   prefer 2
   apply(rule Valid_rep)
   prefer 2
   apply(rule Valid_strengthen_post)
  prefer 2
    apply(rule Valid_assign_sp)
  subgoal
   apply (auto simp add: entails_def emp_assn_def)
  subgoal for s d
    apply (rule exI[where x="[]"])
    apply (metis db1.intros(1) endio.simps(1) fun_upd_idem fun_upd_same)
    done
  done
  apply(rule Valid_ex_pre')
  subgoal for fcs
    apply (rule Valid_echoice_sp)
    apply auto
    subgoal for i cm p
      apply (cases i)
       apply auto
      subgoal
       apply(rule Valid_strengthen_post)
        prefer 2
        apply(rule Valid_skip)
        apply(auto simp add: entails_def)
        subgoal for tr v
          apply(rule exI[where x="fcs@[In v]"])
          by(auto simp add: join_assn_def db1_snoc1 endio_snoc1)
        done
      subgoal
        apply(rule Valid_strengthen_post)
        prefer 2
        apply(rule Valid_skip)
        apply(auto simp add: entails_def)
        subgoal for tr   
          apply(rule exI[where x="fcs@[Out]"])
          by(auto simp add: join_assn_def db1_snoc2 endio_snoc2)
        done
      done
    done
  done
          


lemma coon0_prop:
"\<Turnstile>{\<lambda>(a,s) t. (a,s) = (sch [],\<lambda>_ . 0) \<and> emp\<^sub>t t}
coon0
{\<lambda>(a,s) t. \<exists> list. (a,s) = (sch [],(\<lambda>_ . 0)(data := endio 0 list)) \<and> db1 ''outputs_bus0_img'' ''inputs_imgacpimp_img'' 0 list t}"
  unfolding coon0_def
  by(rule databuffer1_prop)



definition ACT_periodic :: "cname \<Rightarrow> real \<Rightarrow> scheduler proc"  where
"ACT_periodic ch period = Rep(Cm (ch[!](\<lambda>_ .0));Wait(\<lambda>_.period))"

fun ACT_periodic_block :: "cname \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> scheduler tassn" where
  "ACT_periodic_block ch period 0 = emp\<^sub>t"
| "ACT_periodic_block ch period (Suc n) = 
  Out\<^sub>t (EState (sch [], (\<lambda>_ . 0))) ch 0 @\<^sub>t 
  Wait\<^sub>t period (\<lambda>_ . (EState (sch [], (\<lambda>_ . 0)))) ({},{}) @\<^sub>t
  ACT_periodic_block ch period n"

lemma ACT_periodic_block_snoc:
"ACT_periodic_block ch period (Suc n) = 
  ACT_periodic_block ch period n @\<^sub>t 
  Out\<^sub>t (EState (sch [], (\<lambda>_ . 0))) ch 0 @\<^sub>t 
  Wait\<^sub>t period (\<lambda>_ . (EState (sch [], (\<lambda>_ . 0)))) ({},{})"
proof (induction n)
  case 0
  then show ?case 
    using ACT_periodic_block.simps(1)
    by auto
next
  case Con:(Suc n)
  show ?case 
    apply(subst ACT_periodic_block.simps(2)[of ch period "Suc n"])
    apply(subst Con)
    apply(subst ACT_periodic_block.simps(2)[of ch period "n"])
    by(auto simp add: join_assoc)
qed

lemma ACT_periodic_prop:
  assumes "period>0"
  shows"\<Turnstile>{\<lambda>(a,s) t. (a,s) = (sch [],\<lambda>_ . 0) \<and> emp\<^sub>t t}
ACT_periodic ch period
{\<lambda>(a,s) t. \<exists> n. (a,s) = (sch [],(\<lambda>_ . 0)) \<and> ACT_periodic_block ch period n t}"
  unfolding ACT_periodic_def
  apply(rule Valid_weaken_pre)
   prefer 2
   apply(rule Valid_rep)
   apply(rule Valid_ex_pre')
   apply(rule Valid_ex_post')
  subgoal for n
    apply(rule exI[where x="Suc n"])
    apply(rule Valid_seq)
     apply(rule Valid_send_sp_st)
    apply(rule Valid_strengthen_post)
    prefer 2
     apply(rule Valid_wait_sp_st)
    apply(auto simp add:entails_def assms)
    using ACT_periodic_block_snoc[of ch period n]
    by (simp add: join_assoc)
  apply(auto simp add:entails_def)
  subgoal for tr
    apply(rule exI[where x="0"])
    by auto
  done


end
