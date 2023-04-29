theory DiscreteSemantics
  imports DiscreteSyntax 
begin

fun minimal:: "nat list \<Rightarrow> nat" where
  "minimal [] = undefined"
| "minimal (x#xs) = (if xs = [] then x else if x < minimal xs then x else minimal xs)"

\<comment> \<open>Given input il, output vl, out/upd functions fl, outupd_behav_atst il vl fl returns the behavior in terms of constraints at sample time hit.\<close>
fun outupd_behav_atst :: "var list \<Rightarrow> var list \<Rightarrow> offset list \<Rightarrow> outupd list \<Rightarrow> nat \<Rightarrow> behav" where
"outupd_behav_atst il [] ol fl t h = True" |
"outupd_behav_atst il vl ol [] t h = True" |
"outupd_behav_atst il vl [] fl t h = True" |
"outupd_behav_atst il (v#vl) (d#ol) (f#fl) t h = ((h v t = f (map (\<lambda> a. h a (real t-real d)) il)) \<and> outupd_behav_atst il vl ol fl t h)"
(*f may not use all the inputs vars*)

lemma outupd_behav_atst_eq: "\<forall>x \<in> (set vl). (\<forall>t. h1 x t = h2 x t) \<Longrightarrow>
\<forall> x \<in> (set il). (\<forall>t \<le> real (n-(minimal ol)). h1 x t = h2 x t) \<Longrightarrow>
outupd_behav_atst il vl ol fl n h1 \<Longrightarrow>
outupd_behav_atst il vl ol fl n h2"
proof (induction vl arbitrary:ol fl)
  case Nil
  then show ?case by auto
next
  case (Cons a vl)
  then show ?case 
      proof (cases "fl = []")
        case True
        then show ?thesis
          using outupd_behav_atst.elims(3) by blast
      next
        case False
        have 2: "fl = (hd fl) # (tl fl)"
          using False by auto
        then show ?thesis
          proof (cases "ol = []")
            case True
            then show ?thesis
              using outupd_behav_atst.elims(3) by blast
          next
            case False
            have 3: "ol = (hd ol) # (tl ol)"
              using False by auto
            have 4: "outupd_behav_atst il vl (tl ol) (tl fl) n h2"
            proof(cases "(tl ol) = []")
              case True
              then show ?thesis using outupd_behav_atst.elims(3) by force
            next
              case False
              have tmp1: "minimal (tl ol) \<ge> minimal ol"
                using False 3 minimal.simps(2) by (metis less_or_eq_imp_le)
              have tmp2: "\<forall>x\<in>set vl. \<forall>t. h1 x t = h2 x t"
                using Cons(2) by simp
              have tmp3: "\<forall>x\<in>set il. \<forall>t\<le>real (n - minimal (tl ol)). h1 x t = h2 x t"
                using Cons(3) tmp1 by simp
              have tmp4: "outupd_behav_atst il vl (tl ol) (tl fl) n h1"
                using Cons(4) 3 2  outupd_behav_atst.simps(4) by metis
              then show ?thesis using tmp2 tmp3 tmp4 Cons(1) by simp
            qed
            have 5: "h1 a n = (hd fl) (map (\<lambda> a. h1 a (real n-real (hd ol))) il)"
              using Cons 2 3 outupd_behav_atst.simps(4) by metis
            have tmp1 : "h1 a n = h2 a n"
              using Cons by auto
            have tmp2 : "(map (\<lambda> a. h1 a (real n-real (hd ol))) il) = 
                         (map (\<lambda> a. h2 a (real n-real (hd ol))) il)"
              using Cons(3) 
              by (smt (verit, ccfv_SIG) "3" le_eq_less_or_eq map_eq_conv minimal.simps(2) 
                  of_nat_0_le_iff of_nat_diff of_nat_less_iff)
            have 6: "h2 a n = (hd fl) (map (\<lambda> a. h2 a (real n-real (hd ol))) il)"
              using 5 tmp1 tmp2 by auto
            then show ?thesis 
              using 4 5 outupd_behav_atst.simps(4)by (smt (verit, best) "2" "3" map_eq_conv)
          qed
        qed
qed

lemma outupd_behav_atst_eq2: "\<forall>x \<in> (set vl). (\<forall>t. h1 x t = h2 x t) \<Longrightarrow>
\<forall> x \<in> (set il). (\<forall>t \<le> (real n- real (minimal ol)). h1 x t = h2 x t) \<Longrightarrow>
outupd_behav_atst il vl ol fl n h1 \<Longrightarrow>
outupd_behav_atst il vl ol fl n h2"
proof (induction vl arbitrary:ol fl)
  case Nil
  then show ?case by auto
next
  case (Cons a vl)
  then show ?case
      proof (cases "fl = []")
        case True
        then show ?thesis
          using outupd_behav_atst.elims(3) by blast
      next
        case False
        have 2: "fl = (hd fl) # (tl fl)"
          using False by auto
        then show ?thesis
          proof (cases "ol = []")
            case True
            then show ?thesis
              using outupd_behav_atst.elims(3) by blast
          next
            case False
            have 3: "ol = (hd ol) # (tl ol)"
              using False by auto
            have 4: "outupd_behav_atst il vl (tl ol) (tl fl) n h2"
            proof(cases "(tl ol) = []")
              case True
              then show ?thesis using outupd_behav_atst.elims(3) by force
            next
              case False
              have tmp1: "minimal (tl ol) \<ge> minimal ol"
                using False 3 minimal.simps(2) by (metis less_or_eq_imp_le)
              have tmp2: "\<forall>x\<in>set vl. \<forall>t. h1 x t = h2 x t"
                using Cons(2) by simp
              have tmp3: "\<forall>x\<in>set il. \<forall>t\<le>(real n - minimal (tl ol)). h1 x t = h2 x t"
                using Cons(3) tmp1 by simp
              have tmp4: "outupd_behav_atst il vl (tl ol) (tl fl) n h1"
                using Cons(4) 3 2 outupd_behav_atst.simps(4) by metis
              then show ?thesis using tmp2 tmp3 tmp4 Cons(1) by simp
            qed
            have 5: "h1 a n = (hd fl) (map (\<lambda> a. h1 a (real n-real (hd ol))) il)"
              using Cons 2 3 outupd_behav_atst.simps(4) by metis
            have tmp1 : "h1 a n = h2 a n"
              using Cons by auto
            have tmp2 : "(map (\<lambda> a. h1 a (real n-real (hd ol))) il) = 
                         (map (\<lambda> a. h2 a (real n-real (hd ol))) il)"
              using Cons(3) 
              by (smt (verit, ccfv_SIG) "3" le_eq_less_or_eq map_eq_conv minimal.simps(2) 
                  of_nat_0_le_iff of_nat_diff of_nat_less_iff)
            have 6: "h2 a n = (hd fl) (map (\<lambda> a. h2 a (real n-real (hd ol))) il)"
              using 5 tmp1 tmp2 by auto
            then show ?thesis 
              using 4 5 outupd_behav_atst.simps(4)by (smt (verit, best) "2" "3" map_eq_conv)
          qed
        qed
qed

lemma outupd_behav_atst_lemma: "\<forall> t::real. (t \<le> (n::nat)) \<longrightarrow> (\<forall> v. h1 v t = h2 v t) \<Longrightarrow>
outupd_behav_atst il vl ol fl n h1 = 
outupd_behav_atst il vl ol fl n h2"
proof (induction vl arbitrary:ol fl)
  case Nil
  then show ?case by auto
next
  case (Cons a vl)
  then show ?case
      proof (cases "fl = []")
        case True
        then show ?thesis by simp
      next
        case False
        have 2: "fl = (hd fl) # (tl fl)"
          using False by auto
        then show ?thesis 
        proof (cases "ol = []")
          case True
          then show ?thesis
            using 2 
            using outupd_behav_atst.elims(3) by fastforce
        next
          case False
          have 3: "ol = (hd ol) # (tl ol)"
            using False by auto
          then show ?thesis 
            using 2 3 local.Cons(2) outupd_behav_atst.simps(4)[where il = "il" and v = "a" 
                and vl = "vl" and d = "hd ol" and ol = "tl ol" and f = "hd fl" and fl = "tl fl"
                and t = "n" and h = "h1"]
                outupd_behav_atst.simps(4)[where il = "il" and v = "a" 
                and vl = "vl" and d = "hd ol" and ol = "tl ol" and f = "hd fl" and fl = "tl fl"
                and t = "n" and h = "h2"] by (simp add: Cons.IH)           
        qed
      qed
    qed

lemma minimal_lemma: "(\<forall>t \<in> set (x#xs). t > 0) \<longrightarrow> minimal (x#xs) > 0"
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case using list.set_intros(2) by force
qed

lemma outupd_behav_atst_lemma2: "Available (Block il vl ol T fl) \<Longrightarrow>
outupd_behav_atst il vl ol fl n h1 = True \<Longrightarrow>
outupd_behav_atst il vl ol fl n h2 = True \<Longrightarrow> 
\<forall>v \<in> set il. \<forall>t\<le>(real n-(minimal ol)). h1 v t = h2 v t \<Longrightarrow>
\<forall>v \<in> set vl. h1 v n = h2 v n"
proof (induction vl arbitrary:ol fl)
  case Nil
  then show ?case by simp
next
  case (Cons a vl)
  then show ?case
    proof (cases "fl = []")
      case True
      have tmp1: "fl \<noteq> []"
        using Cons(2) unfolding Available_def by force
      then show ?thesis using True by simp
    next
      case False
      have 2: "fl = (hd fl) # (tl fl)"
          using False by auto
        then show ?thesis
      proof (cases "ol = []")
        case True
        have tmp1: "ol \<noteq> []"
          using Cons(2) unfolding Available_def by force
        then show ?thesis using True by simp
      next
        case False
        have 3: "ol = (hd ol) # (tl ol)"
          using False by auto
        have 5: "h1 a (real n) = h2 a (real n)"
        proof -
          have tmp1: "h1 a (real n) = (hd fl) (map (\<lambda> a. h1 a (real n-real (hd ol))) il)"
            using outupd_behav_atst.simps(4)[where il = "il" and v = "a" 
                and vl = "vl" and d = "hd ol" and ol = "tl ol" and f = "hd fl" and fl = "tl fl"
                and t = "n" and h = "h1"]
            using "2" "3"  Cons.prems(2) by simp
          have tmp2: "h2 a (real n) = (hd fl) (map (\<lambda> a. h2 a (real n-real (hd ol))) il)"
            using outupd_behav_atst.simps(4)[where il = "il" and v = "a" 
                and vl = "vl" and d = "hd ol" and ol = "tl ol" and f = "hd fl" and fl = "tl fl"
                and t = "n" and h = "h2"]
            using "2" "3" Cons.prems(3) by force
          have tmp3: "real (hd ol) \<ge> minimal ol"
            using minimal.simps(2)[where x = "hd ol" and xs = "tl ol"]
            using "3" by force
          have tmp4: "real n-real (hd ol) \<le> n - minimal ol"
            using tmp3 by linarith
          have tmp5: "\<forall>v \<in> set il. h1 v (real n-real (hd ol)) = h2 v (real n-real (hd ol))"
            using tmp4 Cons(5) tmp3 by auto
          show ?thesis using tmp1 tmp2 tmp4 Cons(5) 
            by (metis (mono_tags, lifting) map_eq_conv tmp5)
        qed
        have 6: "\<forall>v\<in>set vl. h1 v (real n) = h2 v (real n)"
        proof -
          have tmp1: "Available (Block il vl (tl ol) T (tl fl))"
            using Cons(2) unfolding Available_def apply simp
            by (metis One_nat_def Suc_less_eq diff_Suc_1 nth_Cons_Suc)
          have tmp2: "outupd_behav_atst il vl (tl ol) (tl fl) n h1 = True"
            using Cons(3) 2 3 outupd_behav_atst.simps(4)[where il = "il" and v = "a" 
                and vl = "vl" and d = "hd ol" and ol = "tl ol" and f = "hd fl" and fl = "tl fl"
                and t = "n" and h = "h1"] by force
          have tmp3: "outupd_behav_atst il vl (tl ol) (tl fl) n h2 = True"
            using Cons(4) 2 3 outupd_behav_atst.simps(4)[where il = "il" and v = "a" 
                and vl = "vl" and d = "hd ol" and ol = "tl ol" and f = "hd fl" and fl = "tl fl"
                and t = "n" and h = "h2"] by force
          have tmp5: "tl ol \<noteq> [] \<Longrightarrow> \<forall>v\<in>set il. \<forall>t\<le>(real n - minimal (tl ol)). h1 v t = h2 v t"
            subgoal premises pre
          proof -
            have tmp1: "real (n - minimal ol) \<noteq> real (n - hd ol) \<or> real (n - hd ol) \<noteq> real n - real (hd ol) \<or> real n - real (hd ol) \<noteq> real n - real (minimal ol) \<or> real (n - minimal ol) = real n - real (minimal ol)"
              by presburger
            then show ?thesis using pre Cons(5) tmp1 minimal.simps(2)[where x = "hd ol" and xs = "tl ol"] 3
              by simp
          qed
          done
          show ?thesis 
          proof(cases "vl = []")
            case True
            then show ?thesis by simp
          next
            case False
            have tmp6: "tl ol \<noteq> []"
              using tmp1 False unfolding Available_def by force
            then show ?thesis using tmp1 tmp2 tmp3 tmp5 Cons(1) by auto
          qed
        qed
        then show ?thesis using 5 6 by simp
      qed
    qed
  qed

lemma outupd_behav_atst_lemma3: "length vl = length ol \<and> length ol = length fl \<and> length vl > 0 \<Longrightarrow>
\<forall>i. i \<ge> 0 \<and> i < length vl \<longrightarrow> h (vl ! i) n = (fl ! i) (map (\<lambda> a. h a (real n-real (ol ! i))) il) \<Longrightarrow>
outupd_behav_atst il vl ol fl n h"
proof (induction vl arbitrary:ol fl)
  case Nil
  then show ?case by auto
next
  case (Cons a vl)
  then show ?case
      proof (cases "fl = []")
        case True
        then show ?thesis
          using outupd_behav_atst.elims(3) by blast
      next
        case False
        have 2: "fl = (hd fl) # (tl fl)"
          using False by auto
        then show ?thesis
          proof (cases "ol = []")
            case True
            then show ?thesis
              using outupd_behav_atst.elims(3) by blast
          next
            case False
            have 3: "ol = (hd ol) # (tl ol)"
              using False by auto
            then show ?thesis
            proof(cases "vl = []")
              case True
              have tmp1: "outupd_behav_atst il vl (tl ol) (tl fl) (Suc (n - 1)) h"
                using True by simp
              then show ?thesis using True Cons(2,3) 2 3 outupd_behav_atst.simps(4)[where il = il and
                    v = a and vl = vl and d = "hd ol" and ol = "tl ol" and f = "hd fl" and
                    fl = "tl fl" and t = "n" and h = h]
                by (metis bot_nat_0.extremum nth_Cons_0 outupd_behav_atst.simps(1))
            next
              case False
              have tmp1: "length vl = length (tl ol) \<and> length (tl ol) = length (tl fl) \<and> 0 < length vl"
                using False Cons(2) 2 3 by auto
              have tmp2: " \<forall>i. 0 \<le> i \<and> i < length vl \<longrightarrow>
        h (vl ! i) (real n) = ((tl fl) ! i) (map (\<lambda>a. h a (real n - real ((tl ol) ! i))) il)"
                using Cons(3) 2 3 by (metis Suc_less_eq bot_nat_0.extremum length_Cons nth_Cons_Suc)
              have tmp3: "outupd_behav_atst il vl (tl ol) (tl fl) n h"
                using tmp1 tmp2 Cons(1) by (metis)
              then show ?thesis using Cons(3) 2 3 outupd_behav_atst.simps(4)[where il = il and
                    v = a and vl = vl and d = "hd ol" and ol = "tl ol" and f = "hd fl" and
                    fl = "tl fl" and t = "n" and h = h] 
                by (metis Cons.prems(1) bot_nat_0.extremum nth_Cons_0)
            qed
          qed
  qed
qed

fun outupd_behav_notatst :: "var list \<Rightarrow> var list \<Rightarrow> outupd list \<Rightarrow> sample_time  \<Rightarrow> nat \<Rightarrow> behav" where
"outupd_behav_notatst il [] fl T t h = True" |
"outupd_behav_notatst il vl [] T t h = True" |
"outupd_behav_notatst il (v#vl) (f#fl) T t h = (if T \<le> 0 then True else 
((h v t = h v ((int t div T)*T)) \<and> outupd_behav_notatst il vl fl T t h))"

lemma outupd_behav_notatst_eq: "\<forall>x \<in> (set vl). (\<forall>t. h1 x t = h2 x t) \<Longrightarrow>
outupd_behav_notatst il vl fl T n h1 \<Longrightarrow>
outupd_behav_notatst il vl fl T n h2"
proof (induction vl arbitrary:fl)
  case Nil
  then show ?case by auto
next
  case (Cons a vl)
  then show ?case
  proof (cases "fl = []")
    case True
    then show ?thesis by auto
  next
    case False
    have 1: "fl = (hd fl) # (tl fl)"
      using False by auto
    have 3: "outupd_behav_notatst il vl (tl fl) T n h2"
      using Cons 
      by (metis "1" list.set_intros(2) outupd_behav_notatst.elims(3) outupd_behav_notatst.simps(3))
     then show ?thesis 
       using Cons 3
       by (metis "1" list.set_intros(1) outupd_behav_notatst.simps(3))
  qed
qed

lemma outupd_behav_notatst_lemma: "\<forall> t::real. (t \<le> (n::nat)) \<longrightarrow> (\<forall> v. h1 v t = h2 v t) \<Longrightarrow>
outupd_behav_notatst il vl fl T n h1 = 
outupd_behav_notatst il vl fl T n h2"
proof (induction vl arbitrary:fl)
  case Nil
  then show ?case by auto
next
  case (Cons a vl)
  then show ?case 
  proof (cases "fl = []")
    case True
    then show ?thesis by auto
  next
    case False
    have 1: "fl = (hd fl) # (tl fl)"
       using False by auto
     have pre1: "outupd_behav_notatst il vl (tl fl) T n h1 = 
                outupd_behav_notatst il vl (tl fl) T n h2"
      using Cons by auto
    have 2: "T > 0 \<Longrightarrow> real_of_int (int n div T * T) \<le> real n"
      by (metis mult.commute mult_div_le of_int_le_iff of_int_of_nat_eq)
    have 3: "T > 0 \<Longrightarrow> h1 a (real_of_int (int n div T * T)) = 
                      h2 a (real_of_int (int n div T * T))"
      using Cons(2) 2 by auto
    have pre2: "T > 0 \<Longrightarrow> (h1 a (real n) = h1 a (real_of_int (int n div T * T))) = 
              (h2 a (real n) = h2 a (real_of_int (int n div T * T)))"
      using Cons 3 by auto
    then show ?thesis 
      using 1 Cons(2) outupd_behav_notatst.simps(3)[where il = "il" and v = "a" and vl = "vl" and
          f = "hd fl" and fl = "tl fl" and T = "T" and t = "n" and h = "h1"]
            outupd_behav_notatst.simps(3)[where il = "il" and v = "a" and vl = "vl" and
          f = "hd fl" and fl = "tl fl" and T = "T" and t = "n" and h = "h2"]
        pre1 pre2 by auto
  qed
qed

lemma outupd_behav_notatst_lemma2: "Available (Block il vl ol T fl) \<Longrightarrow>
\<forall>k. int n \<noteq> T * k \<Longrightarrow> T > 0 \<Longrightarrow>
outupd_behav_notatst il vl fl T n h1 = True \<Longrightarrow> 
outupd_behav_notatst il vl fl T n h2 = True \<Longrightarrow> (\<forall> v \<in> set vl. h1 v 0 = h2 v 0) \<Longrightarrow> 
\<forall>v \<in> set vl. \<forall>t\<le> real (n - 1). h1 v t = h2 v t \<Longrightarrow>
(\<forall> v \<in> set vl. h1 v n = h2 v n)"
proof(induction vl arbitrary:ol fl)
  case Nil
  then show ?case by simp
next
  case (Cons a vl)
  have 1: "T > 0 \<Longrightarrow> real_of_int (int n div T * T) \<le> real (n-1)"
    by (smt (verit, best) Cons.prems(2) One_nat_def Suc_leI mult.commute 
        mult_div_le of_nat_Suc of_nat_diff of_nat_le_0_iff of_nat_less_iff 
        of_nat_less_of_int_iff)
  then show ?case
  proof (cases "fl = []")
    case True
    then show ?thesis using Cons(2) unfolding Available_def by fastforce
  next
    case False
    have 2: "fl = (hd fl) # (tl fl)"
      using False by auto
    have 3: "T > 0"
      using Cons(4) by simp
    have 4: "h1 a (real n) = h2 a (real n)"
    proof -
      have tmp1: "h1 a (real n) = h1 a ((int n div T)*T)"
        using outupd_behav_notatst.simps(3)[where il = "il" and v = "a" and vl = "vl" and
          f = "hd fl" and fl = "tl fl" and T = "T" and t = "n" and h = "h1"] 2 Cons(4,5)
        by auto
      have tmp2: "h2 a (real n) = h2 a ((int n div T)*T)"
        using outupd_behav_notatst.simps(3)[where il = "il" and v = "a" and vl = "vl" and
          f = "hd fl" and fl = "tl fl" and T = "T" and t = "n" and h = "h2"] 2 Cons(4,6)
        by auto
      show ?thesis using 1 3 tmp1 tmp2 Cons(8) by auto
    qed
    have 5: "\<forall>v\<in>set vl. h1 v (real n) = h2 v (real n)"
    proof -
      have tmp1: "Available (Block il vl (tl ol) T (tl fl))"
        using Cons(2) 2 unfolding Available_def apply simp
        by (metis One_nat_def Suc_less_eq diff_Suc_1 nth_Cons_Suc)
      have tmp2: "outupd_behav_notatst il vl (tl fl) T n h1 = True"
        using Cons(5) 2 3 outupd_behav_notatst.simps(3)[where il = "il" and v = "a" and vl = "vl" and
          f = "hd fl" and fl = "tl fl" and T = "T" and t = "n" and h = "h1"] by auto
      have tmp3: "outupd_behav_notatst il vl (tl fl) T n h2 = True"
        using Cons(6) 2 3 outupd_behav_notatst.simps(3)[where il = "il" and v = "a" and vl = "vl" and
          f = "hd fl" and fl = "tl fl" and T = "T" and t = "n" and h = "h2"] by auto
      have tmp4: "\<forall>v\<in>set vl. h1 v 0 = h2 v 0"
        using Cons(7) by simp
      have tmp5: "\<forall>v\<in>set vl. \<forall>t\<le>real (n - 1). h1 v t = h2 v t"
        using Cons(8) by simp
      show ?thesis using tmp1 tmp2 tmp3 tmp4 tmp5 Cons(1,3,4) by auto
    qed
    then show ?thesis using "4" by auto
  qed
qed

lemma outupd_behav_notatst_lemma3: "length vl = length fl \<and> length vl > 0 \<Longrightarrow>
T > 0 \<Longrightarrow> (\<forall>i. i \<ge> 0 \<and> i < length vl \<longrightarrow> h (vl ! i) t = h (vl ! i) ((int t div T)*T) \<Longrightarrow>
outupd_behav_notatst il vl fl T t h)"
proof (induction vl arbitrary:fl)
  case Nil
  then show ?case by auto
next
  case (Cons a vl)
  then show ?case
  proof (cases "fl = []")
    case True
    then show ?thesis by auto
  next
    case False
    have 1: "fl = (hd fl) # (tl fl)"
      using False by auto
    then show ?thesis 
    proof(cases "vl = []")
      case True
      have tmp1: "outupd_behav_notatst il vl (tl fl) T t h"
        using True by simp
      then show ?thesis using Cons 1 outupd_behav_notatst.simps(3)[where il = "il" and v = "a" and vl = "vl" and
          f = "hd fl" and fl = "tl fl" and T = "T" and t = t and h = h] 
        by (metis bot_nat_0.extremum nth_Cons_0)
    next
      case False
      have tmp1: "length vl = length (tl fl) \<and> 0 < length vl"
        using False Cons(2) 1 by simp
      have tmp2: "\<forall>i. 0 \<le> i \<and> i < length vl \<longrightarrow> h (vl ! i) (real t) = h (vl ! i) (real_of_int (int t div T * T)) \<Longrightarrow>
    outupd_behav_notatst il vl (tl fl) T t h"
        using Cons(1,3) tmp1 by blast
      have tmp3: "outupd_behav_notatst il vl (tl fl) T t h"
        using Cons(4) tmp2 by (metis Suc_leI le_imp_less_Suc length_Cons less_imp_le_nat list.sel(3) nth_tl)
      have tmp4: "h a (real t) = h a (real_of_int (int t div T * T))"
        using Cons(4) by force
      then show ?thesis using tmp3 outupd_behav_notatst.simps(3)[where il = "il" and v = "a" and vl = "vl" and
          f = "hd fl" and fl = "tl fl" and T = "T" and t = t and h = h] 1 Cons(3) by auto
    qed
  qed
qed

\<comment> \<open>The constraints corresponding to a block. add a nat for max time\<close>
fun behavDisDiag_attime :: "block list \<Rightarrow> nat \<Rightarrow> behav" where
  "behavDisDiag_attime [] n h = True" |
  "behavDisDiag_attime (b#bl) n h = (behavDisDiag_attime bl n h \<and> (if (\<exists> k.  
                                  (n = (get_sample_time b)*k) \<or> (get_sample_time b) = 0) 
                                 then outupd_behav_atst (get_inputs b) (get_outputs b) (get_offsets b) (get_outupd b) n h
                                 else outupd_behav_notatst (get_inputs b) (get_outputs b) (get_outupd b) (get_sample_time b) n h))"
lemma inBlocklistLemma1: "behavDisDiag_attime bl n h \<Longrightarrow> bl \<noteq> [] \<Longrightarrow> a \<in> set bl \<Longrightarrow> v \<in> set (get_outputs a) \<Longrightarrow>
\<exists>k. int n = get_sample_time a * k \<Longrightarrow>
outupd_behav_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) n h"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  have 1: "behavDisDiag_attime bl n h"
    using Cons(2) unfolding behavDisDiag_attime.simps by simp
  then show ?case 
  proof(cases "a \<in> set bl")
    case True
    then show ?thesis using 1 Cons by fastforce
  next
    case False
    have tmp1: "a = b"
      using False Cons by simp
    then show ?thesis using Cons(2,6) unfolding behavDisDiag_attime.simps by auto
  qed
qed

lemma inBlocklistLemma2: "behavDisDiag_attime bl n h \<Longrightarrow> bl \<noteq> [] \<Longrightarrow> a \<in> set bl \<Longrightarrow> v \<in> set (get_outputs a) \<Longrightarrow>
\<forall>k. int n \<noteq> get_sample_time a * k \<or> get_sample_time a = 0 \<Longrightarrow>
outupd_behav_notatst (get_inputs a) (get_outputs a) (get_outupd a) (get_sample_time a) n h"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  have 1: "behavDisDiag_attime bl n h"
    using Cons(2) unfolding behavDisDiag_attime.simps by simp
  then show ?case 
  proof(cases "a \<in> set bl")
    case True
    then show ?thesis using 1 Cons by fastforce
  next
    case False
    have tmp1: "a = b"
      using False Cons by simp
    then show ?thesis using Cons(2,6) unfolding behavDisDiag_attime.simps
      by (smt (z3) outupd_behav_notatst.elims(1))
  qed
qed

lemma blocklist_behav_atst : "behavDisDiag_attime (a#bl) n h \<Longrightarrow> \<exists>t. int n = get_sample_time a * t \<Longrightarrow> 
          outupd_behav_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) n h"
  by auto

lemma blocklist_hebav_attime_eq1: 
"\<forall>x \<in> (Outputs bl). (\<forall>t. h1 x t = h2 x t) \<Longrightarrow> 
\<forall>i. i \<ge> 0 \<and> i < length bl \<longrightarrow> 
(\<forall>x \<in> set (get_inputs (bl ! i)). (\<forall>t \<le> real (n-(minimal (get_offsets (bl ! i)))). h1 x t = h2 x t)) \<Longrightarrow>
behavDisDiag_attime bl n h1 \<Longrightarrow> behavDisDiag_attime bl n h2"
proof (induction bl)
  case Nil
  then show ?case by auto
next
  case (Cons a bl)
  have 1 : "behavDisDiag_attime bl n h2"
  proof -
    have tmp1: "\<forall>x\<in>Outputs bl. \<forall>t. h1 x t = h2 x t"
      using Cons(2) by simp
    have tmp2 : "\<forall>i. 0 \<le> i \<and> i < length bl \<longrightarrow>
        (\<forall>x\<in>set (get_inputs (bl ! i)).
            \<forall>t\<le>real (n - minimal (get_offsets (bl ! i))). h1 x t = h2 x t)"
      using Cons(3) Suc_leI le_imp_less_Suc length_Cons not_less_eq_eq nth_tl by auto
    have tmp3: "behavDisDiag_attime bl n h1"
      using Cons(4) unfolding behavDisDiag_attime.simps by simp
    show ?thesis using Cons(1) tmp1 tmp2 tmp3 by simp
  qed
  have 2 : "(\<exists>k. int n = get_sample_time a * k \<or> get_sample_time a = 0) \<longrightarrow>
     outupd_behav_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) n h1"
    using Cons(4) by simp
  have 3 : "(\<exists>k. int n = get_sample_time a * k \<or> get_sample_time a = 0) \<longrightarrow>
     outupd_behav_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) n h2"
  proof -
    have tmp1: "\<forall>x\<in> set (get_outputs a). \<forall>t. h1 x t = h2 x t"
      using Cons(2) by simp
    have tmp2: "\<forall>x\<in>set (get_inputs a). \<forall>t\<le>real (n - minimal (get_offsets a)). h1 x t = h2 x t"
      using Cons(3) by (metis length_greater_0_conv less_eq_nat.simps(1) neq_Nil_conv nth_Cons_0)
    show ?thesis using 2 tmp1 tmp2 outupd_behav_atst_eq by blast
  qed
  have 4 : "(\<forall>k. int n \<noteq> get_sample_time a * k \<and> get_sample_time a \<noteq> 0) \<longrightarrow>
     outupd_behav_notatst (get_inputs a) (get_outputs a) (get_outupd a) (get_sample_time a) n
      h1"
    using Cons(4) by simp
  have 5 : "(\<forall>k. int n \<noteq> get_sample_time a * k \<and> get_sample_time a \<noteq> 0) \<longrightarrow>
     outupd_behav_notatst (get_inputs a) (get_outputs a) (get_outupd a) (get_sample_time a) n
      h2"
  proof -
    have tmp1: "\<forall>x\<in> set (get_outputs a). \<forall>t. h1 x t = h2 x t"
      using Cons(2) by simp
    show ?thesis using 4 tmp1 outupd_behav_notatst_eq by blast
  qed
  then show ?case 
    using behavDisDiag_attime.simps(2) 1 3 5 by auto
    
qed

lemma blocklist_hebav_attime_eq2: 
"\<forall>x \<in> (Outputs bl). (\<forall>t. h1 x t = h2 x t) \<Longrightarrow> 
\<forall>i. i \<ge> 0 \<and> i < length bl \<longrightarrow> 
(\<forall>x \<in> set (get_inputs (bl ! i)). (\<forall>t \<le> (real n- real (minimal (get_offsets (bl ! i)))). h1 x t = h2 x t)) \<Longrightarrow>
behavDisDiag_attime bl n h1 \<Longrightarrow> behavDisDiag_attime bl n h2"
proof (induction bl)
  case Nil
  then show ?case by auto
next
  case (Cons a bl)
  have 1 : "behavDisDiag_attime bl n h2"
  proof -
    have tmp1: "\<forall>x\<in>Outputs bl. \<forall>t. h1 x t = h2 x t"
      using Cons(2) by simp
    have tmp2 : "\<forall>i. 0 \<le> i \<and> i < length bl \<longrightarrow>
        (\<forall>x\<in>set (get_inputs (bl ! i)).
            \<forall>t\<le>(real n - minimal (get_offsets (bl ! i))). h1 x t = h2 x t)"
      using Cons(3) Suc_leI le_imp_less_Suc length_Cons not_less_eq_eq nth_tl by auto
    have tmp3: "behavDisDiag_attime bl n h1"
      using Cons(4) unfolding behavDisDiag_attime.simps by simp
    show ?thesis using Cons(1) tmp1 tmp2 tmp3 by simp
  qed
  have 2 : "(\<exists>k. int n = get_sample_time a * k \<or> get_sample_time a = 0) \<longrightarrow>
     outupd_behav_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) n h1"
    using Cons(4) by simp
  have 3 : "(\<exists>k. int n = get_sample_time a * k \<or> get_sample_time a = 0) \<longrightarrow>
     outupd_behav_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) n h2"
  proof -
    have tmp1: "\<forall>x\<in> set (get_outputs a). \<forall>t. h1 x t = h2 x t"
      using Cons(2) by simp
    have tmp2: "\<forall>x\<in>set (get_inputs a). \<forall>t\<le>(real n - minimal (get_offsets a)). h1 x t = h2 x t"
      using Cons(3) by (metis length_greater_0_conv less_eq_nat.simps(1) neq_Nil_conv nth_Cons_0)
    show ?thesis using 2 tmp1 tmp2 outupd_behav_atst_eq2 by blast
  qed
  have 4 : "(\<forall>k. int n \<noteq> get_sample_time a * k \<and> get_sample_time a \<noteq> 0) \<longrightarrow>
     outupd_behav_notatst (get_inputs a) (get_outputs a) (get_outupd a) (get_sample_time a) n
      h1"
    using Cons(4) by simp
  have 5 : "(\<forall>k. int n \<noteq> get_sample_time a * k \<and> get_sample_time a \<noteq> 0) \<longrightarrow>
     outupd_behav_notatst (get_inputs a) (get_outputs a) (get_outupd a) (get_sample_time a) n
      h2"
  proof -
    have tmp1: "\<forall>x\<in> set (get_outputs a). \<forall>t. h1 x t = h2 x t"
      using Cons(2) by simp
    show ?thesis using 4 tmp1 outupd_behav_notatst_eq by blast
  qed
  then show ?case 
    using behavDisDiag_attime.simps(2) 1 3 5 by auto
    
qed

lemma blocklist_hebav_attime_lemma: "\<forall> t::real. (t \<le> n) \<longrightarrow> (\<forall> v. h1 v t = h2 v t) \<Longrightarrow>
behavDisDiag_attime bl n h1 = behavDisDiag_attime bl n h2"
proof (induction bl)
  case Nil
  then show ?case by auto
next
  case (Cons a bl)
  have pre1: "behavDisDiag_attime bl n h1 = behavDisDiag_attime bl n h2"
    using Cons by auto
  have pre2: "outupd_behav_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) n h1 = 
              outupd_behav_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) n h2"
    using Cons outupd_behav_atst_lemma by auto
  have pre3: "outupd_behav_notatst (get_inputs a) (get_outputs a) (get_outupd a) (get_sample_time a) n h1 =
              outupd_behav_notatst (get_inputs a) (get_outputs a) (get_outupd a) (get_sample_time a) n h2"
    using Cons outupd_behav_notatst_lemma by auto
  then show ?case 
    using pre1 pre2 pre3 by auto
qed

lemma blocklist_hebav_attime_lemma2: "bl \<noteq> [] \<Longrightarrow> wf0 bl \<Longrightarrow>
behavDisDiag_attime bl n h1 = True \<Longrightarrow> besorted bl  \<Longrightarrow> besorted bl' \<Longrightarrow>
bl <~~> bl' \<Longrightarrow> behavDisDiag_attime bl' n h2 = True \<Longrightarrow> 
(\<forall> v \<in> Outputs bl. h1 v 0 = h2 v 0) \<Longrightarrow> 
\<forall>v \<in> Inputs bl - Outputs bl. \<forall>t \<le> real n. h1 v t = h2 v t \<Longrightarrow> 
\<forall>t. t < real n \<longrightarrow> (\<forall>v\<in>Outputs bl. h1 v t = h2 v t) \<Longrightarrow> 
(\<forall> v \<in> Outputs bl. h1 v n = h2 v n)"
proof(induction bl arbitrary:bl')
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  note Cons1 = Cons
  have 0: "distinct (a#bl)"
    using Cons(3) unfolding wf0_def using Unique'_def Unique'_eq by blast
  have 1: "distinct bl'"
    using  0 Cons(7) distinct_perm by blast
  have 2: "\<forall>x \<in> set (get_outputs a). h1 x (real n) = h2 x (real n)"
    proof(cases "\<exists>k. int n = get_sample_time a * k \<or> get_sample_time a = 0")
      case True
      note True1 = True
      have tmp1: "outupd_behav_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) n h1 = True"
        using Cons(4) unfolding behavDisDiag_attime.simps using True by simp
      have tmp2: "a \<in> set bl'"
        using Cons(7) by (simp add: prem_seteq)
      have tmp3: "outupd_behav_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) n h2 = True"
        using Cons(8)  tmp2 apply simp
      proof(induction bl')
        case Nil
        then show ?case by simp
      next
        case (Cons b bl')
        then show ?case
        proof(cases "a = b")
          case True
          then show ?thesis using Cons True1 unfolding behavDisDiag_attime.simps 
            using Cons1(9) inBlocklistLemma1 tmp2 by fastforce
        next
          case False
          have tmp: "a \<in> set bl'"
            using Cons(3) False by simp
          then show ?thesis using Cons unfolding behavDisDiag_attime.simps
            using Cons1(9) True1 inBlocklistLemma1 list.set_intros(1) tmp2 by fastforce
        qed
      qed
      have tmp4: "\<forall>v \<in> set (get_outputs a). h1 v 0 = h2 v 0"
        using Cons(9) unfolding Outputs.simps by simp
      have tmp5: "get_outputs a \<noteq> [] \<Longrightarrow>
          \<forall>v \<in> set (get_inputs a).\<forall>t\<le>real (n-(minimal (get_offsets a))). h1 v t = h2 v t"
        subgoal premises pre
      proof(cases "set (get_inputs a) \<inter> Outputs bl = {}")
        case True
        have tmp1: "set (get_inputs a) \<inter> set (get_outputs a) = {}"
          using Cons(3) unfolding wf0_def Available_def by auto
        have tmp2: "minimal (get_offsets a) \<ge> 0"
          using Cons(3) unfolding wf0_def Available_def by auto
        have tmp3: "real (n - minimal (get_offsets a)) \<le> real n"
          using tmp2 by force
        then show ?thesis using Cons(10) True tmp1 
          by (metis (no_types, opaque_lifting) DiffI Inputs.simps(2) 
              Int_iff Outputs.simps(2) Un_iff empty_iff order_trans)
      next
        case False
        have tmp1: "minimal (get_offsets a) > 0"
          using Cons(5) False unfolding besorted.simps apply simp 
        proof(induction bl)
          case Nil
          then show ?case by simp
        next
          case (Cons b bl)
          then show ?case 
          proof(cases "set (get_inputs a) \<inter> set (get_outputs b) \<noteq> {}")
            case True
            note True1 = True
            have tmp1: "\<not> check_offset (get_outputs b) (get_inputs a) (get_offsets a)"
              using Cons(2) by simp
            then show ?thesis
            proof(cases "(get_outputs b) = []")
              case True
              then show ?thesis using True1 by simp
            next
              case False
              have False1: "get_outputs b = hd (get_outputs b) # (tl (get_outputs b))"
                using False by auto
              then show ?thesis
              proof(cases "(get_offsets a) = []")
                case True
                then show ?thesis using pre Cons1(3) unfolding wf0_def Available_def by simp
              next
                case False
                have False2 : "get_offsets a = hd (get_offsets a) # (tl (get_offsets a))"
                  using False by auto
                have tmp1: "\<forall>d\<in>set (get_offsets a). d \<noteq> 0"
                  using False1 check_offset.simps(3)[where il = "get_inputs a"
                      and v = "hd (get_outputs b)" and va = "tl (get_outputs b)" and
                      vb = "hd (get_offsets a)" and vc = "tl (get_offsets a)"] tmp1 True1
                  by (metis False2 inf_commute)
                have tmp2: "\<forall>d \<in> set (get_offsets a). d \<ge> 0"
                  using Cons1(3) unfolding wf0_def  Available_def by auto
                then show ?thesis using tmp1 using minimal_lemma False2 by (metis gr0I)
              qed
            qed
          next
            case False
            have tmp1: "set (get_inputs a) \<inter> Outputs bl \<noteq> {}"
              using False Cons(3) by auto
            have tmp2: "besorted bl \<and> (\<forall>aa. aa \<in> set bl \<longrightarrow> 
              \<not> check_offset (get_outputs aa) (get_inputs a) (get_offsets a))"
              using Cons(2) by auto
            then show ?thesis using Cons(1) tmp1 by simp
          qed
        qed
        have tmp2: "\<forall>v\<in>set (get_inputs a) \<inter> Outputs bl. 
              \<forall>t\<le>real (n - minimal (get_offsets a)). h1 v t = h2 v t"
          using tmp1 Cons(11) apply simp 
          by (smt (z3) Cons1(9) IntD2 Outputs.simps(2) Un_iff le_eq_less_or_eq 
              less_imp_of_nat_less of_nat_0 of_nat_0_le_iff of_nat_0_less_iff 
              of_nat_diff tmp1 zero_less_diff)
        have tmp3: "set (get_inputs a) \<inter> set (get_outputs a) = {}"
          using Cons(3) unfolding wf0_def Available_def by (simp add: inf.commute)
        have tmp4: "\<forall>v\<in>set (get_inputs a) - Outputs bl. v \<in>Inputs (a # bl) - Outputs (a # bl)"
          using tmp3 by auto
        have tmp5: "\<forall>v\<in>set (get_inputs a) - Outputs bl. 
              \<forall>t\<le>real (n - minimal (get_offsets a)). h1 v t = h2 v t"
          using tmp4 Cons(10) by auto
        then show ?thesis using tmp2 by auto
      qed
      done
      have tmp6: "Available (Block (get_inputs a) (get_outputs a) (get_offsets a) (get_sample_time a)
       (get_outupd a))"
        using Cons(3) unfolding wf0_def by (simp add: Available_def)
      then show ?thesis using outupd_behav_atst_lemma2[where il = "get_inputs a" and vl = "get_outputs a"
            and ol = "get_offsets a" and T = "get_sample_time a" and fl = "get_outupd a"
            and n = n and ?h1.0 = h1 and ?h2.0 = h2] tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 
        by fastforce
    next
      case False
      note False1 = False
      have tmp1: "Available (Block (get_inputs a) (get_outputs a) (get_offsets a) (get_sample_time a)
       (get_outupd a))"
        using Cons(3) unfolding wf0_def by (simp add: Available_def)
      have tmp2: "outupd_behav_notatst (get_inputs a) (get_outputs a) (get_outupd a)
          (get_sample_time a) n h1"
        using Cons(4) unfolding behavDisDiag_attime.simps using False by simp
      have tmp3: "a \<in> set bl'"
        using Cons(7) by (simp add: prem_seteq)
      have tmp4: "outupd_behav_notatst (get_inputs a) (get_outputs a) (get_outupd a)
          (get_sample_time a) n h2"
        using Cons(8) tmp3 apply simp
      proof(induction bl')
        case Nil
        then show ?case by simp
      next
        case (Cons b bl')
        then show ?case
        proof(cases "a = b")
          case True
          then show ?thesis using Cons(2) False1 unfolding behavDisDiag_attime.simps by simp
        next
          case False
          have tmp: "a \<in> set bl'"
            using Cons(3) False by simp
          then show ?thesis using Cons unfolding behavDisDiag_attime.simps by simp
        qed
      qed
      have tmp5: "\<forall>v \<in> set (get_outputs a). h1 v 0 = h2 v 0"
        using Cons(9) unfolding Outputs.simps by simp
      have tmp6: "\<forall>v\<in>set (get_outputs a). \<forall>t <real n. h1 v t = h2 v t"
        using Cons(11) by simp
      have tmp7: "get_sample_time a > 0"
        using tmp1 False unfolding Available_def by force
      then show ?thesis using outupd_behav_notatst_lemma2 tmp1 tmp2 tmp4 tmp5 tmp6 False
        by (smt (verit, ccfv_SIG) One_nat_def Suc_leI of_nat_0_less_iff of_nat_diff of_nat_le_0_iff zero_less_one)
    qed
  have 3: "\<forall>v\<in>Outputs bl. h1 v (real n) = h2 v (real n)"
  proof(cases "bl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have tmp1: "behavDisDiag_attime bl n h1 = True"
      using Cons(4) unfolding behavDisDiag_attime.simps by auto
    have tmp2: "bl <~~> remove1 a bl'"
      using perm_remove_perm Cons(7) by (metis remove_hd)
    have tmp3: "distinct bl' \<Longrightarrow> behavDisDiag_attime bl' n h2 \<Longrightarrow>
      behavDisDiag_attime (remove1 a bl') n h2 = True"
    proof(induction bl')
      case Nil
      then show ?case by simp
    next
      case (Cons b bl')
      note Cons2 = Cons
      have tmp4: "distinct bl'"
        using Cons2(2) by simp
      then show ?case
      proof(cases "a = b")
        case True
        have tmp5: "remove1 a bl' = bl'"
          using Cons(2) True by (simp add: remove1_idem)
        then show ?thesis using True apply simp using Cons(1,3) tmp4 tmp5 by auto
      next
        case False
        have tmp6: "(remove1 a (b # bl')) = b#(remove1 a bl')"
          using False by auto
        then show ?thesis using False Cons unfolding behavDisDiag_attime.simps by simp
      qed
    qed
    have tmp7: "behavDisDiag_attime (remove1 a bl') n h2 = True"
      using tmp3 Cons(8) 1 by auto
    have tmp8: "\<forall>v\<in>Outputs bl. h1 v 0 = h2 v 0"
      using Cons(9) by simp
    have tmp9: "\<forall>v\<in>Inputs bl - Outputs bl. \<forall>t \<le> real n. h1 v t = h2 v t"
    proof -
      have tmp1: "\<forall>v\<in>Inputs bl - Outputs (a#bl). \<forall>t \<le> real n. h1 v t = h2 v t"
        using Cons(10) by simp
      have tmp2: "\<forall>v\<in> set (get_outputs a). \<forall>t \<le> real n. h1 v t = h2 v t"
        using Cons(11) 2
        by (smt (z3) Outputs.simps(2) Un_iff less_nat_zero_code linorder_not_le 
            nat_less_le nat_less_real_le of_nat_0_less_iff of_nat_1 of_nat_diff)
      show ?thesis using tmp1 tmp2 by (metis Diff_iff Outputs.simps(2) Un_iff)
    qed
    have tmp11: "\<forall>t<real n. \<forall>v\<in>Outputs bl. h1 v t = h2 v t"
      using Cons(11) by simp
    have tmp12: "besorted bl"
    proof -
      have tmp1: "a \<notin> set bl"
        using 0 unfolding distinct.simps by simp
      have tmp2: "remove1 a (a#bl) = bl"
        using tmp1 by (simp add: remove1_append)
      show ?thesis using Cons(5,6) tmp2 by simp
    qed
    have tmp13: "besorted (remove1 a bl')"
    proof -
      have tmp1: "a \<notin> set (remove1 a bl')"
        using 1 by simp
      have tmp2: "a \<in> set bl'"
        using Cons(7) by (simp add: prem_seteq)
      show ?thesis using Cons(7) by (simp add: Cons1(6) besorted_remove2)
    qed
    then show ?thesis using Cons False tmp1 tmp2 tmp3 1 wf0_lemma tmp12 tmp9 by simp
  qed
  then show ?case using 2 by auto
qed

lemma blocklist_hebav_attime_lemma3: "bl \<noteq> [] \<Longrightarrow> wf0 bl \<Longrightarrow>
behavDisDiag_attime bl 0 h1 = True \<Longrightarrow> besorted bl  \<Longrightarrow> besorted bl' \<Longrightarrow>
bl <~~> bl' \<Longrightarrow> behavDisDiag_attime bl' 0 h2 = True \<Longrightarrow> 
\<forall>v \<in> Inputs bl - Outputs bl. \<forall>t \<le> real 0. h1 v t = h2 v t \<Longrightarrow> 
\<forall>t. t < real 0 \<longrightarrow> (\<forall>v\<in>Outputs bl. h1 v t = h2 v t) \<Longrightarrow> 
(\<forall> v \<in> Outputs bl. h1 v 0 = h2 v 0)"
proof(induction bl arbitrary:bl')
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  note Cons1 = Cons
  have 0: "distinct (a#bl)"
    using Cons(3) unfolding wf0_def using Unique'_def Unique'_eq by blast
  have 1: "distinct bl'"
    using  0 Cons(7) distinct_perm by blast
  have 2: "\<forall>x \<in> set (get_outputs a). h1 x 0 = h2 x 0"
    proof(cases "\<exists>k. 0 = get_sample_time a * k \<or> get_sample_time a = 0")
      case True
      note True1 = True
      have tmp1: "outupd_behav_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) 0 h1 = True"
        using Cons(4) unfolding behavDisDiag_attime.simps using True by simp
      have tmp2: "a \<in> set bl'"
        using Cons(7) by (simp add: prem_seteq)
      have tmp3: "outupd_behav_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) 0 h2 = True"
        using Cons(8)  tmp2 apply simp
      proof(induction bl')
        case Nil
        then show ?case by simp
      next
        case (Cons b bl')
        then show ?case
        proof(cases "a = b")
          case True
          then show ?thesis using Cons True1 unfolding behavDisDiag_attime.simps 
            using Cons1(9) inBlocklistLemma1 tmp2 by fastforce
        next
          case False
          have tmp: "a \<in> set bl'"
            using Cons(3) False by simp
          then show ?thesis using Cons unfolding behavDisDiag_attime.simps
            using Cons1(9) True1 inBlocklistLemma1 list.set_intros(1) tmp2 by fastforce
        qed
      qed
      have tmp5: "get_outputs a \<noteq> [] \<Longrightarrow>
          \<forall>v \<in> set (get_inputs a).\<forall>t\<le>(real 0-(minimal (get_offsets a))). h1 v t = h2 v t"
        subgoal premises pre
      proof(cases "set (get_inputs a) \<inter> Outputs bl = {}")
        case True
        have tmp1: "set (get_inputs a) \<inter> set (get_outputs a) = {}"
          using Cons(3) unfolding wf0_def Available_def by auto
        have tmp2: "minimal (get_offsets a) \<ge> 0"
          using Cons(3) unfolding wf0_def Available_def by auto
        have tmp3: "(real 0 - minimal (get_offsets a)) \<le> real 0"
          using tmp2 by force
        then show ?thesis using Cons(9) True tmp1 by (metis (no_types, opaque_lifting) DiffI 
              Inputs.simps(2) Int_iff Outputs.simps(2) Un_iff empty_iff order_trans)
      next
        case False
        have tmp1: "minimal (get_offsets a) > 0"
          using Cons(5) False unfolding besorted.simps apply simp 
        proof(induction bl)
          case Nil
          then show ?case by simp
        next
          case (Cons b bl)
          then show ?case 
          proof(cases "set (get_inputs a) \<inter> set (get_outputs b) \<noteq> {}")
            case True
            note True1 = True
            have tmp1: "\<not> check_offset (get_outputs b) (get_inputs a) (get_offsets a)"
              using Cons(2) by simp
            then show ?thesis
            proof(cases "(get_outputs b) = []")
              case True
              then show ?thesis using True1 by simp
            next
              case False
              have False1: "get_outputs b = hd (get_outputs b) # (tl (get_outputs b))"
                using False by auto
              then show ?thesis
              proof(cases "(get_offsets a) = []")
                case True
                then show ?thesis using pre Cons1(3) unfolding wf0_def Available_def by simp
              next
                case False
                have False2 : "get_offsets a = hd (get_offsets a) # (tl (get_offsets a))"
                  using False by auto
                have tmp1: "\<forall>d\<in>set (get_offsets a). d \<noteq> 0"
                  using False1 check_offset.simps(3)[where il = "get_inputs a"
                      and v = "hd (get_outputs b)" and va = "tl (get_outputs b)" and
                      vb = "hd (get_offsets a)" and vc = "tl (get_offsets a)"] tmp1 True1
                  by (metis False2 inf_commute)
                have tmp2: "\<forall>d \<in> set (get_offsets a). d \<ge> 0"
                  using Cons1(3) unfolding wf0_def  Available_def by auto
                then show ?thesis using tmp1 using minimal_lemma False2 by (metis gr0I)
              qed
            qed
          next
            case False
            have tmp1: "set (get_inputs a) \<inter> Outputs bl \<noteq> {}"
              using False Cons(3) by auto
            have tmp2: "besorted bl \<and> (\<forall>aa. aa \<in> set bl \<longrightarrow> 
              \<not> check_offset (get_outputs aa) (get_inputs a) (get_offsets a))"
              using Cons(2) by auto
            then show ?thesis using Cons(1) tmp1 by simp
          qed
        qed
        have tmp2: "\<forall>v\<in>set (get_inputs a) \<inter> Outputs bl. 
              \<forall>t\<le>(real 0 - minimal (get_offsets a)). h1 v t = h2 v t"
          using tmp1 Cons(10) unfolding Outputs.simps by auto
        have tmp3: "set (get_inputs a) \<inter> set (get_outputs a) = {}"
          using Cons(3) unfolding wf0_def Available_def by (simp add: inf.commute)
        have tmp4: "\<forall>v\<in>set (get_inputs a) - Outputs bl. v \<in>Inputs (a # bl) - Outputs (a # bl)"
          using tmp3 by auto
        have tmp5: "\<forall>v\<in>set (get_inputs a) - Outputs bl. 
              \<forall>t\<le> (real 0 - minimal (get_offsets a)). h1 v t = h2 v t"
          using tmp4 Cons(9) by auto
        then show ?thesis using tmp2 by auto
      qed
      done
      have tmp6: "Available (Block (get_inputs a) (get_outputs a) (get_offsets a) (get_sample_time a)
       (get_outupd a))"
        using Cons(3) unfolding wf0_def by (simp add: Available_def)
      then show ?thesis using outupd_behav_atst_lemma2[where il = "get_inputs a" and vl = "get_outputs a"
            and ol = "get_offsets a" and T = "get_sample_time a" and fl = "get_outupd a"
            and n = 0 and ?h1.0 = h1 and ?h2.0 = h2] tmp1 tmp2 tmp3 tmp5 tmp6
        by fastforce
    next
      case False
      note False1 = False
      have tmp1: "Available (Block (get_inputs a) (get_outputs a) (get_offsets a) (get_sample_time a)
       (get_outupd a))"
        using Cons(3) unfolding wf0_def by (simp add: Available_def)
      have tmp2: "outupd_behav_notatst (get_inputs a) (get_outputs a) (get_outupd a)
          (get_sample_time a) 0 h1"
        using Cons(4) unfolding behavDisDiag_attime.simps using False by simp
      have tmp3: "a \<in> set bl'"
        using Cons(7) by (simp add: prem_seteq)
      have tmp4: "outupd_behav_notatst (get_inputs a) (get_outputs a) (get_outupd a)
          (get_sample_time a) 0 h2"
        using Cons(8) tmp3 apply simp
      proof(induction bl')
        case Nil
        then show ?case by simp
      next
        case (Cons b bl')
        then show ?case
        proof(cases "a = b")
          case True
          then show ?thesis using Cons(2) False1 unfolding behavDisDiag_attime.simps by simp
        next
          case False
          have tmp: "a \<in> set bl'"
            using Cons(3) False by simp
          then show ?thesis using Cons unfolding behavDisDiag_attime.simps by simp
        qed
      qed
      have tmp6: "\<forall>v\<in>set (get_outputs a). \<forall>t <real 0. h1 v t = h2 v t"
        using Cons(10) by simp
      have tmp7: "get_sample_time a > 0"
        using tmp1 False unfolding Available_def by force
      then show ?thesis using outupd_behav_notatst_lemma2 tmp1 tmp2 tmp4 tmp6 False
        by simp
    qed
  have 3: "\<forall>v\<in>Outputs bl. h1 v 0 = h2 v 0"
  proof(cases "bl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have tmp1: "behavDisDiag_attime bl 0 h1 = True"
      using Cons(4) unfolding behavDisDiag_attime.simps by auto
    have tmp2: "bl <~~> remove1 a bl'"
      using perm_remove_perm Cons(7) by (metis remove_hd)
    have tmp3: "distinct bl' \<Longrightarrow> behavDisDiag_attime bl' 0 h2 \<Longrightarrow>
      behavDisDiag_attime (remove1 a bl') 0 h2 = True"
    proof(induction bl')
      case Nil
      then show ?case by simp
    next
      case (Cons b bl')
      note Cons2 = Cons
      have tmp4: "distinct bl'"
        using Cons2(2) by simp
      then show ?case
      proof(cases "a = b")
        case True
        have tmp5: "remove1 a bl' = bl'"
          using Cons(2) True by (simp add: remove1_idem)
        then show ?thesis using True apply simp using Cons(1,3) tmp4 tmp5 by auto
      next
        case False
        have tmp6: "(remove1 a (b # bl')) = b#(remove1 a bl')"
          using False by auto
        then show ?thesis using False Cons unfolding behavDisDiag_attime.simps by simp
      qed
    qed
    have tmp7: "behavDisDiag_attime (remove1 a bl') 0 h2 = True"
      using tmp3 Cons(8) 1 by auto
    have tmp9: "\<forall>v\<in>Inputs bl - Outputs bl. \<forall>t \<le> real 0. h1 v t = h2 v t"
    proof -
      have tmp1: "\<forall>v\<in>Inputs bl - Outputs (a#bl). \<forall>t \<le> real 0. h1 v t = h2 v t"
        using Cons(9) by simp
      have tmp2: "\<forall>v\<in> set (get_outputs a). \<forall>t \<le> real 0. h1 v t = h2 v t"
        using Cons(10) 2 by force
      show ?thesis using tmp1 tmp2 Diff_iff by auto
    qed
    have tmp11: "\<forall>t<real 0. \<forall>v\<in>Outputs bl. h1 v t = h2 v t"
      using Cons(10) by simp
    have tmp12: "besorted bl"
    proof -
      have tmp1: "a \<notin> set bl"
        using 0 unfolding distinct.simps by simp
      have tmp2: "remove1 a (a#bl) = bl"
        using tmp1 by (simp add: remove1_append)
      show ?thesis using Cons(5,6) tmp2 by simp
    qed
    have tmp13: "besorted (remove1 a bl')"
    proof -
      have tmp1: "a \<notin> set (remove1 a bl')"
        using 1 by simp
      have tmp2: "a \<in> set bl'"
        using Cons(7) by (simp add: prem_seteq)
      show ?thesis using Cons(7) by (simp add: Cons1(6) besorted_remove2)
    qed
    then show ?thesis using Cons False tmp1 tmp2 tmp3 1 wf0_lemma tmp12 tmp9 by simp
  qed
  then show ?case using 2 by auto
qed


lemma behavDisDiag_attime_last: "behavDisDiag_attime (a#bl) n h \<Longrightarrow> 
behavDisDiag_attime (bl@[a]) n h"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  have 1: "behavDisDiag_attime ((b # bl) @ [a]) n h 
        = behavDisDiag_attime ((b # (bl@[a]))) n h"
    by force
  then show ?case using Cons unfolding behavDisDiag_attime.simps by blast
qed

lemma behavDisDiag_attime_rev: "behavDisDiag_attime bl n h \<Longrightarrow>
behavDisDiag_attime (rev bl) n h"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  have 1: "behavDisDiag_attime (rev (a # bl)) n h = behavDisDiag_attime (rev bl @ [a]) n h"
    by simp
  have 2: "behavDisDiag_attime (a#rev bl) n h"
    using Cons(1,2) unfolding behavDisDiag_attime.simps by fastforce
  then show ?case using behavDisDiag_attime_last 1 by simp
qed

lemma behavDisDiag_attime_in: "b \<in> set bl \<Longrightarrow> behavDisDiag_attime bl n h \<Longrightarrow>
(if \<exists>k. int n = get_sample_time b * k \<or> get_sample_time b = 0
     then outupd_behav_atst (get_inputs b) (get_outputs b) (get_offsets b) (get_outupd b) n h
     else outupd_behav_notatst (get_inputs b) (get_outputs b) (get_outupd b) (get_sample_time b) n h)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case
  proof(cases "a = b")
    case True
    then show ?thesis using Cons unfolding behavDisDiag_attime.simps by auto
  next
    case False
    then show ?thesis using Cons unfolding behavDisDiag_attime.simps by auto
  qed
qed

lemma behavDisDiag_attime_remove: "behavDisDiag_attime bl n h \<Longrightarrow>
behavDisDiag_attime (remove1 a bl) n h"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  show ?case
  proof(cases "a = b")
    case True
    then show ?thesis using Cons unfolding behavDisDiag_attime.simps by auto
  next
    case False
    then show ?thesis using Cons unfolding behavDisDiag_attime.simps by auto
  qed
qed

lemma behavDisDiag_attime_perm: "al <~~> bl \<Longrightarrow> behavDisDiag_attime al n h \<Longrightarrow>
behavDisDiag_attime bl n h"
proof(induction bl arbitrary: al)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  have 1: "remove1 b al <~~> bl"
    using Cons(2) perm_remove_perm by fastforce
  have 2: "b \<in> set al"
    using Cons(2) by (meson list.set_intros(1) perm_sym prem_seteq)
  have 3: "behavDisDiag_attime bl n h"
    using Cons(1,3) behavDisDiag_attime_remove 1 by presburger
  show ?case unfolding behavDisDiag_attime.simps using 1 2 3 Cons(3)
      behavDisDiag_attime_in by blast
qed

fun behavDisDiag_tilltime :: "block list \<Rightarrow> nat \<Rightarrow> behav" where
  "behavDisDiag_tilltime bl 0 h = behavDisDiag_attime bl 0 h" |
  "behavDisDiag_tilltime bl (Suc n) h = (behavDisDiag_tilltime bl n h 
    \<and> behavDisDiag_attime bl (Suc n) h
    \<and> (\<forall> t::real. (t > n \<and> t < Suc n) \<longrightarrow> (\<forall> v\<in> Outputs bl. h v t = h v n)))"

lemma behavDisDiag_tilltime_lemma: "\<forall> t::real. (t \<le> n) \<longrightarrow> (\<forall> v. h1 v t = h2 v t) \<Longrightarrow>
behavDisDiag_tilltime bl n h1 = behavDisDiag_tilltime bl n h2"
proof (induction n)
  case 0
  then show ?case unfolding behavDisDiag_tilltime.simps
    using blocklist_hebav_attime_lemma by blast
next
  case (Suc n)
  have pre1: "behavDisDiag_tilltime bl n h1 = behavDisDiag_tilltime bl n h2"
    using Suc.IH Suc.prems by force
  have 1: "\<forall>t\<le>n. \<forall>v. h1 v (real t) = h2 v (real t)"
    using pre1 Suc by auto
  have pre2: "(\<forall> t::real. (t > n \<and> t < Suc n) \<longrightarrow> (\<forall> v. h1 v t = h1 v n)) = 
        (\<forall> t::real. (t > n \<and> t < Suc n) \<longrightarrow> (\<forall> v. h2 v t = h2 v n))"
    apply(auto simp add: Suc.prems) done 
  have pre3: "behavDisDiag_attime bl (Suc n) h1 = behavDisDiag_attime bl (Suc n) h2"
    using Suc blocklist_hebav_attime_lemma by auto
  then show ?case 
    using pre1 pre2 pre3 by (simp add: Suc.prems)
qed

lemma blocklist_hebav_tilltime_rev: "behavDisDiag_tilltime bl n h \<Longrightarrow> 
behavDisDiag_tilltime (rev bl) n h"
proof(induction n)
  case 0
  then show ?case unfolding behavDisDiag_tilltime.simps
    using behavDisDiag_attime_rev by blast
next
  case (Suc n)
  have 1: "Outputs bl = Outputs (rev bl)"
    using Outputs_rev by simp
  then show ?case using Suc unfolding behavDisDiag_tilltime.simps 
    using behavDisDiag_attime_rev by presburger
qed

lemma blocklist_hebav_tilltime_perm: "bl <~~> bl' \<Longrightarrow> 
behavDisDiag_tilltime bl n h \<Longrightarrow> behavDisDiag_tilltime bl' n h"
proof(induction n)
  case 0
  then show ?case unfolding behavDisDiag_tilltime.simps
    using behavDisDiag_attime_perm by blast
next
  case (Suc n)
  have 1: "Outputs bl = Outputs bl'"
    using Outputs_perm Suc(2) by simp
  have 2: "behavDisDiag_tilltime bl' n h"
    using Suc unfolding behavDisDiag_tilltime.simps by simp
  then show ?case using Suc unfolding behavDisDiag_tilltime.simps 
    using behavDisDiag_attime_perm 1 by presburger
qed



(*
\<comment> \<open>The constraints corresponding to a block list, add a nat for max time\<close>
definition blocklist_behav :: "block list \<Rightarrow> nat \<Rightarrow> behav" where
"blocklist_behav bl n h =  (\<forall>b \<in> set bl. block_behav b n h)"
*)

fun outupd_exe_atst :: "var list \<Rightarrow> var list \<Rightarrow> offset list \<Rightarrow> outupd list  \<Rightarrow> timed_vars \<Rightarrow> nat \<Rightarrow> timed_vars" where
"outupd_exe_atst il vl ol [] h t = h" |
"outupd_exe_atst il [] ol fl h t = h" |
"outupd_exe_atst il vl [] fl h t = h" |
"outupd_exe_atst il (v#vl) (d#ol) (f#fl) h t = outupd_exe_atst il vl ol fl (\<lambda> vv tt. (if (tt = t \<and> vv = v) 
                                                then f (map (\<lambda> a. h a (real t-real d)) il) else h vv tt)) t"

lemma outupd_exe_atst_eq1: "\<forall>x tt. x \<notin> (set vl)
\<longrightarrow> outupd_exe_atst il vl ol fl h t x tt = h x tt"
proof(induction fl arbitrary:vl ol h)
  case Nil
  then show ?case by auto
next
  case (Cons a fl)
  then show ?case
  proof (cases "vl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have 1: "vl = (hd vl)#(tl vl)"
      using False by auto
    then show ?thesis 
    proof(cases "ol = []")
      case True
      then show ?thesis
        by (metis "1" outupd_exe_atst.simps(3))
    next
      case False
      have 2: "ol = (hd ol)#(tl ol)"
        using False by auto
      then show ?thesis 
        apply clarify
        subgoal premises pre1 for x tt
        proof (cases "x = (hd vl) \<and> tt = t")
          case True
          then show ?thesis using pre1 
            by (metis "1" list.set_intros(1))
        next
          case False
          have 1 : "x \<notin> set (tl vl)"
            using pre1
            by (metis list.sel(2) list.set_sel(2))
          then show ?thesis using 1 outupd_exe_atst.simps(4)[where il = il and v = "hd vl" and vl = "tl vl"
               and d = "hd ol" and ol = "tl ol" and f = a and fl = fl and h = h and t = t]
          Cons[where vl = "tl vl" and ol = "tl ol"] pre1
            by (smt (verit, del_insts) False list.collapse outupd_exe_atst.simps(2))
        qed
        done
    qed
  qed
qed

lemma outupd_exe_atst_eq2: "(\<forall>i. i \<ge> 0 \<and> i < (length ol)
  \<longrightarrow> (nth ol i) \<ge> 0) \<Longrightarrow> (\<forall>i j. i < j \<and> j < (length vl) \<and> j \<ge> 0 
  \<longrightarrow> (nth vl i) \<noteq> (nth vl j)) \<Longrightarrow>
\<forall>x\<in>(set il) \<union> (set vl). \<forall>t \<le> t'. h1 x t = h2 x t \<Longrightarrow>
x'\<in>(set vl) \<Longrightarrow>
(outupd_exe_atst il vl ol fl h1 tt x' t' =
outupd_exe_atst il vl ol fl h2 tt x' t')"
proof(induction fl arbitrary:vl ol h1 h2)
  case Nil
  then show ?case by simp
next
  case (Cons a fl)
  then show ?case
  proof (cases "vl = []")
    case True
    then show ?thesis using Cons.prems(4) by simp
  next
    case False
    have 1: "vl = (hd vl)#(tl vl)"
      using False by auto
    then show ?thesis 
    proof(cases "ol = []")
      case True
      then show ?thesis
        by (smt (z3) "1" Cons.prems Un_iff outupd_exe_atst.simps(3))
    next
      case False
      have 2: "ol = (hd ol)#(tl ol)"
        using False by auto
      have 3: "(hd vl) \<notin> set (tl vl)"
        using Cons(3)
        by (metis (mono_tags, lifting) "1" add.right_neutral add_Suc_right in_set_conv_nth 
           le0 lessI less_trans_Suc list.size(4) nth_Cons_0 nth_Cons_Suc zero_less_Suc)
      have 4: "outupd_exe_atst il (tl vl) (tl ol) fl (\<lambda>vv tta.
         if tta = real tt \<and> vv = hd vl then a (map (\<lambda>a. h1 a (real tt - real (hd ol))) il)
         else h1 vv tta) tt (hd vl) t' = 
         (\<lambda>vv tta. if tta = real tt \<and> vv = hd vl then a (map (\<lambda>a. h1 a (real tt - real (hd ol))) il)
         else h1 vv tta) (hd vl) t'"
          using outupd_exe_atst_eq1 3 by auto
      have 5: "outupd_exe_atst il (tl vl) (tl ol) fl (\<lambda>vv tta.
         if tta = real tt \<and> vv = hd vl then a (map (\<lambda>a. h2 a (real tt - real (hd ol))) il)
         else h2 vv tta) tt (hd vl) t' = 
         (\<lambda>vv tta. if tta = real tt \<and> vv = hd vl then a (map (\<lambda>a. h2 a (real tt - real (hd ol))) il)
         else h2 vv tta) (hd vl) t'"
          using outupd_exe_atst_eq1 3 by auto
      then show ?thesis 
        proof (cases "x' = (hd vl)")
          case True
          then show ?thesis using 1 2 4 5 outupd_exe_atst.simps(4)[where il = il and v = "hd vl" and vl = "tl vl"
               and d = "hd ol" and ol = "tl ol" and f = a and fl = fl and h = h1 and t = tt]
            outupd_exe_atst.simps(4)[where il = il and v = "hd vl" and vl = "tl vl"
               and d = "hd ol" and ol = "tl ol" and f = a and fl = fl and h = h2 and t = tt]
            by (smt (z3) Cons One_nat_def Un_iff diff_Suc_1 length_Cons map_eq_conv 
                not_less_eq_eq nth_Cons_0 of_nat_Suc of_nat_diff of_nat_mono zero_less_Suc)
        next
          case False
          have 6: "\<forall>x\<in>set il \<union> set (tl vl). \<forall>t\<le>t'. (\<lambda>vv tta.
         if tta = real tt \<and> vv = hd vl then a (map (\<lambda>a. h1 a (real tt - real (hd ol))) il)
         else h1 vv tta) x t = (\<lambda>vv tta.
         if tta = real tt \<and> vv = hd vl then a (map (\<lambda>a. h2 a (real tt - real (hd ol))) il)
         else h2 vv tta) x t"
            apply clarify
            subgoal premises pre for x t
            proof (cases "x = hd vl \<and> t = real tt")
              case True
              have tmp1: "hd ol \<ge> 0"
                using Cons(2) 2 by simp
              then show ?thesis using Cons(4) by (smt (verit, del_insts) True UnCI map_eq_conv of_nat_0 of_nat_mono pre(2))
            next
              case False
              then show ?thesis using Cons(4) pre 1 by (metis Un_iff list.set_intros(2))
            qed
            done
          have 7: "outupd_exe_atst il (tl vl) (tl ol) fl (\<lambda>vv tta.
         if tta = real tt \<and> vv = hd vl then a (map (\<lambda>a. h1 a (real tt - real (hd ol))) il)
         else h1 vv tta) tt x' t' 
          = outupd_exe_atst il (tl vl) (tl ol) fl (\<lambda>vv tta.
         if tta = real tt \<and> vv = hd vl then a (map (\<lambda>a. h2 a (real tt - real (hd ol))) il)
         else h2 vv tta) tt x' t'"
          proof - 
            have tmp1: "\<forall>i. 0 \<le> i \<and> i < length (tl ol) \<longrightarrow> 0 \<le> (tl ol) ! i"
              using Cons by auto
            have tmp2: "\<forall>i j. i < j \<and> j < length (tl vl) \<and> 0 \<le> j \<longrightarrow> (tl vl) ! i \<noteq> (tl vl) ! j"
              using Cons by (smt (verit, best) "1" Suc_less_eq bot_nat_0.extremum length_Cons nat_less_le nth_tl order_less_le_trans)
            have tmp3: "x' \<in> set (tl vl)"
              using Cons(5) False by (metis "1" set_ConsD)
            show ?thesis using tmp1 tmp2 tmp3 6 Cons by presburger
          qed
          then show ?thesis using 1 2 outupd_exe_atst.simps(4)[where il = il and v = "hd vl" and vl = "tl vl"
               and d = "hd ol" and ol = "tl ol" and f = a and fl = fl and h = h1 and t = tt]
            outupd_exe_atst.simps(4)[where il = il and v = "hd vl" and vl = "tl vl"
               and d = "hd ol" and ol = "tl ol" and f = a and fl = fl and h = h2 and t = tt] 
              Cons by simp
        qed
    qed
  qed
qed

lemma outupd_exe_atst_eq3: "\<forall>x tt. tt \<noteq> real t
\<longrightarrow> outupd_exe_atst il vl ol fl h t x tt = h x tt"
proof(induction fl arbitrary:vl ol h)
  case Nil
  then show ?case by auto
next
  case (Cons a fl)
  then show ?case
  proof (cases "vl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have 1: "vl = (hd vl)#(tl vl)"
      using False by auto
    then show ?thesis 
    proof(cases "ol = []")
      case True
      then show ?thesis
        by (metis "1" outupd_exe_atst.simps(3))
    next
      case False
      have 2: "ol = (hd ol)#(tl ol)"
        using False by auto
      then show ?thesis 
        apply clarify
        subgoal premises pre1 for x tt
        proof (cases "x = (hd vl) \<and> tt = t")
          case True
          then show ?thesis using pre1 by (metis)
        next
          case False
          then show ?thesis using 1 outupd_exe_atst.simps(4)[where il = il and v = "hd vl" and vl = "tl vl"
               and d = "hd ol" and ol = "tl ol" and f = a and fl = fl and h = h and t = t]
          Cons[where vl = "tl vl" and ol = "tl ol"] pre1 outupd_exe_atst_eq1
            by (smt (verit, best) list.collapse list.sel(2) of_nat_eq_iff)
        qed
        done
    qed
  qed
qed

lemma outupd_exe_atst_lemma: "length vl = length ol \<and> length ol = length fl \<and> length vl > 0 \<Longrightarrow>
Available (Block il vl ol T fl) \<Longrightarrow> \<forall>i. i \<ge> 0 \<and> i < (length vl)
\<longrightarrow> outupd_exe_atst il vl ol fl h t (vl ! i) t = (fl ! i) (map (\<lambda> a. h a (real t-real (ol ! i))) il)"
proof(induction fl arbitrary:vl ol h)
  case Nil
  then show ?case by auto
next
  case (Cons a fl)
  then show ?case
  proof (cases "vl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have 1: "vl = (hd vl)#(tl vl)"
      using False by auto
    then show ?thesis 
    proof(cases "ol = []")
      case True
      then show ?thesis
        using Cons(2) by simp
    next
      case False
      have 2: "ol = (hd ol)#(tl ol)"
        using False by auto
      then show ?thesis
      proof(cases "tl vl = []")
        case True
        have tmp1: "outupd_exe_atst il vl ol (a # fl) h t = (\<lambda>vv tt.
         if tt = real t \<and> vv = hd vl then a (map (\<lambda>a. h a (real t - real (hd ol))) il) else h vv tt)"
          using outupd_exe_atst.simps(4)[where il = il and v = "hd vl" and vl = "tl vl"
               and d = "hd ol" and ol = "tl ol" and f = a and fl = fl and h = h and t = t] True
          by (smt (verit) "1" "2" list.discI outupd_exe_atst.elims)
        then show ?thesis 
          by (smt (verit, ccfv_SIG) "1" "2" One_nat_def Suc_pred True le_eq_less_or_eq 
              length_tl less_trans_Suc list.size(3) map_eq_conv nth_Cons_0 of_nat_less_iff)
      next
        case False
        have tmp1: "length (tl vl) = length (tl ol) \<and> length (tl ol) = length fl \<and> 0 < length (tl vl)"
          using Cons(2) 2 1 False by fastforce
        have tmp2: "Available (Block il (tl vl) (tl ol) T fl)"
          using Cons(3) 2 1 unfolding Available_def apply simp 
          by (metis (no_types, opaque_lifting) disjoint_iff_not_equal 
              less_Suc_eq_0_disj list.set_intros(2) nth_Cons_Suc)
        have tmp3: "hd vl \<notin> set (tl vl)"
            using Cons(3) 1 unfolding Available_def
            by (metis Suc_less_eq bot_nat_0.extremum get_outputs.simps in_set_conv_nth 
                length_Cons nth_Cons_0 nth_Cons_Suc zero_less_Suc)
        have tmp4: "outupd_exe_atst il (tl vl) (tl ol) fl (\<lambda>vv tt. if tt = real t \<and> vv = hd vl 
        then a (map (\<lambda>a. h a (real t - real (hd ol))) il) else h vv tt) t (hd vl) (real t) = 
        a (map (\<lambda>a. h a (real t - real (hd ol))) il)"
          using outupd_exe_atst_eq1 tmp3 by auto
        have tmp5: "\<forall>i. 0 \<le> i \<and> i < length (tl vl) \<longrightarrow>
        outupd_exe_atst il (tl vl) (tl ol) fl (\<lambda>vv tt. if tt = real t \<and> vv = hd vl 
        then a (map (\<lambda>a. h a (real t - real (hd ol))) il) else h vv tt) t ((tl vl) ! i) (real t) =
        (fl ! i) (map (\<lambda>x. (\<lambda>vv tt. if tt = real t \<and> vv = hd vl 
        then a (map (\<lambda>a. h a (real t - real (hd ol))) il) else h vv tt) x (real t - real ((tl ol) ! i))) il)"
          using Cons(1) tmp1 tmp2 by blast
        have tmp6: "set il \<inter> set vl = {}"
          using Cons(3) unfolding Available_def by auto
        have tmp7: "\<forall>i. 0 \<le> i \<and> i < length (tl vl) \<longrightarrow> (fl ! i) (map (\<lambda>x. (\<lambda>vv tt. if tt = real t \<and> vv = hd vl 
        then a (map (\<lambda>a. h a (real t - real (hd ol))) il) else h vv tt) x (real t - real ((tl ol) ! i))) il) = 
        (fl ! i) (map (\<lambda>a. h a (real t - real ((tl ol) ! i))) il)"
          using tmp6 by (smt (verit, ccfv_threshold) "1" Cons.prems(1) 
              disjoint_iff_not_equal map_eq_conv nth_Cons_0 nth_mem)
        have tmp8: "outupd_exe_atst il vl ol (a # fl) h t (hd vl) (real t) = 
          a (map (\<lambda>a. h a (real t - real (hd ol))) il)"
          using outupd_exe_atst.simps(4)[where il = il and v = "hd vl" and vl = "tl vl"
               and d = "hd ol" and ol = "tl ol" and f = a and fl = fl and h = h and t = t] tmp4 1 2
          by force
        have tmp9: "\<forall>i. 0 \<le> i \<and> i < length (tl vl) \<longrightarrow> outupd_exe_atst il (tl vl) (tl ol) fl
         (\<lambda>vv tt. if tt = real t \<and> vv = hd vl then a (map (\<lambda>a. h a (real t - real (hd ol))) il) else h vv tt)
         t (tl vl ! i) (real t) = (fl ! i) (map (\<lambda>a. h a (real t - real (tl ol ! i))) il)"
          using tmp7 tmp5 by simp
        show ?thesis apply clarify
          subgoal premises pre for i
          proof(cases "i = 0")
            case True
            then show ?thesis using tmp8 1 2 by (metis nth_Cons_0)
          next
            case False
            have tmp1: "i > 0 \<and> i < length vl"
              using False pre by simp
            have tmp2: "outupd_exe_atst il vl ol (a # fl) h t (vl ! i) (real t) =
            outupd_exe_atst il (tl vl) (tl ol) fl (\<lambda>vv tt. if tt = real t \<and> vv = hd vl 
            then a (map (\<lambda>a. h a (real t - real (hd ol))) il) else h vv tt) t (vl ! i) (real t)"
              using outupd_exe_atst.simps(4)[where il = il and v = "hd vl" and vl = "tl vl"
               and d = "hd ol" and ol = "tl ol" and f = a and fl = fl and h = h and t = t] 1 2 by auto
            then show ?thesis using tmp9 tmp1 apply simp
              by (smt (verit, ccfv_SIG) "1" "2" Cons.prems(1) False 
                  One_nat_def Suc_less_SucD Suc_pred map_eq_conv nth_Cons')
          qed
          done
      qed
    qed
  qed
qed 

fun outupd_exe_notatst :: "var list \<Rightarrow> var list \<Rightarrow> outupd list \<Rightarrow> sample_time \<Rightarrow> timed_vars \<Rightarrow> nat \<Rightarrow> timed_vars" where
"outupd_exe_notatst il vl [] T h t = h" |
"outupd_exe_notatst il [] fl T h t = h" |
"outupd_exe_notatst il (v#vl) (f#fl) T h t = outupd_exe_notatst il vl fl T (\<lambda> vv tt. (if (tt = t \<and> vv = v) 
                                             then (h v (((int t) div T)*T)) else h vv tt)) t"

lemma outupd_exe_notatst_eq1: "\<forall>x tt. x \<notin> (set vl)
\<longrightarrow> outupd_exe_notatst il vl fl T h t x tt = h x tt"
proof(induction fl arbitrary:vl h)
  case Nil
  then show ?case by auto
next
  case (Cons a fl)
  then show ?case
  proof (cases "vl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have 1: "vl = (hd vl)#(tl vl)"
      using False by auto
    then show ?thesis 
      apply clarify
        subgoal premises pre1 for x tt
        proof (cases "x = (hd vl) \<and> tt = t")
          case True
          then show ?thesis using pre1 
            by (metis "1" list.set_intros(1))
        next
          case False
          then show ?thesis using 1 outupd_exe_notatst.simps(3)[where il = il and v = "hd vl" and vl = "tl vl"
               and f = a and fl = fl and h = h and t = t and T = T]
          Cons[where vl = "tl vl" ] pre1 by (smt (verit, ccfv_threshold) list.set_intros(2))
        qed
        done
  qed
qed


lemma outupd_exe_notatst_eq2: "(\<forall>i j. i < j \<and> j < (length vl) \<and> j \<ge> 0 
  \<longrightarrow> (nth vl i) \<noteq> (nth vl j)) \<Longrightarrow> T > 0 \<Longrightarrow>
\<forall>x\<in>(set il) \<union> (set vl). \<forall>t \<le> t'. h1 x t = h2 x t \<Longrightarrow>
x'\<in>(set vl) \<Longrightarrow>
(outupd_exe_notatst il vl fl T h1 t x' t' =
outupd_exe_notatst il vl fl T h2 t x' t')"
proof(induction fl arbitrary:vl h1 h2)
  case Nil
  then show ?case by simp
next
  case (Cons a fl)
  then show ?case
  proof (cases "vl = []")
    case True
    then show ?thesis using Cons.prems(3,4) by auto
  next
    case False
    have 1: "vl = (hd vl)#(tl vl)"
      using False by auto
    have 2: "(hd vl) \<notin> set (tl vl)"
        using Cons(2)
        by (metis (mono_tags, lifting) "1" add.right_neutral add_Suc_right in_set_conv_nth 
           le0 lessI less_trans_Suc list.size(4) nth_Cons_0 nth_Cons_Suc zero_less_Suc)
    then show ?thesis
        proof (cases "x' = (hd vl)")
          case True
          have tmp1: "(real_of_int (int t div T * T)) \<le> t"
            by (metis Cons.prems(2) mult.commute mult_div_le of_int_le_iff of_int_of_nat_eq)
          have tmp2: "outupd_exe_notatst il (tl vl) fl T (\<lambda>vv tt.
         if tt = real t \<and> vv = hd vl then h1 (hd vl) (real_of_int (int t div T * T))
         else h1 vv tt) t x' t' = (\<lambda>vv tt. if tt = real t \<and> vv = hd vl then 
         h1 (hd vl) (real_of_int (int t div T * T)) else h1 vv tt) x' t'" 
            using 2 outupd_exe_notatst_eq1 True by presburger
          have tmp3: "outupd_exe_notatst il (tl vl) fl T (\<lambda>vv tt.
         if tt = real t \<and> vv = hd vl then h2 (hd vl) (real_of_int (int t div T * T))
         else h2 vv tt) t x' t' = (\<lambda>vv tt. if tt = real t \<and> vv = hd vl then 
         h2 (hd vl) (real_of_int (int t div T * T)) else h2 vv tt) x' t'"
            using 2 outupd_exe_notatst_eq1 True by presburger
          have tmp4: "(real_of_int (int t div T)) \<le> t"
            using Cons(2)
            by (smt (verit) Cons.prems(2) int_of_reals(4) nonzero_mult_div_cancel_left 
                of_int_0_less_iff of_int_le_iff of_nat_0_le_iff pos_imp_zdiv_pos_iff tmp1)
          then show ?thesis using Cons(3) tmp2 1 outupd_exe_notatst.simps(3)[where il = il and v = "hd vl" and vl = "tl vl"
               and f = a and fl = fl and h = h1 and T = T and t = t]
          outupd_exe_notatst.simps(3)[where il = il and v = "hd vl" and vl = "tl vl"
               and f = a and fl = fl and h = h2 and T = T and t = t]
          apply simp using Cons(4) True tmp1 tmp4 tmp3 2 Cons.prems(4) outupd_exe_notatst_eq1 by force
        next
          case False
          have tmp1: "outupd_exe_notatst il (tl vl) fl T (\<lambda>vv tt.
         if tt = real t \<and> vv = hd vl then h1 (hd vl) (real_of_int (int t div T * T))
         else h1 vv tt) t x' t' =
                   outupd_exe_notatst il (tl vl) fl T (\<lambda>vv tt.
         if tt = real t \<and> vv = hd vl then h2 (hd vl) (real_of_int (int t div T * T))
         else h2 vv tt) t x' t'"
          proof -
            have tmp1: "\<forall>i j. i < j \<and> j < length (tl vl) \<and> 0 \<le> j \<longrightarrow> (tl vl) ! i \<noteq> (tl vl) ! j"
              using Cons by (smt (verit, best) "1" Suc_less_eq bot_nat_0.extremum length_Cons nat_less_le nth_tl order_less_le_trans)
            have tmp2: "x' \<in> set (tl vl)"
              using Cons False 1 by (metis set_ConsD)
            have tmp3: "\<forall>x\<in>set il \<union> set (tl vl). \<forall>t2\<le>t'. (\<lambda>vv tt.
         if tt = real t \<and> vv = hd vl then h1 (hd vl) (real_of_int (int t div T * T))
         else h1 vv tt) x t2 = (\<lambda>vv tt.
         if tt = real t \<and> vv = hd vl then h2 (hd vl) (real_of_int (int t div T * T))
         else h2 vv tt) x t2"
              using 1 2 Cons(4) by (metis Cons.prems(2) Un_iff le_sup_iff list.distinct(1) 
              list.set_sel(2) mult.commute mult_div_le of_int_le_iff of_int_of_nat_eq sup.orderE)
            show ?thesis using tmp1 tmp2 tmp3 Cons(3) Cons(1) by simp
          qed
          then show ?thesis using 1 outupd_exe_notatst.simps(3)[where il = il and v = "hd vl" and vl = "tl vl"
               and f = a and fl = fl and h = h1  and T = T and t = t]
          outupd_exe_notatst.simps(3)[where il = il and v = "hd vl" and vl = "tl vl"
               and f = a and fl = fl and h = h2  and T = T and t = t] Cons by simp
            
        qed
  qed
qed

lemma outupd_exe_notatst_eq3: "\<forall>x tt. tt \<noteq> real t
\<longrightarrow> outupd_exe_notatst il vl fl T h t x tt = h x tt"
proof(induction fl arbitrary:vl h)
  case Nil
  then show ?case by auto
next
  case (Cons a fl)
  then show ?case
  proof (cases "vl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have 1: "vl = (hd vl)#(tl vl)"
      using False by auto
    then show ?thesis
      apply clarify
        subgoal premises pre1 for x tt
        proof (cases "x = (hd vl) \<and> tt = t")
          case True
          then show ?thesis using pre1 by (metis)
        next
          case False
          then show ?thesis using 1 outupd_exe_notatst.simps(3)[where il = il and v = "hd vl" and vl = "tl vl"
               and f = a and fl = fl and h = h and t = t and T = T]
          Cons[where vl = "tl vl" ] pre1 by simp
        qed
        done
  qed
qed

lemma outupd_exe_notatst_lemma: "length vl = length fl \<and> length vl > 0 \<Longrightarrow>
distinct vl \<Longrightarrow> \<forall>i. i \<ge> 0 \<and> i < (length vl)
\<longrightarrow> outupd_exe_notatst il vl fl T h t (vl ! i) t = h (vl ! i) (((int t) div T)*T)"
proof(induction fl arbitrary:vl h)
  case Nil
  then show ?case by auto
next
  case (Cons a fl)
  then show ?case
  proof (cases "vl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have 1: "vl = (hd vl)#(tl vl)"
      using False by auto
    then show ?thesis
    proof(cases "tl vl = []")
      case True
      then show ?thesis using outupd_exe_notatst.simps(3)[where il = il and v = "hd vl" and vl = "tl vl"
               and f = a and fl = fl and h = h and t = t and T = T] 1
        by (smt (verit, best) Cons.prems(1) One_nat_def Suc_less_eq impossible_Cons length_Cons 
         length_greater_0_conv less_Suc_eq linorder_not_le nth_Cons_0 outupd_exe_notatst.simps(1))
    next
      case False
      have tmp1: "length (tl vl) = length fl \<and> 0 < length (tl vl)"
        using Cons(2) False 1 by fastforce
      have tmp2: "distinct (tl vl)"
        using Cons(3) by (simp add: distinct_tl)
      have tmp3: "\<forall>i. 0 \<le> i \<and> i < length (tl vl) \<longrightarrow>
        outupd_exe_notatst il (tl vl) fl T 
        (\<lambda>vv tt. if tt = real t \<and> vv = hd vl then h (hd vl) 
        (real_of_int (int t div T * T)) else h vv tt) t ((tl vl) ! i) (real t) =
        (\<lambda>vv tt. if tt = real t \<and> vv = hd vl then h (hd vl) 
        (real_of_int (int t div T * T)) else h vv tt) ((tl vl) ! i) (real_of_int (int t div T * T))"
        using Cons(1) tmp1 tmp2 by blast
      have tmp4: "outupd_exe_notatst il vl (a # fl) T h t (hd vl) (real t) =
        h (hd vl) (real_of_int (int t div T * T))"
        using outupd_exe_notatst.simps(3)[where il = il and v = "hd vl" and vl = "tl vl"
        and f = a and fl = fl and h = h and t = t and T = T] outupd_exe_notatst_eq1
        by (smt (verit, best) "1" Cons.prems(2) distinct.simps(2))
      then show ?thesis using tmp3 outupd_exe_notatst.simps(3)[where il = il and v = "hd vl" and vl = "tl vl"
               and f = a and fl = fl and h = h and t = t and T = T] 1 
        by (smt (verit, best) bot_nat_0.extremum diff_Suc_1 length_Cons less_Suc_eq_0_disj nth_Cons')
    qed
  qed
qed

fun exeDisDiag_interval :: "block list \<Rightarrow> timed_vars \<Rightarrow> real \<Rightarrow> real \<Rightarrow> timed_vars" where
  "exeDisDiag_interval bl h t0 t = (\<lambda>vv tt. (if t0 < tt \<and> tt < t0 + t \<and> vv \<in> Outputs bl
  then h vv t0 else h vv tt))"

\<comment> \<open>Given an initial h, the execution of a diagram at time t produces a new h', 
    which updates the values of corresponding variables at time t. \<close>
primrec exeDisDiag_attime :: "sorted_block_list \<Rightarrow> timed_vars \<Rightarrow> nat \<Rightarrow> timed_vars" where
"exeDisDiag_attime [] h t = h" |
"exeDisDiag_attime (b # bl) h t = (if (\<exists> k. t = (get_sample_time b)*k) \<or> (get_sample_time b) = 0
              then outupd_exe_atst (get_inputs b) (get_outputs b) (get_offsets b) (get_outupd b) (exeDisDiag_attime bl h t) t 
              else outupd_exe_notatst (get_inputs b) (get_outputs b) (get_outupd b) (get_sample_time b) (exeDisDiag_attime bl h t) t)"

lemma exeDisDiag_attime_lemma: "\<forall>x. x \<notin> Outputs bl 
\<longrightarrow> exeDisDiag_attime bl h t1 x t2 = h x t2 "
proof(induction bl)
  case Nil
  then show ?case by auto
next
  case (Cons a bl)
  then show ?case unfolding exeDisDiag_attime.simps
    using outupd_exe_notatst_eq1 outupd_exe_atst_eq1 by simp
qed

lemma exeDisDiag_attime_lemma2: "t \<noteq> real t1 
\<Longrightarrow> exeDisDiag_attime bl h t1 x t = h x t "
proof(induction bl)
  case Nil
  then show ?case by auto
next
  case (Cons a bl)
  then show ?case unfolding exeDisDiag_attime.simps
    using outupd_exe_notatst_eq3 outupd_exe_atst_eq3 by simp
qed

\<comment> \<open>The execution of a discrete diagram till time n, here n is a nat.\<close>
fun exe_discrete_diag_tilltime :: "sorted_block_list \<Rightarrow> timed_vars \<Rightarrow> nat \<Rightarrow> timed_vars" where
"exe_discrete_diag_tilltime bl h0 0 v t = exeDisDiag_attime bl h0 0 v t" |
"exe_discrete_diag_tilltime bl h0 (Suc k) v t = ((if (t = Suc k) then 
     ((exeDisDiag_attime bl (exe_discrete_diag_tilltime bl h0 k) (Suc k)) v t)
     else (if t \<le> k then ((exe_discrete_diag_tilltime bl h0 k) v t) 
     else (if t < Suc k \<and> v \<in> (Outputs bl) then ((exe_discrete_diag_tilltime bl h0 k) v k) 
     else h0 v t) )))"

lemma exe_discrete_diag_tilltime_lemma1: "\<forall>x. x \<notin> Outputs bl 
\<longrightarrow> exe_discrete_diag_tilltime bl h t1 x t2 = h x t2"
proof(induction t1)
  case 0
  then show ?case using exeDisDiag_attime_lemma unfolding exe_discrete_diag_tilltime.simps by simp
next
  case (Suc t1)
  then show ?case unfolding exe_discrete_diag_tilltime.simps 
    subgoal
  proof(cases "t2 \<le> real t1")
    case True
    then show ?thesis apply simp using Suc by simp
  next
    case False
    note False1 = False
    then show ?thesis
    proof(cases "t2 = Suc t1")
      case True
      then show ?thesis using False1 apply simp using exeDisDiag_attime_lemma Suc
        by presburger
    next
      case False
      then show ?thesis
        using False False1 by simp
    qed
  qed
  done
qed

lemma exe_discrete_diag_tilltime_lemma2: "\<forall>t2. t2 > real t1 \<or> t2 < 0
\<longrightarrow> exe_discrete_diag_tilltime bl h t1 x t2 = h x t2"
proof(induction t1)
  case 0
  then show ?case using exeDisDiag_attime_lemma2 unfolding exe_discrete_diag_tilltime.simps by simp
next
  case (Suc t1)
  then show ?case by simp
qed
 


  
lemma exec_diag_tilltime_lammaSucK :
"\<forall> t::real. (t \<le> k) \<longrightarrow> 
(\<forall> v. (exe_discrete_diag_tilltime bl h (Suc k)) v t = (exe_discrete_diag_tilltime bl h k) v t)"
  by auto

lemma existence_discrete_diag_at0: "besorted (rev bl) \<Longrightarrow> wf1 bl \<Longrightarrow> 
behavDisDiag_attime bl 0 (exeDisDiag_attime bl h 0)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  note Cons1 = Cons
  have 1: "\<forall>x t. x \<notin> set(get_outputs a) \<or> (t \<noteq> 0)\<longrightarrow> 
  exeDisDiag_attime bl h 0 x t 
  = exeDisDiag_attime (a # bl) h 0 x t"
  unfolding exeDisDiag_attime.simps using outupd_exe_atst_eq1 outupd_exe_atst_eq3
  outupd_exe_notatst_eq1 outupd_exe_notatst_eq3 by fastforce
  have 2: "besorted (rev bl)"
  proof -
    have tmp1: "remove1 a (rev (a#bl)) = rev bl"
      using Cons(3) unfolding wf1_def wf0_def Unique_def 
      by (metis Suc_eq_plus1 append.right_neutral diff_Suc_1 in_set_conv_nth le_zero_eq 
          length_Cons less_diff_conv list.sel(3) nth_Cons_0 nth_tl remove1_append 
          remove_hd rev.simps(2) set_rev zero_less_Suc)
    show ?thesis using tmp1 besorted_remove2 Cons(2) by metis
  qed
  have 3: "wf0 bl"
    using Cons(3) wf0_lemma unfolding wf1_def by auto
  have 4: "Graph (set bl)"
    using Cons(3) Graph_lemma unfolding wf1_def by auto
  have 5: "\<forall>x\<in>Outputs bl. \<forall>t. exeDisDiag_attime bl h 0 x t 
                = exeDisDiag_attime (a # bl) h 0 x t"
    using 1 Cons(3) by (meson wf1_def wf0_def Cons1(3) Graph_lemma2)
  have 6: "\<forall>i. 0 \<le> i \<and> i < length bl \<longrightarrow> (\<forall>x\<in>set (get_inputs (bl ! i)).
            \<forall>t\<le>(real 0 - real (minimal (get_offsets (bl ! i)))). 
            exeDisDiag_attime bl h 0 x t 
            = exeDisDiag_attime (a # bl) h 0 x t)"
      apply clarify subgoal premises pre for i x t 
      proof(cases "set (get_outputs a) \<inter> set (get_inputs (bl ! i)) = {}")
        case True
        have tmp1: "\<forall>x \<in> set (get_inputs (bl ! i)). (\<forall>t::real. 
              exeDisDiag_attime bl h 0  x t 
              = exeDisDiag_attime (a # bl) h 0 x t)"
          using 1 True pre(1) by blast
        have tmp2: "\<forall>i. 0 \<le> i \<and> i < length bl \<longrightarrow>
        (\<forall>x\<in>set (get_inputs (bl ! i)). x \<in> Inputs bl)"
        proof(induction bl)
          case Nil
          then show ?case by simp
        next
          case (Cons b bl)
          then show ?case unfolding Inputs.simps
            by (metis Un_iff diff_Suc_1 length_Cons less_Suc_eq_0_disj nth_Cons' zero_le)
        qed
        then show ?thesis using pre tmp1 by presburger
      next
        case False
        have tmp1: "minimal (get_offsets (bl ! i)) \<ge> 0"
          using Cons1(3) unfolding wf0_def Available_def by force
        have tmp2: "get_outputs (bl ! i) \<noteq> []"
          using Cons(3) unfolding wf1_def Graph_def by (simp add: pre(3))
        have tmp3: "get_offsets (bl ! i) \<noteq> []"
          using Cons(3) tmp2 unfolding wf1_def wf0_def Available_def 
          by (metis length_0_conv list.set_intros(2) nth_mem pre(3))
        have tmp4: "check_offset (get_outputs a) (get_inputs (bl ! i)) (get_offsets (bl ! i)) = False"
          using Cons(2) besorted_last pre(3) by simp
        have tmp5: "\<forall>d \<in> set (get_offsets (bl ! i)). d \<noteq> 0"
          using check_offset.simps(3) tmp2 tmp3 tmp4 False
          by (metis boolean_algebra.conj_zero_left check_offset.elims(3) empty_set)
        have tmp6: "minimal (get_offsets (bl ! i)) \<ge> 1"
          using tmp1 tmp5
          using leD less_one linorder_le_less_linear list.set(2) 
            minimal.simps(2) minimal_lemma tmp3 by fastforce
        have tmp7: "0 - real (minimal (get_offsets (bl ! i))) < 0"
          using tmp6 by simp
        then show ?thesis using pre 1 by force
      qed
      done
      have 7: "behavDisDiag_attime bl 0 (exeDisDiag_attime bl h 0)"
      using Cons(1) 2 3 4 using wf1_def by simp
    have 8: "behavDisDiag_attime bl 0 (exeDisDiag_attime (a # bl) h 0)"
      using blocklist_hebav_attime_eq2 5 6 7 by simp
    have 9: "(\<exists>ka. 0 = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
       (outupd_behav_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) 0
           (exeDisDiag_attime (a # bl) h 0))"
      proof -
        have tmp1: "length (get_outputs a) = length (get_offsets a) \<and> length (get_offsets a)
               = length (get_outupd a)  \<and> 0 < length (get_outputs a)"
          using Cons(3) unfolding wf1_def Graph_def wf0_def Available_def by fastforce
        have tmp2: "Available (Block (get_inputs a) (get_outputs a) (get_offsets a) 
            (get_sample_time a) (get_outupd a))"
          using Cons(3) unfolding wf1_def wf0_def by (simp add: Available_def)
        have tmp3: "\<forall>i. 0 \<le> i \<and> i < length (get_outputs a) \<longrightarrow>
        outupd_exe_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) 
          (exeDisDiag_attime bl h 0) 0 ((get_outputs a) ! i) 0 =
        ((get_outupd a) ! i) (map (\<lambda>x. (exeDisDiag_attime bl h 0) 
        x (real 0 - real ((get_offsets a) ! i))) (get_inputs a))"
          using tmp1 tmp2 outupd_exe_atst_lemma by (metis of_nat_0)
        have tmp4: "(\<exists>ka. 0 = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow> 
          (\<forall>i. 0 \<le> i \<and> i \<le> length (get_outputs a) \<longrightarrow>
        (exeDisDiag_attime (a # bl) h 0) ((get_outputs a) ! i) (real 0) = 
        outupd_exe_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) 
          (exeDisDiag_attime bl h 0) 0 ((get_outputs a) ! i) (real 0))"
          by simp
        have tmp5: "(\<exists>ka. 0 = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
        (\<forall>i. 0 \<le> i \<and> i < length (get_outputs a)\<longrightarrow> (\<forall>x \<in> set (get_inputs a). 
        (exeDisDiag_attime bl h 0) x (real 0 - real ((get_offsets a) ! i)) = 
        ( exeDisDiag_attime (a # bl) h 0)
        x (real 0 - real ((get_offsets a) ! i))))"
          apply clarify
          subgoal premises pre for ka i x
          proof(cases "get_offsets a ! i = 0")
            case True
            have tmp1: "set (get_inputs a) \<inter> set (get_outputs a) = {}"
              using Cons(3) unfolding wf1_def wf0_def Available_def by auto
            then show ?thesis using True pre apply simp using outupd_exe_atst_eq1 
              by (metis disjoint_iff_not_equal)
          next
            case False
            have tmp1: "get_offsets a ! i \<ge> 1"
              using Cons(3) False unfolding wf0_def Available_def by force
            then show ?thesis using pre apply simp using exeDisDiag_attime_lemma2
              outupd_exe_atst_eq3 by force
          qed
          done
        have tmp6: "(\<exists>ka. 0 = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
        (\<forall>i. 0 \<le> i \<and> i < length (get_outputs a)\<longrightarrow>
    ((get_outupd a) ! i) (map (\<lambda>x. (exeDisDiag_attime (a # bl) h 0)
         x (real 0 - real ((get_offsets a) ! i))) (get_inputs a)) = ((get_outupd a) ! i)
          (map (\<lambda>x. (exeDisDiag_attime bl h 0)
         x (real 0 - real ((get_offsets a) ! i))) (get_inputs a)))"
          using tmp5 by (smt (z3) map_eq_conv)
        have tmp7: "(\<exists>ka. 0 = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
        (\<forall>i. 0 \<le> i \<and> i < length (get_outputs a) \<longrightarrow>
        (exeDisDiag_attime (a # bl) h 0)
         ((get_outputs a) ! i) (real 0) 
        = ((get_outupd a) ! i) (map (\<lambda>x. (exeDisDiag_attime (a # bl) h 0)
         x (real 0 - real ((get_offsets a) ! i))) (get_inputs a)))"
          using tmp3 tmp4 tmp6 le_eq_less_or_eq by simp
        show ?thesis
          using outupd_behav_atst_lemma3 tmp1 tmp7 by simp
      qed
  have 10: "\<not>(\<exists>ka. 0 = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
outupd_behav_notatst (get_inputs a) (get_outputs a) (get_outupd a) (get_sample_time a) 0
           (exeDisDiag_attime (a # bl) h 0)"
        apply clarify subgoal premises pre
      proof -
        have tmp1: "length (get_outputs a) = length (get_outupd a) \<and> 0 < length (get_outputs a)"
          using Cons(3) unfolding wf1_def Graph_def wf0_def Available_def by fastforce
        have tmp2: "(get_sample_time a) > 0"
          using Cons(3) pre unfolding wf0_def Available_def by force
        have tmp3: "distinct (get_outputs a)"
          using Cons(3) unfolding wf1_def wf0_def Available_def
          by (metis distinct_conv_nth less_eq_nat.simps(1) linorder_neqE_nat list.set_intros(1))
        have tmp4: "\<forall>i. 0 \<le> i \<and> i < length (get_outputs a) \<longrightarrow>
        outupd_exe_notatst (get_inputs a) (get_outputs a) (get_outupd a) (get_sample_time a) 
        (exeDisDiag_attime bl h 0) 0 ((get_outputs a) ! i) (real 0) = 
        (exeDisDiag_attime bl h 0) ((get_outputs a) ! i) 
        (real_of_int (int 0 div (get_sample_time a) * (get_sample_time a)))"
          using tmp1 tmp3 outupd_exe_notatst_lemma by blast
        have tmp5: "\<not>(\<exists>ka. 0 = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow> 
          (\<forall>i. 0 \<le> i \<and> i \<le> length (get_outputs a) \<longrightarrow>
        (exeDisDiag_attime (a # bl) h 0) ((get_outputs a) ! i) (real 0) = 
        outupd_exe_notatst (get_inputs a) (get_outputs a) (get_outupd a) (get_sample_time a)
          (exeDisDiag_attime bl h 0) 0 ((get_outputs a) ! i) (real 0))"
          by simp
        have tmp6: "\<not>(\<exists>ka. 0 = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
        (\<forall>i. 0 \<le> i \<and> i \<le> length (get_outputs a)\<longrightarrow>  
        (exeDisDiag_attime bl h 0) ((get_outputs a) ! i) 
        (real_of_int (int 0 div (get_sample_time a) * (get_sample_time a))) = 
        (exeDisDiag_attime (a # bl) h 0)
        ((get_outputs a) ! i) (real_of_int (int 0 div (get_sample_time a) * (get_sample_time a))))"
          apply clarify
          subgoal premises pre for i
          proof -
            show ?thesis using pre exeDisDiag_attime_lemma2 unfolding exeDisDiag_attime.simps
              by simp
          qed
          done
        have tmp7: "\<not>(\<exists>ka. 0 = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
        (\<forall>i. 0 \<le> i \<and> i < length (get_outputs a) \<longrightarrow>
        (exeDisDiag_attime (a # bl) h 0)
        ((get_outputs a) ! i) (real 0) = 
        (exeDisDiag_attime (a # bl) h 0)
        ((get_outputs a) ! i) (real_of_int (int 0 div (get_sample_time a) * (get_sample_time a))))"
          using tmp4 tmp5 tmp6 using less_imp_le_nat by presburger
        show ?thesis using outupd_behav_notatst_lemma3[where vl = "(get_outputs a)" and fl = "(get_outupd a)"
              and T = "get_sample_time a" and t = "0" and il = "get_inputs a" and h = "(
        exeDisDiag_attime (a # bl) h 0)"] 
              tmp1 tmp2 tmp7 pre by fastforce
      qed
      done
  then show ?case unfolding behavDisDiag_attime.simps using 8 9 10 by simp
qed

lemma existence_discrete_diag_attime: "besorted (rev bl) \<Longrightarrow> wf0 bl \<Longrightarrow> Graph (set bl) \<Longrightarrow> 
behavDisDiag_attime bl (Suc k) (exeDisDiag_attime bl h (Suc k))"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  note Cons1 = Cons
  have 1: "\<forall>x t. x \<notin> set(get_outputs a) \<or> (t > real (Suc k) \<or> t \<le> real k)\<longrightarrow> 
  exeDisDiag_attime bl h (Suc k) x t 
  = exeDisDiag_attime (a # bl) h (Suc k) x t"
  unfolding exeDisDiag_attime.simps using outupd_exe_atst_eq1 outupd_exe_atst_eq3
  outupd_exe_notatst_eq1 outupd_exe_notatst_eq3 by fastforce
  have 2: "besorted (rev bl)"
      proof -
        have tmp1: "remove1 a (rev (a#bl)) = rev bl"
          using Cons(3) unfolding wf0_def Unique_def 
          by (metis Suc_eq_plus1 append.right_neutral diff_Suc_1 in_set_conv_nth le_zero_eq 
              length_Cons less_diff_conv list.sel(3) nth_Cons_0 nth_tl remove1_append 
              remove_hd rev.simps(2) set_rev zero_less_Suc)
        show ?thesis using tmp1 besorted_remove2 Cons(2) by metis
      qed
      have 3: "wf0 bl"
        using Cons(3) wf0_lemma by simp
      have 4: "Graph (set bl)"
        using Cons(4) Graph_lemma by simp
      have 5: "\<forall>x\<in>Outputs bl. \<forall>t. exeDisDiag_attime bl h (Suc k) x t 
                = exeDisDiag_attime (a # bl) h (Suc k) x t"
        using 1 Cons(4) unfolding Graph_def by (meson wf0_def Cons1(3) Cons1(4) Graph_lemma2)
      have 6: "\<forall>i. 0 \<le> i \<and> i < length bl \<longrightarrow> (\<forall>x\<in>set (get_inputs (bl ! i)).
            \<forall>t\<le>real ((Suc k) - minimal (get_offsets (bl ! i))). 
            exeDisDiag_attime bl h (Suc k) x t 
            = exeDisDiag_attime (a # bl) h (Suc k) x t)"
      apply clarify subgoal premises pre for i x t 
      proof(cases "set (get_outputs a) \<inter> set (get_inputs (bl ! i)) = {}")
        case True
        have tmp1: "\<forall>x \<in> set (get_inputs (bl ! i)). (\<forall>t::real. 
              exeDisDiag_attime bl h (Suc k)  x t 
              = exeDisDiag_attime (a # bl) h (Suc k) x t)"
          using 1 True pre(1) by blast
        have tmp2: "\<forall>i. 0 \<le> i \<and> i < length bl \<longrightarrow>
        (\<forall>x\<in>set (get_inputs (bl ! i)). x \<in> Inputs bl)"
        proof(induction bl)
          case Nil
          then show ?case by simp
        next
          case (Cons b bl)
          then show ?case unfolding Inputs.simps
            by (metis Un_iff diff_Suc_1 length_Cons less_Suc_eq_0_disj nth_Cons' zero_le)
        qed
        then show ?thesis using pre tmp1 by presburger
      next
        case False
        have tmp1: "minimal (get_offsets (bl ! i)) \<ge> 0"
          using Cons1(3) unfolding wf0_def Available_def by force
        have tmp2: "get_outputs (bl ! i) \<noteq> []"
          using Cons(4) unfolding Graph_def by (simp add: pre(3))
        have tmp3: "get_offsets (bl ! i) \<noteq> []"
          using Cons(3) tmp2 unfolding wf0_def Available_def 
          by (metis length_0_conv list.set_intros(2) nth_mem pre(3))
        have tmp4: "check_offset (get_outputs a) (get_inputs (bl ! i)) (get_offsets (bl ! i)) = False"
          using Cons(2) besorted_last pre(3) by simp
        have tmp5: "\<forall>d \<in> set (get_offsets (bl ! i)). d \<noteq> 0"
          using check_offset.simps(3) tmp2 tmp3 tmp4 False
          by (metis boolean_algebra.conj_zero_left check_offset.elims(3) empty_set)
        have tmp6: "minimal (get_offsets (bl ! i)) \<ge> 1"
          using tmp1 tmp5
          using leD less_one linorder_le_less_linear list.set(2) 
            minimal.simps(2) minimal_lemma tmp3 by fastforce
        have tmp7: "Suc k - minimal (get_offsets (bl ! i)) \<le> k"
          using tmp6 by simp
        then show ?thesis using pre 1 by force
      qed
      done
    have 7: "behavDisDiag_attime bl (Suc k) (exeDisDiag_attime bl h (Suc k))"
      using Cons(1) 2 3 4 by simp
    have 8: "behavDisDiag_attime bl (Suc k) (exeDisDiag_attime (a # bl) h (Suc k))"
      using blocklist_hebav_attime_eq1 5 6 7 by simp
    have 9: "(\<exists>ka. 1 + int k = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
       (outupd_behav_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) (Suc k)
           (exeDisDiag_attime (a # bl) h (Suc k)))"
      proof -
        have tmp1: "length (get_outputs a) = length (get_offsets a) \<and> length (get_offsets a)
               = length (get_outupd a)  \<and> 0 < length (get_outputs a)"
          using Cons(3,4) unfolding Graph_def wf0_def Available_def by fastforce
        have tmp2: "Available (Block (get_inputs a) (get_outputs a) (get_offsets a) 
            (get_sample_time a) (get_outupd a))"
          using Cons(3) unfolding wf0_def by (simp add: Available_def)
        have tmp3: "\<forall>i. 0 \<le> i \<and> i < length (get_outputs a) \<longrightarrow>
        outupd_exe_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) 
          (exeDisDiag_attime bl h (Suc k)) (Suc k) ((get_outputs a) ! i) (real (Suc k)) =
        ((get_outupd a) ! i) (map (\<lambda>x. (exeDisDiag_attime bl h (Suc k)) 
        x (real (Suc k) - real ((get_offsets a) ! i))) (get_inputs a))"
          using tmp1 tmp2 outupd_exe_atst_lemma by blast
        have tmp4: "(\<exists>ka. int (Suc k) = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow> 
          (\<forall>i. 0 \<le> i \<and> i \<le> length (get_outputs a) \<longrightarrow>
        (exeDisDiag_attime (a # bl) h (Suc k)) ((get_outputs a) ! i) (real (Suc k)) = 
        outupd_exe_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) 
          (exeDisDiag_attime bl h (Suc k)) (Suc k) ((get_outputs a) ! i) (real (Suc k)))"
          by simp
        have tmp5: "(\<exists>ka. int (Suc k) = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
        (\<forall>i. 0 \<le> i \<and> i < length (get_outputs a)\<longrightarrow> (\<forall>x \<in> set (get_inputs a). 
        (exeDisDiag_attime bl h (Suc k)) x (real (Suc k) - real ((get_offsets a) ! i)) = 
        ( exeDisDiag_attime (a # bl) h (Suc k))
        x (real (Suc k) - real ((get_offsets a) ! i))))"
          apply clarify
          subgoal premises pre for ka i x
          proof(cases "get_offsets a ! i = 0")
            case True
            have tmp1: "set (get_inputs a) \<inter> set (get_outputs a) = {}"
              using Cons(3) unfolding wf0_def Available_def by auto
            then show ?thesis using True pre apply simp using outupd_exe_atst_eq1 
              by (metis disjoint_iff_not_equal)
          next
            case False
            have tmp1: "get_offsets a ! i \<ge> 1"
              using Cons(3) False unfolding wf0_def Available_def by force
            then show ?thesis using pre apply simp using exeDisDiag_attime_lemma2
              outupd_exe_atst_eq3 by force
          qed
          done
        have tmp6: "(\<exists>ka. int (Suc k) = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
        (\<forall>i. 0 \<le> i \<and> i < length (get_outputs a)\<longrightarrow>
    ((get_outupd a) ! i) (map (\<lambda>x. (exeDisDiag_attime (a # bl) h (Suc k))
         x (real (Suc k) - real ((get_offsets a) ! i))) (get_inputs a)) = ((get_outupd a) ! i)
          (map (\<lambda>x. (exeDisDiag_attime bl h (Suc k))
         x (real (Suc k) - real ((get_offsets a) ! i))) (get_inputs a)))"
          using tmp5 by (smt (z3) map_eq_conv)
        have tmp7: "(\<exists>ka. int (Suc k) = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
        (\<forall>i. 0 \<le> i \<and> i < length (get_outputs a) \<longrightarrow>
        (exeDisDiag_attime (a # bl) h (Suc k))
         ((get_outputs a) ! i) (real (Suc k)) 
        = ((get_outupd a) ! i) (map (\<lambda>x. (exeDisDiag_attime (a # bl) h (Suc k))
         x (real (Suc k) - real ((get_offsets a) ! i))) (get_inputs a)))"
          using tmp3 tmp4 tmp6 le_eq_less_or_eq by presburger
        show ?thesis
          using outupd_behav_atst_lemma3 tmp1 tmp7 by simp
      qed
      have 10: "\<not>(\<exists>ka. int (Suc k) = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
outupd_behav_notatst (get_inputs a) (get_outputs a) (get_outupd a) (get_sample_time a) (Suc k)
           (exeDisDiag_attime (a # bl) h (Suc k))"
        apply clarify subgoal premises pre
      proof -
        have tmp1: "length (get_outputs a) = length (get_outupd a) \<and> 0 < length (get_outputs a)"
          using Cons(3,4) unfolding Graph_def wf0_def Available_def by fastforce
        have tmp2: "(get_sample_time a) > 0"
          using Cons(3) pre unfolding wf0_def Available_def by force
        have tmp3: "distinct (get_outputs a)"
          using Cons(3) unfolding wf0_def Available_def
          by (metis distinct_conv_nth less_eq_nat.simps(1) linorder_neqE_nat list.set_intros(1))
        have tmp4: "\<forall>i. 0 \<le> i \<and> i < length (get_outputs a) \<longrightarrow>
        outupd_exe_notatst (get_inputs a) (get_outputs a) (get_outupd a) (get_sample_time a) 
        (exeDisDiag_attime bl h (Suc k)) (Suc k) ((get_outputs a) ! i) (real (Suc k)) = 
        (exeDisDiag_attime bl h (Suc k)) ((get_outputs a) ! i) 
        (real_of_int (int (Suc k) div (get_sample_time a) * (get_sample_time a)))"
          using tmp1 tmp3 outupd_exe_notatst_lemma by blast
        have tmp5: "\<not>(\<exists>ka. int (Suc k) = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow> 
          (\<forall>i. 0 \<le> i \<and> i \<le> length (get_outputs a) \<longrightarrow>
        (exeDisDiag_attime (a # bl) h (Suc k)) ((get_outputs a) ! i) (real (Suc k)) = 
        outupd_exe_notatst (get_inputs a) (get_outputs a) (get_outupd a) (get_sample_time a)
          (exeDisDiag_attime bl h (Suc k)) (Suc k) ((get_outputs a) ! i) (real (Suc k)))"
          by simp
        have tmp6: "\<not>(\<exists>ka. int (Suc k) = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
        (\<forall>i. 0 \<le> i \<and> i \<le> length (get_outputs a)\<longrightarrow>  
        (exeDisDiag_attime bl h (Suc k)) ((get_outputs a) ! i) 
        (real_of_int (int (Suc k) div (get_sample_time a) * (get_sample_time a))) = 
        (exeDisDiag_attime (a # bl) h (Suc k))
        ((get_outputs a) ! i) (real_of_int (int (Suc k) div (get_sample_time a) * (get_sample_time a))))"
          apply clarify
          subgoal premises pre for i
          proof -
            show ?thesis using pre by (smt (verit, del_insts) exeDisDiag_attime_lemma2 
                  mult.commute of_int_eq_iff of_int_of_nat_eq)
          qed
          done
        have tmp7: "\<not>(\<exists>ka. int (Suc k) = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
        (\<forall>i. 0 \<le> i \<and> i < length (get_outputs a) \<longrightarrow>
        (exeDisDiag_attime (a # bl) h (Suc k))
        ((get_outputs a) ! i) (real (Suc k)) = 
        (exeDisDiag_attime (a # bl) h (Suc k))
        ((get_outputs a) ! i) (real_of_int (int (Suc k) div (get_sample_time a) * (get_sample_time a))))"
          using tmp4 tmp5 tmp6 using less_imp_le_nat by presburger
        show ?thesis using outupd_behav_notatst_lemma3[where vl = "(get_outputs a)" and fl = "(get_outupd a)"
              and T = "get_sample_time a" and t = "Suc k" and il = "get_inputs a" and h = "(
        exeDisDiag_attime (a # bl) h (Suc k))"] 
              tmp1 tmp2 tmp7 pre by fastforce
      qed
      done
  then show ?case unfolding behavDisDiag_attime.simps using 8 9 10 by simp
qed

lemma behavDisDiag_attime_subset: "behavDisDiag_attime bl (Suc k) h \<Longrightarrow>
Unique cl \<Longrightarrow> set cl \<subseteq> set bl \<Longrightarrow>
behavDisDiag_attime cl (Suc k) h"
proof(induction bl arbitrary: cl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case
  proof(cases "a \<in> set cl")
    case True
    have 1: "behavDisDiag_attime (remove1 a cl) (Suc k) h"
    proof -
      have tmp1: "behavDisDiag_attime bl (Suc k) h"
        using Cons(2) by auto
      have tmp2: "Unique (remove1 a cl)"
        using True Cons(3) Unique_remove by fastforce
      have tmp3: "set (remove1 a cl) \<subseteq> set bl"
        using Cons(3,4) unfolding Unique_def by (smt (verit, del_insts) Cons.prems(2) Unique_k 
            bot_nat_0.extremum in_set_conv_nth set_ConsD set_remove1_subset subset_code(1))
      show ?thesis using Cons(1)[of "remove1 a cl"] tmp1 tmp2 tmp3 by simp
    qed
    then show ?thesis using Cons(2,3)
    proof(induction cl)
      case Nil
      then show ?case by simp
    next
      case (Cons c cl)
      then show ?case
      proof(cases "a = c")
        case True
        then show ?thesis using Cons by simp
      next
        case False
        have 2: "behavDisDiag_attime cl (Suc k) h"
          using Cons False by (metis Unique_lemma behavDisDiag_attime.simps(2) 
              remove1.simps(2))
        have 3: "(if \<exists>ka. int (Suc k) = get_sample_time c * ka \<or> get_sample_time c = 0
     then outupd_behav_atst (get_inputs c) (get_outputs c) (get_offsets c) (get_outupd c) (Suc k) h
     else outupd_behav_notatst (get_inputs c) (get_outputs c) (get_outupd c) (get_sample_time c)
           (Suc k) h)"
          using Cons(2) False by simp
        then show ?thesis unfolding behavDisDiag_attime.simps using Cons False 2
          by blast
      qed
    qed
  next
    case False
    then show ?thesis using Cons by auto
  qed
qed

lemma behavDisDiag_tilltime_Suc: "besorted (rev bl) \<Longrightarrow> wf0 bl \<Longrightarrow> Graph (set bl) \<Longrightarrow>
behavDisDiag_tilltime bl k h \<Longrightarrow>
behavDisDiag_tilltime bl (Suc k) (\<lambda>v t.(if (t = Suc k) then 
((exeDisDiag_attime bl h (Suc k)) v t)
else (if t \<le> k then (h v t) 
else (if t < Suc k \<and> v \<in> (Outputs bl) then (h v k) 
else h v t))))"
  unfolding behavDisDiag_tilltime.simps apply simp
  subgoal premises pre
  proof -
    have 1: "behavDisDiag_tilltime bl k
     (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime bl h (Suc k) v t
            else if t \<le> real k then h v t
                 else if t < real (Suc k) \<and> v \<in> Outputs bl then h v (real k) else h v t)"
      using behavDisDiag_tilltime_lemma pre by (smt (verit))
    have 2: "besorted (rev bl) \<Longrightarrow> wf0 bl \<Longrightarrow> Graph (set bl) \<Longrightarrow> behavDisDiag_attime bl (Suc k)
     (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime bl h (Suc k) v t
            else if t \<le> real k then h v t
                 else if t < real (Suc k) \<and> v \<in> Outputs bl then h v (real k) else h v t)"
      
    proof(induction bl)
      case Nil
      then show ?case by simp
    next
      case (Cons a bl)
      note Cons1 = Cons
      have 1: "\<forall>x t. x \<notin> set(get_outputs a) \<or> (t > real (Suc k) \<or> t \<le> real k)\<longrightarrow> 
              (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime bl h (Suc k)
                 v t else if t \<le> real k then h v t
                 else if t < real (Suc k) \<and> v \<in> Outputs bl then h v (real k) else h v t) x t 
              = (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime (a # bl) h (Suc k) v t
            else if t \<le> real k then h v t
                 else if t < real (Suc k) \<and> v \<in> Outputs (a # bl) then h v (real k) else h v t) x t"
        unfolding exeDisDiag_attime.simps using outupd_exe_atst_eq1 outupd_exe_atst_eq3
        outupd_exe_notatst_eq1 outupd_exe_notatst_eq3 by fastforce
      have 2: "besorted (rev bl)"
      proof -
        have tmp1: "remove1 a (rev (a#bl)) = rev bl"
          using Cons(3) unfolding wf0_def Unique_def 
          by (metis Suc_eq_plus1 append.right_neutral diff_Suc_1 in_set_conv_nth le_zero_eq 
              length_Cons less_diff_conv list.sel(3) nth_Cons_0 nth_tl remove1_append 
              remove_hd rev.simps(2) set_rev zero_less_Suc)
        show ?thesis using tmp1 besorted_remove2 Cons(2) by metis
      qed
      have 3: "wf0 bl"
        using Cons(3) wf0_lemma by simp
      have 4: "Graph (set bl)"
        using Cons(4) Graph_lemma by simp
      have 5: "\<forall>x\<in>Outputs bl. \<forall>t. (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime bl h (Suc k)
                 v t else if t \<le> real k then h v t
                 else if t < real (Suc k) \<and> v \<in> Outputs bl then h v (real k) else h v t) x t 
                = (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime (a # bl) h (Suc k) v t
            else if t \<le> real k then h v t
                 else if t < real (Suc k) \<and> v \<in> Outputs (a # bl) then h v (real k) else h v t) x t"
        using 1 Cons(4) unfolding Graph_def by (smt (verit, best) wf0_def Cons1(3) Cons1(4) Graph_lemma2)
      have 6: "\<forall>i. 0 \<le> i \<and> i < length bl \<longrightarrow> (\<forall>x\<in>set (get_inputs (bl ! i)).
            \<forall>t\<le>real ((Suc k) - minimal (get_offsets (bl ! i))). 
            (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime bl h (Suc k)
                 v t else if t \<le> real k then h v t
                 else if t < real (Suc k) \<and> v \<in> Outputs bl then h v (real k) else h v t) x t 
            = (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime (a # bl) h (Suc k) v t
            else if t \<le> real k then h v t
                 else if t < real (Suc k) \<and> v \<in> Outputs (a # bl) then h v (real k) else h v t) x t)"
      apply clarify subgoal premises pre for i x t 
      proof(cases "set (get_outputs a) \<inter> set (get_inputs (bl ! i)) = {}")
        case True
        have tmp1: "\<forall>x \<in> set (get_inputs (bl ! i)). (\<forall>t::real. (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime bl h (Suc k)
                 v t else if t \<le> real k then h v t
                 else if t < real (Suc k) \<and> v \<in> Outputs bl then h v (real k) else h v t) x t 
              = (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime (a # bl) h (Suc k) v t
            else if t \<le> real k then h v t
                 else if t < real (Suc k) \<and> v \<in> Outputs (a # bl) then h v (real k) else h v t) x t)"
          using 1 True pre(1) by blast
        have tmp2: "\<forall>i. 0 \<le> i \<and> i < length bl \<longrightarrow>
        (\<forall>x\<in>set (get_inputs (bl ! i)). x \<in> Inputs bl)"
        proof(induction bl)
          case Nil
          then show ?case by simp
        next
          case (Cons b bl)
          then show ?case unfolding Inputs.simps
            by (metis Un_iff diff_Suc_1 length_Cons less_Suc_eq_0_disj nth_Cons' zero_le)
        qed
        then show ?thesis using pre tmp1 by presburger
      next
        case False
        have tmp1: "minimal (get_offsets (bl ! i)) \<ge> 0"
          using Cons1(3) unfolding wf0_def Available_def by force
        have tmp2: "get_outputs (bl ! i) \<noteq> []"
          using Cons(4) unfolding Graph_def 
          by (metis length_greater_0_conv list.set_intros(2) nth_mem pre(3))
        have tmp3: "get_offsets (bl ! i) \<noteq> []"
          using Cons(3) tmp2 unfolding wf0_def Available_def 
          by (metis length_0_conv list.set_intros(2) nth_mem pre(3))
        have tmp4: "check_offset (get_outputs a) (get_inputs (bl ! i)) (get_offsets (bl ! i)) = False"
          using Cons(2) besorted_last pre(3) by simp
        have tmp5: "\<forall>d \<in> set (get_offsets (bl ! i)). d \<noteq> 0"
          using check_offset.simps(3) tmp2 tmp3 tmp4 False
          by (metis boolean_algebra.conj_zero_left check_offset.elims(3) empty_set)
        have tmp6: "minimal (get_offsets (bl ! i)) \<ge> 1"
          using tmp1 tmp5
          using leD less_one linorder_le_less_linear list.set(2) 
            minimal.simps(2) minimal_lemma tmp3 by fastforce
        have tmp7: "Suc k - minimal (get_offsets (bl ! i)) \<le> k"
          using tmp6 by simp
        then show ?thesis using pre 1 by force
      qed
      done
    have 7: "behavDisDiag_attime bl (Suc k)
     (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime bl h (Suc k) v t
            else if t \<le> real k then h v t
                 else if t < real (Suc k) \<and> v \<in> Outputs bl then h v (real k) else h v t)"
      using Cons(1) 2 3 4 by simp
    have 8: "behavDisDiag_attime bl (Suc k)
     (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime (a # bl) h (Suc k) v t
            else if t \<le> real k then h v t
                 else if t < real (Suc k) \<and> v \<in> Outputs (a # bl) then h v (real k) else h v t)"
        using blocklist_hebav_attime_eq1 5 6 7 by simp
      have 9: "(\<exists>ka. 1 + int k = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
       (outupd_behav_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) (Suc k)
           (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime (a # bl) h (Suc k) v t
                  else if t \<le> real k then h v t
                       else if t < real (Suc k) \<and> v \<in> Outputs (a # bl) then h v (real k) else h v t))"
      proof -
        have tmp1: "length (get_outputs a) = length (get_offsets a) \<and> length (get_offsets a)
               = length (get_outupd a)  \<and> 0 < length (get_outputs a)"
          using Cons(3,4) unfolding Graph_def wf0_def Available_def by fastforce
        have tmp2: "Available (Block (get_inputs a) (get_outputs a) (get_offsets a) 
            (get_sample_time a) (get_outupd a))"
          using Cons(3) unfolding wf0_def by (simp add: Available_def)
        have tmp3: "\<forall>i. 0 \<le> i \<and> i < length (get_outputs a) \<longrightarrow>
        outupd_exe_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) 
          (exeDisDiag_attime bl h (Suc k)) (Suc k) ((get_outputs a) ! i) (real (Suc k)) =
        ((get_outupd a) ! i) (map (\<lambda>x. (exeDisDiag_attime bl h (Suc k)) 
        x (real (Suc k) - real ((get_offsets a) ! i))) (get_inputs a))"
          using tmp1 tmp2 outupd_exe_atst_lemma by blast
        have tmp4: "(\<exists>ka. int (Suc k) = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow> 
          (\<forall>i. 0 \<le> i \<and> i \<le> length (get_outputs a) \<longrightarrow>
        (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime (a # bl) h (Suc k) v t
          else if t \<le> real k then h v t else if t < real (Suc k) \<and> v \<in> Outputs (a # bl) then 
        h v (real k) else h v t) ((get_outputs a) ! i) (real (Suc k)) = 
        outupd_exe_atst (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) 
          (exeDisDiag_attime bl h (Suc k)) (Suc k) ((get_outputs a) ! i) (real (Suc k)))"
          by simp
        have tmp5: "(\<exists>ka. int (Suc k) = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
        (\<forall>i. 0 \<le> i \<and> i < length (get_outputs a)\<longrightarrow> (\<forall>x \<in> set (get_inputs a). 
        (exeDisDiag_attime bl h (Suc k)) x (real (Suc k) - real ((get_offsets a) ! i)) = 
        (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime (a # bl) h (Suc k) v t else if t \<le> real k 
        then h v t else if t < real (Suc k) \<and> v \<in> Outputs (a # bl) then h v (real k) else h v t)
        x (real (Suc k) - real ((get_offsets a) ! i))))"
          apply clarify
          subgoal premises pre for ka i x
          proof(cases "get_offsets a ! i = 0")
            case True
            have tmp1: "set (get_inputs a) \<inter> set (get_outputs a) = {}"
              using Cons(3) unfolding wf0_def Available_def by auto
            then show ?thesis using True pre apply simp using outupd_exe_atst_eq1 
              by (metis disjoint_iff_not_equal)
          next
            case False
            have tmp1: "get_offsets a ! i \<ge> 1"
              using Cons(3) False unfolding wf0_def Available_def by force
            then show ?thesis using pre apply simp using exeDisDiag_attime_lemma2 by simp
          qed
          done
        have tmp6: "(\<exists>ka. int (Suc k) = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
        (\<forall>i. 0 \<le> i \<and> i < length (get_outputs a)\<longrightarrow>
    ((get_outupd a) ! i) (map (\<lambda>x. (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime (a # bl) h (Suc k) v t
           else if t \<le> real k then h v t
           else if t < real (Suc k) \<and> v \<in> Outputs (a # bl) then h v (real k) else h v t)
         x (real (Suc k) - real ((get_offsets a) ! i))) (get_inputs a)) = ((get_outupd a) ! i)
          (map (\<lambda>x. (exeDisDiag_attime bl h (Suc k))
         x (real (Suc k) - real ((get_offsets a) ! i))) (get_inputs a)))"
          using tmp5 by (smt (z3) map_eq_conv)
        have tmp7: "(\<exists>ka. int (Suc k) = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
        (\<forall>i. 0 \<le> i \<and> i < length (get_outputs a) \<longrightarrow>
        (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime (a # bl) h (Suc k) v t
                  else if t \<le> real k then h v t
                       else if t < real (Suc k) \<and> v \<in> Outputs (a # bl) then h v (real k) else h v t)
         ((get_outputs a) ! i) (real (Suc k)) 
        = ((get_outupd a) ! i) (map (\<lambda>x. (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime (a # bl) h (Suc k) v t
           else if t \<le> real k then h v t
           else if t < real (Suc k) \<and> v \<in> Outputs (a # bl) then h v (real k) else h v t)
         x (real (Suc k) - real ((get_offsets a) ! i))) (get_inputs a)))"
          using tmp3 tmp4 tmp6 le_eq_less_or_eq by presburger
        show ?thesis
          using outupd_behav_atst_lemma3 tmp1 tmp7 by simp
      qed
      have 10: "\<not>(\<exists>ka. int (Suc k) = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
outupd_behav_notatst (get_inputs a) (get_outputs a) (get_outupd a) (get_sample_time a) (Suc k)
           (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime (a # bl) h (Suc k) v t
                  else if t \<le> real k then h v t
                       else if t < real (Suc k) \<and> v \<in> Outputs (a # bl) then h v (real k) else h v t)"
        apply clarify subgoal premises pre
      proof -
        have tmp1: "length (get_outputs a) = length (get_outupd a) \<and> 0 < length (get_outputs a)"
          using Cons(3,4) unfolding Graph_def wf0_def Available_def  by fastforce
        have tmp2: "(get_sample_time a) > 0"
          using Cons(3) pre unfolding wf0_def Available_def by force
        have tmp3: "distinct (get_outputs a)"
          using Cons(3) unfolding wf0_def Available_def
          by (metis distinct_conv_nth less_eq_nat.simps(1) linorder_neqE_nat list.set_intros(1))
        have tmp4: "\<forall>i. 0 \<le> i \<and> i < length (get_outputs a) \<longrightarrow>
        outupd_exe_notatst (get_inputs a) (get_outputs a) (get_outupd a) (get_sample_time a) 
        (exeDisDiag_attime bl h (Suc k)) (Suc k) ((get_outputs a) ! i) (real (Suc k)) = 
        (exeDisDiag_attime bl h (Suc k)) ((get_outputs a) ! i) 
        (real_of_int (int (Suc k) div (get_sample_time a) * (get_sample_time a)))"
          using tmp1 tmp3 outupd_exe_notatst_lemma by blast
        have tmp5: "\<not>(\<exists>ka. int (Suc k) = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow> 
          (\<forall>i. 0 \<le> i \<and> i \<le> length (get_outputs a) \<longrightarrow>
        (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime (a # bl) h (Suc k) v t
          else if t \<le> real k then h v t else if t < real (Suc k) \<and> v \<in> Outputs (a # bl) then 
        h v (real k) else h v t) ((get_outputs a) ! i) (real (Suc k)) = 
        outupd_exe_notatst (get_inputs a) (get_outputs a) (get_outupd a) (get_sample_time a)
          (exeDisDiag_attime bl h (Suc k)) (Suc k) ((get_outputs a) ! i) (real (Suc k)))"
          by simp
        have tmp6: "\<not>(\<exists>ka. int (Suc k) = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
        (\<forall>i. 0 \<le> i \<and> i \<le> length (get_outputs a)\<longrightarrow>  
        (exeDisDiag_attime bl h (Suc k)) ((get_outputs a) ! i) 
        (real_of_int (int (Suc k) div (get_sample_time a) * (get_sample_time a))) = 
        (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime (a # bl) h (Suc k) v t else if t \<le> real k 
        then h v t else if t < real (Suc k) \<and> v \<in> Outputs (a # bl) then h v (real k) else h v t)
        ((get_outputs a) ! i) (real_of_int (int (Suc k) div (get_sample_time a) * (get_sample_time a))))"
          apply clarify
          subgoal premises pre for i
          proof -
            show ?thesis using pre
              by (smt (verit, ccfv_threshold) exeDisDiag_attime_lemma2 mult.commute 
                  of_nat_Suc of_nat_less_of_int_iff)
          qed
          done
        have tmp7: "\<not>(\<exists>ka. int (Suc k) = get_sample_time a * ka \<or> get_sample_time a = 0) \<longrightarrow>
        (\<forall>i. 0 \<le> i \<and> i < length (get_outputs a) \<longrightarrow>
        (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime (a # bl) h (Suc k) v t else if t \<le> real k 
        then h v t else if t < real (Suc k) \<and> v \<in> Outputs (a # bl) then h v (real k) else h v t)
        ((get_outputs a) ! i) (real (Suc k)) = 
        (\<lambda>v t. if t = 1 + real k then exeDisDiag_attime (a # bl) h (Suc k) v t else if t \<le> real k 
        then h v t else if t < real (Suc k) \<and> v \<in> Outputs (a # bl) then h v (real k) else h v t)
        ((get_outputs a) ! i) (real_of_int (int (Suc k) div (get_sample_time a) * (get_sample_time a))))"
          using tmp4 tmp5 tmp6 using less_imp_le_nat by presburger
        show ?thesis using outupd_behav_notatst_lemma3[where vl = "(get_outputs a)" and fl = "(get_outupd a)"
              and T = "get_sample_time a" and t = "Suc k" and il = "get_inputs a" and h = "(\<lambda>v t. if t = 1 + real k 
        then exeDisDiag_attime (a # bl) h (Suc k) v t else if t \<le> real k 
        then h v t else if t < real (Suc k) \<and> v \<in> Outputs (a # bl) then h v (real k) else h v t)"] 
              tmp1 tmp2 tmp7 pre by fastforce
      qed
      done
      show ?case unfolding behavDisDiag_attime.simps using 8 9 10 
        Available_def wf0_def Cons1(3) plus_1_eq_Suc by fastforce
    qed
  show ?thesis using 1 2 pre by simp
  qed
  done

lemma existence_of_exe: 
shows "besorted (rev bl)  \<Longrightarrow> wf1 bl  \<Longrightarrow>
       behavDisDiag_tilltime bl k (exe_discrete_diag_tilltime bl h k)"
proof(induction k)                                
  case 0
  then show ?case using existence_discrete_diag_at0 by simp
next
  case (Suc k)
  have 1: "(\<lambda>v t::real.(if (t = Suc k) then 
  ((exeDisDiag_attime bl (exe_discrete_diag_tilltime bl h k) (Suc k)) v t)
  else (if t \<le> k then ((exe_discrete_diag_tilltime bl h k) v t) 
  else (if t < Suc k \<and> v \<in> (Outputs bl) then ((exe_discrete_diag_tilltime bl h k) v k) 
  else (exe_discrete_diag_tilltime bl h k) v t)))) = (\<lambda>v t::real.(if (t = Suc k) then 
  ((exeDisDiag_attime bl (exe_discrete_diag_tilltime bl h k) (Suc k)) v t)
  else (if t \<le> k then ((exe_discrete_diag_tilltime bl h k) v t) 
  else (if t < Suc k \<and> v \<in> (Outputs bl) then ((exe_discrete_diag_tilltime bl h k) v k) 
  else h v t))))"
  proof -
    have 1: "\<forall>v t. t > Suc k \<or> (t < Suc k \<and> v \<notin> (Outputs bl)) \<longrightarrow> 
  (exe_discrete_diag_tilltime bl h k) v t = h v t"
      using exe_discrete_diag_tilltime_lemma1 exe_discrete_diag_tilltime_lemma2 by simp
    show ?thesis using 1 using exe_discrete_diag_tilltime_lemma2 by fastforce
  qed
  have 2: "behavDisDiag_tilltime bl k (exe_discrete_diag_tilltime bl h k)"
    using Suc by simp
  show ?case unfolding exe_discrete_diag_tilltime.simps using 2 1 Suc unfolding wf1_def using 
        behavDisDiag_tilltime_Suc[where bl = bl and k = k and h = 
          "(exe_discrete_diag_tilltime bl h k)"] by presburger
qed

lemma existence_of_discrete_diag : 
shows "loop_free bl \<Longrightarrow> sortDiag bl = bl' \<Longrightarrow>
       wf1 bl \<Longrightarrow> behavDisDiag_tilltime bl k (exe_discrete_diag_tilltime (rev bl') h k)"
  subgoal premises pre
  proof -
    have 1: "besorted bl'"
      using pre(3) sort_is_sorted wf0_def pre(2) unfolding wf1_def by blast
    have 2: "bl <~~> bl'"
      using pre(1,2) unfolding sortDiag_def loop_free_def using toposort_perm
      by (metis append.right_neutral)
    have 3: "Graph (set (rev bl')) = True"
      using pre(3) unfolding wf1_def using 2 Graph_Permutation by simp
    have 4: "wf0 (rev bl')"
      using 2 pre(3) wf0_Permutation unfolding wf1_def by (metis perm_rev rev_rev_ident)
    have 5: "behavDisDiag_tilltime (rev bl') k (exe_discrete_diag_tilltime (rev bl') h k)"
      using existence_of_exe 1 3 4 unfolding wf1_def by simp
  show ?thesis using 5 blocklist_hebav_tilltime_perm
    by (meson "2" perm_rev perm_sym)
qed
  done

lemma behavDisDiag_tilltime_unique: "behavDisDiag_tilltime bl n h1 = True \<Longrightarrow> 
bl <~~> bl' \<Longrightarrow> bl \<noteq> [] \<Longrightarrow> wf0 bl \<Longrightarrow> besorted bl  \<Longrightarrow> besorted bl' \<Longrightarrow>
behavDisDiag_tilltime bl' n h2 = True \<Longrightarrow> (\<forall> v \<in> Outputs bl. \<forall>t < 0. h1 v t = h2 v t) \<Longrightarrow> 
\<forall>v \<in> Inputs bl - Outputs bl. \<forall>t::real. h1 v t = h2 v t \<Longrightarrow>
\<forall> t::real. (t \<le> n \<and> t \<ge> 0) \<longrightarrow> (\<forall> v \<in> Outputs bl. h1 v t = h2 v t)"
proof(induction n)
  case 0
  then show ?case unfolding behavDisDiag_tilltime.simps using blocklist_hebav_attime_lemma3 by force
next
  case (Suc n)
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
  show ?case using Suc apply clarify
    subgoal premises pre for t v
  proof(cases "t \<le> real n")
    case True
    have tmp1: "(behavDisDiag_tilltime bl n h1 = True \<and> 
                behavDisDiag_tilltime bl' n h2) = True"
      using pre unfolding behavDisDiag_tilltime.simps by meson
    then show ?thesis using pre True unfolding behavDisDiag_tilltime.simps by blast
  next
    case False
    note False1 = False
    then show ?thesis
    proof(cases "t > real n \<and> t < real (Suc n)")
      case True
      have tmp1: "\<forall>t. t \<le> real n \<and> 0 \<le> t \<longrightarrow> (\<forall>v\<in>Outputs bl. h1 v t = h2 v t)"
        using pre unfolding behavDisDiag_tilltime.simps by blast
      then show ?thesis using 1 pre True unfolding behavDisDiag_tilltime.simps
        by (smt (verit, del_insts) Un_iff tmp1)
    next
      case False
      have tmp1: "t = Suc n"
        using False False1 pre(12) by simp
      have tmp2: "\<forall>t. t \<le> real n \<longrightarrow> (\<forall>v\<in>Outputs bl. h1 v t = h2 v t)"
        using pre unfolding behavDisDiag_tilltime.simps by (smt (verit))
      have tmp3: "\<forall>t<real (Suc n). \<forall>v\<in>Outputs bl. h1 v t = h2 v t"
      proof -
        have tmp4: "\<forall>t. real n < t \<and> t < real (Suc n) \<longrightarrow> (\<forall>v\<in>Outputs bl. h1 v t = h1 v (real n))"
          using pre unfolding behavDisDiag_tilltime.simps by simp
        have tmp5: "\<forall>t. real n < t \<and> t < real (Suc n) \<longrightarrow> (\<forall>v\<in>Outputs bl. h2 v t = h2 v (real n))"
          using 1 pre unfolding behavDisDiag_tilltime.simps by simp
        show ?thesis using tmp4 tmp5 tmp2 by (metis linorder_not_le order_refl)
      qed
      have tmp4: "distinct bl"
        using pre(5) unfolding wf0_def using Unique'_def Unique'_eq by blast
      have tmp5: "\<forall>v \<in> Outputs bl. h1 v 0 = h2 v 0"
        using tmp2 by simp
      then show ?thesis using pre unfolding behavDisDiag_tilltime.simps 
        using blocklist_hebav_attime_lemma2[where bl = bl and n = "(Suc n)" and ?h1.0 = h1 
            and ?h2.0 = h2 and bl' = bl'] tmp1 tmp3
        by (smt (verit, ccfv_threshold) diff_Suc_1)
    qed
  qed
  done
qed

 
lemma uniqueness_of_exe : "wf1 bl \<Longrightarrow>  bl <~~> bl' \<Longrightarrow> 
besorted bl \<Longrightarrow> besorted bl' \<Longrightarrow> \<forall>v \<in> Outputs bl. \<forall>t \<le> k.
exe_discrete_diag_tilltime (rev bl) h k v t = exe_discrete_diag_tilltime (rev bl') h k v t"
  subgoal premises pre
  proof(cases "bl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have 1: "behavDisDiag_tilltime (rev bl) k (exe_discrete_diag_tilltime (rev bl) h k)"
      using pre by (metis wf1_def wf0_def Unique_rev existence_of_exe rev_rev_ident set_rev)
  have 2: "behavDisDiag_tilltime bl k (exe_discrete_diag_tilltime (rev bl) h k)"
    using 1 blocklist_hebav_tilltime_rev by force
  have 3: "behavDisDiag_tilltime (rev bl') k (exe_discrete_diag_tilltime (rev bl') h k)"
    using pre(1,2) unfolding wf1_def using wf0_Permutation Graph_Permutation 
    by (metis existence_of_exe perm_rev pre(4) rev_rev_ident wf1_def)
  have 4: "behavDisDiag_tilltime bl' k (exe_discrete_diag_tilltime (rev bl') h k)"
    using 3 blocklist_hebav_tilltime_rev by force
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
  have 6: "(\<forall> v \<in> Outputs bl. \<forall>t <0. 
    (exe_discrete_diag_tilltime (rev bl) h k) v t = (exe_discrete_diag_tilltime (rev bl') h k) v t)"
    apply clarify
    subgoal premises pre1 for v t
  proof -
    have tmp1: "(exe_discrete_diag_tilltime (rev bl) h k) v t = h v t"
      using exe_discrete_diag_tilltime_lemma2[where bl = "rev bl" and h = h and ?t1.0 = k and x = v] pre1 
      by blast
    have tmp2: "(exe_discrete_diag_tilltime (rev bl') h k) v t = h v t"
      using exe_discrete_diag_tilltime_lemma2[where bl = "rev bl'" and h = h and ?t1.0 = k and x = v] pre1 
      by blast 
    show ?thesis using tmp1 tmp2 by simp
  qed
  done
  have 7: "\<forall>v \<in> Inputs bl - Outputs bl. 
    \<forall>t::real. (exe_discrete_diag_tilltime (rev bl) h k) v t = (exe_discrete_diag_tilltime (rev bl') h k) v t"
    apply clarify
    subgoal premises pre1 for v t
    proof -
      have tmp1: "v \<notin> Outputs (rev bl)"
        using pre1(2) Outputs_rev by simp
      have tmp2: "v \<notin> Outputs (rev bl')"
        using pre1(2) pre(2) 5 Outputs_rev by simp
      show ?thesis using tmp1 tmp2 exe_discrete_diag_tilltime_lemma1 by simp
    qed
    done
  have 8: "distinct bl"
    using pre(1) unfolding wf1_def wf0_def using Unique'_eq unfolding Unique'_def by auto
  show ?thesis using 2 4 6 7 8 behavDisDiag_tilltime_unique pre False unfolding wf1_def
    by (smt (verit) of_nat_mono)
  qed
  done
  
lemma uniqueness_of_discrete_diag' : 
"wf1 bl \<Longrightarrow>  bl <~~> bl' \<Longrightarrow> 
besorted bl \<Longrightarrow> besorted bl' \<Longrightarrow> \<forall>v \<in> Outputs bl. \<forall>t \<le> k.
exe_discrete_diag_tilltime (rev bl) h k v t = exe_discrete_diag_tilltime (rev bl') h k v t"
  using uniqueness_of_exe unfolding wf1_def wf0_def by simp

lemma uniqueness_of_discrete_diag : 
"wf1 bl \<Longrightarrow>  bl <~~> bl' \<Longrightarrow> 
besorted bl \<Longrightarrow> besorted bl' \<Longrightarrow> \<forall>v t::nat.
exe_discrete_diag_tilltime (rev bl) h k v t = exe_discrete_diag_tilltime (rev bl') h k v t"
  subgoal premises pre
proof -
  have 1: "Outputs bl = Outputs bl'"
    using pre(2) Outputs_perm by auto
  have 2: "\<forall>v t. v \<notin> Outputs bl \<longrightarrow>
exe_discrete_diag_tilltime (rev bl) h k v t = exe_discrete_diag_tilltime (rev bl') h k v t"
  proof -
    have tmp1: "\<forall>v t. v \<notin> Outputs bl \<longrightarrow>
exe_discrete_diag_tilltime (rev bl) h k v t = h v t"
      using exe_discrete_diag_tilltime_lemma1 Outputs_rev by simp
    have tmp2: "\<forall>v t. v \<notin> Outputs bl \<longrightarrow>
exe_discrete_diag_tilltime (rev bl') h k v t = h v t"
      using exe_discrete_diag_tilltime_lemma1 Outputs_rev 1 by simp
    show ?thesis using tmp1 tmp2 by simp
  qed
  have 3: "\<forall>v t. t > k \<longrightarrow>
exe_discrete_diag_tilltime (rev bl) h k v t = exe_discrete_diag_tilltime (rev bl') h k v t"
  proof -
    have tmp1: "\<forall>v t. t > k \<longrightarrow>
exe_discrete_diag_tilltime (rev bl) h k v t = h v t"
      using exe_discrete_diag_tilltime_lemma2 by simp
    have tmp2: "\<forall>v t. t > k \<longrightarrow>
exe_discrete_diag_tilltime (rev bl') h k v t = h v t"
      using exe_discrete_diag_tilltime_lemma2 1 by simp
    show ?thesis using tmp1 tmp2 by simp
  qed
  have 4: "\<forall>v \<in> Outputs bl. \<forall>t \<le> k.
exe_discrete_diag_tilltime (rev bl) h k v t = exe_discrete_diag_tilltime (rev bl') h k v t"
    using uniqueness_of_discrete_diag' pre by presburger
  show ?thesis apply clarify subgoal for v t
    proof(cases "v \<notin> Outputs bl")
      case True
      then show ?thesis using 2 by simp
    next
      case False
      note F1 = False
      then show ?thesis
      proof(cases "t > k")
        case True
        then show ?thesis using 3 using exe_discrete_diag_tilltime_lemma2 by presburger
      next
        case False
        then show ?thesis using F1 4 by simp
      qed
    qed
    done
  qed
done
 
end
