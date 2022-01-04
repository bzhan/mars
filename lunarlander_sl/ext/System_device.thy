theory System_device
  imports System_coon
begin

definition device_camera :: "scheduler proc" where
  "device_camera = 
Rep (Cm (''outputs_camera_image''[!](\<lambda>_. -1)); Wait (\<lambda>_ . 0.2))"

fun device_camera_block :: "nat \<Rightarrow> scheduler tassn" where
  "device_camera_block 0 = emp\<^sub>t"
| "device_camera_block (Suc n) = 
    Out\<^sub>t (EState (sch [],\<lambda>_ . 0)) ''outputs_camera_image'' (-1) @\<^sub>t
    Wait\<^sub>t 0.2 (\<lambda>_. EState (sch [],\<lambda>_ . 0)) ({}, {}) @\<^sub>t
   device_camera_block n"

lemma device_camera_block_snoc:
"device_camera_block (Suc n) = device_camera_block n @\<^sub>t
Out\<^sub>t (EState (sch [],\<lambda>_ . 0)) ''outputs_camera_image'' (-1) @\<^sub>t
    Wait\<^sub>t 0.2 (\<lambda>_. EState (sch [],\<lambda>_ . 0)) ({}, {})"
proof (induction n)
  case 0
  then show ?case by auto
next
  case Con:(Suc n)
  then show ?case 
    apply (subst device_camera_block.simps(2)[of "n"])
    apply (subst device_camera_block.simps(2)[of "Suc n"])
    apply (subst Con)
    by (smt (z3) join_assoc)
qed

lemma device_camera_prop:
"\<Turnstile>{\<lambda>(a,s) t. (a,s) = (sch [],\<lambda>_ . 0) \<and> emp\<^sub>t t}
device_camera
{\<lambda>(a,s) t. \<exists> n. (a,s) = (sch [],\<lambda>_ . 0) \<and> device_camera_block n t}"
  unfolding device_camera_def
  apply(rule Valid_weaken_pre)
   prefer 2
   apply (rule Valid_rep)
   apply(rule Valid_ex_pre')
  subgoal for n
    apply(rule Valid_seq)
     apply(rule Valid_send_sp_st)
    apply (rule Valid_strengthen_post)
     prefer 2
     apply (rule Valid_wait_sp_st)
    apply (auto simp add: entails_def)
    apply(rule exI[where x="Suc n"])
      apply(subst device_camera_block_snoc)
      by(auto simp add: join_assoc)
  apply(auto simp add: entails_def)
  apply(rule exI[where x="0"])
    by auto


definition device_radar :: "scheduler proc" where
  "device_radar =
    t ::= (\<lambda>_ .0);
    data ::= (\<lambda>_ . 0);
    Rep (
      IF (\<lambda>(a,s). s t < 10) THEN
        data ::= (\<lambda>_ . 0)
      ELSE (IF (\<lambda>(a,s). s t < 20) THEN
        data ::= (\<lambda>(a,s). 2 * s t + 15)
      ELSE
        data ::= (\<lambda>_ . 0)
      FI) FI;
      Cm (''outputs_radar_obsposradar''[!](\<lambda>(a,s). s data)); 
      Wait (\<lambda>_ . 0.01);
      t ::= (\<lambda>(a,s). s t + 0.01)
    )"

fun device_radar_func :: "real \<Rightarrow> real" where
  "device_radar_func tt = (if tt < 10 then 0 else (if tt < 20 then 2 * tt + 15 else 0))"

fun device_radar_block :: "nat \<Rightarrow> nat \<Rightarrow> scheduler tassn" where
  "device_radar_block start 0 = emp\<^sub>t"
| "device_radar_block start (Suc n) =
   device_radar_block start n @\<^sub>t
   Out\<^sub>t (EState (sch [], (\<lambda>_ . 0)(data := device_radar_func (0.01 * (n + start)),
                                  t := 0.01 * (n + start))))
        ''outputs_radar_obsposradar''
        (device_radar_func (0.01 * (n + start))) @\<^sub>t
   Wait\<^sub>t 0.01 (\<lambda>_. EState (sch [],(\<lambda>_ . 0)(data := device_radar_func (0.01 * (n + start)),
                                           t := 0.01 * (n + start))))
         ({}, {})"

lemma device_radar_block_cons:
  "device_radar_block start (Suc n) =
   Out\<^sub>t (EState (sch [], (\<lambda>_ . 0)(data := device_radar_func (0.01 * (start)),
                                  t := 0.01 * (start))))
        ''outputs_radar_obsposradar''
        (device_radar_func (0.01 * (start))) @\<^sub>t
   Wait\<^sub>t 0.01 (\<lambda>_. EState (sch [],(\<lambda>_ . 0)(data := device_radar_func (0.01 * (start)),
                                           t := 0.01 * (start))))
         ({}, {}) @\<^sub>t
   device_radar_block (Suc start) n"
proof(induction start arbitrary: n)
  case 0
  then show ?case 
  proof(induction n)
    case 0
    then show ?case 
      apply(subst device_radar_block.simps(1))
      apply(subst device_radar_block.simps(2))
      apply(subst device_radar_block.simps(1))
      by(auto simp add:join_assoc)
  next
    case Conn:(Suc n)
    have a: "real n + real (Suc 0) = real (Suc n) + real 0"
      by auto
    then show ?case 
      apply(subst device_radar_block.simps(2)[of 0 "Suc n"])
      apply(subst device_radar_block.simps(2)[of "Suc 0" "n"])
      apply(subst Conn)
      unfolding a
      by(auto simp add: join_assoc)
  qed
next
  case Cons:(Suc start)
  then show ?case 
  proof(induction n)
    case 0
    then show ?case 
      apply(subst device_radar_block.simps(2)[of "Suc start" 0])
      apply(subst device_radar_block.simps(1))+
      by(auto simp add:join_assoc)
  next
    case Conn:(Suc n)
    then show ?case 
    proof-
      have a:"device_radar_block (Suc start) (Suc n) =
  Out\<^sub>t
   (EState
     (System_coon.scheduler.sch [], (\<lambda>_. 0)
      (data := device_radar_func (1 / 10\<^sup>2 * real (Suc start)),
       t := 1 / 10\<^sup>2 * real (Suc start))))
   ''outputs_radar_obsposradar'' (device_radar_func (1 / 10\<^sup>2 * real (Suc start))) @\<^sub>t
  Wait\<^sub>t (1 / 10\<^sup>2)
   (\<lambda>_. EState
         (System_coon.scheduler.sch [], (\<lambda>_. 0)
          (data := device_radar_func (1 / 10\<^sup>2 * real (Suc start)),
           t := 1 / 10\<^sup>2 * real (Suc start))))
   ({}, {}) @\<^sub>t
  device_radar_block (Suc (Suc start)) n"
        using Conn by blast
      have b:"real n + real (Suc (Suc start)) = real (Suc n) + real (Suc start)"
        by auto
      show ?thesis
        apply(subst device_radar_block.simps(2))
        apply(subst a)
        apply(subst device_radar_block.simps(2))
        apply(subst b)+
        by(auto simp add:join_assoc)
    qed
qed
qed

lemma device_radar_prop:
"\<Turnstile>{\<lambda>(a,s) tr. (a,s) = (sch [],\<lambda>_ . 0) \<and> emp\<^sub>t tr}
device_radar
{\<lambda>(a,s) tr. \<exists> n. (a,s) = (sch [],(\<lambda>_ . 0)(data := device_radar_func (0.01 * (n-1)),t := 0.01 * n)) \<and> device_radar_block 0 n tr}"
  unfolding device_radar_def
  apply(rule Valid_seq)
   prefer 2
   apply(rule Valid_seq)
  prefer 2
    apply(rule Valid_rep)
  subgoal
    apply(rule Valid_ex_pre')
    apply(rule Valid_ex_post')
    subgoal for n
      apply(rule exI[where x= "Suc n"])
    apply(rule Valid_cond_split')
    subgoal
     apply(rule Valid_seq)
       apply(rule Valid_assign_sp_bst')
      apply(rule Valid_seq)
       apply(rule Valid_send_sp_bst)
      apply(rule Valid_seq)
       apply(rule Valid_wait_sp_bst)
      apply(rule Valid_strengthen_post)
      prefer 2
       apply(rule Valid_assign_sp_bst)
      apply(auto simp add: entails_def fun_upd_def join_assoc)
      apply(subgoal_tac"(\<lambda>x. if x = data then 0
                   else if x = t then real n / 100 else if x = data then 0 else 0) = (\<lambda>x. if x = t then real n / 100 else if x = data then 0 else 0)")
     by auto
   apply(rule Valid_cond_split')
    subgoal
      apply(rule Valid_seq)
      apply(rule Valid_weaken_pre[where P'="\<lambda>s ta. ((case s of (a, s) \<Rightarrow> s t < 20) \<and>
               \<not> (case s of (a, s) \<Rightarrow> s t < 10))\<and>
               s =
               (System_coon.scheduler.sch [], (\<lambda>_. 0)
                (data := device_radar_func (1 / 10\<^sup>2 * (real n - 1)),
                 t := 1 / 10\<^sup>2 * real n)) \<and>
               device_radar_block 0 n ta"])
      subgoal 
        by(auto simp add: entails_def)
        apply(rule Valid_assign_sp_bst')
      apply(rule Valid_seq)
       apply(rule Valid_send_sp_bst)
      apply(rule Valid_seq)
       apply(rule Valid_wait_sp_bst)
      apply(rule Valid_strengthen_post)
      prefer 2
       apply(rule Valid_assign_sp_bst)
      apply(auto simp add: entails_def fun_upd_def)
      subgoal premises pre for tr
      proof -
        have a1: "n = 1000"
          using pre by auto
        have a2: "(\<lambda>x. if x = t then real 1000 / 100
                 else if x = data then 2 * (real 1000 / 100) + 15 else 0) = 
                  (\<lambda>x. if x = data then real 1000 / 50 + 15
            else if x = t then real 1000 / 100 else if x = data then 0 else 0)"
          by auto
        show ?thesis
          using pre(3)
          unfolding a1 a2  by(auto simp add:join_assoc)
      qed
      subgoal premises pre for tr
      proof -
        have a: "(\<lambda>x. if x = t then real n / 100
                 else if x = data then 2 * (real n / 100) + 15 else 0)
                  =(\<lambda>x. if x = data then real n / 50 + 15
                 else if x = t then real n / 100
                      else if x = data then 2 * ((real n - 1) / 100) + 15 else 0)"
          by auto
        show ?thesis using pre(3)
          unfolding a by(auto simp add:join_assoc)
      qed
      done
    apply(rule Valid_seq)
      apply(rule Valid_weaken_pre[where P'="(\<lambda>s ta.
       ( \<not> (case s of (a, s) \<Rightarrow> s t < 20) \<and>
        \<not> (case s of (a, s) \<Rightarrow> s t < 10)) \<and>
        s =
               (System_coon.scheduler.sch [], (\<lambda>_. 0)
                (data := device_radar_func (1 / 10\<^sup>2 * (real n - 1)),
                 t := 1 / 10\<^sup>2 * real n)) \<and>
        device_radar_block 0 n ta)"])
      subgoal by(auto simp add: entails_def)
      apply(rule Valid_assign_sp_bst')
      apply(rule Valid_seq)
       apply(rule Valid_send_sp_bst)
      apply(rule Valid_seq)
       apply(rule Valid_wait_sp_bst)
      apply(rule Valid_strengthen_post)
      prefer 2
       apply(rule Valid_assign_sp_bst)
      apply(auto simp add: entails_def)
      subgoal premises pre for tr
      proof-
        have a:"(\<lambda>_. 0)(data := 0, t := real n / 100) = (\<lambda>_. 0)(t := real n / 100, data := 0)"
          by auto
        show ?thesis using pre unfolding a
          by(auto simp add: join_assoc)
      qed
      done
    done
  prefer 2
  apply(rule Valid_assign_sp_st')
  apply(rule Valid_ex_post')
  apply(rule exI[where x=0])
  apply(rule Valid_strengthen_post)
  prefer 2
  apply(rule Valid_assign_sp_st')
  by(auto simp add:entails_def)


definition device_actuator :: "scheduler proc" where
" device_actuator = 
Rep (Cm (''inputs_actuator_cmd''[?] cmd); Cm (''outputs_PHYvehicleimp_veha''[!] (\<lambda>(a,s). s cmd)); Wait (\<lambda>_. 0.002))"

fun device_actuator_block :: "real \<Rightarrow> real list \<Rightarrow> scheduler tassn" where
  "device_actuator_block init [] = emp\<^sub>t"
| "device_actuator_block init (r#res) = 
  In\<^sub>t (EState (sch [], ((\<lambda>_ . 0)(cmd := init)))) ''inputs_actuator_cmd'' r  @\<^sub>t 
  Out\<^sub>t (EState (sch [], ((\<lambda>_ . 0)(cmd := r)))) ''outputs_PHYvehicleimp_veha'' r @\<^sub>t 
  Wait\<^sub>t 0.002 (\<lambda>_ . (EState (sch [], ((\<lambda>_ . 0)(cmd := r))))) ({},{}) @\<^sub>t
  device_actuator_block r res"

lemma device_actuator_block_snoc:
"device_actuator_block init (fcs@[r]) = 
    device_actuator_block init fcs @\<^sub>t 
  In\<^sub>t (EState (sch [], ((\<lambda>_ . 0)(cmd := last(init#fcs))))) ''inputs_actuator_cmd'' r  @\<^sub>t 
  Out\<^sub>t (EState (sch [], ((\<lambda>_ . 0)(cmd := r)))) ''outputs_PHYvehicleimp_veha'' r @\<^sub>t 
  Wait\<^sub>t 0.002 (\<lambda>_ . (EState (sch [], ((\<lambda>_ . 0)(cmd := r))))) ({},{})"
proof(induction fcs arbitrary: init r)
  case Nil
  then show ?case 
    apply(subst device_actuator_block.simps(1))
    by auto
next
  case Con:(Cons a fcs)
  have a:"(a # fcs) @ [r] = a # (fcs @ [r])"
    by auto
  have b:"last (a # fcs) = last (init # a # fcs)"
    by auto
  show ?case 
    apply(subst a)
    apply(subst device_actuator_block.simps(2)[of init a "fcs @ [r]"])
    apply(subst Con)
    apply(subst device_actuator_block.simps(2)[of init a "fcs"])
    unfolding b
    by(auto simp add:join_assoc)
qed

lemma device_actuator_prop:
"\<Turnstile>{\<lambda>(a,s) tr. (a,s) = (sch [],\<lambda>_ . 0) \<and> emp\<^sub>t tr}
device_actuator
{\<lambda>(a,s) tr. \<exists> list. (a,s) = (sch [],(\<lambda>_ . 0)(cmd := last (0#list))) \<and> device_actuator_block 0 list tr}"
  unfolding device_actuator_def
  apply(rule Valid_weaken_pre)
   prefer 2
   apply(rule Valid_rep)
   apply(rule Valid_ex_pre')
  apply(rule Valid_seq)
  apply(rule Valid_receive_sp_st)
   apply(rule Valid_ex_pre) 
  subgoal for list v
    apply(rule Valid_ex_post')
    apply(rule exI[where x="list@[v]"])
   apply(rule Valid_seq)
    apply(rule Valid_send_sp_st)
   apply(rule Valid_strengthen_post)
  prefer 2
     apply(rule Valid_wait_sp_st)
    unfolding device_actuator_block_snoc[of 0 list v]
    apply(auto simp add:entails_def fun_upd_def)
     apply (metis join_assoc)
    apply(subgoal_tac "(\<lambda>x. if x = cmd then v else 0) = (\<lambda>x. if x = cmd then v else if x = cmd then last list else 0)")
    by(auto simp add:join_assoc)
  apply(simp add:entails_def)
  apply clarify 
  subgoal premises pre for tr
    apply(rule exI[where x="[]"])
    by auto
  done
 
    
definition device_gps :: "scheduler proc" where
" device_gps = 
Rep (Cm (''inputs_PHYvehicleimp_vehs''[?] data); Cm (''outputs_gps_vehpos''[!] (\<lambda>(a,s). s data)); Wait (\<lambda>_. 0.006))"

fun device_gps_block :: "real \<Rightarrow> real list \<Rightarrow> scheduler tassn" where
  "device_gps_block init [] = emp\<^sub>t"
| "device_gps_block init (r#res) = 
  In\<^sub>t (EState (sch [], ((\<lambda>_ . 0)(data := init)))) ''inputs_PHYvehicleimp_vehs'' r  @\<^sub>t 
  Out\<^sub>t (EState (sch [], ((\<lambda>_ . 0)(data := r)))) ''outputs_gps_vehpos'' r @\<^sub>t 
  Wait\<^sub>t 0.006 (\<lambda>_ . (EState (sch [], ((\<lambda>_ . 0)(data := r))))) ({},{}) @\<^sub>t
  device_gps_block r res"

lemma device_gps_block_snoc:
"device_gps_block init (fcs@[r]) = 
    device_gps_block init fcs @\<^sub>t 
  In\<^sub>t (EState (sch [], ((\<lambda>_ . 0)(data := last(init#fcs))))) ''inputs_PHYvehicleimp_vehs'' r  @\<^sub>t 
  Out\<^sub>t (EState (sch [], ((\<lambda>_ . 0)(data := r)))) ''outputs_gps_vehpos'' r @\<^sub>t 
  Wait\<^sub>t 0.006 (\<lambda>_ . (EState (sch [], ((\<lambda>_ . 0)(data := r))))) ({},{})"
proof(induction fcs arbitrary: init r)
  case Nil
  then show ?case 
    apply(subst device_gps_block.simps(1))
    by auto
next
  case Con:(Cons a fcs)
  have a:"(a # fcs) @ [r] = a # (fcs @ [r])"
    by auto
  have b:"last (a # fcs) = last (init # a # fcs)"
    by auto
  show ?case 
    apply(subst a)
    apply(subst device_gps_block.simps(2)[of init a "fcs @ [r]"])
    apply(subst Con)
    apply(subst device_gps_block.simps(2)[of init a "fcs"])
    unfolding b
    by(auto simp add:join_assoc)
qed

lemma device_gps_prop:
"\<Turnstile>{\<lambda>(a,s) tr. (a,s) = (sch [],\<lambda>_ . 0) \<and> emp\<^sub>t tr}
device_gps
{\<lambda>(a,s) tr. \<exists> list. (a,s) = (sch [],(\<lambda>_ . 0)(data := last (0#list))) \<and> device_gps_block 0 list tr}"
  unfolding device_gps_def
  apply(rule Valid_weaken_pre)
   prefer 2
   apply(rule Valid_rep)
   apply(rule Valid_ex_pre')
  apply(rule Valid_seq)
  apply(rule Valid_receive_sp_st)
   apply(rule Valid_ex_pre) 
  subgoal for list v
    apply(rule Valid_ex_post')
    apply(rule exI[where x="list@[v]"])
   apply(rule Valid_seq)
    apply(rule Valid_send_sp_st)
   apply(rule Valid_strengthen_post)
  prefer 2
     apply(rule Valid_wait_sp_st)
    unfolding device_gps_block_snoc[of 0 list v]
    apply(auto simp add:entails_def fun_upd_def)
     apply (metis join_assoc)
    apply(subgoal_tac "(\<lambda>x. if x = data then v else 0) = (\<lambda>x. if x = data then v else if x = data then last list else 0)")
    by(auto simp add:join_assoc)
  apply(simp add:entails_def)
  apply clarify 
  subgoal premises pre for tr
    apply(rule exI[where x="[]"])
    by auto
  done


definition device_laser :: "scheduler proc" where
" device_laser = 
Rep (Cm (''inputs_PHYvehicleimp_vehv1''[?] data); t::= (\<lambda>_ .0);
Interrupt (ODE ((\<lambda> _ _.0)(t := (\<lambda> _ . 1)))) (\<lambda> s. s t < 0.01) [(''outputs_laser_laservalid''[!](\<lambda> _. 1), Cm (''outputs_laser_laserv''[!] (\<lambda>(a,s). s data)))];
Cont (ODE ((\<lambda> _ _.0)(t := (\<lambda> _ . 1)))) (\<lambda> s. s t < 0.01))"

inductive device_laser_block :: "nat \<Rightarrow> scheduler tassn" where
  "device_laser_block 0 []"
| "
device_laser_block (Suc n) []"




