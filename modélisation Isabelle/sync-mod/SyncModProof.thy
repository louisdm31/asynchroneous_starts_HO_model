theory SyncModProof
imports "../HOModel" SyncMod
begin

definition HOMachine_to_Algorithm :: "(Proc, pstate, SendVal) HOMachine \<Rightarrow> (Proc, pstate, SendVal) CHOAlgorithm" where
"HOMachine_to_Algorithm mach = (| CinitState = CinitState mach, sendMsg = sendMsg mach, CnextState = CnextState mach |)"


definition monovalent :: "(nat \<Rightarrow> Proc \<Rightarrow> pstate proc_state) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"monovalent rho v n \<equiv> !p ss st. rho n p = Active ss \<longrightarrow> rho (Suc n) p = Active st \<longrightarrow> x st = v"

(*lemma A1 : assumes "rho r p = Active s"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "x s = k-1"
and "p : HO (Suc r) q"
and "rho r q ~= Aslept"
shows "!st. rho (Suc r) q = Active st \<longrightarrow> x st = 0"
proof (rule+)
    fix st
    assume "rho (Suc r) q = Active st"
    show "x st = 0"
    proof -
        *)
lemma stating : assumes "0 < n \<longrightarrow> rho (n-1) p = Aslept"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "rho n p = Active s"
shows "x s = k" and "!q. HOrcvdMsgs ?A q (HO (Suc n) q) (rho n) p = (if p : HO (Suc n) q then Content Nope else Void)" and "~ forc s"
proof -
    have "CHOinitConfig ?A rho (%w ww. undefined)"
        using run HORun_def[of ?A rho HO] CHORun_def[of ?A rho HO "%w ww. undefined"] by simp
    hence "CinitState ?A p s undefined"
        using CHOinitConfig_def[of ?A rho] `rho n p = Active s` `0 < n \<longrightarrow> rho (n-1) p = Aslept` by auto
    hence "k_mod.SyncMod_initState k p s"
        using HOMachine_to_Algorithm_def by (simp add:k_mod.SyncMod_HOMachine_def)
    hence "x s = k" and "~ forc s" using k_mod.SyncMod_initState_def[of k p s] by auto
    hence "!q. k_mod.SyncMod_sendMsg k p q s = Nope"
        using k_mod.SyncMod_sendMsg_def[of k p _ s] by fastforce
    hence "!q. sendMsg ?A p q s = Nope"
        using HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def by (simp add: k_mod.SyncMod_HOMachine_def)
    hence "!q. HOrcvdMsgs ?A q (HO (Suc n) q) (rho n) p = (if p : HO (Suc n) q then Content Nope else Void)"
        using HOrcvdMsgs_def[of ?A p "HO (Suc n) p" "rho n"] by (simp add: HOrcvdMsgs_def assms(3))
    thus "x s = k" and "!q. HOrcvdMsgs ?A q (HO (Suc n) q) (rho n) p = (if p : HO (Suc n) q then Content Nope else Void)" and "~ forc s"
        using `x s  = k` `~ forc s` by auto
qed

lemma sending : assumes run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A rho HO")
assumes "(HOrcvdMsgs ?A p (HO (Suc (Suc r)) p) (rho (Suc r))) q = Content (Val v)" (is "?msgs q = _")
shows "? s ss. rho r q = Active s \<and> rho (Suc r) q = Active ss \<and> x ss = v"
proof (cases "rho (Suc r) q")
    case Aslept
    hence "?msgs q = (if q : HO (Suc (Suc r)) p then Bot else Void)"
        using HOrcvdMsgs_def[of ?A p "HO (Suc (Suc r)) p" "rho (Suc r)"] by auto
    thus "? s ss. rho r q = Active s \<and> rho (Suc r) q = Active ss \<and> x ss = v" using `?msgs q = Content (Val v)` by auto
next
    case (Active sq)
    have "sendMsg ?A q p sq = Val (x sq)"
        using HOrcvdMsgs_def[of ?A p "HO (Suc (Suc r)) p" "rho (Suc r)"] `?msgs q = Content (Val v)`
        by (simp add: Active HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def k_mod.SyncMod_sendMsg_def)
    hence "k_mod.SyncMod_sendMsg k q p sq = Val (x sq)"
        using HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def by 
        (simp add: `\<And>k. k_mod.SyncMod_HOMachine k \<equiv> (|CinitState = %p st crd. k_mod.SyncMod_initState k p st,
        sendMsg = k_mod.SyncMod_sendMsg k, CnextState = %p st msgs crd. k_mod.SyncMod_nextState k p st msgs,
        HOcommPerRd = k_mod.SyncMod_commPerRd, HOcommGlobal = k_mod.SyncMod_commGlobal,
        HOcommSchedule = k_mod.SyncMod_commSchedule|)`)
    hence "rho r q ~= Aslept"
        using stating[of "Suc r" rho q k HO sq] `rho (Suc r) q = Active sq`
        by (metis SendVal.distinct(1) diff_Suc_1 k_mod.SyncMod_sendMsg_def run)
    then obtain s where "rho r q = Active s" by (cases "rho r q") auto
    moreover have "?msgs q = Content (Val (x sq))"
        using HOrcvdMsgs_def[of ?A p "HO (Suc (Suc r)) p" "rho (Suc r)"] `?msgs q = Content (Val v)`
        by (simp add: Active `sendMsg (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) q p sq = Val (x sq)`)
    ultimately have "rho r q = Active s \<and> rho (Suc r) q = Active sq \<and> x sq = v"
        using `rho (Suc r) q = Active sq` `?msgs q = Content (Val v)` k_mod.SyncMod_sendMsg_def[of k q p sq] by auto
    thus "? s ss. rho r q = Active s \<and> rho (Suc r) q = Active ss \<and> x ss = v"  by auto
qed

lemma transition : assumes s_def:"rho r p = Active s"
and ss_def:"rho (Suc r) p = Active ss"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "k > 2"
shows "k_mod.SyncMod_nextState k p s (HOrcvdMsgs ?A p (HO (Suc r) p) (rho r)) ss" (is "k_mod.SyncMod_nextState  _ _ _ ?msgs _")
and "x ss < k"
proof -
    have "CHOnextConfig ?A (rho r) (HO (Suc r)) (%w. undefined) (rho (Suc r))" using run by (simp add:HORun_def CHORun_def)
    then obtain sss where "rho (Suc r) p = Active sss \<and> CnextState ?A p s ?msgs undefined sss" 
        using CHOnextConfig_def[of ?A "rho r" "HO (Suc r)" "%w. undefined" "rho (Suc r)"] s_def by fastforce
    hence "CnextState ?A p s ?msgs undefined ss" using ss_def by auto
    hence nxt:"k_mod.SyncMod_nextState k p s ?msgs ss"
        using HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def[of k] by (simp add:k_mod.simp_nextState)
    hence "x ss < k"
    proof (cases "k_mod.ready_force k ?msgs s")
        case True
        thus "x ss < k" using nxt k_mod.SyncMod_nextState_def `k > 2` by auto
    next
        case False
        thus "x ss < k"
        proof (cases "x ss = 0")
            case True
            thus "x ss < k" using `k > 2` by auto
        next
            case False
            hence "(x ss) mod k = x ss" using nxt k_mod.SyncMod_nextState_def by auto
            thus "x ss < k" using `k > 2` by (metis less_Suc_eq_0_disj less_imp_Suc_add mod_less_divisor)
        qed
    qed
    thus "k_mod.SyncMod_nextState k p s ?msgs ss" and "x ss < k" using nxt by auto
qed

lemma A2 : assumes "k_mod.xi_nek HO xi"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "rho r xi = Active s"
and "x s = k - 1"
and "k > 2"
shows "monovalent rho 0 r"
proof -
    have "!p ss st. rho r p = Active ss \<longrightarrow> rho (Suc r) p = Active st \<longrightarrow> x st = 0"
    proof (rule+)
        fix p
        fix ss
        fix st
        assume "rho r p = Active ss"
        assume "rho (Suc r) p = Active st"
        show "x st = 0"
        proof (rule ccontr)
            assume "x st ~= 0"
            let ?msgs = "HOrcvdMsgs ?A p (HO (Suc r) p) (rho r)"
            have "k_mod.SyncMod_sendMsg k xi p s = Val (x s)"
                using  k_mod.SyncMod_sendMsg_def[of k xi p s] `x s = k - 1` `k > 2` by simp
            hence "sendMsg ?A xi p s = Val (x s)"
                using HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def 
                by (simp add: `\<And>k. k_mod.SyncMod_HOMachine k \<equiv> (|CinitState = %p st crd. k_mod.SyncMod_initState k p st,
                sendMsg = k_mod.SyncMod_sendMsg k, CnextState = %p st msgs crd. k_mod.SyncMod_nextState k p st msgs,
                HOcommPerRd = k_mod.SyncMod_commPerRd, HOcommGlobal = k_mod.SyncMod_commGlobal,
                HOcommSchedule = k_mod.SyncMod_commSchedule|)`)
            hence "?msgs xi = Content (Val (x s))"
                using `k_mod.xi_nek HO xi` HOrcvdMsgs_def[of ?A p "HO (Suc r) p" "rho r"] `rho r xi = Active s`
                k_mod.xi_nek_def[of HO xi] by auto
            hence non_forc:"~ (k_mod.ready_force k ?msgs ss)"
                    using k_mod.ready_force_def[of k ?msgs ss] `x s = k-1` by auto

            have "CnextState ?A p ss ?msgs undefined st" 
                using HORun_def CHORun_def run CHOnextConfig_def[of ?A "rho r" _ _ "rho (Suc r)"]
                `rho r p = Active ss`
                `rho (Suc r) p = Active st` by fastforce
            hence "k_mod.SyncMod_nextState k p ss ?msgs st"
                using HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def[of k]
                by (simp add: k_mod.simp_nextState)
            moreover from this have "EX v. k_mod.concordant ?msgs v"
                using k_mod.SyncMod_nextState_def[of k p ss ?msgs st] `x st ~= 0` non_forc apply(presburger) done
            moreover from this have "k_mod.concordant ?msgs (Eps (%v. k_mod.concordant ?msgs v))" (is "k_mod.concordant ?msgs ?v")
                using someI[of "%v. k_mod.concordant ?msgs v"] by auto
            hence "?v = k-1"
                using `?msgs xi = Content (Val (x s))` k_mod.concordant_def[of ?msgs ?v] `x s = k-1` by auto
            ultimately have "x st = (Suc ?v) mod k"
                using k_mod.SyncMod_nextState_def[of k p ss ?msgs st] `x st ~= 0`  non_forc by auto
            hence "x st = 0" using `?v = k-1` `k > 2` by auto
            thus "False" using `x st ~= 0` by auto
        qed
    qed
    thus "monovalent rho 0 r" using monovalent_def[of rho 0 r] by auto
qed

lemma A3 : assumes "k_mod.xi_nek HO xi"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "rho r xi = Active s"
and "x s = k - 1"
and "k > 2"
and "monovalent rho (v mod k) r"
shows "monovalent rho ((v+i) mod k) (r+i)"
proof (induction i)
    from assms(6) show "monovalent rho ((v+0) mod k) (r+0)" by auto
next
    case (Suc i)
    let "?msgs p" = "(HOrcvdMsgs ?A p (HO (Suc (r+Suc i)) p) (rho (r+Suc i)))"
    have no_discord:"!p q vv. ?msgs p q = Content (Val vv) \<longrightarrow> vv = (v+i) mod k"
    proof (rule+)
        fix p q vv
        assume "?msgs p q = Content (Val vv)"
        then obtain s ss where " rho (r+i) q = Active s \<and> rho (r+Suc i) q = Active ss \<and> x ss = vv"
            using run sending[of k rho HO p "r+i" q vv] by auto
        thus "vv = (v+i) mod k"
            using Suc.IH monovalent_def[of rho "(v+i) mod k" "r+i"] by auto
    qed

    have "rho (r+i) xi ~= Aslept"
        using run HORun_def assms(3) nonAsleepAgain[of rho r xi ?A HO _ i] by (simp add: HORun_def add.commute)
    then obtain sx where "rho (r+i) xi = Active sx" by (cases "rho (r+i) xi") auto
    moreover have "rho (Suc (r+i)) xi ~= Aslept"
        using run HORun_def assms(3) nonAsleepAgain[of rho r xi ?A HO _ "i+1"] by (simp add: HORun_def add.commute)
    then obtain sxx where "rho (Suc (r+i)) xi = Active sxx" by (cases "rho (Suc (r+i)) xi") auto
    ultimately have "x sxx = (v+i) mod k" using Suc.IH monovalent_def[of rho "(v+i) mod k" "r+i" ] by auto
    hence "!p. k_mod.SyncMod_sendMsg k xi p sxx = Val ((v+i) mod k)" using k_mod.SyncMod_sendMsg_def by 
        (metis One_nat_def add_lessD1 assms(5) linorder_not_less mod_le_divisor mod_less_divisor
        neq0_conv not_add_less2 numerals(2) plus_1_eq_Suc)
    hence "!p. sendMsg ?A xi p sxx = Val ((v+i) mod k)"
        using HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def by (simp add: k_mod.SyncMod_HOMachine_def)
    hence "!p. ?msgs p xi = Content (Val ((v+i) mod k))" (is "!p. ?msgs p xi = _")
        using assms(1) by (simp add: HOrcvdMsgs_def k_mod.xi_nek_def `rho (Suc (r + i)) xi = Active sxx`)

    hence concord:"!p. k_mod.concordant (?msgs p) ((v+i) mod k)"
        using k_mod.concordant_def[of _ "(v+i) mod k"] no_discord by smt

    have "!p ss st. rho (r+Suc i) p = Active ss \<longrightarrow> rho (Suc (r+Suc i)) p = Active st \<longrightarrow> x st = (v + Suc i) mod k"
    proof (rule+)
        fix p ss st
        assume "rho (r+Suc i) p = Active ss" and "rho (Suc (r+Suc i)) p = Active st"
        hence "k_mod.SyncMod_nextState k p ss (?msgs p) st" using run transition[of rho "r+Suc i" p ss st k HO] assms(5) by blast
        show "x st = (v + Suc i) mod k"
        proof (cases "k_mod.ready_force k (?msgs p) ss")
            case True
            hence "? p1 p2 v1 v2. (?msgs p) p1 = Content (Val v1) \<and> (?msgs p) p2 = Content (Val v2) \<and> v1 ~= v2"
                using k_mod.ready_force_def by blast
            then obtain p1 p2 v1 v2 where "(?msgs p) p1 = Content (Val v1)" and
                                          "(?msgs p) p2 = Content (Val v2)" and "v1 ~= v2" by auto
            then obtain s1 s2 ss1 ss2 where "rho (r+i) p1 = Active s1" and "rho (r+Suc i) p1 = Active ss1 \<and> x ss1 = v1" and
                                            "rho (r+i) p2 = Active s2" and "rho (r+Suc i) p2 = Active ss2 \<and> x ss2 = v2"
                using run sending[of k rho HO p "r+i" p1 v1] sending[of k rho HO p "r+i" p2 v2] by auto
            hence "v1 = (v+i) mod k" and "v2 = (v+i) mod k" using Suc.IH monovalent_def[of rho "(v+i) mod k" "r+i"] by auto
            thus "x st = (v + Suc i) mod k" using `v1 ~= v2` by auto
        next
            case False
            hence "x st = (Suc (Eps (%v. k_mod.concordant (?msgs p) v))) mod k"
                using `k_mod.SyncMod_nextState k p ss (?msgs p) st` k_mod.SyncMod_nextState_def concord by auto
            hence "x st = (Suc ((v+i) mod k)) mod k" using `!p. ?msgs p xi = Content (Val ((v+i) mod k))` k_mod.concordant_def by (metis concord someI_ex)
            thus "x st = (v + Suc i) mod k" using mod_Suc_eq by auto
        qed
    qed
    thus "monovalent rho ((v+Suc i) mod k) (r+Suc i)" using monovalent_def[of rho "(v+Suc i) mod k" "r+Suc i"] by auto
qed

lemma A4 : assumes "k_mod.xi_nek HO xi"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "rho r xi = Active s"
and "x s = k - 1"
and "k > 2"
assumes commS:"HOcommSchedule (k_mod.SyncMod_HOMachine k) (Schedule rho)"
shows "k_mod.liveness rho"
proof -
    have "? n. Schedule rho n = UNIV" using commS by (simp add:k_mod.SyncMod_HOMachine_def k_mod.SyncMod_commSchedule_def )
    then obtain n :: nat where "!p. rho n p ~= Aslept" by auto

    have "monovalent rho 0 r" using A2 assms by auto
    moreover have "(0+(n+1)*k-1) mod k = k-1"
        by (smt Suc_diff_1 add.commute add.left_neutral add_diff_inverse_nat diff_Suc_1 diff_add_zero
        mod_Suc mod_mult_self2_is_0 no_zero_divisors zero_eq_add_iff_both_eq_0 zero_neq_one)
    ultimately have monoval:"monovalent rho ((k-1) :: nat) ((r+(n+1)*k-1) :: nat)" 
        using A3[where ?v = 0 and ?i = "(n+1)*k-1" and ?r = r] assms 
        by (metis (no_types, lifting) add.left_neutral less_one linorder_not_less mod_mult_self1 mod_mult_self2_is_0
        no_zero_divisors not_less0 ordered_cancel_comm_monoid_diff_class.add_diff_assoc zero_eq_add_iff_both_eq_0)
    have "!p r. rho r p ~= Aslept --> (? rf sf. rho rf p = Active sf & fire sf)"
    proof (rule allI impI)+
        fix p
        fix r :: nat
        assume "rho r p ~= Aslept"
        moreover have "1 \<le> (n+1)*k" using `k > 2` by auto
        hence "r+((n+1)*k-1) = r+(n+1)*k-1" (is "_ = ?rd") using  ordered_cancel_comm_monoid_diff_class.add_diff_assoc[of 1 "(n+1)*k" r] by auto
        ultimately have "rho (Suc ?rd) p ~= Aslept" using nonAsleepAgain[of rho r p _ _ _ "(n+1)*k"] run HORun_def
            by (smt `1 \<le> (n + 1) * k` add.commute add_Suc_right ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
        then obtain ss where "rho (Suc ?rd) p = Active ss" by (cases "rho (Suc ?rd) p") auto
        moreover from this have "rho (Suc (Suc ?rd)) p ~= Aslept"
            using nonAsleepAgain[of rho "Suc ?rd" p _ _ _ 1] run HORun_def Suc_diff_1 assms(5) by fastforce
        then obtain st where "rho (Suc (Suc ?rd)) p = Active st" by (cases "rho (Suc (Suc ?rd)) p") auto
        ultimately have nxt:"k_mod.SyncMod_nextState k p ss (HOrcvdMsgs ?A p (HO (Suc (Suc ?rd)) p) (rho (Suc ?rd))) st"
            (is "k_mod.SyncMod_nextState  _ _ _ ?msgs _")
            using transition[of rho "Suc ?rd" p ss st] run assms(5) by auto
        have "!q. ?msgs q = Void \<or> ?msgs q = Content (Val (k-1))"
        proof
            fix q
            have "?rd-n = r+n*k+1*k-1-n" using `k > 2` by simp
            hence positiv:"?rd-n > 0" using `k > 2`
                by (metis add.commute add_lessD1 diff_diff_left mult.commute mult.right_neutral mult_less_cancel2
                one_add_one trans_less_add2 zero_less_diff )
            hence "rho ?rd q ~= Aslept"
                using nonAsleepAgain[of rho n q ?A HO "%r q. undefined" "?rd-n"]
                run HORun_def[of ?A rho HO] `!p. rho n p ~= Aslept` `k > 2` by auto
            then obtain sq where "rho ?rd q = Active sq" by (cases "rho ?rd q") auto
            moreover have "rho (Suc ?rd) q ~= Aslept"
                using run HORun_def[of ?A rho HO] `k > 2`
                by (metis `rho ?rd q ~= Aslept` nonAsleepAgain plus_1_eq_Suc)
            then obtain sqq where "rho (Suc ?rd) q = Active sqq" by (cases "rho (Suc ?rd) q") auto
            moreover have "r+(n+1)*k > 0" using `k > 2` by auto


            moreover have "monovalent rho ((k - 1) :: nat) (?rd :: nat)" using monoval by auto
    


            ultimately have "x sqq = k-1"
                using assms monovalent_def[of rho "k-1" ?rd] by auto

            hence "k_mod.SyncMod_sendMsg k q p sqq = Val (k-1)"
                using k_mod.SyncMod_sendMsg_def[of k q p sqq] `k > 2` by auto 
            hence "sendMsg ?A q p sqq = Val (k-1)"
                using k_mod.SyncMod_HOMachine_def HOMachine_to_Algorithm_def
                by (simp add: `\<And>k. k_mod.SyncMod_HOMachine k \<equiv> (| CinitState = %p st crd. k_mod.SyncMod_initState k p st,
                sendMsg = k_mod.SyncMod_sendMsg k, CnextState = %p st msgs crd. k_mod.SyncMod_nextState k p st msgs,
                HOcommPerRd = k_mod.SyncMod_commPerRd, HOcommGlobal = k_mod.SyncMod_commGlobal, HOcommSchedule = k_mod.SyncMod_commSchedule |)`)
            hence "?msgs q = (if q : HO (Suc (Suc ?rd)) p then Content (Val (k-1)) else Void)"
                using HOrcvdMsgs_def[of ?A p "HO (Suc (Suc ?rd)) p" "rho (Suc ?rd)"] `rho (Suc ?rd) q = Active sqq` by auto
            thus "?msgs q = Void | ?msgs q = Content (Val (k-1))" by auto
        qed
        hence "k_mod.ready_fire k ?msgs" using k_mod.ready_fire_def[of k ?msgs] by auto
        hence "fire st" using nxt k_mod.SyncMod_nextState_def by auto
        hence "rho (Suc (Suc ?rd)) p = Active st & fire st" using `rho (Suc (Suc ?rd)) p = Active st` by auto
        thus "? rf sf. rho rf p = Active sf & fire sf" by auto
    qed
    thus "k_mod.liveness rho" using k_mod.liveness_def by auto
qed

definition round_force where
"round_force rho p == Eps (%r. ? s. rho r p = Active s & forc s)"

lemma nonForceAgain : assumes "round_force rho p <= n"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "rho n p = Active sr"
and "rho (Suc n) p = Active s"
and "k > 2"
shows "~ k_mod.ready_force k (HOrcvdMsgs ?A p (HO (Suc n) p) (rho n)) s" (is "~ k_mod.ready_force k ?msgs s")
proof (cases "? r s. rho r p = Active s & forc s")
    case True
    then obtain r where "? s. rho r p = Active s & forc s" by auto
    then obtain s where rd_forc:"rho (round_force rho p) p = Active s & forc s"
        using round_force_def[of rho p]  someI[of "%r. ? s. rho r p = Active s & forc s" r] by auto 
    have "!i ss. rho (round_force rho p + i) p = Active ss --> forc ss"
    proof (rule allI)+
        fix i ss
        show "rho (round_force rho p + i) p = Active ss --> forc ss"
        proof (induction i arbitrary:ss)
            case 0
            thus "rho (round_force rho p + 0) p = Active ss --> forc ss" using rd_forc by auto
        next
            case (Suc ii)
            moreover have "rho (ii + round_force rho p) p ~= Aslept"
                using nonAsleepAgain[of rho "round_force rho p" p ?A HO _ ii] run HORun_def rd_forc by auto
            then obtain st where "rho (ii + round_force rho p) p = Active st" by (cases "rho (ii + round_force rho p) p") auto
            ultimately have "forc st" using add.commute[of ii "round_force rho p"] by auto
            show "rho (round_force rho p + (Suc ii)) p = Active ss --> forc ss" 
            proof
                assume "rho (round_force rho p + (Suc ii)) p = Active ss" 
                hence "k_mod.SyncMod_nextState k p st (HOrcvdMsgs ?A p (HO (Suc (round_force rho p + ii)) p) (rho (round_force rho p + ii))) ss"
                    using transition[of rho "round_force rho p + ii" p st ss k HO] `2 < k` run by (simp add:`rho (ii+round_force rho p) p = Active st` add.commute)
                thus "forc ss" using `forc st` k_mod.SyncMod_nextState_def by auto
            qed
        qed
    qed
    thus ?thesis using k_mod.ready_force_def[of k ?msgs s]
        by (metis add_Suc_right assms(1) assms(4) k_mod.ready_force_def ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
next
    case False
    hence "~ forc s" using assms(4) by auto
    have "k_mod.SyncMod_nextState k p sr ?msgs s" using transition[of rho n p sr s k HO] assms by auto
    thus ?thesis using k_mod.SyncMod_nextState_def by (simp add:`~ forc s` k_mod.ready_force_def)
qed

lemma SuncMod_liveness : assumes "k_mod.xi_nek HO xi"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "k > 2"
assumes commS:"HOcommSchedule (k_mod.SyncMod_HOMachine k) (Schedule rho)"
shows "k_mod.liveness rho"
proof -
    have "EX n. Schedule rho n = UNIV" using commS by (simp add:k_mod.SyncMod_HOMachine_def k_mod.SyncMod_commSchedule_def )
    then obtain n :: nat where "!p. rho n p ~= Aslept" by auto
    let ?n = "n + Max ( (round_force rho) ` Proc)"
    let ?txi = "round_force rho xi"
    show ?thesis
    proof (cases "EX s. rho ?txi xi = Active s & forc s")
        case True