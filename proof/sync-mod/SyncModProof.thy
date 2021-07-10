theory SyncModProof
imports "../HOModel" SyncMod
begin

definition HOMachine_to_Algorithm :: "(Proc, pstate, SendVal) HOMachine => (Proc, pstate, SendVal) CHOAlgorithm" where
"HOMachine_to_Algorithm mach = 
  (| CinitState = CinitState mach, sendMsg = sendMsg mach, CnextState = CnextState mach |)"


definition monovalent :: "(nat => Proc => pstate proc_state) => nat => nat => bool" where
"monovalent rho v n == ALL p ss st. rho n p = Active ss --> rho (Suc n) p = Active st --> x st = v"

(*lemma A1 : assumes "rho r p = Active s"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "x s = k-1"
and "p : HO (Suc r) q"
and "rho r q ~= Asleep"
shows "ALL st. rho (Suc r) q = Active st --> x st = 0"
proof (rule+)
    fix st
    assume "rho (Suc r) q = Active st"
    show "x st = 0"
    proof -
        *)
lemma starting: 
assumes prev: "0 < n --> rho (n-1) p = Asleep"
  and run: "HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
  and act: "rho n p = Active s"
shows "x s = k" 
  and "ALL q. HOrcvdMsgs ?A q (HO (Suc n) q) (rho n) p = (if p : HO (Suc n) q then Content Nope else Void)"
  and "~ forc s"
proof -
  from act have 1: "~ always_asleep rho p"
    unfolding always_asleep_def by force
  from run prev act have 2: "first_awake rho p = n"
    by (rule first_awake_HO)
  from run have "CHOinitConfig ?A rho (%_ _. undefined)"
    by (simp add: HORun_def CHORun_def)
  with 1 2 act have "CinitState ?A p s undefined"
    by (auto simp: CHOinitConfig_def)
  hence 3: "k_mod.SyncMod_initState k p s"
    by (simp add:k_mod.SyncMod_HOMachine_def HOMachine_to_Algorithm_def)
  from 3 show "x s = k" "~ forc s" 
    by (auto simp: k_mod.SyncMod_initState_def)
  with act show "ALL q. HOrcvdMsgs ?A q (HO (Suc n) q) (rho n) p = 
                     (if p : HO (Suc n) q then Content Nope else Void)"
    by (auto simp: HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def 
                   k_mod.SyncMod_sendMsg_def HOrcvdMsgs_def)
qed

lemma sending : assumes run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A rho HO")
assumes "(HOrcvdMsgs ?A p (HO (Suc (Suc r)) p) (rho (Suc r))) q = Content (Val v)" (is "?msgs q = _")
shows "? s ss. rho r q = Active s & rho (Suc r) q = Active ss & x ss = v"
proof (cases "rho (Suc r) q")
    case Asleep
    hence "?msgs q = (if q : HO (Suc (Suc r)) p then Bot else Void)"
        using HOrcvdMsgs_def[of ?A p "HO (Suc (Suc r)) p" "rho (Suc r)"] by auto
    thus "? s ss. rho r q = Active s & rho (Suc r) q = Active ss & x ss = v" using `?msgs q = Content (Val v)` by auto
next
    case (Active sq)
    have "sendMsg ?A q p sq = Val (x sq)"
        using HOrcvdMsgs_def[of ?A p "HO (Suc (Suc r)) p" "rho (Suc r)"] `?msgs q = Content (Val v)`
        by (simp add: Active HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def k_mod.SyncMod_sendMsg_def)
    hence "k_mod.SyncMod_sendMsg k q p sq = Val (x sq)"
        using HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def by 
        (simp add: `\<And>k. k_mod.SyncMod_HOMachine k == (|CinitState = %p st crd. k_mod.SyncMod_initState k p st,
        sendMsg = k_mod.SyncMod_sendMsg k, CnextState = %p st msgs crd. k_mod.SyncMod_nextState k p st msgs,
        HOcommPerRd = k_mod.SyncMod_commPerRd, HOcommGlobal = k_mod.SyncMod_commGlobal,
        HOcommSchedule = k_mod.SyncMod_commSchedule|)`)
    hence "rho r q ~= Asleep"
        using starting[of "Suc r" rho q k HO sq] `rho (Suc r) q = Active sq`
        by (metis SendVal.distinct(1) diff_Suc_1 k_mod.SyncMod_sendMsg_def run)
    then obtain s where "rho r q = Active s" by (cases "rho r q") auto
    moreover have "?msgs q = Content (Val (x sq))"
        using HOrcvdMsgs_def[of ?A p "HO (Suc (Suc r)) p" "rho (Suc r)"] `?msgs q = Content (Val v)`
        by (simp add: Active `sendMsg (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) q p sq = Val (x sq)`)
    ultimately have "rho r q = Active s & rho (Suc r) q = Active sq & x sq = v"
        using `rho (Suc r) q = Active sq` `?msgs q = Content (Val v)` k_mod.SyncMod_sendMsg_def[of k q p sq] by auto
    thus "? s ss. rho r q = Active s & rho (Suc r) q = Active ss & x ss = v"  by auto
qed

lemma transition : assumes s_def:"rho r p = Active s"
and ss_def:"rho (Suc r) p = Active ss"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "k > 2"
shows "k_mod.SyncMod_nextState k p s (HOrcvdMsgs ?A p (HO (Suc r) p) (rho r)) ss" (is "k_mod.SyncMod_nextState  _ _ _ ?msgs _")
and "x ss < k"
proof -
    have "CHOnextConfig ?A (rho r) (HO (Suc r)) (%w. undefined) (rho (Suc r))" using run by (simp add:HORun_def CHORun_def)
    then obtain sss where "rho (Suc r) p = Active sss & CnextState ?A p s ?msgs undefined sss" 
        using CHOnextConfig_def[of ?A "rho r" "HO (Suc r)" "%w. undefined" "rho (Suc r)"] s_def by fastforce
    hence "CnextState ?A p s ?msgs undefined ss" using ss_def by auto
    hence nxt:"k_mod.SyncMod_nextState k p s ?msgs ss"
        using HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def[of k] by (simp add:k_mod.simp_nextState)
    hence "x ss < k"
    proof (cases "k_mod.ready_force k ?msgs s")
        case True
        thus "x ss < k" using nxt k_mod.SyncMod_nextState_def `k > 2` by auto
    next
        case non_forc:False
        thus "x ss < k"
        proof (cases "ALL q v. ?msgs q ~= Content (Val v)")
            case True
            thus "x ss < k" using `k > 2` nxt k_mod.SyncMod_nextState_def by auto
        next
            case False
            hence "EX q v. ?msgs q = Content (Val v) & Suc v mod k = x ss" 
              using non_forc nxt unfolding k_mod.SyncMod_nextState_def by metis
            thus "x ss < k" using `k > 2` by (metis less_Suc_eq_0_disj less_imp_Suc_add mod_less_divisor)
        qed
    qed
    thus "k_mod.SyncMod_nextState k p s ?msgs ss" and "x ss < k" using nxt by auto
qed

lemma sending_rec : assumes "p : HO (Suc r) q"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "rho r p = Active s"
and "x s < k"
shows "HOrcvdMsgs ?A q (HO (Suc r) q) (rho r) p = Content (Val (x s))"
proof -
    have "sendMsg ?A p q s = Val (x s)" using HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def `x s < k`
        by (simp add: `!!k. k_mod.SyncMod_HOMachine k ==
        (|CinitState = %p st crd. k_mod.SyncMod_initState k p st, sendMsg = k_mod.SyncMod_sendMsg k,
        CnextState = %p st msgs crd. k_mod.SyncMod_nextState k p st msgs, HOcommPerRd = k_mod.SyncMod_commPerRd,
        HOcommGlobal = k_mod.SyncMod_commGlobal, HOcommSchedule = k_mod.SyncMod_commSchedule |)` k_mod.SyncMod_sendMsg_def)
    thus ?thesis 
        using HOrcvdMsgs_def[of _ q "HO (Suc r) p" "rho r"] assms(1) `rho r p = Active s` k_mod.xi_nek_def[of HO p]
        by (simp add:HOrcvdMsgs_def k_mod.xi_nek_def)
qed

lemma A2 : assumes "k_mod.xi_nek HO xi"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "rho r xi = Active s"
and "x s = k - 1"
and "k > 2"
shows "monovalent rho 0 r"
proof -
    have "ALL p ss st. rho r p = Active ss --> rho (Suc r) p = Active st --> x st = 0"
    proof (rule+)
        fix p
        fix ss
        fix st
        assume "rho r p = Active ss"
        assume "rho (Suc r) p = Active st"
        let ?msgs = "HOrcvdMsgs ?A p (HO (Suc r) p) (rho r)"
        have "k_mod.SyncMod_sendMsg k xi p s = Val (x s)"
            using  k_mod.SyncMod_sendMsg_def[of k xi p s] `x s = k - 1` `k > 2` by simp
        hence "?msgs xi = Content (Val (x s))"
            using sending_rec[of xi HO r p k rho s] assms(1) assms(3) run k_mod.xi_nek_def `x s = k - 1` `k > 2`
            by (metis SendVal.distinct(1) diff_le_self k_mod.SyncMod_sendMsg_def nat_less_le)
        hence non_forc:"~ (k_mod.ready_force k ?msgs ss)"
                using k_mod.ready_force_def[of k ?msgs ss] `x s = k-1` by auto
        have "CnextState ?A p ss ?msgs undefined st" 
            using HORun_def CHORun_def run CHOnextConfig_def[of ?A "rho r" _ _ "rho (Suc r)"]
            `rho r p = Active ss`
            `rho (Suc r) p = Active st` by fastforce
        hence "k_mod.SyncMod_nextState k p ss ?msgs st"
            using HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def[of k]
            by (simp add: k_mod.simp_nextState)
        hence "Suc (x s) mod k >= x st" using `?msgs xi = Content (Val (x s))` 
            k_mod.SyncMod_nextState_def[of k p ss ?msgs st] non_forc by auto
        thus "x st = 0" using `x s = k - 1` `k > 2` by auto
    qed
    thus "monovalent rho 0 r" using monovalent_def[of rho 0 r] by auto
qed

lemma A3 : assumes "k_mod.xi_nek HO xi"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "rho r xi = Active s"
and "k > 2"
and "monovalent rho (v mod k) r"
shows "monovalent rho ((v+i) mod k) (r+i)"
proof (induction i)
    from assms(5) show "monovalent rho ((v+0) mod k) (r+0)" by auto
next
    case (Suc i)
    let "?msgs p" = "(HOrcvdMsgs ?A p (HO (Suc (r+Suc i)) p) (rho (r+Suc i)))"
    have no_discord:"ALL p q vv. ?msgs p q = Content (Val vv) --> vv = (v+i) mod k"
    proof (rule+)
        fix p q vv
        assume "?msgs p q = Content (Val vv)"
        then obtain s ss where " rho (r+i) q = Active s & rho (r+Suc i) q = Active ss & x ss = vv"
            using run sending[of k rho HO p "r+i" q vv] by auto
        thus "vv = (v+i) mod k"
            using Suc.IH monovalent_def[of rho "(v+i) mod k" "r+i"] by auto
    qed

    obtain sx where "rho (r+i) xi = Active sx"
        using run HORun_def assms(3) nonAsleepAgain[of rho r xi ?A HO _ i] by fastforce
    moreover obtain sxx where sxx:"rho (Suc (r+i)) xi = Active sxx" 
        using run HORun_def assms(3) nonAsleepAgain[of rho r xi ?A HO _ "i+1"] by fastforce
    ultimately have "x sxx = (v+i) mod k" using Suc.IH monovalent_def[of rho "(v+i) mod k" "r+i" ] by auto
    hence "ALL p. ?msgs p xi = Content (Val ((v+i) mod k))" (is "ALL p. ?msgs p xi = _")
        using sending_rec[of xi HO "r+Suc i" _ k rho sxx] assms sxx by (simp add:k_mod.xi_nek_def )

    have "ALL p ss st. rho (r+Suc i) p = Active ss --> rho (Suc (r+Suc i)) p = Active st --> x st = (v + Suc i) mod k"
    proof (rule+)
        fix p ss st
        assume "rho (r+Suc i) p = Active ss" and "rho (Suc (r+Suc i)) p = Active st"
        hence "k_mod.SyncMod_nextState k p ss (?msgs p) st" using run transition[of rho "r+Suc i" p ss st k HO] `k > 2` by blast
        show "x st = (v + Suc i) mod k"
        proof (cases "k_mod.ready_force k (?msgs p) ss")
            case True
            hence "EX p1 p2 v1 v2. (?msgs p) p1 = Content (Val v1) & (?msgs p) p2 = Content (Val v2) & v1 ~= v2"
                using k_mod.ready_force_def by blast
            then obtain p1 p2 v1 v2 where "(?msgs p) p1 = Content (Val v1)" and
                                          "(?msgs p) p2 = Content (Val v2)" and "v1 ~= v2" by auto
            then obtain s1 s2 ss1 ss2 where "rho (r+i) p1 = Active s1" and "rho (r+Suc i) p1 = Active ss1 & x ss1 = v1" and
                                            "rho (r+i) p2 = Active s2" and "rho (r+Suc i) p2 = Active ss2 & x ss2 = v2"
                using run sending[of k rho HO p "r+i" p1 v1] sending[of k rho HO p "r+i" p2 v2] by auto
            hence "v1 = (v+i) mod k" and "v2 = (v+i) mod k" using Suc.IH monovalent_def[of rho "(v+i) mod k" "r+i"] by auto
            thus "x st = (v + Suc i) mod k" using `v1 ~= v2` by auto
        next
            case False
            moreover from `ALL p. ?msgs p xi = Content (Val ((v+i) mod k))` have "~ (ALL q v. (?msgs p) q ~= Content (Val v))" by auto
            ultimately have "EX q v. ?msgs p q = Content (Val v) & Suc v mod k = x st"
              using `k_mod.SyncMod_nextState k p ss (?msgs p) st`
              unfolding k_mod.SyncMod_nextState_def by fastforce
            hence "Suc ((v+i) mod k) mod k = x st" using no_discord by auto
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
    have "EX n. Schedule rho n = UNIV" using commS by (simp add:k_mod.SyncMod_HOMachine_def k_mod.SyncMod_commSchedule_def )
    then obtain n :: nat where "ALL p. rho n p ~= Asleep"
      unfolding Schedule_def by auto

    have "monovalent rho 0 r" using A2 assms by auto
    moreover have "(0+(n+1)*k-1) mod k = k-1"
        by (smt Suc_diff_1 add.commute add.left_neutral add_diff_inverse_nat diff_Suc_1 diff_add_zero
        mod_Suc mod_mult_self2_is_0 no_zero_divisors zero_eq_add_iff_both_eq_0 zero_neq_one)
    ultimately have monoval:"monovalent rho ((k-1) :: nat) ((r+(n+1)*k-1) :: nat)" 
        using A3[where ?v = 0 and ?i = "(n+1)*k-1" and ?r = r] assms 
        by (metis (no_types, lifting) add.left_neutral less_one linorder_not_less mod_mult_self1 mod_mult_self2_is_0
        no_zero_divisors not_less0 ordered_cancel_comm_monoid_diff_class.add_diff_assoc zero_eq_add_iff_both_eq_0)
    have "ALL p. EX rf sf. rho rf p = Active sf & fire sf"
    proof (rule allI impI)+
        fix p
        have "r + (n+1)*(k-1) = r + ((n+1)*k-1) - n" (is "_ = ?rd - n")
            using `k > 2` by (smt Groups.mult_ac(2) Nat.add_diff_assoc2 add.commute add_diff_inverse_nat diff_Suc_Suc
            less_one linorder_not_less mod_if mod_mult_self2_is_0 mult.right_neutral no_zero_divisors not_less0 plus_1_eq_Suc
            right_diff_distrib' zero_eq_add_iff_both_eq_0)
        hence "?rd >= n" using `k > 2`
            by (metis add_gr_0 add_lessD1 less_imp_le_nat mult_pos_pos one_add_one zero_less_diff zero_less_one)
        then obtain ss where "rho (Suc ?rd) p = Active ss" 
            using run HORun_def nonAsleepAgain[of rho n p _ _ _ "Suc ?rd - n"] using `ALL p. rho n p ~= Asleep` by fastforce
        moreover from this obtain st where "rho (Suc (Suc ?rd)) p = Active st"
            using nonAsleepAgain[of rho "Suc ?rd" p _ _ _ 1] run HORun_def Suc_diff_1 by fastforce
        ultimately have nxt:"k_mod.SyncMod_nextState k p ss (HOrcvdMsgs ?A p (HO (Suc (Suc ?rd)) p) (rho (Suc ?rd))) st"
            (is "k_mod.SyncMod_nextState  _ _ _ ?msgs _")
            using transition[of rho "Suc ?rd" p ss st] run assms(5) by auto
        have "ALL q. ?msgs q = Void | ?msgs q = Content (Val (k-1))"
        proof
            fix q
            obtain sq where "rho ?rd q = Active sq"
                using run HORun_def nonAsleepAgain[of rho n q _ _ _ "?rd - n"] using `ALL p. rho n p ~= Asleep` `?rd >= n` by fastforce
            moreover obtain sqq where "rho (Suc ?rd) q = Active sqq"
                using run HORun_def nonAsleepAgain[of rho n q _ _ _ "Suc ?rd - n"] using `ALL p. rho n p ~= Asleep` `?rd >= n` by fastforce
            ultimately have "x sqq = k-1"
                using assms monovalent_def[of rho "k-1" ?rd] monoval assms(5) by auto

            hence "k_mod.SyncMod_sendMsg k q p sqq = Val (k-1)"
                using k_mod.SyncMod_sendMsg_def[of k q p sqq] `k > 2` by auto 
            hence "sendMsg ?A q p sqq = Val (k-1)"
                using k_mod.SyncMod_HOMachine_def HOMachine_to_Algorithm_def
                by (simp add: `\<And>k. k_mod.SyncMod_HOMachine k == (| CinitState = %p st crd. k_mod.SyncMod_initState k p st,
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
    thus "k_mod.liveness rho" using k_mod.liveness_def by fastforce
qed

definition round_force where
"round_force rho p == Eps (%r. EX sa saa. rho r p = Active sa & (~ forc sa) & rho (Suc r) p = Active saa & forc saa)"

lemma nonForceAgain : assumes "round_force rho p < n"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "rho n p = Active sr"
and "rho (Suc n) p = Active s"
and "k > 2"
shows "~ k_mod.ready_force k (HOrcvdMsgs ?A p (HO (Suc n) p) (rho n)) sr" (is "~ k_mod.ready_force k ?msgs sr")
proof (cases "EX r sa saa. rho r p = Active sa & (~ forc sa) & rho (Suc r) p = Active saa & forc saa")
    case True
    then obtain r where "EX sa saa. rho r p = Active sa & (~ forc sa) & rho (Suc r) p = Active saa & forc saa" by auto
    then obtain sa saa where rd_forc:"rho (round_force rho p) p = Active sa & (~ forc sa) & rho (Suc (round_force rho p)) p = Active saa & forc saa"
        using round_force_def[of rho p]  someI[of "%r. EX sa saa. rho r p = Active sa & (~ forc sa) & rho (Suc r) p = Active saa & forc saa" r] by auto 
    have "ALL i ss. rho (Suc i + round_force rho p) p = Active ss --> forc ss"
    proof (rule allI)+
        fix i ss
        show "rho (Suc i + round_force rho p) p = Active ss --> forc ss"
        proof (induction i arbitrary:ss)
            case 0
            thus "rho (Suc 0 + round_force rho p) p = Active ss --> forc ss" using rd_forc by auto
        next
            case (Suc ii)
            moreover obtain st where "rho (Suc ii + round_force rho p) p = Active st" 
                using nonAsleepAgain[of rho "round_force rho p" p ?A HO _ "Suc ii"] run HORun_def rd_forc by (metis add.commute proc_state.distinct(1))
            ultimately have "forc st" using add.commute[of "Suc ii" "round_force rho p"] by auto
            show "rho (Suc (Suc ii) + round_force rho p) p = Active ss --> forc ss" 
            proof
                assume "rho (Suc (Suc ii) + round_force rho p) p = Active ss" 
                hence "k_mod.SyncMod_nextState k p st (HOrcvdMsgs ?A p (HO (Suc (Suc ii + round_force rho p)) p) (rho (Suc ii + round_force rho p))) ss"
                    using transition[of rho "Suc ii + round_force rho p" p st ss k HO] `2 < k` run `rho (Suc ii + round_force rho p) p = Active st` by auto
                thus "forc ss" using `forc st` k_mod.SyncMod_nextState_def by auto
            qed
        qed
    qed
    hence "ALL s. rho n p = Active sr --> forc sr"
        using assms(1) allE[of "%i. ALL ss. rho (Suc i + round_force rho p) p = Active ss --> forc ss" "n - Suc (round_force rho p)"] by auto
    thus ?thesis using k_mod.ready_force_def[of k ?msgs sr] by (metis assms(3))
next
    case False
    hence "~ forc s | forc sr" using assms(3) assms(4) by auto
    thus ?thesis
    proof
        assume "~ forc s"
        have "k_mod.SyncMod_nextState k p sr ?msgs s" using transition[of rho n p sr s k HO] assms by auto
        thus ?thesis using k_mod.SyncMod_nextState_def[of k p sr _ s] by (simp add:`~ forc s` k_mod.ready_force_def)
    next
        assume "forc sr"
        thus ?thesis using k_mod.ready_force_def[of k _ sr] by auto
    qed
qed

lemma neverForce : assumes "~ (EX sa saa. rho (round_force rho xi) xi = Active sa & (~ forc sa) & rho (Suc (round_force rho xi)) xi = Active saa & forc saa)"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
shows "ALL i. rho i xi = Active st --> ~ forc st"
proof
    fix i
    show "rho i xi = Active st --> ~ forc st"
    proof (induction i arbitrary:st)
        case 0
        show "rho 0 xi = Active st --> ~ forc st" using assms starting[of 0 rho xi ] by auto
    next
        case (Suc ii)
        show "rho (Suc ii) xi = Active st --> ~ forc st"
        proof (cases "rho ii xi")
            case Asleep
            thus "rho (Suc ii) xi = Active st --> ~ forc st" using run starting[of "Suc ii" rho xi ] by auto
        next
            case (Active sxi)
            moreover have "ALL sa saa l. rho l xi = Active sa --> (~ forc sa) --> rho (Suc l) xi = Active saa --> (~ forc saa)"
                using assms(1)
                someI_ex[of "%l. EX sa saa. rho l xi = Active sa & (~ forc sa) & rho (Suc l) xi = Active saa & forc saa"]
                round_force_def by (smt Eps_cong)
            ultimately show "rho (Suc ii) xi = Active st --> ~ forc st" using Suc.IH[of sxi] by auto
        qed
    qed
qed

lemma A5 : assumes "k_mod.xi_nek HO xi"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "rho r xi ~= Asleep"
and "rho (Suc r) xi = Active sxi"
and "k > 2"
and commS:"HOcommSchedule (k_mod.SyncMod_HOMachine k) (Schedule rho)"
and "ALL p. round_force rho p < Suc r"
and "rho (Suc r) p = Active sp"
and "rho (Suc (Suc r)) p = Active spp"
shows "x spp <= (Suc (x sxi)) mod k"
proof -
    from assms(3) obtain s where "rho r xi = Active s" by (cases "rho r xi") auto
    have nxt:"k_mod.SyncMod_nextState k p sp (HOrcvdMsgs ?A p (HO (Suc (Suc r)) p) (rho (Suc r))) spp" (is "k_mod.SyncMod_nextState k p sp (?msgs p) spp")
        using transition[of rho "Suc r" p sp spp k HO] assms by auto
    obtain sx where "rho (Suc r) xi = Active sx" using run HORun_def nonAsleepAgain[of rho r xi _ _ _ 1] assms(3) by fastforce
    hence "x sxi < k" and "x sx < k" using `rho r xi = Active s` transition run assms by auto
    have "~ k_mod.ready_force k (?msgs p) sp" using nonForceAgain[of rho p "Suc r" k HO sp spp] `k > 2` assms(8) assms(9) assms(7) run less_SucI by blast
    moreover have "?msgs p xi = Content (Val (x sxi))"
        using sending_rec[of xi HO "Suc r" p k rho sxi] assms(1) `rho (Suc r) xi = Active sxi` run k_mod.xi_nek_def `x sxi < k` by metis
    ultimately show ?thesis using k_mod.SyncMod_nextState_def `k > 2` nxt by auto
qed

lemma A6 : assumes "k_mod.xi_nek HO xi"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "rho r xi = Active s"
and "monovalent rho (v mod k) r"
and "k > 2"
assumes commS:"HOcommSchedule (k_mod.SyncMod_HOMachine k) (Schedule rho)"
shows "k_mod.liveness rho"
proof -
    have "monovalent rho ((v+(k - 1 - v mod k)) mod k) (r+(k - 1 - v mod k))" using A3[of HO xi k rho ] assms by auto
    hence "monovalent rho (k-1) (r+(k - 1 - v mod k))"
        by (smt One_nat_def Suc_leI assms(5) diff_diff_cancel diff_is_0_eq mod_add_left_eq mod_less
        mod_less_divisor not_less ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc zero_less_Suc)
    moreover have "rho (r+(k - 1 - v mod k)) xi ~= Asleep" using nonAsleepAgain[of rho r xi _ _ _ "k - 1 - v mod k"] assms(3) run HORun_def
        by (smt add.commute proc_state.distinct(1))
    then obtain sxi where sxi_def:"rho (r+(k - 1 - v mod k)) xi = Active sxi" by (cases "rho (r+(k - 1 - v mod k)) xi") auto
    moreover from this have "rho (Suc (r+(k - 1 - v mod k))) xi ~= Asleep" using nonAsleepAgain[of rho "r+(k - 1 - v mod k)" xi _ _ _ 1] run HORun_def by fastforce
    then obtain sxii where sxii_def:"rho (Suc (r+(k - 1 - v mod k))) xi = Active sxii" by (cases "rho (Suc (r+(k - 1 - v mod k))) xi") auto
    ultimately have "x sxii = k-1" using monovalent_def[of rho "k-1" "r+(k - 1 - v mod k)"] assms(3) by auto
    thus ?thesis using A4 assms sxi_def sxii_def by auto
qed

lemma A7 : assumes run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "rho r xi = Active s"
and "rho (Suc r) xi = Active ss"
and "HOrcvdMsgs (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) xi (HO (Suc r) xi) (rho r) p = Content (Val (k-1))" (is "?msgs p = _")
and "k > 2"
and "round_force rho xi < r"
shows "x ss = 0"
proof -
    have nforc:"~ k_mod.ready_force k ?msgs s" using nonForceAgain[of rho xi r k HO s ss] assms by auto
    have nxt:"k_mod.SyncMod_nextState k xi s ?msgs ss" using transition[of rho r xi s ss k HO] assms by auto
    hence "ALL q v. ?msgs q = Content (Val v) --> Suc v mod k >= x ss" using k_mod.SyncMod_nextState_def nforc by auto
    thus ?thesis using `?msgs p = Content (Val (k-1))` `k > 2` by fastforce
qed

lemma A8 : assumes "k_mod.xi_nek HO xi"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "k > 2"
and "n > 4"
and rd:"ALL p. round_force rho p < n - 4"
and sxx:  "rho (n-3) xi = Active sxx"
and sxs:  "rho (n-2) xi = Active sxs"
and ss:   "rho (n-1) xi = Active ss"
and sxiii:"rho n xi = Active sxiii"
and sxii: "rho (Suc n) xi = Active sxii"
and non_forc:"~ (EX sa saa. rho (round_force rho xi) xi = Active sa & (~ forc sa) & rho (Suc (round_force rho xi)) xi = Active saa & forc saa)"
and commS:"HOcommSchedule (k_mod.SyncMod_HOMachine k) (Schedule rho)"
and "Suc (n-2) = n-1"
and "Suc (n-3) = n-2"
shows "x sxii = Suc (x sxiii) mod k"
proof -
    let ?msgx = "%p. HOrcvdMsgs ?A xi (HO (Suc (n-1)) xi) (rho (n-1)) p"
    from rd have rd3:"ALL p. round_force rho p < n - 3"
        by (metis One_nat_def Suc_diff_Suc Suc_lessD add_Suc assms(4) numeral_3_eq_3 numeral_Bit0 one_add_one plus_1_eq_Suc trans_less_add2)
    hence rd2:"ALL p. round_force rho p < n - 2"
        by (metis One_nat_def Suc_diff_Suc Suc_lessD add_Suc assms(4) numeral_3_eq_3 numeral_Bit0 one_add_one plus_1_eq_Suc trans_less_add2)
    hence rd1:"ALL p. round_force rho p < n - 1"
        by (metis One_nat_def Suc_diff_Suc Suc_lessD add_Suc assms(4) numeral_Bit0 one_add_one plus_1_eq_Suc trans_less_add2)
    hence rd0:"ALL p. round_force rho p < n"
        by (metis add_Suc add_diff_inverse_nat assms(4) not_less_eq numeral_Bit0 one_add_one trans_less_add2)
    have "k_mod.SyncMod_nextState k xi sxiii (HOrcvdMsgs ?A xi (HO (Suc n) xi) (rho n)) sxii"
        (is "k_mod.SyncMod_nextState k xi sxiii ?msgs sxii")
        using transition[of rho n xi sxiii sxii] run assms by auto
    hence "~ k_mod.ready_force k ?msgs sxiii" using run nonForceAgain[of rho xi n k HO sxiii sxii] `k > 2` sxiii sxii rd0 by auto
    hence "forc sxiii |
        (EX p. ?msgs p = Content (Val (k-1))) |
        (ALL p q v1 v2. ?msgs p = Content (Val v1) --> ?msgs q = Content (Val v2) --> v1 = v2)"
        using k_mod.ready_force_def[of k ?msgs sxiii] by auto
    thus ?thesis
    proof
        assume "forc sxiii"
        thus ?thesis using neverForce[of rho xi k HO sxiii] run non_forc sxiii by auto
    next
        assume "(EX p. ?msgs p = Content (Val (k-1))) |
            (ALL p q v1 v2. ?msgs p = Content (Val v1) --> ?msgs q = Content (Val v2) --> v1 = v2)"
        thus ?thesis 
        proof
            assume "EX p. ?msgs p = Content (Val (k-1))"
            then obtain p where "?msgs p = Content (Val (k-1))" by auto
            hence "x sxii = 0" using A7[of k rho HO n xi sxiii sxii p] assms sxii sxiii using rd0 by auto
            obtain sp spp where sp:"rho (n-1) p = Active sp" and spp:"rho n p = Active spp" and "x spp = k - 1"
                using sending[of k rho HO xi "n-1" p "k-1"] assms `?msgs p = Content (Val (k-1))` by auto
            hence "x spp <= Suc (x ss) mod k"
                using A5[of HO xi k rho "n-2" ss p sp spp] assms rd1 by auto
            hence "k-1 = Suc (x ss) mod k"
                using `k > 2` `x spp = k-1` by (metis Suc_diff_1 le_less_Suc_eq less_Suc_eq_0_disj less_imp_Suc_add mod_less_divisor)
            moreover have "x ss < k" using transition assms ss by auto
            ultimately have "x ss = k - 2" using `k > 2`
                by (metis Suc_lessI add_lessD1 diff_Suc_1 diff_diff_left less_numeral_extra(3) mod_less mod_self one_add_one zero_less_diff)
            have "ALL q. ?msgx q ~= Content (Val (k-1))" 
            proof (rule+)
                fix q
                assume "?msgx q = Content (Val (k-1))"
                (*hence "x sxiii = 0" using A7[of k rho HO "n-1" xi ss sxiii q] rd2 ss sxiii `k > 2` run by auto*)
                then obtain sq sqq where sq:"rho (n-2) q = Active sq" and sqq:"rho (n-1) q = Active sqq" and "x sqq = k-1"
                    using sending[of k rho HO xi "n-2" q "k-1"] assms by auto
                hence "x sqq <= Suc (x sxs) mod k"
                    using assms A5[of HO xi k rho "n-3" sxs q sq sqq] sxs rd2 by auto
                hence "k-1 = Suc (x sxs) mod k"
                    using `k > 2` `x sqq = k-1` by (metis Suc_diff_1 le_less_Suc_eq less_Suc_eq_0_disj less_imp_Suc_add mod_less_divisor)
                
                moreover have "x sxs < k" using assms transition[of rho "n-3" xi sxx sxs k HO] sxs by auto
                ultimately have "x sxs = k-2" by (smt Suc_1 Suc_inject assms(3) diff_Suc_Suc
                    less_imp_le_nat mod_Suc mod_if nat.simps(3) ordered_cancel_comm_monoid_diff_class.add_diff_assoc plus_1_eq_Suc)
                let ?msg1 = "%p. HOrcvdMsgs ?A xi (HO (Suc (n-2)) xi) (rho (n-2)) p"
                have nxt:"k_mod.SyncMod_nextState k xi sxs ?msg1 ss"
                    using transition[of rho "n-2" xi sxs ss k] assms by auto
                have nfor:"~ k_mod.ready_force k ?msg1 sxs"
                    using rd2 nonForceAgain[of rho xi "n-2" k HO sxs ss] assms by auto
                hence "ALL qq. ?msg1 qq = Content (Val (k-1)) --> x ss <= Suc (k-1) mod k" using nxt by (simp add:k_mod.SyncMod_nextState_def)
                hence "ALL qq. ?msg1 qq ~= Content (Val (k-1))" using `x ss = k-2` `k > 2` by auto

                have "?msg1 xi = Content (Val (k-2))" 
                    using sending_rec[of xi HO "n-2" xi k rho sxs] assms `x sxs = k-2`
                    by (metis `x sxs < k` k_mod.xi_nek_def)
                then obtain qq v where "?msg1 qq = Content (Val v)" and "Suc v mod k = k-2" using `x ss = k - 2` nxt nfor k_mod.SyncMod_nextState_def by fastforce
                have "EX ssqq sssqq. rho (n-3) qq = Active ssqq & rho (n-2) qq = Active sssqq & x sssqq = v"
                    using sending[of k rho HO xi "n-3" qq v] `?msg1 qq = Content (Val v)` run `k > 2` assms(14) by simp
                hence "v < k" using transition assms by auto
                hence "?msg1 qq = Content (Val (k-3))" using `k > 2` `?msg1 qq = Content (Val v)` `Suc v mod k = k-2`
                    by (smt Suc_diff_Suc diff_Suc_1 diff_is_0_eq linorder_not_less mod_Suc mod_if numeral_3_eq_3 one_add_one plus_1_eq_Suc)
                hence "EX p1 p2 v1 v2. ?msg1 p1 = Content (Val v1) & ?msg1 p2 = Content (Val v2) & v1 ~= v2" using `?msg1 xi = Content (Val (k-2))` `k > 2` by fastforce
                hence "forc sxs" using nfor `ALL qq. ?msg1 qq ~= Content (Val (k-1))` k_mod.ready_force_def[of k ?msg1 sxs] `k > 2` by auto
                thus "False" using neverForce[of rho xi k HO sxs] run non_forc sxs by auto
            qed
            moreover have "~ k_mod.ready_force k ?msgx ss" using run nonForceAgain[of rho xi "n-1" k HO ss sxiii] `k > 2` ss sxiii rd1 by (simp add: nat_diff_split)
            ultimately have "forc ss | (ALL p q v1 v2. ?msgx p = Content (Val v1) --> ?msgx q = Content (Val v2) --> v1 = v2)"
                using k_mod.ready_force_def[of k ?msgx ss] by auto
            thus ?thesis
            proof
                assume "forc ss"
                thus ?thesis using neverForce[of rho xi k HO ss] run non_forc ss by auto
            next
                assume "ALL p q v1 v2. ?msgx p = Content (Val v1) --> ?msgx q = Content (Val v2) --> v1 = v2"
                moreover have "?msgx xi = Content (Val (k-2))"
                    using ` x ss = k - 2` sending_rec[of xi HO "n-1" xi k rho ss] `k_mod.xi_nek HO xi` `k > 2` ss `n > 4`
                    by (simp add: k_mod.xi_nek_def run less_natE)
                ultimately have "ALL p v. ?msgx p = Content (Val v) --> v = k - 2" by auto
                have "k_mod.SyncMod_nextState k xi ss ?msgx sxiii"
                    using transition[of rho "n-1" xi ss sxiii k] assms by auto
                hence "EX q v. ?msgx q = Content (Val v) & Suc v mod k = x sxiii"
                  using `?msgx xi = Content (Val (k-2))` `~ k_mod.ready_force k ?msgx ss`
                  unfolding k_mod.SyncMod_nextState_def by fastforce
                hence "EX v. v = k - 2 & Suc v mod k = x sxiii" using `ALL p v. ?msgx p = Content (Val v) --> v = k - 2` by auto
                hence "x sxiii = k - 1" using `k > 2` by fastforce
                thus ?thesis using `x sxii = 0` `k > 2` by auto
            qed
        next
            assume "ALL p q v1 v2. ?msgs p = Content (Val v1) --> ?msgs q = Content (Val v2) --> v1 = v2"
            moreover have "x sxiii < k" 
                using transition[of rho "n-1" xi ss sxiii k] assms by auto
            hence "?msgs xi = Content (Val (x sxiii))"
                using sending_rec[of xi HO n xi k rho sxiii] `k_mod.xi_nek HO xi` `k > 2` sxiii `n > 4`
                by (simp add: k_mod.xi_nek_def run less_natE)
            ultimately have "ALL p v. ?msgs p = Content (Val v) --> v = x sxiii" by auto
            have "k_mod.SyncMod_nextState k xi sxiii ?msgs sxii"
                using transition[of rho n xi sxiii sxii k] assms by auto
            moreover have "~ k_mod.ready_force k ?msgs sxiii"
                using run nonForceAgain[of rho xi n k HO sxiii sxii] `k > 2` sxii sxiii rd0 by simp 
            ultimately have "EX q v. ?msgs q = Content (Val v) & Suc v mod k = x sxii"
              using `?msgs xi = Content (Val (x sxiii))`
              unfolding k_mod.SyncMod_nextState_def by fastforce
            hence "EX v. v = x sxiii & Suc v mod k = x sxii" using `ALL p v. ?msgs p = Content (Val v) --> v = x sxiii` by auto
            thus ?thesis by auto
        qed
    qed
qed
                                            
lemma SyncMod_safety : assumes "k_mod.xi_nek HO xi"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "k > 2"
assumes commS:"HOcommSchedule (k_mod.SyncMod_HOMachine k) (Schedule rho)"
shows "k_mod.safety k rho"
proof -
    have monov:"ALL p r s ss. rho r p = Active s --> rho (Suc r) p = Active ss --> fire ss --> ~ fire s --> monovalent rho 0 r & rho r xi ~= Asleep"
    proof (rule+)
        fix p r s ss
        assume s:"rho r p = Active s" and ss:"rho (Suc r) p = Active ss" and "fire ss" and "~ fire s" 
        show "monovalent rho 0 r" and "rho r xi ~= Asleep"
        proof -
            let ?msgs = "%q. HOrcvdMsgs ?A p (HO (Suc r) p) (rho r) q"
            have "k_mod.SyncMod_nextState k p s ?msgs ss"
                using transition[of rho r p s ss k] assms s ss by auto
            hence "k_mod.ready_fire k ?msgs" using k_mod.SyncMod_nextState_def `fire ss` `~ fire s` by auto
            hence "?msgs xi = Content (Val (k-1))" using k_mod.xi_nek_def `k_mod.xi_nek HO xi` k_mod.ready_fire_def HOrcvdMsgs_def
                by (metis HOrcvMsgs_q.elims message.distinct(3) message.distinct(5))
            hence "rho r xi ~= Asleep" using HOrcvdMsgs_def[of ?A p "HO (Suc r) p" "rho r"] assms by auto
            have "r ~= 0"
            proof
                assume "r = 0"
                then obtain sz where sz:"rho 0 xi = Active sz" using `rho r xi ~= Asleep` by (cases "rho 0 xi") auto
                hence "?msgs xi = (if xi : HO (Suc 0) p then Content Nope else Void)"
                  using starting[of 0 rho xi k HO sz] s assms `r = 0` by auto
                thus "False" using `?msgs xi = Content (Val (k-1))` by auto
            qed
            then obtain sx sxx where "rho (r-1) xi = Active sx" and "rho r xi = Active sxx" and "x sxx = k-1"
                using `?msgs xi = Content (Val (k-1))` sending[of k rho HO p "r-1" xi "k-1"] run by auto
            thus "monovalent rho 0 r" and "rho r xi ~= Asleep" using A2[of HO xi k rho r sxx] assms by auto
        qed
    qed
    show ?thesis
    proof (cases "EX p r s ss. rho r p = Active s & rho (Suc r) p = Active ss & fire ss & ~ fire s")
        case False
        hence "ALL p rf ss sf. rho rf p = Active ss -->
                    (~ fire ss) --> rho (Suc rf) p = Active sf --> fire sf --> rf mod k = 0" by blast
        hence "EX c. ALL p rf ss sf. rho rf p = Active ss -->
                    (~ fire ss) --> rho (Suc rf) p = Active sf --> fire sf --> rf mod k = c" by auto
        thus ?thesis by (simp add:k_mod.safety_def)
    next
        case True
        then obtain p r s ss where s:"rho r p = Active s" and ss:"rho (Suc r) p = Active ss" and "fire ss" and "~ fire s" by auto
        hence "monovalent rho 0 r" and "rho r xi ~= Asleep" using monov by auto
        then obtain sx where "rho r xi = Active sx" by (cases "rho r xi") auto
        have "ALL p rf ss sf. rho rf p = Active ss -->
                    (~ fire ss) --> rho (Suc rf) p = Active sf --> fire sf --> rf mod k = r mod k"
        proof (rule+)
            fix q rq sq sqq
            assume sq:"rho rq q = Active sq" and sqq:"rho (Suc rq) q = Active sqq" and "~ fire sq" and "fire sqq"
            hence "monovalent rho 0 rq" and "rho rq xi ~= Asleep" using monov by auto
            then obtain sxq where "rho rq xi = Active sxq" by (cases "rho rq xi") auto
            show "rq mod k = r mod k" 
            proof (cases "rq > r")
                case True
                hence "monovalent rho ((rq-r) mod k) rq" using A3[of HO xi k rho r sx 0 "rq-r"] assms `monovalent rho 0 r` `rho r xi = Active sx` by auto
                hence "x sqq = (rq-r) mod k" using monovalent_def[of rho "(rq-r) mod k" rq] sq sqq by auto
                moreover have "x sqq = 0" using monovalent_def[of rho 0 rq] `monovalent rho 0 rq` sq sqq by auto
                ultimately show ?thesis by (metis True mod_eq_dvd_iff_nat mod_greater_zero_iff_not_dvd nat_less_le)
            next
                case False
                hence "monovalent rho ((r-rq) mod k) r" using A3[of HO xi k rho rq sxq 0 "r-rq"] assms `monovalent rho 0 rq` `rho rq xi = Active sxq` by auto
                hence "x ss = (r-rq) mod k" using monovalent_def[of rho "(r-rq) mod k" r] s ss by auto
                moreover have "x ss = 0" using monovalent_def[of rho 0 r] `monovalent rho 0 r` s ss by auto
                ultimately show ?thesis by (metis False less_numeral_extra(3) linorder_not_less mod_eq_dvd_iff_nat mod_greater_zero_iff_not_dvd)
            qed
        qed
        hence "EX c. ALL p rf ss sf. rho rf p = Active ss -->
                    (~ fire ss) --> rho (Suc rf) p = Active sf --> fire sf --> rf mod k = c" by auto
        thus ?thesis using k_mod.safety_def by auto
    qed
qed


lemma SyncMod_liveness : assumes "k_mod.xi_nek HO xi"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "k > 2"
assumes commS:"HOcommSchedule (k_mod.SyncMod_HOMachine k) (Schedule rho)"
shows "k_mod.liveness rho"
proof -
    let ?txi = "round_force rho xi"
    show ?thesis
    proof (cases "EX sa saa. rho ?txi xi = Active sa & (~ forc sa) & rho (Suc ?txi) xi = Active saa & forc saa")
        case True
        then obtain sx sxx where "rho ?txi xi = Active sx" and "~ forc sx" and "rho (Suc ?txi) xi = Active sxx" and "forc sxx" by auto
        hence nxt:"k_mod.SyncMod_nextState k xi sx (HOrcvdMsgs ?A xi (HO (Suc ?txi) xi) (rho ?txi)) sxx" (is "SyncMod.k_mod.SyncMod_nextState k xi sx ?msgs sxx")
            using transition[of rho ?txi xi sx sxx k HO] assms by auto
        hence "k_mod.ready_force k ?msgs sx" using k_mod.SyncMod_nextState_def `~ forc sx` `forc sxx` by auto
        hence "x sxx = k-1" using nxt k_mod.SyncMod_nextState_def[of k xi sx _ sxx] by auto
        thus ?thesis using A4 `rho (Suc ?txi) xi = Active sxx` assms by auto
    next
        case False
        have "EX n. Schedule rho n = UNIV" using commS by (simp add:k_mod.SyncMod_HOMachine_def k_mod.SyncMod_commSchedule_def )
        then obtain n :: nat where "ALL p. rho n p ~= Asleep" unfolding Schedule_def by auto
        let ?n = "Suc (Suc (Suc (Suc (Suc n)))) + Sum ( (round_force rho) ` UNIV)"
        obtain sxi where "rho ?n xi = Active sxi" 
            using nonAsleepAgain[of rho n xi _ _ _ "Suc (Suc (Suc (Suc (Suc (Sum ( (round_force rho) ` UNIV))))))"] run HORun_def `ALL p. rho n p ~= Asleep`
            by (smt add.commute add_Suc_shift)
        show ?thesis
        proof (cases "EX v :: nat. v < k & monovalent rho v ?n")
            case True
            thus ?thesis using A6[of HO xi k rho ?n sxi] assms `rho ?n xi = Active sxi` by (metis mod_if)
        next
            case False
            have escalier:"ALL i sxii. rho (?n + i) xi = Active sxii --> x sxii = (x sxi + i) mod k"
            proof (rule allI)+
                fix i sxii
                show "rho (?n + i) xi = Active sxii --> x sxii = (x sxi + i) mod k"
                proof (induction i arbitrary:sxii)
                    case 0
                    obtain sx where "rho (?n-1) xi = Active sx"
                        using nonAsleepAgain[of rho n xi _ _ _ "Suc (Suc (Suc (Suc (Sum ( (round_force rho) ` UNIV)))))"] run HORun_def `ALL p. rho n p ~= Asleep`
                        by (smt Nat.add_diff_assoc2 add.commute diff_Suc_1 le_add1 plus_1_eq_Suc)
                    hence "x sxi < k" using transition[of rho "?n-1" xi sx sxi] run `rho ?n xi = Active sxi` assms(3) by auto
                    thus "rho (?n + 0) xi = Active sxii --> x sxii = (x sxi + 0) mod k" using `rho ?n xi = Active sxi` by auto
                next
                    case (Suc ii)
                    show "rho (?n + Suc ii) xi = Active sxii --> x sxii = (x sxi + Suc ii) mod k"
                    proof 
                        assume "rho (?n + Suc ii) xi = Active sxii"
                        hence "rho (Suc ?n + ii) xi = Active sxii" by auto
                        moreover have "ALL p. round_force rho p < ?n +ii - 4"
                        proof
                            fix p
                            have rd_forc:"round_force rho p <= Sum ((round_force rho) ` UNIV)"
                                by (meson finite_UNIV finite_imageI le0 range_eqI sum_nonneg_leq_bound)
                            hence "round_force rho p <= Sum ((round_force rho) ` UNIV) + ((Suc (Suc (Suc (Suc n)))) + ii - 4)" using trans_le_add1 by blast
                            moreover have "Suc (Suc (Suc (Suc n))) + ii >= 4" by auto
                            hence " Sum ((round_force rho) ` UNIV) + ((Suc (Suc (Suc (Suc n)))) + ii - 4) =
                                    Sum ((round_force rho) ` UNIV) + (Suc (Suc (Suc (Suc n)))) + ii - 4"
                                using add_diff_assoc[of 4 "Suc (Suc (Suc (Suc n))) + ii" "Sum (range (round_force rho))"] by fastforce
                            ultimately have "round_force rho p <= Sum ((round_force rho) ` UNIV) + (Suc (Suc (Suc (Suc n)))) + ii - 4"
                                by fastforce
                            thus "round_force rho p < ?n + ii - 4" by auto
                        qed
                        moreover obtain sxx where "rho (n+Suc (Suc (Sum ( (round_force rho) ` UNIV)))+ii) xi = Active sxx"
                            using nonAsleepAgain[of rho n xi _ _ _ "Suc (Suc (Sum ((round_force rho) ` UNIV)))+ii"] run HORun_def `ALL p. rho n p ~= Asleep`
                            by (metis add.assoc)
                        hence "rho (?n+ii-3) xi = Active sxx" by fastforce
                        moreover from this obtain sxs where "rho (?n+ii-2) xi = Active sxs"
                            using nonAsleepAgain[of rho "?n+ii-3" xi _ _ _ 1] run HORun_def by fastforce
                        moreover from this obtain ss where "rho (?n+ii-1) xi = Active ss"
                            using nonAsleepAgain[of rho "?n+ii-2" xi _ _ _ 1] run HORun_def by fastforce
                        moreover from this obtain sxiii where "rho (?n+ii) xi = Active sxiii"
                            using nonAsleepAgain[of rho "?n+ii-1" xi _ _ _ 1] run HORun_def by fastforce
                        moreover from `rho (?n+ii) xi = Active sxiii` have "x sxiii = (x sxi + ii) mod k" using Suc.IH[of sxiii] by auto
                        moreover have "Suc (?n + ii - 2) = ?n + ii - 1" by auto
                        moreover have "Suc (?n + ii - 3) = ?n + ii - 2" by auto
                        moreover have "?n+ii > 4" by auto
                        ultimately have "x sxii = Suc (x sxiii) mod k"
                            using A8[of HO xi k rho "?n+ii" sxx sxs ss sxiii sxii] assms
                            `~ (EX sa saa. rho ?txi xi = Active sa & (~ forc sa) & rho (Suc ?txi) xi = Active saa & forc saa)` by fastforce
                        thus "x sxii = (x sxi + Suc ii) mod k" using Suc.IH[of sxiii] `rho (?n+ii) xi = Active sxiii` by presburger
                    qed
                qed
            qed
            obtain sxx where "rho (?n-1) xi = Active sxx" 
                using nonAsleepAgain[of rho n xi _ _ _ "Suc (Suc (Suc (Suc (Suc (Sum (range (round_force rho)))))))-1"]
                run HORun_def add_diff_assoc[of 1 "Suc (Suc (Suc (Suc (Suc (Sum (range (round_force rho)))))))" n] `ALL p. rho n p ~= Asleep`
                by (smt add_Suc add_Suc_shift diff_Suc_1)
            hence "k-1 >= x sxi"
                using transition[of rho "?n-1" xi sxx sxi k] assms `rho ?n xi = Active sxi` by fastforce
            obtain s where "rho (?n+(k-1-x sxi)) xi = Active s"
                using nonAsleepAgain[of rho ?n xi _ _ _ "k-1-x sxi"] run HORun_def `rho ?n xi = Active sxi` by fastforce

            hence "x s = (x sxi + (k-1-x sxi)) mod k" using escalier by auto
            hence "x s = k - 1" using `k - 1 >= x sxi` by (simp add: add_diff_inverse_nat nat_diff_split)
            thus ?thesis using A4[of HO xi k rho "?n+(k-1-x sxi)" s] assms `rho (?n+(k-1-x sxi)) xi = Active s` by auto
        qed
    qed
qed
