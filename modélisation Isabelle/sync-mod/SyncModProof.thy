theory SyncModProof
imports "../HOModel" SyncMod
begin

definition HOMachine_to_Algorithm :: "(Proc, pstate, SendVal) HOMachine \<Rightarrow> (Proc, pstate, SendVal) CHOAlgorithm" where
"HOMachine_to_Algorithm mach = \<lparr> CinitState = CinitState mach, sendMsg = sendMsg mach, CnextState = CnextState mach \<rparr>"


definition monovalent where
"monovalent rho v n \<equiv> \<forall>p ss st. rho n p = Active ss \<longrightarrow> rho (Suc n) p = Active st \<longrightarrow> x st = v"

(*lemma A1 : assumes "rho r p = Active s"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "x s = k-1"
and "p \<in> HO (Suc r) q"
and "rho r q \<noteq> Aslept"
shows "\<forall>st. rho (Suc r) q = Active st \<longrightarrow> x st = 0"
proof (rule+)
    fix st
    assume "rho (Suc r) q = Active st"
    show "x st = 0"
    proof -
        *)
lemma sending : assumes run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A rho HO")
assumes "(HOrcvdMsgs ?A p (HO (Suc r) p) (rho r)) q = Content (Val v)" (is "?msgs q = _")
shows "\<exists>s. rho r q = Active s \<and> x s = v"
proof (cases "rho r q")
    case Aslept
    hence "?msgs q = (if q \<in> HO (Suc r) p then Bot else Void)" using HOrcvdMsgs_def[of ?A p "HO (Suc r) p" "rho r"] by auto
    thus "\<exists>s. rho r q = Active s \<and> x s = v" using \<open>?msgs q = Content (Val v)\<close> by auto
next
    case (Active sq)
    have "sendMsg ?A q p sq = Val (x sq)" using HOrcvdMsgs_def[of ?A p "HO (Suc r) p" "rho r"] \<open>?msgs q = Content (Val v)\<close>
        by (simp add: Active HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def k_mod.SyncMod_sendMsg_def)
    hence "k_mod.SyncMod_sendMsg k q p sq = Val (x sq)"
        using HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def by 
        (simp add: \<open>\<And>k. k_mod.SyncMod_HOMachine k \<equiv> \<lparr>CinitState = \<lambda>p st crd. k_mod.SyncMod_initState k p st,
        sendMsg = k_mod.SyncMod_sendMsg k, CnextState = \<lambda>p st msgs crd. k_mod.SyncMod_nextState k p st msgs,
        HOcommPerRd = k_mod.SyncMod_commPerRd, HOcommGlobal = k_mod.SyncMod_commGlobal,
        HOcommSchedule = k_mod.SyncMod_commSchedule\<rparr>\<close>)
    hence "?msgs q = Content (Val (x sq))" using HOrcvdMsgs_def[of ?A p "HO (Suc r) p" "rho r"] \<open>?msgs q = Content (Val v)\<close>
        by (simp add: Active \<open>sendMsg (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) q p sq = Val (x sq)\<close>)
    hence "rho r q = Active sq \<and> x sq = v"
        using \<open>rho r q = Active sq\<close> \<open>?msgs q = Content (Val v)\<close> k_mod.SyncMod_sendMsg_def[of k q p sq] by auto
    thus "\<exists>s. rho r q = Active s \<and> x s = v"  by auto
qed

lemma transition : assumes s_def:"rho r p = Active s"
and ss_def:"rho (Suc r) p = Active ss"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
shows "k_mod.SyncMod_nextState k p s (HOrcvdMsgs ?A p (HO (Suc r) p) (rho r)) ss" (is "k_mod.SyncMod_nextState  _ _ _ ?msgs _")
proof -
    have "CHOnextConfig ?A (rho r) (HO (Suc r)) (\<lambda>w. undefined) (rho (Suc r))" using run by (simp add:HORun_def CHORun_def)
    then obtain sss where "rho (Suc r) p = Active sss \<and> CnextState ?A p s ?msgs undefined sss" 
        using CHOnextConfig_def[of ?A "rho r" "HO (Suc r)" "\<lambda>w. undefined" "rho (Suc r)"] s_def by fastforce
    hence "CnextState ?A p s ?msgs undefined ss" using ss_def by auto
    thus ?thesis using HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def[of k] by (simp add:k_mod.simp_nextState)
qed

lemma stating : assumes "0 < n \<longrightarrow> rho (n-1) p = Aslept"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "rho n p = Active s"
shows "x s = k" and "\<forall>q. HOrcvdMsgs ?A q (HO (Suc n) q) (rho n) p = (if p \<in> HO (Suc n) q then Content Nope else Void)"
proof -
    have "CHOinitConfig ?A rho (\<lambda>w ww. undefined)"
        using run HORun_def[of ?A rho HO] CHORun_def[of ?A rho HO "\<lambda>w ww. undefined"] by simp
    hence "CinitState ?A p s undefined"
        using CHOinitConfig_def[of ?A rho] \<open>rho n p = Active s\<close> \<open>0 < n \<longrightarrow> rho (n-1) p = Aslept\<close> by auto
    hence "k_mod.SyncMod_initState k p s"
        using HOMachine_to_Algorithm_def by (simp add:k_mod.SyncMod_HOMachine_def)
    hence "x s = k" using k_mod.SyncMod_initState_def[of k p s] by auto
    hence "\<forall>q. k_mod.SyncMod_sendMsg k p q s = Nope"
        using k_mod.SyncMod_sendMsg_def[of k p _ s] by fastforce
    hence "\<forall>q. sendMsg ?A p q s = Nope"
        using HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def by (simp add: k_mod.SyncMod_HOMachine_def)
    hence "\<forall>q. HOrcvdMsgs ?A q (HO (Suc n) q) (rho n) p = (if p \<in> HO (Suc n) q then Content Nope else Void)"
        using HOrcvdMsgs_def[of ?A p "HO (Suc n) p" "rho n"] by (simp add: HOrcvdMsgs_def assms(3))
    thus "x s = k" and "\<forall>q. HOrcvdMsgs ?A q (HO (Suc n) q) (rho n) p = (if p \<in> HO (Suc n) q then Content Nope else Void)"
        using \<open>x s  = k\<close> by auto
qed



lemma A2 : assumes "k_mod.xi_nek HO xi"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "rho r xi = Active s"
and "x s = k - 1"
and "k > 2"
shows "monovalent rho 0 r"
proof -
    have "\<forall>p ss st. rho r p = Active ss \<longrightarrow> rho (Suc r) p = Active st \<longrightarrow> x st = 0"
    proof (rule+)
        fix p
        fix ss
        fix st
        assume "rho r p = Active ss"
        assume "rho (Suc r) p = Active st"
        show "x st = 0"
        proof (rule ccontr)
            assume "x st \<noteq> 0"
            let ?msgs = "HOrcvdMsgs ?A p (HO (Suc r) p) (rho r)"
            have "k_mod.SyncMod_sendMsg k xi p s = Val (x s)"
                using  k_mod.SyncMod_sendMsg_def[of k xi p s] \<open>x s = k - 1\<close> \<open>k > 2\<close> by simp
            hence "sendMsg ?A xi p s = Val (x s)"
                using HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def 
                by (simp add: \<open>\<And>k. k_mod.SyncMod_HOMachine k \<equiv> \<lparr>CinitState = \<lambda>p st crd. k_mod.SyncMod_initState k p st,
                sendMsg = k_mod.SyncMod_sendMsg k, CnextState = \<lambda>p st msgs crd. k_mod.SyncMod_nextState k p st msgs,
                HOcommPerRd = k_mod.SyncMod_commPerRd, HOcommGlobal = k_mod.SyncMod_commGlobal,
                HOcommSchedule = k_mod.SyncMod_commSchedule\<rparr>\<close>)
            hence "?msgs xi = Content (Val (x s))"
                using \<open>k_mod.xi_nek HO xi\<close> HOrcvdMsgs_def[of ?A p "HO (Suc r) p" "rho r"] \<open>rho r xi = Active s\<close>
                k_mod.xi_nek_def[of HO xi] by auto
            hence "\<not> (k_mod.ready_force k ?msgs ss)"
                    using k_mod.ready_force_def[of k ?msgs ss] \<open>x s = k-1\<close> by auto

            moreover have "CnextState ?A p ss ?msgs undefined st" 
                using HORun_def CHORun_def run CHOnextConfig_def[of ?A "rho r" _ _ "rho (Suc r)"]
                \<open>rho r p = Active ss\<close>
                \<open>rho (Suc r) p = Active st\<close> by fastforce
            hence "k_mod.SyncMod_nextState k p ss ?msgs st"
                using HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def[of k]
                by (simp add: k_mod.simp_nextState)
            ultimately have "k_mod.concordant ?msgs ((x st - 1) mod k)" and "(x st) mod k = x st"
                using k_mod.SyncMod_nextState_def[of k p ss ?msgs st] \<open>x st \<noteq> 0\<close> 
                by auto
            hence "\<forall>vv. ?msgs xi = Content (Val vv) \<longrightarrow> vv = ((x st - 1) mod k)"
                using k_mod.concordant_def[of ?msgs "(x st - 1) mod k"] by auto
            hence "k - 1 = (x st - 1) mod k"
                using \<open>?msgs xi = Content (Val (x s))\<close> \<open>x s = k - 1\<close> by auto
            hence "(x st) mod k = 0"  using \<open>(x st) mod k = x st\<close>
                by (smt SendVal.distinct(1) \<open>k_mod.SyncMod_sendMsg k xi p s = Val (x s)\<close>
                add_diff_inverse_nat add_le_cancel_left
                assms(4) diff_is_0_eq k_mod.SyncMod_sendMsg_def le_add_diff_inverse linorder_not_less
                mod_by_1 mod_if mod_less_divisor mod_less_eq_dividend nat_code(2))
            thus "False" using \<open>(x st) mod k = x st\<close> \<open>x st \<noteq> 0\<close> by auto
        qed
    qed
    thus "monovalent rho 0 r" using monovalent_def[of rho 0 r] by auto
qed

lemma A3 : assumes "k_mod.xi_nek HO xi"
and run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "rho r xi = Active s"
and "x s = k - 1"
and "k > 2"
and "monovalent rho v r"
shows "monovalent rho (v+i) (r+i)"
proof (induction i)
    from assms(6) show \<open>monovalent rho (v+0) (r+0)\<close> by auto
next
    case (Suc i)
    have "rho (r+i) xi \<noteq> Aslept"
        using run HORun_def assms(3) nonAsleepAgain[of rho r xi ?A HO _ i] by (simp add: HORun_def add.commute)
    then obtain sx where "rho (r+i) xi = Active sx" by (cases "rho (r+i) xi") auto
    moreover have "rho (Suc (r+i)) xi \<noteq> Aslept"
        using run HORun_def assms(3) nonAsleepAgain[of rho r xi ?A HO _ "i+1"] by (simp add: HORun_def add.commute)
    then obtain sxx where "rho (Suc (r+i)) xi = Active sxx" by (cases "rho (Suc (r+i)) xi") auto
    ultimately have "x sxx = v+i" using Suc.IH monovalent_def[of rho "v+i" "r+i" ] by auto
    have "\<forall>p ss st. rho (r+Suc i) p = Active ss \<longrightarrow> rho (Suc (r+Suc i)) p = Active st \<longrightarrow> x st = v"
    proof (rule+)
        fix p ss st
        assume "rho (r+Suc i) p = Active ss" and "rho (Suc (r+Suc i)) p = Active st"
        hence "k_mod.SyncMod_nextState k p ss (HOrcvdMsgs ?A p (HO (Suc (r+Suc i)) p) (rho (r+Suc i))) st"
            (is "k_mod.SyncMod_nextState k p ss ?msgs st") using run by (simp add:transition)
        show "x st = v"
        proof (cases "k_mod.ready_force k ?msgs ss")
            case True
            hence "\<exists>p1 p2 v1 v2. ?msgs p1 = Content (Val v1) \<and> ?msgs p2 = Content (Val v2) \<and> v1 \<noteq> v2"
                using k_mod.ready_force_def by blast
            then obtain p1 p2 v1 v2 where "?msgs p1 = Content (Val v1)" and "?msgs p2 = Content (Val v2)" and "v1 \<noteq> v2" by auto
            then obtain s1 s2 where "rho (r+Suc i) p1 = Active s1 \<and> x s1 = v1" and "rho (r+Suc i) p2 = Active s2 \<and> x s2 = v2"
                using run sending[of k rho HO p "r+Suc i" p1 v1] sending[of k rho HO p "r+Suc i" p2 v2] by auto
            hence ""
    show "monovalent rho (v+Suc i) (r+Suc i)"