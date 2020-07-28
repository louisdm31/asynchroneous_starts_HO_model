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

lemma A1 : assumes run:"HORun (HOMachine_to_Algorithm (k_mod.SyncMod_HOMachine k)) rho HO" (is "HORun ?A _ _")
and "k > 2"
shows "\<forall>r v p s ss. rho r p = Active s \<longrightarrow> rho (Suc r) p = Active ss \<longrightarrow> x ss = v \<longrightarrow> 0 \<le> v \<and> v < k"
proof (rule allI)+
    fix r v s ss p
    show "rho r p = Active s \<longrightarrow> rho (Suc r) p = Active ss \<longrightarrow> x ss = v \<longrightarrow> 0 \<le> v \<and> v < k"
    proof (induction r arbitrary:p v s ss)
        case 0
        show ?case
        proof (rule impI)+
            assume s_def:"rho 0 p = Active s"
            assume ss_def:"rho (Suc 0) p = Active ss"
            assume "x ss = v"
            have no_content:"\<forall>v q. HOrcvdMsgs ?A p (HO 1 p) (rho 0) q \<noteq> Content (Val v)" (is "\<forall>v q. ?msgs q \<noteq> _")
            proof (rule allI)+
                fix v
                fix q
                show "?msgs q \<noteq> Content (Val v)"
                proof (cases "rho 0 q")
                    case "Aslept"
                    hence "?msgs q = (if q \<in> HO 1 p then Bot else Void)" using HOrcvdMsgs_def[of ?A p "HO 1 p" "rho 0"] by auto
                    thus "?msgs q \<noteq> Content (Val v)" by auto
                next
                    case (Active sq)
                    hence "?msgs q = (if q \<in> HO 1 p then Content Nope else Void)"
                        using stating[of 0 rho q k HO sq] run by auto
                    thus "?msgs q \<noteq> Content (Val v)" by auto
                qed
            qed
            hence "\<forall>v. \<not> k_mod.concordant ?msgs v" by (simp add: k_mod.concordant_def)
            moreover have "k_mod.SyncMod_nextState k p s ?msgs ss"
                using transition[of rho 0 p s ss k HO] s_def ss_def run  by auto
            ultimately have v_possible:"if k_mod.ready_force k ?msgs s then x ss = k - 1 else if x ss = 0 then True else False" 
            using k_mod.SyncMod_nextState_def[of k p s ?msgs ss] by fastforce
            show "0 \<le> v \<and> v < k"
            proof (cases "k_mod.ready_force k ?msgs s") 
                case True
                thus "0 \<le> v \<and> v < k" using v_possible \<open>x ss = v\<close> by (meson no_content k_mod.ready_force_def)
            next
                case False
                hence "v = 0" using v_possible \<open>x ss = v\<close> by simp
                thus "0 \<le> v \<and> v < k" using \<open>k > 2\<close> by auto
            qed
        qed
    next
        case (Suc r)
        fix p
        show "rho (Suc r) p = Active s \<longrightarrow> rho (Suc (Suc r)) p = Active ss \<longrightarrow> x ss = v \<longrightarrow> 0 \<le> v \<and> v < k"
        proof (rule impI)+
            assume "rho (Suc r) p = Active s"
            assume "rho (Suc (Suc r)) p = Active ss"
            assume "x ss = v"
            have "\<forall>q vv. HOrcvdMsgs ?A p (HO (Suc (Suc r)) p) (rho (Suc r)) q = Content (Val vv) \<longrightarrow> 0 \<le> vv \<and> vv < k"
                (is "\<forall>q vv. ?msgs q = _ \<longrightarrow> _")
            proof (rule allI impI)+
                fix q :: Proc
                fix vv
                assume "?msgs q = Content (Val vv)"
                show "0 \<le> vv \<and> vv < k"
                proof (cases "rho (Suc r) q")
                    case Aslept
                    hence "?msgs q = (if q \<in> HO (Suc (Suc r)) p then Bot else Void)"
                        using HOrcvdMsgs_def[of ?A p "HO (Suc (Suc r)) p" "rho (Suc r)"] by auto
                    thus "0 \<le> vv \<and> vv < k" using \<open>?msgs q = Content (Val vv)\<close> by auto
                next
                    case (Active sq)
                    show "0 \<le> vv \<and> vv < k"
                    proof (cases "rho r q")
                        case Aslept
                        hence "?msgs q = (if q \<in> HO (Suc r) p then Content Nope else Void)"
                            using run stating[of "Suc r" rho q k HO sq] \<open>rho (Suc r) q = Active sq\<close>
                            \<open>?msgs q = Content (Val vv)\<close> by auto
                        thus "0 \<le> vv \<and> vv < k" using \<open>?msgs q = Content (Val vv)\<close> by auto
                    next
                        case (Active sqq)
                        have "sendMsg ?A q p sq = Val vv"
                            using HOrcvdMsgs_def[of ?A p "HO (Suc (Suc r)) p" "rho (Suc r)"] \<open>?msgs q = Content (Val vv)\<close>
                            \<open>rho (Suc r) q = Active sq\<close> by auto
                        hence "x sq = vv" using HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def by 
                            (simp add: \<open>\<And>k. k_mod.SyncMod_HOMachine k \<equiv> \<lparr>CinitState = \<lambda>p st crd. k_mod.SyncMod_initState k p st,
                            sendMsg = k_mod.SyncMod_sendMsg k,
                            CnextState = \<lambda>p st msgs crd. k_mod.SyncMod_nextState k p st msgs,
                            HOcommPerRd = k_mod.SyncMod_commPerRd, HOcommGlobal = k_mod.SyncMod_commGlobal,
                            HOcommSchedule = k_mod.SyncMod_commSchedule\<rparr>\<close>
                            k_mod.SyncMod_sendMsg_def)
                        thus "0 \<le> vv \<and> vv < k"
                            using Suc.IH[of q sqq sq] \<open>rho r q = Active sqq\<close> \<open>rho (Suc r) q = Active sq\<close> by auto
                    qed
                qed
            qed

            have trans:"k_mod.SyncMod_nextState k p s ?msgs ss"
                using run \<open>rho (Suc r) p = Active s\<close> \<open>rho (Suc (Suc r)) p = Active ss\<close> transition by auto
            thus "0 \<le> v \<and> v < k"
            proof (cases "k_mod.ready_force k ?msgs s")
                case True
                hence "x ss = k - 1" using trans k_mod.SyncMod_nextState_def by auto
                thus "0 \<le> v \<and> v < k" using \<open>x ss = v\<close> \<open>k > 2\<close> by auto
            next
                case non_force:False
                show "0 \<le> v \<and> v < k"
                proof (cases "x ss = 0")
                    case True
                    thus "0 \<le> v \<and> v < k" using \<open>x ss = v\<close> \<open>k > 2\<close> by auto
                next
                    case False
                    hence "\<exists>q. ?msgs q = Content (Val ((x ss - 1) mod k))"
                        using trans k_mod.concordant_def k_mod.SyncMod_nextState_def[of k p s ?msgs ss] non_force by auto


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
            ultimately have "k_mod.concordant ?msgs ((x st - 1) mod k)"
                using k_mod.SyncMod_nextState_def[of k p ss ?msgs st] \<open>x st \<noteq> 0\<close> 
                by auto
            hence "\<forall>vv. ?msgs xi = Content (Val vv) \<longrightarrow> vv = ((x st - 1) mod k)" 
                using k_mod.concordant_def[of ?msgs "(x st - 1) mod k"] by auto
            hence "k - 1 = (x st - 1) mod k"
                using \<open>?msgs xi = Content (Val (x s))\<close> \<open>x s = k - 1\<close> by auto
            hence "0 = x st" by 
            hence "\<exists>tem. ?msgs tem = Content (Val (x st)) \<and> (\<forall>q vv. ?msgs q = Content (Val vv) \<longrightarrow> vv = (x st))"
                using k_mod.concordant_def[of ?msgs] by auto

end