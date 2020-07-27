theory SyncModProof
imports "../HOModel" SyncMod
begin

definition HOMachine_to_Algorithm :: "(Proc, pstate, SendVal) HOMachine \<Rightarrow> (Proc, pstate, SendVal) CHOAlgorithm" where
"HOMachine_to_Algorithm mach = \<lparr> CinitState = CinitState mach, sendMsg = sendMsg mach, CnextState = CnextState mach \<rparr>"


definition monovalent where
"monovalent rho v n \<equiv> \<forall>p ss st. rho n p = Active ss \<longrightarrow> rho (Suc n) p = Active st \<longrightarrow> x st = v"

lemma A1 : assumes "xi_nek HO xi"
and run:"HORun (HOMachine_to_Algorithm SM_M) rho HO" (is "HORun ?A _ _")
and "rho r xi = Active s"
and "x s = k - 1"
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
        proof -
            have "CHOnextConfig ?A (rho r) (HO r) (\<lambda>q. undefined) (rho (Suc r))" 
                using HORun_def CHORun_def run
                by fastforce
            hence "\<exists>st. CnextState ?A p ss (HOrcvdMsgs ?A p (HO (Suc r) p) (rho (Suc r))) undefined st"
            using CHOnextConfig_def[of ?A "rho r" "HO r" _ "rho (Suc r)"] \<open>rho r p = Active ss\<close> by 
                
            hence "k_mod.concordant (HOrcvdMsgs ?A p (HO (Suc r) p) (rho (Suc r))) (k-1)"
                using HOMachine_to_Algorithm_def k_mod.SyncMod_HOMachine_def k_mod.SyncMod_nextState_def CHOnextConfig_def
                by 

end