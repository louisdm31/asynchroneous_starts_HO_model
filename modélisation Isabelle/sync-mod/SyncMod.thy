theory SyncMod
imports "../HOModel"
begin

typedecl Proc
axiomatization where Proc_finite: "OFCLASS(Proc, finite_class)"
instance Proc :: finite by (rule Proc_finite)

abbreviation "N \<equiv> card (UNIV :: Proc set)"

record pstate = 
     x :: nat
     forc :: bool
     fire :: bool
    
datatype SendVal = Val nat | Nope

locale k_mod = fixes k :: nat
begin

definition SyncMod_initState where 
"SyncMod_initState p st \<equiv> x st = k \<and> (\<not> forc st) \<and> \<not> fire st"

definition concordant where
"concordant msgs v \<equiv> \<exists>p. msgs p = Content (Val v) \<and> (\<forall>q vv. msgs q = Content (Val vv) \<longrightarrow> vv = v)"

definition ready_fire where
"ready_fire msgs \<equiv> \<forall>p. msgs p = Void \<or> msgs p = Content (Val (k-1))"

definition ready_force where
"ready_force msgs ss \<equiv> (\<not> forc ss) \<and> (\<forall>p. msgs p \<noteq> Content (Val (k-1))) \<and> 
(\<exists>p q v1 v2. msgs p = Content (Val v1) \<and> msgs q = Content (Val v2) \<and> v1 \<noteq> v2)"

definition SyncMod_nextState :: "Proc \<Rightarrow> pstate \<Rightarrow> (Proc \<Rightarrow> SendVal message) \<Rightarrow> pstate \<Rightarrow> bool" where
"SyncMod_nextState p ss msgs st \<equiv>
    ((fire ss \<and> fire st) | (fire st \<longleftrightarrow> ready_fire msgs)) \<and>
    (if ready_force msgs ss then
        x st = k-1 \<and> forc st
        else forc ss = forc st & (
        if x st = 0 then
            \<forall>v. concordant msgs v \<longrightarrow> v = k - 1 else
            concordant msgs ((x st - 1) mod k)) \<and> (x st) mod k = x st)"

definition SyncMod_sendMsg where
"SyncMod_sendMsg p q st \<equiv> if x st = k then Nope else Val (x st)"

definition SyncMod_commPerRd where
"SyncMod_commPerRd HO \<equiv> True"

definition xi_nek where 
"xi_nek HO xi \<equiv> \<forall>p n. xi \<in> HO n p"

definition SyncMod_commGlobal where
"SyncMod_commGlobal HO \<equiv> \<exists>xi. xi_nek HO xi"

definition SyncMod_commSchedule where
"SyncMod_commSchedule sched \<equiv> \<exists>n. sched n = UNIV"

definition SyncMod_HOMachine where
"SyncMod_HOMachine \<equiv> \<lparr>
    CinitState = (\<lambda> p st crd. SyncMod_initState p st),
    sendMsg = SyncMod_sendMsg,
    CnextState = (\<lambda> p st msgs crd. SyncMod_nextState p st msgs),
    HOcommPerRd = SyncMod_commPerRd,
    HOcommGlobal = SyncMod_commGlobal,
    HOcommSchedule = SyncMod_commSchedule
\<rparr>"

lemma simp_nextState : "CnextState SyncMod_HOMachine = (\<lambda>p ss ms cr. SyncMod_nextState p ss ms)"
using SyncMod_HOMachine_def
by (simp add: SyncMod_HOMachine_def)

definition liveness where
"liveness rho \<equiv> \<forall>p r. rho r p \<noteq> Aslept \<longrightarrow> (\<exists>rf sf. rho rf p = Active sf \<and> fire sf)"

definition safety where
"safety rho \<equiv> \<exists>c. \<forall>p rf ss sf. rho rf p = Active ss \<longrightarrow> (\<not> fire ss) \<longrightarrow> rho (Suc rf) p = Active sf \<longrightarrow> fire sf \<longrightarrow> (rf + c) mod k = 0"

end
end