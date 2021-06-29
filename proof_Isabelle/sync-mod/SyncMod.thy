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

definition ready_fire where
"ready_fire msgs \<equiv> \<forall>p. msgs p = Void \<or> msgs p = Content (Val (k-1))"

definition ready_force where
  "ready_force msgs s \<equiv> 
     \<not> forc s
   \<and> (\<forall>p. msgs p \<noteq> Content (Val (k-1)))
   \<and> (\<exists>p q v1 v2. msgs p = Content (Val v1) \<and> msgs q = Content (Val v2) \<and> v1 \<noteq> v2)"

definition SyncMod_nextState :: "Proc \<Rightarrow> pstate \<Rightarrow> (Proc \<Rightarrow> SendVal message) \<Rightarrow> pstate \<Rightarrow> bool" where
"SyncMod_nextState p s msgs s' \<equiv>
    fire s' = (ready_fire msgs \<or> fire s)
  \<and> (if ready_force msgs s then
        x s' = k-1 \<and> forc s'
        else forc s' = forc s 
           \<and> (if \<forall>q v. msgs q \<noteq> Content (Val v) then x s' = 0 
              else \<exists>q v. msgs q = Content (Val v) \<and> x s' = Suc v mod k)
           \<and> (\<forall>q v. msgs q = Content (Val v) \<longrightarrow> x s' \<le> Suc v mod k))"

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
    CinitState = (\<lambda>p st crd. SyncMod_initState p st),
    sendMsg = SyncMod_sendMsg,
    CnextState = (\<lambda>p st msgs crd. SyncMod_nextState p st msgs),
    HOcommPerRd = SyncMod_commPerRd,
    HOcommGlobal = SyncMod_commGlobal,
    HOcommSchedule = SyncMod_commSchedule
\<rparr>"

lemma simp_nextState : "CnextState SyncMod_HOMachine = (\<lambda>p ss ms cr. SyncMod_nextState p ss ms)"
using SyncMod_HOMachine_def
by (simp add: SyncMod_HOMachine_def)

definition liveness where
"liveness rho \<equiv> \<forall>p r. rho r p \<noteq> Asleep \<longrightarrow> (\<exists>rf sf. rho rf p = Active sf \<and> fire sf)"

definition safety where
"safety rho \<equiv> \<exists>c. \<forall>p rf s s'. rho rf p = Active s \<longrightarrow>
                (\<not> fire s) \<longrightarrow> rho (Suc rf) p = Active s' \<longrightarrow> fire s' \<longrightarrow> rf mod k = c"

end
end