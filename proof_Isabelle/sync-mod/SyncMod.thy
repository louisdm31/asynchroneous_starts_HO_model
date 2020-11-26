theory SyncMod
imports "../HOModel"
begin

typedecl Proc
axiomatization where Proc_finite: "OFCLASS(Proc, finite_class)"
instance Proc :: finite by (rule Proc_finite)

abbreviation "N == card (UNIV :: Proc set)"

record pstate = 
     x :: nat
     forc :: bool
     fire :: bool
    
datatype SendVal = Val nat | Nope

locale k_mod = fixes k :: nat
begin

definition SyncMod_initState where 
"SyncMod_initState p st == x st = k & (~ forc st) & ~ fire st"

definition concordant where
"concordant msgs v == EX p. msgs p = Content (Val v) & (ALL q vv. msgs q = Content (Val vv) --> vv = v)"

definition ready_fire where
"ready_fire msgs == ALL p. msgs p = Void \<or> msgs p = Content (Val (k-1))"

definition ready_force where
"ready_force msgs ss == (~ forc ss) & (ALL p. msgs p ~= Content (Val (k-1))) &
(EX p q v1 v2. msgs p = Content (Val v1) & msgs q = Content (Val v2) & v1 ~= v2)"

definition SyncMod_nextState :: "Proc => pstate => (Proc => SendVal message) => pstate => bool" where
"SyncMod_nextState p ss msgs st ==
    fire st = (ready_fire msgs | fire ss) &
    (if ready_force msgs ss then
        x st = k-1 & forc st
        else forc ss = forc st & (if ALL q v. msgs q ~= Content (Val v) then x st = 0 else EX q v. msgs q = Content (Val v) & Suc v mod k = x st) &
        (ALL q v. msgs q = Content (Val v) --> Suc v mod k >= x st))"

definition SyncMod_sendMsg where
"SyncMod_sendMsg p q st == if x st = k then Nope else Val (x st)"

definition SyncMod_commPerRd where
"SyncMod_commPerRd HO == True"

definition xi_nek where 
"xi_nek HO xi == ALL p n. xi : HO n p"

definition SyncMod_commGlobal where
"SyncMod_commGlobal HO == EX xi. xi_nek HO xi"

definition SyncMod_commSchedule where
"SyncMod_commSchedule sched == EX n. sched n = UNIV"

definition SyncMod_HOMachine where
"SyncMod_HOMachine == \<lparr>
    CinitState = (% p st crd. SyncMod_initState p st),
    sendMsg = SyncMod_sendMsg,
    CnextState = (% p st msgs crd. SyncMod_nextState p st msgs),
    HOcommPerRd = SyncMod_commPerRd,
    HOcommGlobal = SyncMod_commGlobal,
    HOcommSchedule = SyncMod_commSchedule
\<rparr>"

lemma simp_nextState : "CnextState SyncMod_HOMachine = (% p ss ms cr. SyncMod_nextState p ss ms)"
using SyncMod_HOMachine_def
by (simp add: SyncMod_HOMachine_def)

definition liveness where
"liveness rho == ALL p r. rho r p ~= Aslept --> (EX rf sf. rho rf p = Active sf \<and> fire sf)"

definition safety where
"safety rho == EX c. ALL p rf ss sf. rho rf p = Active ss -->
                (~ fire ss) --> rho (Suc rf) p = Active sf --> fire sf --> rf mod k = c"

end
end