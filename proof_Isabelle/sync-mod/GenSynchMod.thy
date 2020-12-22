theory GenSynchMod
imports "../HOModel"
begin

typedecl Proc
axiomatization where Proc_finite: "OFCLASS(Proc, finite_class)"
instance Proc :: finite by (rule Proc_finite)

abbreviation "N == card (UNIV :: Proc set)"

record locState = 
     x :: nat
     conc :: bool
     ready :: bool
     forc :: nat
     level :: nat
    
record sendVal = 
     x :: nat
     conc :: bool
     ready :: bool
     forc :: nat
    
locale k_mod = fixes k :: nat
begin

definition gen_initState where 
"gen_initState p st == x st = 0 & (~ conc st) & (~ ready st) & forc st = 0 & level st = 0"

fun forceMsgs msgs where
  "forceMsgs (Content m) = forc m"
| "forceMsgs Void = 0"
| "forceMsgs Bot  = 0"

definition maxForce where
"maxMorce rcvd = Max ((range rcvd) ` forceMsgs)"

definition isConc where
"isConc rcvd = ALL p m. rcvd p ~= Void --> rcvd p = Content m --> ready m"

definition isReady where
"isReady rcvd = ALL p m. rcvd p = Content m --> ready m"

definition minMsgs where
"minMsgs rcvd = LEAST v. EX m p. rcvd p = Content m & forc m = maxForce rcvd & c m = v"

definition ready_level1 where
"ready_level1 msgs s = isConc msgs & minMsgs msgs mod k = 0 & level s = 0"

definition ready_level2 where
"ready_level2 msgs s = (maxForce msgs = 2 | (isConc msgs & isReady msgs)) & minMsgs msgs mod k = 0 & level s = 1"

definition gen_nextState :: "Proc => pstate => (Proc => SendVal message) => pstate => bool" where
"gen_nextState p s msgs s' ==
    if ~ (ready_level1 | ready_level2) then
        x s' = minMsgs msgs & forc s' = maxForce msgs
        if minMsgs msgs mod k = 0 then
            ready s' = (level s' > 0) & conc s' 
        else
            conc s' = isConc msgs & ready s' = isReady msgs
    else
        x s' = 0 & forc s' = (if ready_level1 then 1 else 2) & level s' = forc s'"

definition gen_sendMsg where
"gen_sendMsg p q st == (| x = x st, conc = conc st, ready = ready st, forc = forc st |)"

definition gen_commPerRd where
"gen_commPerRd HO == True"

definition xi_nek where 
"xi_nek HO xi == ALL p n. EX path. path 0 = xi & path (k/2) = p & (ALL i < k/2. path i : HO (n+i) (path (Suc i)))"

definition gen_commGlobal where
"gen_commGlobal HO == EX xi. xi_nek HO xi"

definition gen_commSchedule where
"gen_commSchedule sched == EX n. sched n = UNIV"

definition gen_HOMachine where
"gen_HOMachine == (|
    CinitState = (%p st crd. gen_initState p st),
    sendMsg = gen_sendMsg,
    CnextState = (%p st msgs crd. gen_nextState p st msgs),
    HOcommPerRd = gen_commPerRd,
    HOcommGlobal = gen_commGlobal,
    HOcommSchedule = gen_commSchedule
|)"

lemma simp_nextState : "CnextState gen_HOMachine = (%p ss ms cr. gen_nextState p ss ms)"
using gen_HOMachine_def
by (simp add: gen_HOMachine_def)

definition liveness where
"liveness rho == ALL p r. rho r p ~= Asleep --> (EX rf sf. rho rf p = Active sf & level sf = 2)"

definition safety where
"safety rho == EX c. ALL p rf s s'. rho rf p = Active s -->
                (level s < 2) --> rho (Suc rf) p = Active s' --> level s' = 2 --> rf mod k = c"

end
end
