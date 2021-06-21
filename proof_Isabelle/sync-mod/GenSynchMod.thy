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
    
locale k_mod = fixes k :: nat
begin

definition gen_initState where
"gen_initState = (| x = 0, conc = False, ready = False, forc = 1, level = 0 |)"

fun forceMsgs where
  "forceMsgs (Content m) = forc m"
| "forceMsgs _ = 0"

definition maxForce where
"maxForce rcvd == Max (forceMsgs ` (range rcvd))"

definition isReady where
"isReady rcvd == ALL p m. rcvd p = Content m --> ready m"

definition minMsgs where
"minMsgs rcvd == LEAST v. EX m p. rcvd p = Content m & forc m = maxForce rcvd & x m = v"

definition isConc where
"isConc rcvd == ALL p. rcvd p ~= Void --> (EX m. rcvd p = Content m & conc m & (x m) mod k = (minMsgs rcvd) mod k)"

definition ready_level1 where
"ready_level1 msgs s == isConc msgs & minMsgs msgs mod k = k - 1 & level s = 0"

definition ready_level2 where
"ready_level2 msgs s == isConc msgs & isReady msgs
    & minMsgs msgs mod k = k - 1 & level s = 1"

definition gen_nextState :: "Proc => locState => (Proc => locState message) => locState => bool" where
"gen_nextState p s msgs s' ==
    if ~ (ready_level1 msgs s | ready_level2 msgs s) then
        x s' = Suc (minMsgs msgs) & forc s' = maxForce msgs & level s = level s' & (
        if x s' mod k = 0 then
            ready s' = (level s' > 0) & conc s' 
        else
            conc s' = isConc msgs & ready s' = isReady msgs)
    else
        level s' = (if ready_level1 msgs s then 1 else 2) &
        (if maxForce msgs > Suc (level s') then
            x s' = Suc (minMsgs msgs) & forc s' = maxForce msgs
        else
            x s' = 0 & forc s' = Suc (level s'))
        & ready s' = (level s' > 0) & conc s'"

definition gen_sendMsg where
"gen_sendMsg p q st == st"

definition gen_commPerRd where
"gen_commPerRd HO == True"

(*existence of a path from xi to any node, between any round interval [n, n+k/2]*)
definition path where 
"path HO p q n D == EX seq. seq 0 = p & seq D = q &
    (ALL i < D. seq i : HO (n+Suc i) (seq (Suc i)))"

definition gen_commGlobal where
"gen_commGlobal HO == EX xi. ALL p n. path HO xi p n (k div 2)"

definition gen_commSchedule where
"gen_commSchedule sched == EX n. sched n = UNIV"

definition gen_HOMachine where
"gen_HOMachine == (|
    CinitState = (%_ st _. gen_initState = st),
    sendMsg = gen_sendMsg,
    CnextState = (%p st msgs _. gen_nextState p st msgs)
|)"

definition liveness where
"liveness rho == ALL p r. rho r p ~= Asleep --> (EX rf sf. rho rf p = Active sf & level sf = 2)"

definition safety where
"safety rho == EX c. ALL p rf s s'. rho rf p = Active s -->
                (level s < 2) --> rho (Suc rf) p = Active s' --> level s' = 2 --> rf mod k = c"

end
end
