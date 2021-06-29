theory GenSynchMod
imports "../HOModel"
begin

typedecl Proc
axiomatization where Proc_finite: "OFCLASS(Proc, finite_class)"
instance Proc :: finite by (rule Proc_finite)

abbreviation "N \<equiv> card (UNIV :: Proc set)"

record locState = 
     x :: nat
     conc :: bool
     ready :: bool
     forc :: nat
     level :: nat
    
locale k_mod = fixes k :: nat
begin

definition gen_initState where
"gen_initState = \<lparr> x = 0, conc = False, ready = False, forc = 1, level = 0 \<rparr>"

fun forceMsgs where
  "forceMsgs (Content m) = forc m"
| "forceMsgs _ = 0"

definition maxForce where
"maxForce rcvd \<equiv> Max (forceMsgs ` (range rcvd))"

definition isReady where
"isReady rcvd \<equiv> \<forall>p m. rcvd p = Content m \<longrightarrow> ready m"

definition minMsgs where
"minMsgs rcvd \<equiv> LEAST v. \<exists>m p. rcvd p = Content m \<and> forc m = maxForce rcvd \<and> x m = v"

definition isConc where
"isConc rcvd \<equiv> \<forall>p. rcvd p \<noteq> Void \<longrightarrow> (\<exists>m. rcvd p = Content m \<and> conc m \<and> (x m) mod k = (minMsgs rcvd) mod k)"

definition ready_level1 where
"ready_level1 msgs s \<equiv> isConc msgs \<and> minMsgs msgs mod k = k - 1 \<and> level s = 0"

definition ready_level2 where
"ready_level2 msgs s \<equiv> isConc msgs \<and> isReady msgs
    \<and> minMsgs msgs mod k = k - 1 \<and> level s = 1"

definition gen_nextState :: "Proc \<Rightarrow> locState \<Rightarrow> (Proc \<Rightarrow> locState message) \<Rightarrow> locState \<Rightarrow> bool" where
"gen_nextState p s msgs s' \<equiv>
    if \<not> (ready_level1 msgs s \<or> ready_level2 msgs s) then
        x s' = Suc (minMsgs msgs) \<and> forc s' = maxForce msgs \<and> level s = level s' \<and> (
        if x s' mod k = 0 then
            ready s' = (level s' > 0) \<and> conc s' 
        else
            conc s' = isConc msgs \<and> ready s' = isReady msgs)
    else
        level s' = (if ready_level1 msgs s then 1 else 2) \<and>
        (if maxForce msgs > Suc (level s') then
            x s' = Suc (minMsgs msgs) \<and> forc s' = maxForce msgs
        else
            x s' = 0 \<and> forc s' = Suc (level s'))
        \<and> ready s' = (level s' > 0) \<and> conc s'"

definition gen_sendMsg where
"gen_sendMsg p q st \<equiv> st"

definition gen_commPerRd where
"gen_commPerRd HO \<equiv> True"

(*existence of a path from xi to any node, between any round interval [n, n+k/2]*)
definition path where 
"path HO p q n D \<equiv> \<exists>seq. seq 0 = p \<and> seq D = q \<and>
    (\<forall>i < D. seq i \<in> HO (n+Suc i) (seq (Suc i)))"

definition gen_commGlobal where
"gen_commGlobal HO \<equiv> \<exists>xi. \<forall>p n. path HO xi p n (k div 2)"

definition gen_commSchedule where
"gen_commSchedule sched \<equiv> \<exists>n. sched n = UNIV"

definition gen_HOMachine where
"gen_HOMachine \<equiv> \<lparr>
    CinitState = (\<lambda>_ st _. gen_initState = st),
    sendMsg = gen_sendMsg,
    CnextState = (\<lambda>p st msgs _. gen_nextState p st msgs)
\<rparr>"

definition liveness where
"liveness rho \<equiv> \<forall>p r. rho r p \<noteq> Asleep \<longrightarrow> (\<exists>rf sf. rho rf p = Active sf \<and> level sf = 2)"

definition safety where
"safety rho \<equiv> \<exists>c. \<forall>p rf s s'. rho rf p = Active s \<longrightarrow>
                (level s < 2) \<longrightarrow> rho (Suc rf) p = Active s' \<longrightarrow> level s' = 2 \<longrightarrow> rf mod k = c"

end
end
