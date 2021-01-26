theory Views
imports "../HOModel" 
begin

typedecl Proc
axiomatization where Proc_finite: "OFCLASS(Proc, finite_class)"
instance Proc :: finite by (rule Proc_finite)

definition set_computable  where
"set_computable f == EX algo comput. ALL rho HO r p s. HORun algo rho HO --> rho r p = Active s --> f rho HO p r = comput s"

fun incoming where
"incoming rho HO p t 0 = {p}" |
"incoming rho HO p t (Suc r) = (UN q : incoming rho HO p t r. if rho (t-r) q = Asleep then {q} else HO (t-r) q)"

definition incoming_compute where
"incoming_compute = (| 
    CinitState = (%p st _. st = {p}),
    sendMsg = (%_ _ st. st),
    CnextState = (%_ s msgs _ s'. s' = Union (range (%p.
        if msgs p = Void then {} else
        if msgs p = Bot then {p} else
            SOME s. msgs p = Content s)))
|)"

lemma incoming_computable : 
assumes run:"HORun incoming_compute rho HO"
shows "ALL r t p. (r = 0 | rho (r-1) p = Asleep) --> rho r p ~= Asleep --> (SOME s. rho (r+t) p = Active s) = incoming rho HO p r t"
proof 
    fix r 
    show "ALL t p. (r = 0 | rho (r-1) p = Asleep) --> rho r p ~= Asleep --> (SOME s. rho (r+t) p = Active s) = incoming rho HO p r t"
    proof
        fix t
        show "ALL p. (r = 0 | rho (r-1) p = Asleep) --> rho r p ~= Asleep --> (SOME s. rho (r+t) p = Active s) = incoming rho HO p r t"
proof (induction "r+t")
    case 0
    show ?case
    proof (rule allI impI)+
        fix p
        assume "r = 0 | rho (r-1) p = Asleep"
        assume act:"rho r p ~= Asleep"
        from this "0.hyps" obtain s where s:"rho 0 p = Active s" using the_state.cases by auto 
        from run have "CHOinitConfig incoming_compute rho (%_ _. undefined)" (is "CHOinitConfig ?A _ _")
            by (simp add: HORun_def CHORun_def)
        moreover from act "0.hyps" have "first_awake rho p = 0"
            unfolding first_awake_def by auto
        moreover from act have "~ always_asleep rho p" unfolding always_asleep_def by auto
        ultimately have "CinitState incoming_compute p s undefined" using assms s unfolding CHOinitConfig_def by auto
        hence "s = {p}" unfolding incoming_compute_def by auto
        thus "(SOME s. rho (r+t) p = Active s) = incoming rho HO p r t" using "0.hyps" by (simp add:s)
    qed
next
    case (Suc tt)
    show ?case
    proof (rule allI impI)+
        fix p
        assume "r = 0 | rho (r-1) p = Asleep"
        assume act:"rho r p ~= Asleep"
        from nonAsleepAgain[of _ r p] run this obtain s where "rho (r+t) p = Active s" unfolding HORun_def by blast

