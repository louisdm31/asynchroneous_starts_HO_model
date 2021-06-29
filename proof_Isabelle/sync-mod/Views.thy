theory Views
imports "../HOModel"
begin

typedecl Proc
axiomatization where Proc_finite: "OFCLASS(Proc, finite_class)"
instance Proc :: finite by (rule Proc_finite)

datatype tree_2col =
    Initial |
    Node bool "tree_2col list"

fun list_in where
"list_in v [] = False" |
"list_in v (a#l) = ((v = a) \<or> list_in v l)"

definition view_compute where
"view_compute = \<lparr> 
    CinitState = (\<lambda>p st _. st = Initial),
    sendMsg = (\<lambda>_ _ st. st),
    CnextState = (%_ s msgs _ s'. s' = Node
        (\<exists>p. msgs p = Bot)
        (SOME l :: tree_2col list. \<forall>child :: tree_2col. ((list_in child l) = (\<exists>p. msgs p = Content child))))
\<rparr>"

record locState = 
     x :: nat
     conc :: bool
     ready :: bool
     forc :: nat
     level :: nat

fun tree_to_state where
"tree_to_state k Initial = \<lparr> x = 0, conc = False, ready = False, forc = 0, level = 0 \<rparr>" |
"tree_to_state k (Node passiv_rcvd siblings) = (
    let msgs = List.map (tree_to_state k) siblings in
    let max_f = Max (forc ` (List.set msgs)) in
    let v = Suc (LEAST v. \<exists>s. list_in s msgs \<and> x s = v) in 
    let concr = \<not> passiv_rcvd \<and> (\<forall>s. list_in s msgs \<longrightarrow> conc s) in
    let readyr = \<forall>s. list_in s msgs \<longrightarrow> ready s in
    \<lparr> x = v, conc = concr \<or> v mod k = 0, ready = readyr \<or> v mod k = 0, forc = 0, level = 0 \<rparr>)"

definition view where
"view rho HO p t 0 = Initial" |
"view rho HO p t (Suc r) = (UN q \<in> incoming rho HO p t r. if rho (t-r) q = Asleep then {q} else HO (t-r) q)"


definition set_computable  where
"set_computable f \<equiv> \<exists>algo comput. \<forall>rho HO r p s. HORun algo rho HO \<longrightarrow> rho r p = Active s \<longrightarrow> f rho HO p r = comput s"

fun incoming where
"incoming rho HO p t 0 = {p}" |
"incoming rho HO p t (Suc r) = (UN q \<in> incoming rho HO p t r. if rho (t-r) q = Asleep then {q} else HO (t-r) q)"

definition incoming_compute where
"incoming_compute = \<lparr> 
    CinitState = (\<lambda>p st _. st = {p}),
    sendMsg = (\<lambda>_ _ st. st),
    CnextState = (%_ s msgs _ s'. s' = Union (range (\<lambda>p.
        if msgs p = Void then {} else
        if msgs p = Bot then {p} else
            SOME s. msgs p = Content s)))
\<rparr>"

lemma incoming_computable : 
assumes run:"HORun incoming_compute rho HO"
shows "\<forall>r t p. (r = 0 \<or> rho (r-1) p = Asleep) \<longrightarrow> rho r p \<noteq> Asleep \<longrightarrow> (SOME s. rho (r+t) p = Active s) = incoming rho HO p r t"
proof 
    fix r 
    show "\<forall>t p. (r = 0 \<or> rho (r-1) p = Asleep) \<longrightarrow> rho r p \<noteq> Asleep \<longrightarrow> (SOME s. rho (r+t) p = Active s) = incoming rho HO p r t"
    proof
        fix t
        show "\<forall>p. (r = 0 \<or> rho (r-1) p = Asleep) \<longrightarrow> rho r p \<noteq> Asleep \<longrightarrow> (SOME s. rho (r+t) p = Active s) = incoming rho HO p r t"
proof (induction "r+t")
    case 0
    show ?case
    proof (rule allI impI)+
        fix p
        assume "r = 0 \<or> rho (r-1) p = Asleep"
        assume act:"rho r p \<noteq> Asleep"
        from this "0.hyps" obtain s where s:"rho 0 p = Active s" using the_state.cases by auto 
        from run have "CHOinitConfig incoming_compute rho (\<lambda>_ _. undefined)" (is "CHOinitConfig ?A _ _")
            by (simp add: HORun_def CHORun_def)
        moreover from act "0.hyps" have "first_awake rho p = 0"
            unfolding first_awake_def by auto
        moreover from act have "\<not> always_asleep rho p" unfolding always_asleep_def by auto
        ultimately have "CinitState incoming_compute p s undefined" using assms s unfolding CHOinitConfig_def by auto
        hence "s = {p}" unfolding incoming_compute_def by auto
        thus "(SOME s. rho (r+t) p = Active s) = incoming rho HO p r t" using "0.hyps" by (simp add:s)
    qed
next
    case (Suc tt)
    show ?case
    proof (rule allI impI)+
        fix p
        assume "r = 0 \<or> rho (r-1) p = Asleep"
        assume act:"rho r p \<noteq> Asleep"
        from nonAsleepAgain[of _ r p] run this obtain s where "rho (r+t) p = Active s" unfolding HORun_def by blast

