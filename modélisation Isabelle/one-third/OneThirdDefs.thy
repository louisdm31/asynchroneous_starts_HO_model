theory OneThirdDefs
  imports "../HOModel"
begin

typedecl Proc \<comment> \<open>the set of processes\<close>
axiomatization where Proc_finite: "OFCLASS(Proc, finite_class)"
instance Proc :: finite by (rule Proc_finite)
consts msg_ord :: "'msg \<Rightarrow> 'msg \<Rightarrow> bool"
consts nproc :: nat

record 'val pstate =
  Val :: 'val
  Decide :: "'val option"

definition msgRcvd where  \<comment> \<open>processes from which some message was received\<close>
  "msgRcvd (msgs:: Proc \<Rightarrow> 'val message) = {q . msgs q \<noteq> Void}"

fun FrequenceValRcvd :: "'val message list \<Rightarrow> ('val \<Rightarrow> nat) \<Rightarrow> ('val \<Rightarrow> nat)" where
"FrequenceValRcvd Nil freq = freq" |
"FrequenceValRcvd (Cons Bot ms) freq = freq" |
"FrequenceValRcvd (Cons Void ms) freq = freq" |
"FrequenceValRcvd (Cons (Content m) ms) freq = (\<lambda>l. if l = m then Suc (freq l) else freq m)"

fun MaxFrequence :: "'val message list \<Rightarrow> ('val \<Rightarrow> nat) \<Rightarrow> 'val message \<Rightarrow> 'val message" where
"MaxFrequence (Cons (Content m) ms) freq (Content v) = MaxFrequence ms freq 
                                                      (Content (if (freq m > freq v) \<and>
                                                      (freq m = freq v \<longrightarrow> msg_ord m v)
                                                      then m else v))" |
"MaxFrequence Nil _ v = v" |
"MaxFrequence (Cons m ms) freq v = MaxFrequence ms freq v"

fun send_onethird :: "'proc \<Rightarrow> 'val pstate \<Rightarrow> 'val" where
"send_onethird p st = Val st"

fun transition_onethird :: "'proc \<Rightarrow> 'val pstate \<Rightarrow> 'val message list \<Rightarrow> 'val pstate" where
"transition_onethird p \<lparr> Val = x, Decide = dec \<rparr> msgs =
                let xmaj = MaxFrequence msgs (FrequenceValRcvd msgs ())
                (if dec = None then st else st)" 


