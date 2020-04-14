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

fun AddFrequence :: "('val message \<Rightarrow> nat) \<Rightarrow> 'val \<Rightarrow> 'val message \<Rightarrow> nat" where
"AddFrequence freq m (Content l) = (if l = m then Suc (freq (Content l)) else freq (Content m))" |
"AddFrequence freq m _ = freq (Content m)"

fun FrequenceValRcvd :: "'val message list \<Rightarrow> ('val message  \<Rightarrow> nat) \<Rightarrow> 'val message \<Rightarrow> nat" where
"FrequenceValRcvd Nil freq = freq" |
"FrequenceValRcvd (Cons Bot ms) freq = freq" |
"FrequenceValRcvd (Cons Void ms) freq = freq" |
"FrequenceValRcvd (Cons (Content m) ms) freq = AddFrequence freq m"

fun MaxFrequence :: "'val message list \<Rightarrow> ('val message \<Rightarrow> nat) \<Rightarrow> 'val message \<Rightarrow> 'val message" where
"MaxFrequence Nil _ v = v" |
"MaxFrequence (Cons (Content m) ms) freq (Content v) = MaxFrequence ms freq 
                                                      (Content (if (freq (Content m) > freq (Content v)) \<and>
                                                      (freq (Content m) = freq (Content v) \<longrightarrow> msg_ord m v)
                                                      then m else v))" |
"MaxFrequence (Cons (Content m) ms) freq v = MaxFrequence ms freq (Content m)" |
"MaxFrequence (Cons m ms) freq v = MaxFrequence ms freq v"

fun send_onethird :: "'proc \<Rightarrow> 'val pstate \<Rightarrow> 'val" where
"send_onethird p st = Val st"

fun transition_one :: "('val message \<Rightarrow> nat) \<Rightarrow> 'val message \<Rightarrow> 'val \<Rightarrow> 'val option \<Rightarrow> 'val pstate" where
"transition_one freq (Content mmaj) x dec = (if dec = None then
                (if freq (Content mmaj) > nproc then \<lparr> Val = mmaj, Decide = Some mmaj \<rparr>
                else  \<lparr> Val = mmaj, Decide = None \<rparr>) else  \<lparr> Val = x, Decide = dec \<rparr>)" |
"transition_one _ _ x dec = \<lparr> Val = x, Decide = dec\<rparr>"

fun transition_onethird :: "'proc \<Rightarrow> 'val pstate \<Rightarrow> 'val message list \<Rightarrow> 'val pstate" where
"transition_onethird p \<lparr> Val = x, Decide = dec \<rparr> msgs = (
                let freq = FrequenceValRcvd msgs (\<lambda>n.0) in (
                let xmaj = MaxFrequence msgs freq Bot in
                transition_one freq xmaj x dec))"


