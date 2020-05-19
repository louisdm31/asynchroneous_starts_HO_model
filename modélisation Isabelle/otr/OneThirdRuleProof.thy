theory OneThirdRuleProof
imports OneThirdRuleDefs Tiroir
begin

text \<open>
  We prove that \emph{One-Third Rule} solves the Consensus problem
  under the communication predicate defined above. The proof is
  split into proofs of the Integrity, Agreement, and Termination
  properties.
\<close>

subsection \<open>Proof of Integrity\<close>

text \<open>
  Showing integrity of the algorithm is a simple, if slightly tedious
  exercise in invariant reasoning. The following inductive invariant
  asserts that the values of the \<open>x\<close> and \<open>decide\<close> fields
  of the process states are limited to the \<open>x\<close> values present
  in the initial states since the algorithm does not introduce any
  new values.
\<close>

fun getDec where
"getDec (Active s) = (if decide s then Some (x s) else None)" |
"getDec Aslept = None"

definition VInv :: "(nat \<Rightarrow> Proc \<Rightarrow> ('val::linorder) pstate proc_state) \<Rightarrow> nat \<Rightarrow> bool" where
  "VInv rho n \<equiv>
   let xinit =  {x s | s. \<exists>p. getInitValue rho p = Active s}
   in \<forall>p s. rho n p = Active s \<longrightarrow> x s \<in> xinit"


definition HOMachine_to_Algorithm :: "(Proc, 'val::linorder pstate, 'val) HOMachine \<Rightarrow>
                                      (Proc, 'val::linorder pstate, 'val) CHOAlgorithm" where
"HOMachine_to_Algorithm mach = \<lparr> CinitState = CinitState mach, sendMsg = sendMsg mach, CnextState = CnextState mach \<rparr>"

lemma MFR_finite : assumes "v = Min {v. MFR msgs v}" (is "v = Min ?ens")
  and "msgs q = Content s"
  shows "MFR msgs v"
proof -
  show ?thesis
  proof cases
    assume zer:"card ?ens = 0"
    hence vidinfi:"?ens = {} \<or> infinite ?ens" by (simp add:card_eq_0_iff)
    hence "\<forall>v. v \<notin> ?ens"
    proof cases
      assume "?ens = {}"
      thus ?thesis by auto
    next
      assume "?ens \<noteq> {}"
      hence infens:"infinite ?ens"  using vidinfi by blast
      hence "q \<in> HOV msgs s" using HOV_def MFR_def assms by force
      hence exval:"\<exists>v. card (HOV msgs v) \<ge> 1"
        by (metis One_nat_def Suc_leI card_eq_0_iff empty_iff finite_code not_gr_zero)
      hence "\<forall>qq. MFR msgs qq \<longrightarrow> card (HOV msgs qq) \<ge> 1"
        using MFR_def order.trans by fastforce
      moreover have "\<forall>qq. card (HOV msgs qq) \<ge> 1 \<longrightarrow> (\<exists>pp. msgs pp = Content qq)"
        using HOV_def
        by (smt Collect_empty_eq One_nat_def card.empty nat.simps(3) zero_order(2))
      ultimately have "\<forall>qq. MFR msgs qq \<longrightarrow> (\<exists>pp. msgs pp = Content qq)" by auto
      hence "?ens \<subseteq> {qq. \<exists>pp. msgs pp = Content qq}" by auto
      hence infini:"infinite {qq. \<exists>pp. msgs pp = Content qq}"
        using infens rev_finite_subset by blast

      have "finite {pp :: Proc. True}" by auto
      hence "finite (msgs ` {p | p. True})" by force
      hence "finite {msgs p | p. True}" using setcompr_eq_image[where ?f = msgs] by (smt Collect_cong)
      hence "finite {v. \<exists>p. msgs p = v}" by (smt Collect_cong finite_image_set)
      moreover have "{Content v | v.  \<exists>p. msgs p = Content v} \<subseteq> {v. \<exists>p. msgs p = v}"
        by blast
      ultimately have fincontens:"finite {Content v | v.  \<exists>p. msgs p = Content v}"
        by (meson rev_finite_subset)
      moreover have "\<forall>vv1 vv2. Content vv1 = Content vv2 \<longrightarrow> vv1 = vv2" by auto
      ultimately have "finite {v. \<exists>p. msgs p = Content v}" using tiroir2  by force
      hence "False" using infini by auto
      thus ?thesis by auto
    qed
    hence "\<forall>v. \<not> (MFR msgs v)" by simp
    hence "False" using MFR_exists by fastforce
    thus ?thesis by auto
  next
    assume "card ?ens \<noteq> 0"
    hence "finite ?ens" by (meson card_infinite)
    thus ?thesis using Min_in \<open>card ?ens \<noteq> 0\<close> assms by auto
  qed
qed

lemma vinv_invariant:
  assumes run:"HORun (HOMachine_to_Algorithm OTR_M) rho HOs" (is "HORun ?A rho HOs")
  shows "VInv rho n"
proof -
  have pro:"\<forall> p::Proc. \<forall>s. \<forall>n::nat. rho n p = Active s \<longrightarrow>
      (\<exists> m q ss. (m = 0 \<or> rho (m-1) q = Aslept) \<and> rho m q = Active ss \<and> x ss = x s)"
  proof
    fix p :: Proc
    show "\<forall>s. \<forall>n::nat. rho n p = Active s \<longrightarrow>
      (\<exists> m q ss. (m = 0 \<or> rho (m-1) q = Aslept) \<and> rho m q = Active ss \<and> x ss = x s)"
    proof
      fix s
      show " \<forall>n::nat. rho n p = Active s \<longrightarrow>
      (\<exists> m q ss. (m = 0 \<or> rho (m-1) q = Aslept) \<and> rho m q = Active ss \<and> x ss = x s)"
       proof
        fix n :: nat
        show "rho n p = Active s \<longrightarrow>
            (\<exists> m q ss. (m = 0 \<or> rho (m-1) q = Aslept) \<and> rho m q = Active ss \<and> x ss = x s)"
        proof (induction n arbitrary:s p)
          case 0
          show ?case
          proof
            assume  pst:"rho 0 p = Active s"
            hence "0 = 0 \<and> rho 0 p = Active s \<and> x s = x s" by auto
            thus "\<exists> m q ss. (m = 0 \<or> rho (m-1) q = Aslept) \<and> rho m q = Active ss \<and> x ss = x s" by auto
          qed
        next
          case (Suc n)
          show ?case
          proof
            assume pst:"rho (Suc n) p = Active s"
            have nex:"CHOnextConfig ?A (rho n) (HOs n) (\<lambda>l. undefined) (rho (Suc n))"
              using run by (auto simp:HORun_def CHORun_def)
            thus "\<exists> m q ss. (m = 0 \<or> rho (m-1) q = Aslept) \<and> rho m q = Active ss \<and> x ss = x s"
            proof (cases)
              assume "rho n p = Aslept"
              hence "rho ((Suc n)-1) p = Aslept \<and> rho (Suc n) p = Active s \<and> x s = x s" using pst by auto
              hence "\<exists> m. (rho (m-1) p = Aslept) \<and> rho m p = Active s \<and> x s = x s" by blast
              thus "\<exists> m q ss. (m = 0 \<or> rho (m-1) q = Aslept) \<and> rho m q = Active ss \<and> x ss = x s" by auto
            next
              assume "rho n p \<noteq> Aslept" (is "?st \<noteq> Aslept")
              hence "\<exists>ss. rho n p = Active ss" by (cases ?st) auto
              then obtain ss where actt:"rho n p = Active ss" by auto
              hence "\<exists>s'. rho (Suc n) p = Active s' \<and>
                      CnextState ?A p ss (HOrcvdMsgs ?A p (HOs n p) (rho n)) undefined s'"
                (is "\<exists>s'. _ \<and> CnextState ?A p ss ?rcvd undefined s'")
                using nex by (auto simp:CHOnextConfig_def)
              then obtain s' where nxx:"rho (Suc n) p = Active s'\<and>
                      CnextState ?A p ss ?rcvd undefined s'" by auto
              hence "s = s'" using pst by auto
              hence nst:"CnextState ?A p ss ?rcvd undefined s" using nxx by auto
              hence otrn:"OTR_nextState p ss ?rcvd s" by (auto simp:OTR_HOMachine_def HOMachine_to_Algorithm_def)
              hence "(s \<noteq> ss \<and> x s = Min {v. MFR ?rcvd v}) \<or> s = ss" by (auto simp:OTR_nextState_def)
              thus "\<exists> m q ss. (m = 0 \<or> rho (m-1) q = Aslept) \<and> rho m q = Active ss \<and> x ss = x s"
              proof
                assume "s = ss"
                hence "\<exists>m q ss. (m = 0 \<or> rho (m - 1) q = Aslept) \<and> rho m q = Active ss \<and> x ss = x s"
                  using actt Suc.IH by auto
                thus ?thesis using Suc.IH by auto
              next
                assume dans:"s \<noteq> ss \<and> x s =  Min {v. MFR ?rcvd v}" (is "_ \<and> x s = Min ?ens")
                hence "card {q. ?rcvd q \<noteq> Bot \<and> ?rcvd q \<noteq> Void} > (2*N) div 3"
                proof
                  have "\<forall>msgs st st'. OTR_nextState p (st::('val::linorder) pstate) msgs st' \<longrightarrow>
                      (2*N) div 3 \<ge> card {q. msgs q \<noteq> Void \<and> msgs q \<noteq> Bot} \<longrightarrow> st = st'"
                    by (auto simp:OTR_nextState_def)
                  hence "(2*N) div 3 \<ge> card {q. ?rcvd q \<noteq> Void \<and> ?rcvd q \<noteq> Bot} \<longrightarrow> s = ss"
                    using otrn by auto
                  hence " (card {q. ?rcvd q \<noteq> Void \<and> ?rcvd q \<noteq> Bot} > (2*N) div 3)" using dans by auto                
                  thus ?thesis by (metis (no_types, lifting) Collect_cong)
                qed
                hence "card {q. ?rcvd q \<noteq> Bot \<and> ?rcvd q \<noteq> Void} > 0" by auto
                then obtain q where "?rcvd q \<noteq> Void \<and> ?rcvd q \<noteq> Bot" by (auto simp: less_le)
                hence excont:"\<exists>v. ?rcvd q = Content v" by (cases "?rcvd q") auto
                have "\<exists>v. q \<in> (HOV ?rcvd v)" using excont HOV_def by fastforce
                then obtain v where cardun:"card (HOV ?rcvd v) > 0" using less_Suc_eq_0_disj by fastforce
                hence "MFR ?rcvd (x s)" using MFR_finite excont dans by auto
                hence "card (HOV ?rcvd (x s)) \<ge> card (HOV ?rcvd v)" using MFR_def by fastforce
                hence "card (HOV ?rcvd (x s)) > 0" using cardun MFR_def by auto
                then obtain emet where rcemet:"?rcvd emet = Content (x s)"
                  by (auto simp:HOV_def card_gt_0_iff)
                hence "rho n emet \<noteq> Aslept" using HOrcvdMsgs_def
                  by (metis HOrcvMsgs_q.simps(2) message.distinct(1) message.distinct(3))
                then obtain semet where semetdef:"rho n emet = Active semet" by (cases "rho n emet") auto
                hence "\<exists> m q ss. (m = 0 \<or> rho (m-1) q = Aslept) \<and> rho m q = Active ss \<and> x ss = x semet"
                  using Suc.IH by auto
                moreover have "x semet = x s" using rcemet semetdef
                  by (simp add: HOrcvdMsgs_def OTR_HOMachine_def OTR_sendMsg_def HOMachine_to_Algorithm_def)
                ultimately show "\<exists> m q ss. (m = 0 \<or> rho (m-1) q = Aslept) \<and> rho m q = Active ss \<and> x ss = x s"
                  by auto
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  let ?xinit = "{x s | s. \<exists>p. getInitValue rho p = Active s}"
  have "\<forall>p s. rho n p = Active s \<longrightarrow> x s \<in> ?xinit"
  proof
    fix p
    show "\<forall>s. rho n p = Active s \<longrightarrow> x s \<in> ?xinit"
    proof
      fix s
      show "rho n p = Active s \<longrightarrow> x s \<in> ?xinit"
      proof
        assume "rho n p = Active s"
        then obtain m q ss where toto:"m = 0 \<or> rho (m-1) q = Aslept"
                              and qact:"rho m q = Active ss" and "x ss = x s"
          using pro by meson
        from toto have "Active ss = getInitValue rho q"
        proof (rule disjE)
          assume "m = 0"
          hence nonasl:"\<forall>n. rho n q \<noteq> Aslept" using nonAsleepAgain qact run HORun_def
            by (metis add.right_neutral proc_state.distinct(1))
          hence "{n + 1 | n. rho n q = Aslept } \<union> {0} = {0}" by simp
          hence "0 = Max ({n + 1 | n. rho n q = Aslept } \<union> {0})" using qact by (metis Max_singleton)
          hence "rho 0 q = getInitValue rho q" by (simp add: nonasl getInitValue_def)
          thus ?thesis using qact by (simp add: \<open>m = 0\<close>)
        next
          assume "rho (m-1) q = Aslept"
          hence masl:"m \<in> {n + 1 | n. rho n q = Aslept }" by (smt CollectI One_nat_def Suc_leI
                le_add_diff_inverse2 not_gr_zero not_less_zero proc_state.simps(3) qact zero_less_diff)
          have "\<forall>n. n \<ge> m \<longrightarrow> rho n q \<noteq> Aslept" using nonAsleepAgain qact
            by (metis HORun_def le_add_diff_inverse2 proc_state.simps(3) run)
          hence "{n. rho n q = Aslept } \<subseteq> {n. n < m}" by (meson Collect_mono not_le_imp_less)
          hence bornensl:"{n + 1 | n. rho n q = Aslept } \<subseteq> {n. n \<le> m}" (is "?ensl \<subseteq> _")
            using discrete by auto
          moreover from this have "finite ?ensl" using rev_finite_subset by auto
          ultimately have "Max {n + 1 | n. rho n q = Aslept } = m"
            using Max_def masl Max_in Max_ge \<open>finite ?ensl\<close> by fastforce
          hence "Max (?ensl \<union> {0}) = m"
          by (smt Max_ge Max_in Un_empty Un_insert_right \<open>finite ?ensl\<close> antisym
              finite_insert insertCI insertE le_zero_eq masl sup_bot.right_neutral)
          hence "rho m q = getInitValue rho q" by (simp add:getInitValue_def)
          thus "Active ss = getInitValue rho q" using qact by auto
        qed
        hence "x ss \<in> ?xinit" by force
        thus "x s \<in> ?xinit" using \<open>x ss = x s\<close> by auto
      qed
    qed
  qed
  thus ?thesis using VInv_def by auto
qed

lemma OTR_integrity:
  assumes run:"HORun (HOMachine_to_Algorithm OTR_M) rho HOs" (is "HORun ?A _ _")
  and "rho n p = Active \<lparr> x = v, decide = True \<rparr>"
shows "\<exists>q s. x s = v \<and> getInitValue rho q = Active s"
  using vinv_invariant assms VInv_def by fastforce

subsection \<open>Proof of Agreement\<close>

text \<open>
  The following lemma \<open>A1\<close> asserts that if process \<open>p\<close> 
  decides in a round on a value \<open>v\<close> then more than $2/3$ of 
  all processes have \<open>v\<close> as their \<open>x\<close> value in their 
  local state.

  We show a few simple lemmas in preparation.
\<close>

lemma nextState_change:
  assumes "HORun (HOMachine_to_Algorithm OTR_M) rho HOs" (is "HORun ?A _ _")
      and "\<not> ((2*N) div 3 
              < card {q.  (HOrcvdMsgs (HOMachine_to_Algorithm OTR_M) p (HOs n p) (rho n)) q \<noteq> Void \<and>
                          (HOrcvdMsgs (HOMachine_to_Algorithm OTR_M) p (HOs n p) (rho n)) q \<noteq> Bot })"
  shows "rho n p = Aslept \<or> rho (Suc n) p = rho n p"
proof (cases "rho n p")
  case (Active ss)
  then obtain st where "rho (Suc n) p = Active st" using HORun_def CHOnextConfig_def by (metis CHORun_def assms(1))
  hence "OTR_nextState p ss (HOrcvdMsgs ?A p (HOs n p) (rho n)) st" (is "OTR_nextState p ss ?rcvd st")
    using assms unfolding HORun_def CHORun_def HOnextConfig_def CHOnextConfig_def 
    by (smt Active CHOAlgorithm.simps(3) HOMachine_to_Algorithm_def OTR_HOMachine_def proc_state.inject)
  moreover have "\<not> (2*N) div 3 < card {q. ?rcvd q \<noteq> Void \<and> ?rcvd q \<noteq> Bot}" using assms by auto
  ultimately have "ss = st" by (simp add:OTR_nextState_def)
  thus ?thesis by (simp add: Active \<open>rho (Suc n) p = Active st\<close>)
next
  case (Aslept)
  thus ?thesis by auto
qed

lemma A1:
  assumes run:"HORun (HOMachine_to_Algorithm OTR_M) rho HOs" (is "HORun ?A _ _")
  and dec1: "rho n       p = Active \<lparr> x = v1, decide = True \<rparr>" (is "_ = Active ?ss")
  and dec2: "rho (Suc n) p = Active \<lparr> x = v2, decide = True \<rparr>" (is "_ = Active ?st")
  and chg:"v1 \<noteq> v2"
  shows "(2*N) div 3 < card { q . \<exists>b. (rho n q) = Active \<lparr> x = v2, decide = b \<rparr> }"
proof -
  have "OTR_nextState p ?ss (HOrcvdMsgs ?A p (HOs n p) (rho n)) ?st" (is "OTR_nextState p ?ss ?rcvd ?st")
    using assms unfolding HORun_def CHORun_def HOnextConfig_def CHOnextConfig_def HOMachine_to_Algorithm_def OTR_HOMachine_def
    by fastforce
  moreover have "?ss \<noteq> ?st" using assms by auto
  ultimately have maj:"(2*N) div 3 < card {q. ?rcvd q \<noteq> Void \<and> ?rcvd q \<noteq> Bot}"
      and exmaj:"\<exists>vv. TwoThirds ?rcvd vv"
      and v2mfr:"v2 = Min {v. MFR ?rcvd v}" by (auto simp:OTR_nextState_def)
  hence "TwoThirds ?rcvd v2"
  proof -
    from exmaj obtain vv where majvv:"TwoThirds ?rcvd vv" by auto
    moreover have "vv = v2"
    proof (rule ccontr)
      assume "\<not> vv = v2"
      then obtain q where "?rcvd q \<noteq> Void \<and> ?rcvd q \<noteq> Bot" using maj by (smt Collect_empty_eq card.empty not_less0)
      hence "\<exists>v. ?rcvd q = Content v" by (cases "?rcvd q") auto
      hence "MFR ?rcvd v2" using v2mfr MFR_finite maj by auto
      hence "card (HOV ?rcvd v2) \<ge> card (HOV ?rcvd vv)" by (simp add:MFR_def)

      moreover have "HOV ?rcvd v2 \<inter> HOV ?rcvd vv = {}" by (smt CollectD HOV_def \<open>vv \<noteq> v2\<close> disjoint_iff_not_equal message.inject)
      hence "card (HOV ?rcvd v2 \<union> HOV ?rcvd vv) = card (HOV ?rcvd v2) + card (HOV ?rcvd vv)" (is "?cardunion = _")
        by (simp add: card_Un_disjoint)

      moreover have "\<forall>k. k > (2*N) div 3 \<longrightarrow> 2*k > N" by auto
      hence "2 * card (HOV ?rcvd vv) > N" using majvv TwoThirds_def by fastforce

      ultimately have "?cardunion > N" by auto
      thus "False" by (meson card_mono finite leD le_iff_sup sup_top_right)
    qed
    ultimately show ?thesis by auto
  qed
  moreover have "\<forall>q v. ?rcvd q = Content v \<longrightarrow> (\<exists>b. rho n q = Active \<lparr> x = v, decide = b \<rparr>)"
  proof
    fix q
    show "\<forall>v. ?rcvd q = Content v \<longrightarrow> (\<exists>b. rho n q = Active \<lparr> x = v, decide = b \<rparr>)"
    proof
      fix v
      show "?rcvd q = Content v \<longrightarrow> (\<exists>b. rho n q = Active \<lparr> x = v, decide = b \<rparr>)"
      proof
        assume sdf:"?rcvd q = Content v"
        hence "(HOrcvdMsgs ?A p (HOs n p) (rho n)) q = Content v" by (simp add:HOrcvdMsgs_def)
        moreover have "\<exists>s. rho n q = Active s" using sdf
          by (metis HOrcvMsgs_q.elims HOrcvdMsgs_def message.simps(3) message.simps(5))
        then obtain s where stat:"rho n q = Active s" by auto
        ultimately have "v = sendMsg ?A q p s"
          by (metis HOrcvMsgs_q.simps(1) HOrcvdMsgs_def message.inject message.simps(5))
        hence "x s = v" by (simp add:HOMachine_to_Algorithm_def OTR_HOMachine_def OTR_sendMsg_def)
        hence "\<exists>b. s = \<lparr> x = v, decide = b \<rparr>" by (metis old.unit.exhaust pstate.surjective)
        thus "\<exists>b. rho n q = Active \<lparr> x = v, decide = b \<rparr>" using stat by auto
      qed
    qed
  qed
  hence "\<forall>v. HOV ?rcvd v \<subseteq> { q . \<exists>b. (rho n q) = Active \<lparr> x = v, decide = b \<rparr> }" using HOV_def by fastforce
  ultimately show ?thesis by (smt Collect_cong TwoThirds_def card_mono finite leD order.trans order_less_le)
qed

text \<open>
  The following lemma \<open>A2\<close> contains the crucial correctness argument:
  if more than $2/3$ of all processes send \<open>v\<close> and process \<open>p\<close>
  hears from more than $2/3$ of all processes then the \<open>x\<close> field of
  \<open>p\<close> will be updated to \<open>v\<close>.
\<close>

lemma A2:
  assumes run: "HORun (HOMachine_to_Algorithm OTR_M) rho HOs" (is "HORun ?A _ _")
  and HO: "(2*N) div 3
             < card { q . HOrcvdMsgs (HOMachine_to_Algorithm OTR_M) p (HOs n p) (rho n) q \<noteq> Void \<and>
                          HOrcvdMsgs (HOMachine_to_Algorithm OTR_M) p (HOs n p) (rho n) q \<noteq> Bot }"
  and maj: "(2*N) div 3 < card { q . \<exists>s. x s = v \<and> (rho n q) = Active s }"
  and act:"rho n p = Active ss"
  and acts:"rho (Suc n) p = Active st"
  shows "x st = v"
proof -
  have nxt: "OTR_nextState p ss (HOrcvdMsgs ?A p (HOs n p) (rho n)) st" (is "OTR_nextState _ _ ?msgs _")
    using HORun_def CHORun_def HOnextConfig_def OTR_HOMachine_def HOMachine_to_Algorithm_def run act acts
    by (smt CHOAlgorithm.select_convs(3) CHOnextConfig_def proc_state.inject)
  let ?HOVothers = "\<Union> { HOV ?msgs w | w . w \<noteq> v}"
  \<comment> \<open>processes from which @{text p} received values different from @{text v}\<close>
  
  have "HOV ?msgs v \<union> ?HOVothers = \<Union> {HOV ?msgs w | w .True}" by auto
  also have "\<dots> = {q. \<exists>v. q \<in> HOV ?msgs v}" by auto
  also have "\<dots> = {q. \<exists>v. ?msgs q = Content v}" by (simp add:HOV_def)
  also have"\<dots> = {q. \<exists>v. ?msgs q \<noteq> Void \<and> ?msgs q \<noteq> Bot}" by (metis message.distinct(3) message.exhaust message.simps(3))
  finally have unio:"HOV ?msgs v \<union> ?HOVothers = {q. \<exists>v. ?msgs q \<noteq> Void \<and> ?msgs q \<noteq> Bot}" .

  moreover have "\<forall>q w. w \<noteq> v \<longrightarrow> q \<in> HOV ?msgs v \<longrightarrow> q \<notin> HOV ?msgs w" by (auto simp:HOV_def)
  hence "HOV ?msgs v \<inter> ?HOVothers = {}" by auto

  ultimately have "card (HOV ?msgs v) + card ?HOVothers = card {q. ?msgs q \<noteq> Void \<and> ?msgs q \<noteq> Bot}"
    by (metis (no_types, lifting) card_Un_disjoint finite)

  moreover have "\<forall>q w. w \<noteq> v \<longrightarrow> q \<in> HOV ?msgs w \<longrightarrow> \<not>(\<exists>s. x s = v \<and> (rho n q) = Active s)"
  proof
    fix q
    show "\<forall>w. w \<noteq> v \<longrightarrow> q \<in> HOV ?msgs w \<longrightarrow> \<not>(\<exists>s. x s = v \<and> (rho n q) = Active s)"
    proof
      fix w
      show "w \<noteq> v \<longrightarrow> q \<in> HOV ?msgs w \<longrightarrow> \<not>(\<exists>s. x s = v \<and> (rho n q) = Active s)"
      proof
        assume diff:"w \<noteq> v"
        show "q \<in> HOV ?msgs w \<longrightarrow> \<not>(\<exists>s. x s = v \<and> (rho n q) = Active s)"
        proof
          assume "q \<in> HOV ?msgs w"
          hence contw:"?msgs q = Content w" by (simp add:HOV_def)
          show "\<not>(\<exists>s. x s = v \<and> (rho n q) = Active s)"
          proof
            assume "\<exists>s. x s = v \<and> rho n q = Active s"
            then obtain s where "x s = v" and "rho n q = Active s" by auto
            hence "sendMsg ?A q p s = v"
              by (metis CHOAlgorithm.select_convs(2) HOMachine_to_Algorithm_def OTR_HOMachine_def OTR_sendMsg_def)
            hence "?msgs q = Content v" using HOrcvdMsgs_def
              by (metis HOrcvMsgs_q.simps(1) \<open>?msgs q = Content w\<close> \<open>rho n q = Active s\<close> message.simps(5))
            thus "False" using diff contw by auto
          qed
        qed
      qed
    qed
  qed
  hence intervide:"?HOVothers \<inter> { q . \<exists>s. x s = v \<and> (rho n q) = Active s } = {}" by blast
  hence "card ?HOVothers + card { q . \<exists>s. x s = v \<and> (rho n q) = Active s} \<le> N"
    by (metis (no_types, lifting) card_Un_disjoint card_mono finite top.extremum)
  hence "card ?HOVothers \<le> N div 3" using maj by auto

  ultimately have "card ?HOVothers < card (HOV ?msgs v)" using HO by auto
  moreover have "\<forall>ww. ww \<noteq> v \<longrightarrow> HOV ?msgs ww \<subseteq> ?HOVothers" by auto
  ultimately have v_seul_MFR:"\<forall>ww. ww \<noteq> v \<longrightarrow> card (HOV ?msgs ww) < card (HOV ?msgs v)"
    by (smt card_seteq finite less_imp_le_nat not_le_imp_less order.trans)

  have "{v. MFR ?msgs v} = {v}"
  proof
    show "{v. MFR ?msgs v} \<subseteq> {v}"
    proof
      fix ww
      assume "ww \<in> {v. MFR ?msgs v}"
      hence "card (HOV ?msgs ww) \<ge> card (HOV ?msgs v)" by (simp add:MFR_def)
      thus "ww \<in> {v}"  using v_seul_MFR by auto
    qed
  next
    show "{v} \<subseteq> {v. MFR ?msgs v}"
    proof
      fix ww
      assume "ww \<in> {v}"
      hence "ww = v" by auto
      moreover have "MFR ?msgs v" using MFR_def v_seul_MFR by fastforce
      ultimately show "ww \<in> {v. MFR ?msgs v}" by auto
    qed
  qed
  hence "v = Min {vv. MFR ?msgs vv}" by auto
  moreover have "st = \<lparr> x = Min {vv. MFR ?msgs vv}, decide = \<exists>v. TwoThirds ?msgs v \<rparr>" using HO nxt OTR_nextState_def by fastforce
  ultimately show ?thesis by auto
qed

text \<open>
  Therefore, once more than two thirds of the processes hold \<open>v\<close>
  in their \<open>x\<close> field, this will remain true forever.
\<close>

lemma A3:
  assumes run:"HORun (HOMachine_to_Algorithm OTR_M) rho HOs" (is "HORun ?A _ _")
      and n: "(2*N) div 3 < card { q. \<exists>s. x s = v \<and> (rho n q) = Active s }" (is "?twothird n")
  shows "?twothird (n+k)"
proof (induct k)
  from n show "?twothird (n+0)" by simp
next
  case (Suc m)
  assume m: "?twothird (n+m)"

  have "{p . \<exists>s. x s = v \<and> (rho (n+m) p) = Active s } \<subseteq> { p. \<exists>s. x s = v \<and> (rho (n+Suc m) p) = Active s }"
  proof
    fix p
    assume "p \<in> {p . \<exists>s. x s = v \<and> (rho (n+m) p) = Active s }"
    then obtain ss where vss:"x ss = v" and rhoss:"rho (n+m) p = Active ss" by auto
    hence "rho (1+(n+m)) p \<noteq> Aslept" using run nonAsleepAgain HORun_def by (metis proc_state.distinct(1))
    then obtain st where rhost:"rho (n+Suc m) p = Active st" by (cases "rho (n+Suc m) p") auto
    let ?msgs = "HOrcvdMsgs ?A p (HOs (n+m) p) (rho (n+m))"
    show "p \<in> { p. \<exists>s. x s = v \<and> (rho (n+Suc m) p) = Active s }"
    proof (cases "(2*N) div 3 < card { q. ?msgs q \<noteq> Void \<and> ?msgs q \<noteq> Bot }")
      case True
      hence "x st = v" using A2 run Suc.hyps rhoss rhost by auto
      thus "p \<in> {p . \<exists>s. x s = v \<and> (rho (n+Suc m) p) = Active s }" using rhost by auto
    next
      case False
      hence "ss = st" using nextState_change run rhoss rhost by fastforce
      thus "p \<in> {p . \<exists>s. x s = v \<and> (rho (n+Suc m) p) = Active s }" using rhost vss by auto
    qed
  qed
  hence "card {p. \<exists>s. x s = v \<and> rho (n + m) p = Active s} \<le> card {p. \<exists>s. x s = v \<and> rho (n + Suc m) p = Active s}"
    by (simp add: card_mono)
  thus "2*N div 3 < card {p. \<exists>s. x s = v \<and> rho (n + Suc m) p = Active s}" using Suc.hyps by auto
qed

text \<open>
  It now follows that once a process has decided on some value \<open>v\<close>, 
  more than two thirds of all processes continue to hold \<open>v\<close> in
  their \<open>x\<close> field.
\<close>

lemma A4:
  assumes run: "HORun (HOMachine_to_Algorithm OTR_M) rho HOs" (is "HORun ?A _ _")
  shows "\<forall>v k n. rho n p = Active \<lparr> x = v, decide = True \<rparr>
          \<longrightarrow> (2*N) div 3 < card { q. \<exists>s. x s = v \<and> rho (n+k) q = Active s }"
    (is "\<forall>v k n.  _ \<longrightarrow> (2*N) div 3 < card (?vproc n k v)")
proof
  fix v
  show "\<forall>k n. rho n p = Active  \<lparr> x = v, decide = True \<rparr>
        \<longrightarrow> (2*N) div 3 < card (?vproc n k v)" (is "\<forall>k n. rho _ _ = Active ?vstate \<longrightarrow> _")
  proof
    fix k
    show "\<forall>n. rho n p = Active ?vstate
        \<longrightarrow> (2*N) div 3 < card (?vproc n k v)"
    proof
      fix n
      show "rho n p = Active ?vstate
        \<longrightarrow> (2*N) div 3 < card (?vproc n k v)"
      proof (induction n arbitrary:k)
        case 0
        show "rho 0 p = Active ?vstate \<longrightarrow>
                (2*N) div 3 < card (?vproc 0 k v)"
        proof
          assume zer:"rho 0 p = Active ?vstate"
          have "CHOinitConfig ?A rho (\<lambda>r q. undefined)" using HORun_def CHORun_def run by fastforce
          hence "OTR_initState p ?vstate"
            using HOMachine_to_Algorithm_def CHOinitConfig_def OTR_HOMachine_def zer 
            by (smt CHOAlgorithm.select_convs(1) not_gr_zero)
          hence "decide ?vstate = False" by (simp add:OTR_initState_def)
          hence "False" using zer by auto
          thus "(2*N) div 3 < card (?vproc 0 k v)" by auto
        qed
      next
        case (Suc m)
        show "rho (Suc m) p = Active ?vstate \<longrightarrow>
                (2*N) div 3 < card (?vproc (Suc m) k v)"
        proof
          assume st:"rho (Suc m) p = Active ?vstate"
          show "(2*N) div 3 < card (?vproc (Suc m) k v)"
          proof (cases "rho m p = Active ?vstate")
            case True
            thus "(2*N) div 3 < card (?vproc (Suc m) k v)" using Suc.IH[where ?k = "k+1"] by auto
          next
            case False
            hence ssdiffst:"rho m p \<noteq> Active ?vstate" using st by auto
            show "(2*N) div 3 < card (?vproc (Suc m) k v)"
            proof (cases "rho m p")
              case ss_def:(Active ss)
              have "CHOnextConfig ?A (rho m) (HOs m) (\<lambda>w. undefined) (rho (Suc m))" using run CHORun_def HORun_def by fastforce
              hence "\<exists>st. rho (Suc m) p = Active st \<and> CnextState ?A p ss (HOrcvdMsgs ?A p (HOs m p) (rho m)) undefined st"
                (is "\<exists>st. _ \<and> CnextState _ _ _ ?msgs _ _") using \<open>rho m p = Active ss\<close> by (simp add:CHOnextConfig_def)
              hence "\<exists>st. rho (Suc m) p = Active st \<and> OTR_nextState p ss ?msgs st"
                by (simp add: HOMachine_to_Algorithm_def OTR_HOMachine_def)
              hence nextstat:"OTR_nextState p ss ?msgs ?vstate" using st by auto
              hence "\<exists>vv. TwoThirds ?msgs vv" using ssdiffst ss_def by (simp add: OTR_nextState_def)
              then obtain vv where "TwoThirds ?msgs vv" by auto
              hence majHO:"(2*N) div 3 < card {q. ?msgs q = Content vv}" by (simp add:TwoThirds_def HOV_def HOrcvdMsgs_def)
              moreover have "\<forall>q. ?msgs q = Content vv \<longrightarrow> (\<exists>s. rho m q = Active s \<and> sendMsg ?A q p s = vv)"
                using HOrcvdMsgs_def  by (metis HOrcvMsgs_q.elims message.distinct(1) message.distinct(3) message.inject)
              hence "\<forall>q. ?msgs q = Content vv \<longrightarrow> (\<exists>s. rho m q = Active s \<and> OTR_sendMsg q p s = vv)"
                by (simp add: OTR_HOMachine_def HOMachine_to_Algorithm_def)
              hence "\<forall>q. ?msgs q = Content vv \<longrightarrow> (\<exists>s. rho m q = Active s \<and> x s = vv)" by (simp add: OTR_sendMsg_def)
              hence "{q. ?msgs q = Content vv} \<subseteq>  {q. \<exists>s. rho m q = Active s \<and> x s = vv}" by auto
              hence "card {q. ?msgs q = Content vv} \<le> card {q. \<exists>s. rho m q = Active s \<and> x s = vv}" by (simp add: card_mono)
              ultimately have majvv:"(2*N) div 3 < card {q. \<exists>s. x s = vv \<and> rho m q = Active s }"
                by (smt Collect_cong less_le_trans)

              moreover have "?msgs qq = Content vv \<longrightarrow> (?msgs qq \<noteq> Void \<and> ?msgs qq \<noteq> Bot)" by (cases "?msgs qq") auto
              hence "{q. ?msgs q = Content vv} \<subseteq> {q. ?msgs q \<noteq> Void \<and> ?msgs q \<noteq> Bot}" by auto
              hence "card {q. ?msgs q = Content vv} \<le> card {q. ?msgs q \<noteq> Void \<and> ?msgs q \<noteq> Bot}" by (simp add: card_mono)
              hence "(2*N) div 3 < card {q. ?msgs q \<noteq> Void \<and> ?msgs q \<noteq> Bot}" using majHO by auto
              ultimately have  "x ?vstate = vv"
                using run A2[where ?n = m and ?v = vv and ?ss = ss and ?st = "?vstate"] ss_def st by auto
              hence "v = vv" by auto
              hence "(2*N) div 3 < card {q. \<exists>s. x s = v \<and> rho m q = Active s }" using majvv by auto
              thus "(2*N) div 3 < card (?vproc (Suc m) k v)" using run A3[where ?k = "Suc k"] by auto
            next
              case Aslept
              moreover have "CHOinitConfig ?A rho (\<lambda>r q. undefined)" using HORun_def CHORun_def run by fastforce
              hence "rho m p = Aslept \<longrightarrow> rho (Suc m) p = Active ?vstate \<longrightarrow> CinitState ?A p ?vstate undefined"
                using CHOinitConfig_def by (metis diff_Suc_1)
              ultimately have "OTR_initState p ?vstate"
                using HOMachine_to_Algorithm_def CHOinitConfig_def OTR_HOMachine_def st 
                by (smt CHOAlgorithm.select_convs(1) not_gr_zero)
              hence "decide ?vstate = False" by (simp add:OTR_initState_def)
              hence "False" by auto
              thus "(2*N) div 3 < card (?vproc (Suc m) k v)" by auto
            qed
          qed
        qed
      qed
    qed
  qed
qed

text \<open>
  The Agreement property follows easily from lemma \<open>A4\<close>: if processes
  \<open>p\<close> and \<open>q\<close> decide values \<open>v\<close> and \<open>w\<close>,
  respectively, then more than two thirds of the processes must propose
  \<open>v\<close> and more than two thirds must propose \<open>w\<close>.
  Because these two majorities must have an intersection, we must have
  \<open>v=w\<close>.

  We first prove an ``asymmetric'' version of the agreement property before
  deriving the general agreement theorem.
\<close>


lemma A5:
  assumes run:"HORun (HOMachine_to_Algorithm OTR_M) rho HOs"
  and p: "rho n p = Active \<lparr> x = v, decide = True\<rparr>"
  and p': "rho (n+k) p' = Active \<lparr> x = w, decide = True \<rparr>"
  shows "v = w"
proof -  
  show ?thesis
  proof (rule ccontr)
    assume diff:"\<not> v = w"
    moreover have "(2*N) div 3 < card {q. \<exists>s. x s = v \<and> rho (n+k) q = Active s}" (is "_ < card ?V")
      using run p by (blast dest: A4)
    moreover have "(2*N) div 3 < card {q. \<exists>s. x s = w \<and> rho ((n+k)+0) q = Active s}" (is "_ < card ?W")
      using run p' by (blast dest: A4)
    moreover have "?V \<inter> ?W = {}" using diff by auto
    hence "card (?V \<union> ?W) = card ?V + card ?W" using card_Un_disjoint by (simp add: card_Un_disjoint)
    moreover have "\<forall>k. k > (2*N) div 3 \<longrightarrow> 2*k > N" by auto
    ultimately have "card (?V \<union> ?W) > N" by auto
    moreover have "card (?V \<union> ?W) \<le> N" by (simp add: card_mono)
    ultimately show "False" by auto
  qed
qed

theorem OTR_agreement:
  assumes run:"HORun (HOMachine_to_Algorithm OTR_M) rho HOs"
  and p: "rho n p = Active \<lparr> x = v, decide = True \<rparr>"
  and p': "rho m p' = Active \<lparr> x = w, decide = True \<rparr>"
  shows "v = w"
proof (cases "n \<le> m")
  case True
  then obtain k where "m = n+k" by (auto simp add: le_iff_add)
  with run p p' show ?thesis by (auto elim: A5)
next
  case False
  hence "m \<le> n" by auto
  then obtain k where "n = m+k"  by (auto simp add: le_iff_add)
  with run p p' have "w = v" by (auto elim: A5)
  thus ?thesis ..
qed


subsection \<open>Proof of  Termination\<close>

text \<open>
  We now show that every process must eventually decide.

  The idea of the proof is to observe that the communication predicate
  guarantees the existence of two uniform rounds where every process hears
  from the same two-thirds majority of processes. The first such round
  serves to ensure that all \<open>x\<close> fields hold the same value, the
  second round copies that value into all decision fields.

  Lemma \<open>A2\<close> is instrumental in this proof.
\<close>

lemma commute_set : "card {q. \<exists>s. A s q \<and> B s q} = card {q. \<exists>s. B s q \<and> A s q}"
   by meson

theorem OTR_termination:
  assumes run: "HORun (HOMachine_to_Algorithm OTR_M) rho HOs" (is "HORun ?A _ _")
  and commG: "HOcommActive OTR_M HOs rho"
  shows "\<exists>r v. rho r p = Active \<lparr> x = v, decide = True \<rparr>"
proof -
have aslasl:"\<forall>p. \<exists>rmax. \<forall>n. n \<ge> rmax \<longrightarrow> rho n p = Aslept \<longrightarrow> rho (Suc n) p = Aslept"
proof
  fix p
  have "(\<exists>rmax. \<forall>n. n \<ge> rmax \<longrightarrow> rho n p \<noteq> Aslept) \<or> \<not> (\<exists>rmax. \<forall>n. n \<ge> rmax \<longrightarrow> rho n p \<noteq> Aslept)" by auto
  hence "\<exists>rmax. \<forall>n. n \<ge> rmax \<longrightarrow> rho n p = Aslept \<longrightarrow> rho (Suc n) p = Aslept"
  proof
    assume "\<exists>rmax. \<forall>n. n \<ge> rmax \<longrightarrow> rho n p \<noteq> Aslept"
    thus ?thesis by auto
  next
    assume "\<not> (\<exists>rmax. \<forall>n. n \<ge> rmax \<longrightarrow> rho n p \<noteq> Aslept)"
    hence aslinf:"\<forall>rmax. \<exists>n. n \<ge> rmax \<and> rho n p = Aslept" by auto
    have "\<forall>n. rho n p = Aslept"
    proof (rule ccontr)
      assume "\<not> (\<forall>n. rho n p = Aslept)"
      hence "\<exists>n. rho n p \<noteq> Aslept" by auto
      then obtain n where "rho n p \<noteq> Aslept" by auto
      moreover have "\<exists>nasl. nasl \<ge> n \<and> rho nasl p = Aslept" using aslinf by auto
      then obtain nasl where "nasl \<ge> n " and "rho nasl p = Aslept" by auto
      ultimately show "False" using nonAsleepAgain[where ?n = n and ?m = "nasl - n"] run HORun_def by fastforce
    qed
    thus ?thesis by auto
  qed
  thus "\<exists>rmax. \<forall>n. n \<ge> rmax \<longrightarrow> rho n p = Aslept \<longrightarrow> rho (Suc n) p = Aslept" by auto
qed
have "\<forall>subP. \<exists>rmax. \<forall>n p. p \<in> subP \<longrightarrow> n \<ge> rmax \<longrightarrow> rho n p = Aslept \<longrightarrow> rho (Suc n) p = Aslept"
proof
  fix subP
  show "\<exists>rmax. \<forall>n p. p \<in> subP \<longrightarrow> n \<ge> rmax \<longrightarrow> rho n p = Aslept \<longrightarrow> rho (Suc n) p = Aslept"
  proof (induction "card subP" arbitrary:subP)
    case 0
    thus "\<exists>ramx. \<forall>n p. p \<in> subP \<longrightarrow> n \<ge> ramx \<longrightarrow> rho n p = Aslept \<longrightarrow> rho (Suc n) p = Aslept" by auto
  next
    case (Suc m)
    hence "\<exists>subsubP pp. subP = subsubP \<union> {pp} \<and> pp \<notin> subsubP" by (metis Un_insert_right card_eq_SucD sup_bot_right)
    then obtain subsubP pp where subpun:"subP = subsubP \<union> {pp}" and "pp \<notin> subsubP" by auto
    hence "card subsubP = m" using Suc by auto
    then obtain nn where nn_def:"\<forall>n p. p \<in> subsubP \<longrightarrow> n \<ge> nn \<longrightarrow> rho n p = Aslept \<longrightarrow> rho (Suc n) p = Aslept"
      using Suc.hyps by fastforce
    from aslasl obtain rmax where  rmax_def:"\<forall>n. n \<ge> rmax \<longrightarrow> rho n pp = Aslept \<longrightarrow> rho (Suc n) pp = Aslept" by auto
    have  "\<forall>n p. p \<in> subP \<longrightarrow> n \<ge> (max nn rmax) \<longrightarrow> rho n p = Aslept \<longrightarrow> rho (Suc n) p = Aslept"
      using nn_def rmax_def by (simp add:subpun)
    thus "\<exists>ramx. \<forall>n p. p \<in> subP \<longrightarrow> n \<ge> ramx \<longrightarrow> rho n p = Aslept \<longrightarrow> rho (Suc n) p = Aslept" by (rule exI)
  qed 
qed
hence "\<exists>rmax. \<forall>n p. p \<in> UNIV \<longrightarrow> n \<ge> rmax \<longrightarrow> rho n p = Aslept \<longrightarrow> rho (Suc n) p = Aslept" by (rule allE)
then obtain rmax where "\<forall>n p. n \<ge> rmax \<longrightarrow> rho n p = Aslept \<longrightarrow> rho (Suc n) p = Aslept" by auto




have "\<exists>rs rp S P. rs \<ge> rmax \<and> (\<forall>p \<in> S. rho rs p \<noteq> Aslept) \<and> card S > (2*N) div 3 \<and> (\<forall>p \<in> S. S = HOs rs p) \<and>
   rp \<ge> rmax \<and> card P > (2*N) div 3 \<and> (\<forall>p \<in> P. rho rp p \<noteq> Aslept) \<and> (\<forall>p \<in> P. \<forall> q. p \<in> HOs rp q)"
    using commG by (simp add:OTR_commActive_def OTR_HOMachine_def)
then obtain rs S where "rs \<ge> rmax" and Sact:"\<forall>p \<in> S. rho rs p \<noteq> Aslept" and
  pic:"card S > (2*N) div 3" and pi:"\<forall>p \<in> S. S = HOs rs p" by auto

  have allact:"\<forall>p \<in> S. \<exists>ss. rho rs p = Active ss"
  proof
    fix p
    assume "p \<in> S"
    thus "\<exists>ss. rho rs p = Active ss" using \<open>\<forall>p \<in> S. rho rs p \<noteq> Aslept\<close> by (cases "rho rs p") auto
  qed
  let "?msgs q r" = "HOrcvdMsgs (HOMachine_to_Algorithm OTR_M) q (HOs r q) (rho r)"

  have msgs_eq:"\<forall>p q. p \<in> S \<longrightarrow> q \<in> S \<longrightarrow> ?msgs q rs = ?msgs p rs"
  proof 
    fix p 
    show "\<forall>q. p \<in> S \<longrightarrow> q \<in> S \<longrightarrow> ?msgs q rs = ?msgs p rs"
    proof
      fix q
      show "p \<in> S \<longrightarrow> q \<in> S \<longrightarrow> ?msgs q rs = ?msgs p rs"
      proof 
        assume pinS:"p \<in> S"
        show "q \<in> S \<longrightarrow> ?msgs q rs = ?msgs p rs"
        proof
          assume qinS:"q \<in> S"
          show "?msgs q rs = ?msgs p rs"
          proof
            fix h
            show "?msgs q rs h = ?msgs p rs h"
            proof (cases "h \<in> S")
              assume "h \<in> S"
              from allact and this obtain sh where "rho rs h = Active sh" by auto
              hence "?msgs p rs h = (if h \<in> S then Content (x sh) else Void)"
                using pi Sact HOrcvdMsgs_def HOMachine_to_Algorithm_def OTR_HOMachine_def OTR_sendMsg_def
                by (metis (no_types, lifting) CHOAlgorithm.select_convs(2) HOrcvMsgs_q.simps(1) pinS) 
              moreover have "?msgs q rs h = (if h \<in> S then Content (x sh) else Void)"
                using pi Sact HOrcvdMsgs_def HOMachine_to_Algorithm_def OTR_HOMachine_def OTR_sendMsg_def \<open>rho rs h = Active sh\<close>
                by (metis (no_types, lifting) CHOAlgorithm.select_convs(2) HOrcvMsgs_q.simps(1) qinS) 
              finally show "?msgs q rs h = ?msgs p rs h" by auto
            next
              assume "\<not> h \<in> S"
              hence "?msgs p rs h = Void" using pi Sact HOrcvdMsgs_def by (metis (no_types, lifting) pinS) 
              moreover have "?msgs q rs h = Void" using pi Sact HOrcvdMsgs_def \<open>\<not> h \<in> S\<close> by (metis (no_types, lifting) qinS) 
              finally show "?msgs q rs h = ?msgs p rs h" by auto
            qed
          qed
        qed
      qed
    qed
  qed

  moreover from pic obtain exppp where "exppp \<in> S" by fastforce
  ultimately have "\<forall>q \<in> S. ?msgs q rs = ?msgs exppp rs" by blast
  let ?mu = "?msgs exppp rs"
  have majHO:"\<forall>p \<in> S. (2*N) div 3 < card {q. ?msgs p rs q \<noteq> Void \<and> ?msgs p rs q \<noteq> Bot}"
  proof
    fix p
    assume "p \<in> S"
    have "\<forall>h. h \<in> S \<longrightarrow> ?msgs p rs h \<noteq> Void \<and> ?msgs p rs h \<noteq> Bot"
    proof (rule allI impI )
      fix h
      show "h \<in> S \<longrightarrow> ?msgs p rs h \<noteq> Void \<and> ?msgs p rs h \<noteq> Bot"
      proof
        assume "h \<in> S"
        hence "h \<in> HOs rs p" using pi \<open>p \<in> S\<close> by auto
        moreover from allact obtain sh where "rho rs h = Active sh" using \<open>h \<in> S\<close> by auto
        ultimately have "?msgs p rs h = Content (sendMsg ?A h p sh)" 
          by (auto simp: run HORun_def CHOnextConfig_def HOrcvdMsgs_def CHORun_def)
        thus "?msgs p rs h \<noteq> Void \<and> ?msgs p rs h \<noteq> Bot" by (cases "?msgs p rs h") auto
      qed
    qed
    thus "(2*N) div 3 < card {q. ?msgs p rs q \<noteq> Void \<and> ?msgs p rs q \<noteq> Bot}" using pic 
      by (smt HOrcvdMsgs_def \<open>p \<in> S\<close> mem_Collect_eq pi subsetI subset_antisym) 
  qed
  have "\<forall>q \<in> S. \<exists>sq. rho (Suc rs) q = Active sq \<and> x sq = Min {v . MFR (?msgs q rs) v}"
  proof
    fix q
    assume "q \<in> S"
    from allact and this obtain sq where "rho rs q = Active sq" by auto
    hence chonxt:"CHOnextConfig ?A (rho rs) (HOs rs) (\<lambda>w. undefined) (rho (Suc rs))" using run by (simp add:HORun_def CHORun_def)
    then obtain sqq where "rho (Suc rs) q = Active sqq" and "CnextState ?A q sq (?msgs q rs) undefined sqq"
      using \<open>rho rs q = Active sq\<close> by (auto simp:CHOnextConfig_def)
    hence "x sqq =  Min {v . MFR (?msgs q rs) v}"
      using majHO \<open>q \<in> S\<close> by (simp add:OTR_HOMachine_def HOMachine_to_Algorithm_def OTR_nextState_def )
    thus "\<exists>sq. rho (Suc rs) q = Active sq \<and> x sq = Min {v . MFR (?msgs q rs) v}" using \<open>rho (Suc rs) q = Active sqq\<close> by auto
  qed
  hence "\<forall>q \<in> S. \<exists>sq. rho (Suc rs) q = Active sq \<and> x sq = Min {v . MFR ?mu v}" by (metis msgs_eq \<open>exppp \<in> S\<close>)
  then obtain v where "\<forall>q \<in> S. \<exists>sq. rho (Suc rs) q = Active sq \<and> x sq = v" by auto
  hence "S \<subseteq> {q. \<exists>sq. rho (Suc rs) q = Active sq \<and> x sq = v}" by auto
  moreover have "N > 0" by (rule finite_UNIV_card_ge_0) simp
  hence "finite {q. \<exists>sq. rho (Suc rs) q = Active sq \<and> x sq = v}" by auto
  ultimately have "(2*N) div 3 < card {q. \<exists>sq. rho (Suc rs) q = Active sq \<and> x sq = v}"
    using card_mono pic  by (smt card_seteq le_trans nat_less_le) 
  hence majv:"\<forall>k :: nat. (2*N) div 3 < card {q. \<exists>sq. x sq = v \<and> rho (Suc rs + k) q = Active sq}"
    using A3[where ?n = "Suc rs"] run commute_set[of "\<lambda>s q. rho (Suc rs) q = Active s" "\<lambda>s q. x s = v"] by auto


  have "\<exists>rs0 rp S P. rs0 \<ge> Suc rs \<and> (\<forall>p \<in> S. rho rs0 p \<noteq> Aslept) \<and> card S > (2*N) div 3 \<and> (\<forall>p \<in> S. S = HOs rs0 p) \<and>
    rp \<ge> Suc rs \<and> card P > (2*N) div 3 \<and> (\<forall>p \<in> P. rho rp p \<noteq> Aslept) \<and> (\<forall>p \<in> P. \<forall> q. p \<in> HOs rp q)"
      using commG by (simp add:OTR_commActive_def OTR_HOMachine_def)
  then obtain rp P where "rp \<ge> Suc rs" and Pact:"\<forall>p \<in> P. rho rp p \<noteq> Aslept" and
    pic:"card P > (2*N) div 3" and pi:"\<forall>p \<in> P. \<forall>q. p \<in> HOs rp q" by auto

  have v:"\<forall>p. rho rp p \<noteq> Aslept \<longrightarrow> (\<exists>b. rho (Suc rp) p = Active (\<lparr> x = v, decide = b \<rparr>))"
  proof (rule allI)
    fix p
    show "rho rp p \<noteq> Aslept \<longrightarrow> (\<exists>b. rho (Suc rp) p = Active (\<lparr> x = v, decide = b \<rparr>))"
    proof
      assume "rho rp p \<noteq> Aslept"
      then obtain sp where "rho rp p = Active sp" by (cases "rho rp p") auto
      hence "rho (Suc rp) p \<noteq> Aslept" using nonAsleepAgain[of rho rp p _ HOs _ "1"] run HORun_def by fastforce
      then obtain spp where "rho (Suc rp) p = Active spp" by (cases "rho (Suc rp) p") auto
      let ?rcvd = "HOrcvdMsgs (HOMachine_to_Algorithm OTR_M) p (HOs rp p) (rho rp)"
      have "\<forall>q \<in> P. ?rcvd q \<noteq> Void \<and> ?rcvd q \<noteq> Bot" using pi run HOrcvdMsgs_def Pact
        by (metis HOrcvMsgs_q.elims message.simps(3) message.simps(5))
      hence "P \<subseteq> {q. ?rcvd q \<noteq> Void \<and> ?rcvd q \<noteq> Bot}" by auto
      hence "(2*N) div 3 < card {q. ?rcvd q \<noteq> Void \<and> ?rcvd q \<noteq> Bot}" using pic card_mono \<open>N > 0\<close>
        by (smt finite_code le_trans linorder_not_less)
      moreover have "2 * N div 3 < card {q :: Proc. \<exists>sq. x sq = v \<and> rho (Suc rs + (rp - Suc rs)) q = Active sq}"
        using majv \<open>rp \<ge> Suc rs\<close>
        allE[of "\<lambda>k. 2 * N div 3 < card {q :: Proc. \<exists>sq. x sq = v \<and> rho (Suc rs + k) q = Active sq}" "rp - Suc rs" _] by simp
      hence "2 * N div 3 < card {q :: Proc. \<exists>sq. x sq = v \<and> rho rp q = Active sq}" using \<open>rp \<ge> Suc rs\<close> by auto
      ultimately have "x spp = v" using A2[where ?n = rp] run majv \<open>rho rp p = Active sp\<close> \<open>rho (Suc rp) p = Active spp\<close> by simp
      hence "rho (Suc rp) p = Active (\<lparr> x = v, decide = decide spp \<rparr>)" using \<open>rho (Suc rp) p = Active spp\<close> by auto
      thus "\<exists>b. rho (Suc rp) p = Active (\<lparr> x = v, decide = b \<rparr>)" using \<open>rho (Suc rp) p = Active spp\<close> by auto
    qed
  qed

  have P:"\<forall>k. \<forall>q. rho rp q \<noteq> Aslept \<longrightarrow> (\<exists>b. rho (Suc rp + k) q = Active \<lparr> x = v, decide = b \<rparr>)"
  proof
    fix k
    show "\<forall>q. rho rp q \<noteq> Aslept \<longrightarrow> (\<exists>b. rho (Suc rp + k) q = Active \<lparr> x = v, decide = b \<rparr>)"
    proof (induct k)
      show "\<forall>q. rho rp q \<noteq> Aslept \<longrightarrow> (\<exists>b. rho (Suc rp + 0) q = Active \<lparr> x = v, decide = b \<rparr>)" using v by auto
    next
      fix k
      assume ih:"\<forall>q. rho rp q \<noteq> Aslept \<longrightarrow> (\<exists>b. rho (Suc rp + k) q = Active \<lparr> x = v, decide = b \<rparr>)"
      show "\<forall>q. rho rp q \<noteq> Aslept \<longrightarrow> (\<exists>b. rho (Suc rp + Suc k) q = Active \<lparr> x = v, decide = b \<rparr>)"
      proof
        fix q
        show "rho rp q \<noteq> Aslept \<longrightarrow> (\<exists>b. rho (Suc rp + Suc k) q = Active \<lparr> x = v, decide = b \<rparr>)"
        proof
        assume "rho rp q \<noteq> Aslept"
        show "\<exists>b. rho (Suc rp + Suc k) q = Active \<lparr> x = v, decide = b \<rparr>"
        proof (cases "(2*N) div 3 < card { p . ?msgs q (Suc rp + k) p \<noteq> Void \<and> ?msgs q (Suc rp + k) p \<noteq> Bot }")
          case True
          have "\<exists>b. rho (Suc rp + k) q = Active \<lparr> x = v, decide = b \<rparr>" using ih \<open>rho rp q \<noteq> Aslept\<close> by simp
          from this obtain sp where "rho (Suc rp + k) q = Active sp" by auto
          moreover have "rho (Suc rp + Suc k) q \<noteq> Aslept" 
            using nonAsleepAgain[where ?n = "Suc rp + k" and ?p = q]
             run HORun_def  by (smt Groups.add_ac(2) \<open>rho rp q \<noteq> Aslept\<close> nonAsleepAgain proc_state.simps(3) v)
          then obtain spp where "rho (Suc rp + Suc k) q = Active spp" by (cases "rho (Suc rp + Suc k) q") auto
          moreover from majv have "2 * N div 3 < card {q. \<exists>s. x s = v \<and> rho (Suc rp + k) q = Active s}"
            using allE[of "\<lambda>k. 2 * N div 3 < card {q. \<exists>s. x s = v \<and> rho (Suc rs + k) q = Active s}" "rp - rs + k" _]
            \<open>rp \<ge> Suc rs\<close> by simp
          ultimately have "x spp = v" using A2[where ?n = "Suc rp + k" and ?p = q] run majv True by simp
          thus "rho (Suc rp + Suc k) q = Active \<lparr> x = v, decide = b \<rparr>"
          hence "\<forall>p. \<exists>s. x s = v \<and> rho (Suc rp + k) p = Active s" using ih by force
          hence "{p :: Proc. \<exists>s. x s = v \<and> rho (Suc r0 + k) p = Active s} = (UNIV :: Proc set)" by auto
          hence "card {p :: Proc. \<exists>s. x s = v \<and> rho (Suc r0 + k) p = Active s} = N" by simp
          moreover have "N > 0" by (rule finite_UNIV_card_ge_0) simp
          hence "N > (2*N) div 3" by auto
          ultimately have "(2*N) div 3 < card {p :: Proc . \<exists>s. x s = v \<and> rho (Suc r0 + k) p = Active s}" by auto
          
          moreover have "Suc r0 + Suc k \<ge> eveil" using \<open>r0 \<ge> eveil\<close> by auto
          hence "rho (Suc r0 + Suc k) q \<noteq> Aslept" 
            using nonAsleepAgain[where ?m = "Suc r0 + Suc k - eveil" and ?n = eveil and ?p = q]
            \<open>\<forall>p. rho eveil p \<noteq> Aslept\<close> run HORun_def  by (smt Nat.le_imp_diff_is_add eq_imp_le)
          then obtain sqq where "rho (Suc r0 + Suc k) q = Active sqq" by (cases "rho (Suc r0 + Suc k) q") auto
          moreover from ih obtain sq where "rho (Suc r0 + k) q = Active sq" by auto

          ultimately have "x sqq = v" using True run A2 majHO by auto 
          thus ?thesis using \<open>rho (Suc r0 + Suc k) q = Active sqq\<close> by (metis pstate.cases pstate.select_convs(1))
        next
          case False
          have "{p. ?msgs q (Suc r0 + k) p \<noteq> Void \<and> ?msgs q (Suc r0 + k) p \<noteq> Bot} \<subseteq>
                {p. ?msgs q (Suc r0 + k) p \<noteq> Void }" by auto
          hence " card {p. ?msgs q (Suc r0 + k) p \<noteq> Void \<and> ?msgs q (Suc r0 + k) p \<noteq> Bot} \<le>
                  card {p. ?msgs q (Suc r0 + k) p \<noteq> Void }" by (simp add: card_mono)
          hence "\<not> (2*N) div 3 < card {p. ?msgs q (Suc r0 + k) p \<noteq> Void \<and> ?msgs q (Suc r0 + k) p \<noteq> Bot}" using False by auto 
          with run ih have "rho (Suc r0 + k) q = Aslept \<or> rho (Suc r0 + k) q = rho (Suc r0 + Suc k) q"
            by (auto dest: nextState_change)
          moreover have "Suc r0 + k \<ge> eveil" using \<open>r0 \<ge> eveil\<close> by auto
          hence "rho (Suc r0 + k) q \<noteq> Aslept" 
            using nonAsleepAgain[where ?m = "Suc r0 + k - eveil" and ?n = eveil] \<open>\<forall>p. rho eveil p \<noteq> Aslept\<close> run HORun_def 
            by (smt Nat.le_imp_diff_is_add eq_imp_le)
          ultimately have "rho (Suc r0 + k) q = rho (Suc r0 + Suc k) q" by auto
          thus ?thesis using ih by metis
        qed
      qed
    qed
  qed

  from commG obtain r0' \<Pi>'
    where r0': "r0' \<ge> Suc r0"
      and pi': "\<forall>q. HOs r0' q = \<Pi>'"
      and pic': "card \<Pi>' > (2*N) div 3"
    by (force simp: OTR_HOMachine_def OTR_commGlobal_def)
  from r0' P have v':"\<forall>q. \<exists>b. rho r0' q = Active \<lparr> x = v, decide = b \<rparr>" by (auto simp: le_iff_add)
  then obtain sp where "rho r0' p = Active sp" by auto

  have "CHOnextConfig ?A (rho r0') (HOs r0') (\<lambda>l. undefined) (rho (Suc r0'))" using run by (auto simp:HORun_def CHORun_def)
  hence "\<exists>s'. rho (Suc r0') p = Active s' \<and> CnextState ?A p sp (?msgs p r0') undefined s'"
    using \<open>rho r0' p = Active sp\<close> by (auto simp:CHOnextConfig_def)
  then obtain spp where nxx:"rho (Suc r0') p = Active spp" and "CnextState ?A p sp (?msgs p r0') undefined spp" by auto
  hence "CnextState ?A p sp (?msgs p r0') undefined spp" by auto
  hence nxt:"OTR_nextState p sp (?msgs p r0') spp" by (auto simp:OTR_HOMachine_def HOMachine_to_Algorithm_def)

  have "\<forall>h. ?msgs p r0' h \<noteq> Bot"
  proof
    fix h
    show "?msgs p r0' h \<noteq> Bot"
    proof
      assume "?msgs p r0' h = Bot"
      hence "rho r0' h = Aslept" using HOrcvdMsgs_def
        by (metis HOrcvMsgs_q.elims message.distinct(5) message.simps(3))
      moreover have "r0' \<ge> eveil" using \<open>r0 \<ge> eveil\<close> and \<open>r0' \<ge> Suc r0\<close> by auto
      hence "rho r0' h \<noteq> Aslept" 
        using nonAsleepAgain[where ?m = "r0' - eveil" and ?n = eveil] \<open>\<forall>p. rho eveil p \<noteq> Aslept\<close> run HORun_def 
        by (smt Nat.le_imp_diff_is_add eq_imp_le)  
      ultimately show "False" by auto
    qed
  qed

  hence "\<forall>qq. qq \<in> \<Pi>' \<longrightarrow> ?msgs p r0' qq \<noteq> Void \<and> ?msgs p r0' qq \<noteq> Bot" using HOrcvdMsgs_def  pi'
    by (metis HOrcvMsgs_q.elims message.distinct(3) message.distinct(5))
  hence "card \<Pi>' \<le>  card {q. (?msgs p r0') q \<noteq> Void \<and> ?msgs p r0' q \<noteq> Bot}" by (simp add: card_mono subsetI)
  hence majv:"(2*N) div 3 < card {q. (?msgs p r0') q \<noteq> Void \<and> ?msgs p r0' q \<noteq> Bot}" using pic' by auto

  have "\<forall>qq. qq \<in> \<Pi>' \<longrightarrow> ?msgs p r0' qq = Content v" 
  proof (rule+)
    fix qq
    assume "qq \<in> \<Pi>'"
    hence "qq \<in> HOs r0' p" using pi' by auto
    moreover from v' have "\<forall>q. \<exists>ss. x ss = v \<and> rho r0' q = Active ss" by (meson pstate.select_convs(1))
    then obtain sqq where "x sqq = v" and "rho r0' qq = Active sqq" by auto
    ultimately show "?msgs p r0' qq = Content v" using  \<open>x sqq = v\<close>
      by (simp add: HOMachine_to_Algorithm_def OTR_sendMsg_def OTR_HOMachine_def HOrcvdMsgs_def)
  qed
  hence "\<Pi>' \<subseteq> HOV (?msgs p r0') v" using HOV_def by fastforce
  hence "card \<Pi>' \<le> card (HOV (?msgs p r0') v)" by (simp add: card_mono)
  hence "TwoThirds (?msgs p r0') v" using TwoThirds_def pi' pic' by fastforce

  hence "decide spp = True" using majv nxt OTR_nextState_def[where ?st' = spp] by fastforce
  hence "rho (Suc r0') p = Active \<lparr> x = x spp, decide = True \<rparr>" using \<open>rho (Suc r0') p = Active spp\<close> by auto
  thus ?thesis by auto
qed


subsection \<open>\emph{One-Third Rule} Solves Consensus\<close>

text \<open>
  Summing up, all (coarse-grained) runs of \emph{One-Third Rule} for
  HO collections that satisfy the communication predicate satisfy
  the Consensus property.
\<close>

fun getX where
"getX (Active s) = x s"

theorem OTR_consensus:
  assumes run: "HORun (HOMachine_to_Algorithm OTR_M) (rho :: nat \<Rightarrow> Proc \<Rightarrow> _ pstate proc_state) HOs"  (is "HORun ?A _ _")
  and commG: "HOcommGlobal OTR_M HOs"
  assumes  not_inf:"\<forall>p. \<exists>n. rho n p \<noteq> Aslept"
  shows "consensus (\<lambda>p. getX (getInitValue rho p)) getDec rho" (is "consensus ?vals _ _")
proof -
  have "\<forall>p n v. getDec (rho n p) = Some v \<longrightarrow> v \<in> range ?vals"
  proof
    fix p
    show "\<forall>n v. getDec (rho n p) = Some v \<longrightarrow> v \<in> range ?vals"
    proof
      fix n
      show "\<forall>v. getDec (rho n p) = Some v \<longrightarrow> v \<in> range ?vals"
      proof
        fix v
        show "getDec (rho n p) = Some v \<longrightarrow> v \<in> range ?vals"
        proof
          assume "getDec (rho n p) = Some v"
          hence "rho n p = Active \<lparr> x = v, decide = True \<rparr>"
            by (metis getDec.elims old.unit.exhaust option.distinct(1) option.sel pstate.surjective)
          hence "\<exists>q s. x (s :: 'a pstate) = (v :: 'a) \<and> getInitValue rho q = Active s" using run OTR_integrity by fastforce
          thus "v \<in> range ?vals" by (metis getX.simps range_eqI)
        qed
      qed
    qed
  qed
  moreover have "(\<forall>m n p q v w. getDec (rho m p) = Some v \<and> getDec (rho n q) = Some w  \<longrightarrow> v = w)"
    using run OTR_agreement getDec.elims getDec.simps
    by (smt old.unit.exhaust option.sel option.simps(3) pstate.surjective)
  moreover have "\<forall>p. \<exists>n. getDec (rho n p) \<noteq> None"
    using run not_inf commG OTR_termination
    by (smt getDec.simps(1) option.simps(3) pstate.ext_inject pstate.select_convs(1) pstate.surjective)

  ultimately show ?thesis using consensus_def[where ?vals = "\<lambda>p. getX (getInitValue rho p)" and ?rho = rho] by fastforce
qed

(*
text \<open>
  By the reduction theorem, the correctness of the algorithm also follows
  for fine-grained runs of the algorithm. It would be much more tedious
  to establish this theorem directly.
\<close>

theorem OTR_consensus_fg:
  assumes run: "fg_run OTR_M rho HOs HOs (\<lambda>r q. undefined)"
      and commG: "HOcommGlobal OTR_M HOs"
  shows "consensus (\<lambda>p. x (state (rho 0) p)) decide (state \<circ> rho)"
    (is "consensus ?inits _ _")
proof (rule local_property_reduction[OF run consensus_is_local])
  fix crun
  assume crun: "CSHORun OTR_M crun HOs HOs (\<lambda>r q. undefined)"
     and init: "crun 0 = state (rho 0)"
  from crun have "HORun OTR_M crun HOs" by (unfold HORun_def SHORun_def)
  from this commG have "consensus (x \<circ> (crun 0)) decide crun" by (rule OTR_consensus)
  with init show "consensus ?inits decide crun" by (simp add: o_def)
qed
*)

end
