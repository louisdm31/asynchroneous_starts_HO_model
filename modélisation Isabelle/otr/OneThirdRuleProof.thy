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
  have "card ?ens = 1 \<or> card ?ens = 0 \<or> card ?ens > 1" by auto
  thus ?thesis
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
      hence "finite {msgs p | p. True}" using tiroir by blast
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
  assumes not_inf:"\<forall>p. \<exists>n. rho n p \<noteq> Aslept"
  and run:"HORun (HOMachine_to_Algorithm OTR_M) rho HOs" (is "HORun ?A rho HOs")
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

lemma nextState_decide:
  assumes run:"HORun (HOMachine_to_Algorithm OTR_M) rho HOs"
  and chg: "x1 \<noteq> x2 \<and> rho (Suc n) p = Active \<lparr> x = x2, decide = True\<rparr> \<and> rho n p = Active \<lparr> x = x1, decide = True\<rparr>"
  shows "TwoThirds (HOrcvdMsgs (HOMachine_to_Algorithm OTR_M) p (HOs n p) (rho n))
                   (the (decide (rho (Suc n) p)))"
proof -
  from run
  have "OTR_nextState n p (rho n p)
                    (HOrcvdMsgs OTR_M n p (HOs n p) (rho n)) (rho (Suc n) p)"
    by (simp add: HORun_eq HOnextConfig_eq OTR_HOMachine_def nextState_def)
  with chg show ?thesis by (auto simp: OTR_nextState_def elim: someI)
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
  assumes run: "HORun OTR_M rho HOs" 
  and dec: "decide (rho n p) = Some v" (is "?dec n")
  shows "\<forall>k. (2*N) div 3 < card { q . x (rho (n+k) q) = v }"
        (is "\<forall>k. ?twothird (n+k)")
using dec proof (induct n)
  \<comment> \<open>The base case is trivial since no process has decided\<close>
  assume "?dec 0" with run show "\<forall>k. ?twothird (0+k)"
    by (simp add: HORun_eq HOinitConfig_eq OTR_HOMachine_def 
                  initState_def OTR_initState_def)
next
  \<comment> \<open>For the inductive step, we assume that process @{text p} has decided on @{text v}.\<close>
  fix m
  assume ih: "?dec m \<Longrightarrow> \<forall>k. ?twothird (m+k)" and m: "?dec (Suc m)"
  show "\<forall>k. ?twothird ((Suc m) + k)"
  proof
    fix k
    have "?twothird (m + Suc k)"
    txt \<open>
      There are two cases to consider: if \<open>p\<close> had already decided on \<open>v\<close>
      before, the assertion follows from the induction hypothesis. Otherwise, the
      assertion follows from lemmas \<open>A1\<close> and \<open>A3\<close>.
\<close>
    proof (cases "?dec m")
      case True with ih show ?thesis by blast
    next
      case False
      with run m have "?twothird m" by (auto elim: A1)
      with run show ?thesis by (blast dest: A3)
    qed
    thus "?twothird ((Suc m) + k)" by simp
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
  assumes run:"HORun OTR_M rho HOs"
  and p: "decide (rho n p) = Some v"
  and p': "decide (rho (n+k) p') = Some w"
  shows "v = w"
proof -
  from run p 
  have "(2*N) div 3 < card {q. x (rho (n+k) q) = v}" (is "_ < card ?V")
    by (blast dest: A4)
  moreover
  from run p'
  have "(2*N) div 3 < card {q. x (rho ((n+k)+0) q) = w}" (is "_ < card ?W")
    by (blast dest: A4)
  ultimately
  have "N < card ?V + card ?W" by auto
  then obtain proc where "proc \<in> ?V \<inter> ?W" by (auto dest: majorities_intersect)
  thus ?thesis by auto
qed

theorem OTR_agreement:
  assumes run:"HORun OTR_M rho HOs"
  and p: "decide (rho n p) = Some v"
  and p': "decide (rho m p') = Some w"
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

theorem OTR_termination:
  assumes run: "HORun OTR_M rho HOs"
      and commG: "HOcommGlobal OTR_M HOs"
  shows "\<exists>r v. decide (rho r p) = Some v"
proof -
  from commG obtain r0 \<Pi> where 
    pi: "\<forall>q. HOs r0 q = \<Pi>" and pic: "card \<Pi> > (2*N) div 3"
    by (auto simp: OTR_HOMachine_def OTR_commGlobal_def)
  let "?msgs q r" = "HOrcvdMsgs OTR_M r q (HOs r q) (rho r)"

  from run pi have "\<forall>p q. ?msgs q r0 = ?msgs p r0"
    by (auto simp: HORun_eq OTR_HOMachine_def HOrcvdMsgs_def OTR_sendMsg_def)
  then obtain \<mu> where "\<forall>q. ?msgs q r0 = \<mu>" by auto
  moreover
  from pi pic have "\<forall>p. (2*N) div 3 < card {q. ?msgs p r0 q \<noteq> None}"
    by (auto simp: HORun_eq HOnextConfig_eq HOrcvdMsgs_def)
  with run have "\<forall>q. x (rho (Suc r0) q) = Min {v . MFR (?msgs q r0) v}"
    by (auto simp: HORun_eq HOnextConfig_eq OTR_HOMachine_def 
                   nextState_def OTR_nextState_def)
  ultimately
  have "\<forall>q. x (rho (Suc r0) q) = Min {v . MFR \<mu> v}" by auto
  then obtain v where v:"\<forall>q. x (rho (Suc r0) q) = v" by auto

  have P:"\<forall>k. \<forall>q. x (rho (Suc r0+k) q) = v"
  proof
    fix k
    show "\<forall>q. x (rho (Suc r0+k) q) = v"
    proof (induct k)
      from v show "\<forall>q. x (rho (Suc r0+0) q) = v" by simp
    next
      fix k
      assume ih:"\<forall>q. x (rho (Suc r0 + k) q) = v"
      show "\<forall>q. x (rho (Suc r0 + Suc k) q) = v"
      proof
        fix q
        show "x (rho (Suc r0 + Suc k) q) = v"
        proof (cases "(2*N) div 3 < card { p . ?msgs q (Suc r0 + k) p \<noteq> None }")
          case True
          have "N > 0" by (rule finite_UNIV_card_ge_0) simp
          with ih 
          have "(2*N) div 3 < card { p . x (rho (Suc r0 + k) p) = v }" by auto
          with True run show ?thesis by (auto elim: A2)
        next
          case False
          with run ih show ?thesis by (auto dest: nextState_change)
        qed
      qed
    qed
  qed

  from commG obtain r0' \<Pi>'
    where r0': "r0' \<ge> Suc r0"
      and pi': "\<forall>q. HOs r0' q = \<Pi>'"
      and pic': "card \<Pi>' > (2*N) div 3"
    by (force simp: OTR_HOMachine_def OTR_commGlobal_def)
  from r0' P have v':"\<forall>q. x (rho r0' q) = v" by (auto simp: le_iff_add)

  from run 
  have "OTR_nextState r0' p (rho r0' p) (?msgs p r0') (rho (Suc r0') p)"
    by (simp add: HORun_eq HOnextConfig_eq OTR_HOMachine_def nextState_def)
  moreover 
  from pi' pic' have "(2*N) div 3 < card {q. (?msgs p r0') q \<noteq> None}"
    by (auto simp: HOrcvdMsgs_def OTR_sendMsg_def)
  moreover
  from pi' pic' v' have "TwoThirds (?msgs p r0') v"
    by (simp add: TwoThirds_def HOrcvdMsgs_def OTR_HOMachine_def 
                  OTR_sendMsg_def HOV_def)
  ultimately
  have "decide (rho (Suc r0') p) = Some (\<some>v. TwoThirds (?msgs p r0') v)"
    by (auto simp: OTR_nextState_def)
  thus ?thesis by blast
qed


subsection \<open>\emph{One-Third Rule} Solves Consensus\<close>

text \<open>
  Summing up, all (coarse-grained) runs of \emph{One-Third Rule} for
  HO collections that satisfy the communication predicate satisfy
  the Consensus property.
\<close>

theorem OTR_consensus:
  assumes run: "HORun OTR_M rho HOs" and commG: "HOcommGlobal OTR_M HOs"
  shows "consensus (x \<circ> (rho 0)) decide rho"
  using OTR_integrity[OF run] OTR_agreement[OF run] OTR_termination[OF run commG]
  by (auto simp: consensus_def image_def)

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


end
