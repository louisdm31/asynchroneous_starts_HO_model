theory OneThirdRuleProof
imports OneThirdRuleDefs 
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

lemma tiroir2: assumes inject:"\<forall>v1 v2. f v1 = f v2 \<longrightarrow> v1 = v2"
  shows "finite {f v | v. E v} \<longrightarrow> finite {v. E v}"
proof -
  have "card {f v | v. E v} \<ge> 0" (is "?cardens \<ge> 0") by auto
  show ?thesis
  proof (induction ?cardens arbitrary:E)
    case 0
    hence zercrd:"card {f v | v. E v} = 0" by auto
    show ?case 
    proof
      assume fini:"finite {f v | v. E v}"
      hence "{f v | v. E v} = {}"  using zercrd by auto
      thus "finite {v. E v}" by auto
    qed
  next
    case (Suc crd)
    show ?case proof assume "finite {f v | v. E v}"
    hence succrd:"card {f v | v. E v} = Suc crd" using Suc.hyps by auto
    hence nonvoid:"card {f v | v. E v} > 0" by auto
    hence finii:"finite {f v | v. E v}" using card_ge_0_finite by blast
    hence "\<exists>vv. vv \<in> {f v | v. E v}" using nonvoid by (simp add: card_gt_0_iff)
    then obtain vv where vvin:"vv \<in> {v. E v}" by auto
    have "\<forall>v. E v = (\<lambda>t. if t = vv then True else E t) v" using vvin by simp
    hence "{f v | v. E v} = {f v | v. (\<lambda>t. if t = vv then True else E t) v}" by blast
    hence dehorsvv:"{f v | v. E v} = {f  v | v. (\<lambda>t. if t = vv then False else E t) v} \<union> {f vv}" by auto
    hence finiii:"finite {f  v | v. (\<lambda>t. if t = vv then False else E t) v}" using finii by auto

    have "f vv \<notin> {f  v | v. (\<lambda>t. if t = vv then False else E t) v}"
    proof
      assume "f vv \<in> {f v | v. (\<lambda>t. if t = vv then False else E t) v}"
      hence "\<exists>vv2. f vv2 = f vv \<and>  (\<lambda>t. if t = vv then False else E t) vv2" by (smt mem_Collect_eq)
      then obtain vv2 where exvv2:"f vv2 = f vv \<and>  (\<lambda>t. if t = vv then False else E t) vv2" by blast
      hence "vv2 = vv" using inject by auto
      hence " (\<lambda>t. if t = vv then False else E t) vv" using exvv2 by auto
      thus "False" by simp
    qed
    hence "{f v | v. (\<lambda>t. if t = vv then False else E t) v} \<inter> {f vv} = {}" by auto
    hence "card {f v | v. E v} = card {f  v | v. (\<lambda>t. if t = vv then False else E t) v} + 1"
      using dehorsvv
      by (metis (no_types, lifting) One_nat_def Un_insert_right
          \<open>0 < card {f v |v. E v}\<close> \<open>f vv \<notin> {f v |v. if v = vv then False else E v}\<close>
          add.right_neutral add_Suc_right card_infinite card_insert_disjoint finite_Un
          less_le sup_bot.right_neutral)
    have  "{f  v | v. (\<lambda>t. if t = vv then False else E t) v} \<subseteq> {f v | v. E v}" using dehorsvv by auto
    hence "finite {f  v | v. (\<lambda>t. if t = vv then False else E t) v}" using finiii by blast
    moreover have "card {f  v | v. (\<lambda>t. if t = vv then False else E t) v} = crd" using succrd
      by (simp add: \<open>card {f v |v. E v} = card {f v |v. if v = vv then False else E v} + 1\<close>)
    ultimately have "finite {v. (\<lambda>t. if t = vv then False else E t) v}" using Suc.hyps by auto
    hence "finite ({v. (\<lambda>t. if t = vv then False else E t) v} \<union> {vv})" by auto
    moreover have "{v. E v} = {v. (\<lambda>t. if t = vv then False else E t) v} \<union> {vv}"
      using vvin by auto
    ultimately show "finite {v. E v}" by simp
  qed
qed qed

lemma vinv_invariant:
  assumes not_inf:"\<forall>p. \<exists>n. rho n p \<noteq> Aslept"
  and run:"HORun (\<lparr> CinitState = CinitState OTR_M, sendMsg = sendMsg OTR_M, CnextState = CnextState OTR_M \<rparr>
                  ::(Proc, 'val::linorder pstate, 'val) CHOAlgorithm)
                  rho HOs"
    (is "HORun ?A rho HOs")
  shows "VInv rho n"
proof -
  have pro:"\<forall> p::Proc. \<forall>s::'val pstate. \<forall>n::nat. rho n p = Active s \<longrightarrow>
      (\<exists> m q ss. (m = 0 \<or> rho (m-1) q = Aslept) \<and> rho m q = Active ss \<and> x ss = x s)"
  proof
    fix p :: Proc
    show "\<forall>s::'val pstate. \<forall>n::nat. rho n p = Active s \<longrightarrow>
      (\<exists> m q ss. (m = 0 \<or> rho (m-1) q = Aslept) \<and> rho m q = Active ss \<and> x ss = x s)"
    proof
      fix s :: "'val pstate "
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
              hence otrn:"OTR_nextState p ss ?rcvd s" by (auto simp:OTR_HOMachine_def)
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
                hence excont:"\<exists>v. ?rcvd q = Content v" (is "\<exists>v. ?q = _") by (cases ?q) auto
                have "\<exists>v. q \<in> (HOV ?rcvd v)" using excont HOV_def by fastforce
                then obtain v where cardun:"card (HOV ?rcvd v) > 0" using less_Suc_eq_0_disj by fastforce
                have "card ?ens = 1 \<or> card ?ens = 0 \<or> card ?ens > 1" by auto
                hence "MFR ?rcvd ((x s)::'val::linorder)"
                proof cases
                  assume zer:"card ?ens = 0"
                  hence vidinfi:"?ens = {} \<or> infinite ?ens" by (simp add:card_eq_0_iff)
                  hence "\<forall>v. v \<notin> ?ens"
                  proof cases
                    assume "?ens = {}"
                    thus ?thesis by auto
                  next
                    assume "?ens \<noteq> {}"
                    hence infens:"infinite ?ens" using vidinfi by blast
                    have "\<exists>v. ?rcvd q = Content v" using excont by auto
                    hence "\<exists>v. q \<in> HOV ?rcvd v" using HOV_def by (simp add: HOV_def)
                    hence exval:"\<exists>v. card (HOV ?rcvd v) \<ge> 1"
                      by (metis One_nat_def Suc_leI card_eq_0_iff empty_iff finite_code not_gr_zero)
                    hence "\<forall>qq. MFR ?rcvd qq \<longrightarrow> card (HOV ?rcvd qq) \<ge> 1"
                      using MFR_def order.trans by fastforce
                    moreover have "\<forall>qq. card (HOV ?rcvd qq) \<ge> 1 \<longrightarrow> (\<exists>pp. ?rcvd pp = Content qq)"
                      using HOV_def
                      by (smt Collect_empty_eq One_nat_def card.empty nat.simps(3) zero_order(2))
                    ultimately have "\<forall>qq. MFR ?rcvd qq \<longrightarrow> (\<exists>pp. ?rcvd pp = Content qq)" by auto
                    hence "?ens \<subseteq> {qq. \<exists>pp. ?rcvd pp = Content qq}" by auto
                    hence infini:"infinite {qq. \<exists>pp. ?rcvd pp = Content qq}"
                      using infens rev_finite_subset by blast

                    have "finite {pp :: Proc. True}" by auto
                    hence "finite {v. \<exists>p. ?rcvd p = v}" by (smt Collect_cong finite_image_set)
                    moreover have "{Content v | v.  \<exists>p. ?rcvd p = Content v} \<subseteq> {v. \<exists>p. ?rcvd p = v}"
                      by blast
                    ultimately have fincontens:"finite {Content v | v.  \<exists>p. ?rcvd p = Content v}"
                      by (meson rev_finite_subset)
                    moreover have "\<forall>vv1 vv2. Content vv1 = Content vv2 \<longrightarrow> vv1 = vv2" by auto
                    ultimately have "finite {v. \<exists>p. ?rcvd p = Content v}" using tiroir2  by force
                    hence "False" using infini by auto
                    thus ?thesis by auto
                  qed
                  hence "\<forall>v. \<not> (MFR ?rcvd v)" by simp
                  hence "False" using MFR_exists by fastforce
                  thus ?thesis by auto
                next
                  assume "card ?ens \<noteq> 0"
                  hence "finite ?ens" by (meson card_infinite)
                  thus ?thesis using Min_in \<open>card ?ens \<noteq> 0\<close> dans by auto
                qed
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
                  by (simp add: HOrcvdMsgs_def OTR_HOMachine_def OTR_sendMsg_def)
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
  assumes "HORun OTR_M rho HOs"
      and "\<not> ((2*N) div 3 
              < card {q. (HOrcvdMsgs OTR_M n p (HOs n p) (rho n)) q \<noteq> None})"
  shows "rho (Suc n) p = rho n p"
  using assms
  by (auto simp: HORun_eq HOnextConfig_eq OTR_HOMachine_def
                 nextState_def OTR_nextState_def)

lemma nextState_decide:
  assumes run:"HORun OTR_M rho HOs"
  and chg: "decide (rho (Suc n) p) \<noteq> decide (rho n p)"
  shows "TwoThirds (HOrcvdMsgs OTR_M n p (HOs n p) (rho n))
                   (the (decide (rho (Suc n) p)))"
proof -
  from run
  have "OTR_nextState n p (rho n p)
                    (HOrcvdMsgs OTR_M n p (HOs n p) (rho n)) (rho (Suc n) p)"
    by (simp add: HORun_eq HOnextConfig_eq OTR_HOMachine_def nextState_def)
  with chg show ?thesis by (auto simp: OTR_nextState_def elim: someI)
qed

lemma A1:
  assumes run:"HORun OTR_M rho HOs"
  and dec: "decide (rho (Suc n) p) = Some v"
  and chg: "decide (rho (Suc n) p) \<noteq> decide (rho n p)" (is "decide ?st' \<noteq> decide ?st")
  shows "(2*N) div 3 < card { q . x (rho n q) = v }"
proof -
  from run chg
  have "TwoThirds (HOrcvdMsgs OTR_M n p (HOs n p) (rho n)) 
                  (the (decide ?st'))"
    (is "TwoThirds ?msgs _")
    by (rule nextState_decide)
  with dec have "TwoThirds ?msgs v" by simp
  hence "(2*N) div 3 < card { q . ?msgs q = Some v }"
    by (simp add: TwoThirds_def HOV_def)
  moreover
  have "{ q . ?msgs q = Some v } \<subseteq> { q . x (rho n q) = v }"
    by (auto simp: OTR_HOMachine_def OTR_sendMsg_def HOrcvdMsgs_def)
  hence "card { q . ?msgs q = Some v } \<le> card { q . x (rho n q) = v }"
    by (simp add: card_mono)
  ultimately
  show ?thesis by simp
qed


text \<open>
  The following lemma \<open>A2\<close> contains the crucial correctness argument:
  if more than $2/3$ of all processes send \<open>v\<close> and process \<open>p\<close>
  hears from more than $2/3$ of all processes then the \<open>x\<close> field of
  \<open>p\<close> will be updated to \<open>v\<close>.
\<close>

lemma A2:
  assumes run: "HORun OTR_M rho HOs"
  and HO: "(2*N) div 3
             < card { q . HOrcvdMsgs OTR_M n p (HOs n p) (rho n) q \<noteq> None }"
  and maj: "(2*N) div 3 < card { q . x (rho n q) = v }"
  shows "x (rho (Suc n) p) = v"
proof -
  from run 
  have nxt: "OTR_nextState n p (rho n p) 
                      (HOrcvdMsgs OTR_M n p (HOs n p) (rho n)) 
                      (rho (Suc n) p)"
        (is "OTR_nextState _ _ ?st ?msgs ?st'")
    by (simp add: HORun_eq HOnextConfig_eq OTR_HOMachine_def nextState_def)
  let ?HOVothers = "\<Union> { HOV ?msgs w | w . w \<noteq> v}"
  \<comment> \<open>processes from which @{text p} received values different from @{text v}\<close>

  have w: "card ?HOVothers \<le> N div 3"
  proof -
    have "card ?HOVothers \<le> card (UNIV - { q . x (rho n q) = v })"
      by (auto simp: HOV_def HOrcvdMsgs_def OTR_HOMachine_def OTR_sendMsg_def 
               intro: card_mono)
    also have "\<dots> = N - card { q . x (rho n q) = v }"
      by (auto simp: card_Diff_subset)
    also from maj have "\<dots> \<le> N div 3" by auto
    finally show ?thesis .
  qed

  have hov: "HOV ?msgs v = { q . ?msgs q \<noteq> None } - ?HOVothers"
    by (auto simp: HOV_def) blast

  have othHO: "?HOVothers \<subseteq> { q . ?msgs q \<noteq> None }"
    by (auto simp: HOV_def)

  txt \<open>Show that \<open>v\<close> has been received from more than $N/3$ processes.\<close>
  from HO have "N div 3 < card { q . ?msgs q \<noteq> None } - (N div 3)" 
    by auto
  also from w HO have "\<dots> \<le> card { q . ?msgs q \<noteq> None } - card ?HOVothers" 
    by auto
  also from hov othHO have "\<dots> = card (HOV ?msgs v)" 
    by (auto simp: card_Diff_subset)
  finally have HOV: "N div 3 < card (HOV ?msgs v)" .

  txt \<open>All other values are received from at most $N/3$ processes.\<close>
  have "\<forall>w. w \<noteq> v \<longrightarrow> card (HOV ?msgs w) \<le> card ?HOVothers"
    by (force intro: card_mono)
  with w have cardw: "\<forall>w. w \<noteq> v \<longrightarrow> card (HOV ?msgs w) \<le> N div 3" by auto

  txt \<open>In particular, \<open>v\<close> is the single most frequently received value.\<close>
  with HOV have "MFR ?msgs v" by (auto simp: MFR_def)

  moreover
  have "\<forall>w. w \<noteq> v \<longrightarrow> \<not>(MFR ?msgs w)"
  proof (auto simp: MFR_def not_le)
    fix w
    assume "w \<noteq> v"
    with cardw HOV have "card (HOV ?msgs w) < card (HOV ?msgs v)" by auto
    thus "\<exists>v. card (HOV ?msgs w) < card (HOV ?msgs v)" ..
  qed

  ultimately
  have mfrv: "{ w . MFR ?msgs w } = {v}" by auto

  have "card { q . ?msgs q = Some v } \<le> card { q . ?msgs q \<noteq> None }"
    by (auto intro: card_mono)
  with HO mfrv nxt show ?thesis by (auto simp: OTR_nextState_def)
qed

text \<open>
  Therefore, once more than two thirds of the processes hold \<open>v\<close>
  in their \<open>x\<close> field, this will remain true forever.
\<close>

lemma A3:
  assumes run:"HORun OTR_M rho HOs"
      and n: "(2*N) div 3 < card { q . x (rho n q) = v }" (is "?twothird n")
  shows "?twothird (n+k)"
proof (induct k)
  from n show "?twothird (n+0)" by simp
next
  fix m
  assume m: "?twothird (n+m)"
  have "\<forall>q. x (rho (n+m) q) = v \<longrightarrow> x (rho (n + Suc m) q) = v"
  proof (rule+)
    fix q
    assume q: "x ((rho (n+m)) q) = v"
    let ?msgs = "HOrcvdMsgs OTR_M (n+m) q (HOs (n+m) q) (rho (n+m))"
    show "x (rho (n + Suc m) q) = v"
    proof (cases "(2*N) div 3 < card { q . ?msgs q \<noteq> None }")
      case True
      from m have "(2*N) div 3 < card { q . x (rho (n+m) q) = v }" by simp
      with True run show ?thesis by (auto elim: A2)
    next
      case False
      with run q show ?thesis by (auto dest: nextState_change)
    qed
  qed
  hence "card {q. x (rho (n+m) q) = v} \<le> card {q. x (rho (n + Suc m) q) = v}"
    by (auto intro: card_mono)
  with m show "?twothird (n + Suc m)" by simp
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
