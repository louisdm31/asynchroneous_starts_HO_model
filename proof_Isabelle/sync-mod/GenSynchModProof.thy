theory GenSynchModProof
imports "../HOModel" GenSynchMod
begin

lemma sending:
assumes s:"rho r p = Active s"
  and run: "HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A _ _")
shows "ALL q. HOrcvdMsgs (k_mod.gen_HOMachine k) q (HO (Suc r) q) (rho r) p
    = (if p : HO (Suc r) q then Content s else Void)"
using HOrcvdMsgs_def[of ?A] s by (simp add: k_mod.gen_HOMachine_def k_mod.gen_sendMsg_def)

lemma sending_rec : assumes run:"HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A rho HO")
  assumes "(HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc r) p) (rho r)) q = Content v" (is "?msgs q = _")
  shows "rho r q = Active v"
proof (cases "rho r q")
  case Asleep
  hence "?msgs q = (if q : HO (Suc r) p then Bot else Void)"
  using HOrcvdMsgs_def[of ?A p "HO (Suc r) p" "rho r"] by auto
  thus "rho r q = Active v" using `?msgs q = Content v` by auto
next
  case (Active sq)
  hence "k_mod.gen_sendMsg q p sq = v"
  using assms unfolding k_mod.gen_HOMachine_def HOrcvdMsgs_def by auto
  thus "rho r q = Active v" using Active unfolding k_mod.gen_sendMsg_def by auto
qed

lemma starting: 
assumes prev: "0 < n --> rho (n-1) p = Asleep"
  and run: "HORun (k_mod.gen_HOMachine k) rho HO" 
  and act: "rho n p = Active s"
  shows "s = k_mod.gen_initState"
proof -
  from act have 1: "~ always_asleep rho p"
    unfolding always_asleep_def by force
  from run prev act have 2: "first_awake rho p = n"
    by (rule first_awake_HO)
  from run have "CHOinitConfig (k_mod.gen_HOMachine k) rho (%_ _. undefined)" (is "CHOinitConfig ?A _ _")
    by (simp add: HORun_def CHORun_def)
  with 1 2 act have "CinitState ?A p s undefined"
    by (auto simp: CHOinitConfig_def)
  thus ?thesis by (simp add:k_mod.gen_HOMachine_def act)
qed

lemma path_extend:
assumes "ALL p t. k_mod.path HO xi p t D"
and "D>0"
shows "ALL i t. k_mod.path HO xi p t (D+i)"
proof (rule allI)+
  fix i t
  show "k_mod.path HO xi p t (D+i)"
  proof (induction i arbitrary:p)
    case 0
    show ?case using assms by auto
  next
    case (Suc i)
    from assms obtain seq where "seq D = p" and
      "ALL j < D. seq j : HO (t+Suc i+Suc j) (seq (Suc j))" unfolding k_mod.path_def by fastforce
    hence 1:"seq (D-1) : HO (t+D+Suc i) (seq D)" using `D>0`
      by (metis (full_types) Suc_diff_1 add.assoc add.commute add_Suc_right lessI)
    from Suc.IH obtain seqD where D0:"seqD 0 = xi" and Di:"seqD (D+i) = seq (D-1)" and
      seqD:"ALL j < D+i. seqD j : HO (t+Suc j) (seqD (Suc j))" unfolding k_mod.path_def by fastforce
    let "?seq_tot j" = "if j = D + Suc i then p else seqD j"
    have "?seq_tot 0 = xi" and "?seq_tot (D+Suc i) = p" using D0 by auto
    moreover from this have "ALL j < D+Suc i. ?seq_tot j : HO (t+Suc j) (?seq_tot (Suc j))" 
      using 1 `seq D = p` D0 Di
      by (smt add.assoc add_Suc_right add_diff_cancel_left' less_antisym less_irrefl_nat plus_1_eq_Suc seqD)
    ultimately show "k_mod.path HO xi p t (D+Suc i)"
      unfolding k_mod.path_def using exI[of _ ?seq_tot] by auto 
  qed
qed

lemma transition : assumes s_def:"rho r p = Active s"
and ss_def:"rho (Suc r) p = Active ss"
and run:"HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A _ _")
and "k > 2"
shows "k_mod.gen_nextState k p s (HOrcvdMsgs ?A p (HO (Suc r) p) (rho r)) ss" (is "k_mod.gen_nextState  _ _ _ ?msgs _")
proof -
    have "CHOnextConfig ?A (rho r) (HO (Suc r)) (%w. undefined) (rho (Suc r))" using run by (simp add:HORun_def CHORun_def)
    then obtain sss where "rho (Suc r) p = Active sss & CnextState ?A p s ?msgs undefined sss" 
        using CHOnextConfig_def[of ?A "rho r" "HO (Suc r)" "%w. undefined" "rho (Suc r)"] s_def by fastforce
    hence "CnextState ?A p s ?msgs undefined ss" using ss_def by auto
    thus nxt:"k_mod.gen_nextState k p s ?msgs ss" unfolding k_mod.gen_HOMachine_def by auto
qed

(*this lemma is the induction case of the backward induction used in lemma A1.
If a node p is concordant in round r+2, we can deduce several facts about the incoming neighbours of p.*)
lemma path_conc:
assumes "rho (Suc (Suc r)) p = Active sp"
and "x sp mod k ~= 1"
and conc_ss:"k_mod.isConc k (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc (Suc r)) p) (rho (Suc r)))"
  (is "k_mod.isConc k ?msgs")
and run: "HORun (k_mod.gen_HOMachine k) rho HO" 
and loop:"ALL p r. p : HO r p"
and "q : HO (Suc (Suc r)) p"
and "k > 2"
shows "k_mod.isConc k (HOrcvdMsgs (k_mod.gen_HOMachine k) q (HO (Suc r) q) (rho r))" (is "k_mod.isConc k ?msg")
and "k_mod.isReady (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc (Suc r)) p) (rho (Suc r))) -->
     k_mod.isReady (HOrcvdMsgs (k_mod.gen_HOMachine k) q (HO (Suc r) q) (rho r))"
and "EX s. rho (Suc r) q = Active s & (Suc (x s)) mod k = x sp mod k"
proof -
  have "~ rho (Suc r) p = Asleep"
  proof
    assume "rho (Suc r) p = Asleep"
    hence "sp = k_mod.gen_initState" using starting[of "Suc (Suc r)" rho p k HO sp] assms by auto
    hence "?msgs p ~= Bot" using conc_ss unfolding k_mod.isConc_def by (metis message.distinct(1) message.distinct(5))
    thus "False" using loop `rho (Suc r) p = Asleep` unfolding HOrcvdMsgs_def by auto
  qed
  then obtain ssp where ssp:"rho (Suc r) p = Active ssp" by (cases "rho (Suc r) p") auto
  hence trans:"k_mod.gen_nextState k p ssp ?msgs sp"
    using transition[of rho "Suc r" p ssp sp k HO] assms by auto
  have "(EX s. rho (Suc r) q = Active s & (Suc (x s)) mod k = x sp mod k) &
    k_mod.isConc k ?msg &
    (k_mod.isReady ?msgs --> k_mod.isReady ?msg)"
  proof (cases "rho (Suc r) q")
    case Asleep
    hence "?msgs q = Bot" 
      unfolding HOrcvdMsgs_def using assms by auto
    hence "~ k_mod.isConc k ?msgs" unfolding k_mod.isConc_def by (metis message.distinct(1) message.distinct(5))
    hence "False" using assms trans k_mod.gen_nextState_def by auto
    thus ?thesis by auto
  next
    case (Active sq)
    from sending have "?msgs q = Content sq" using assms `rho (Suc r) q = Active sq` by auto 
    moreover from trans assms k_mod.gen_nextState_def have coc:"k_mod.isConc k ?msgs" by auto
    ultimately have xsq:"x sq mod k = k_mod.minMsgs ?msgs mod k"
      unfolding k_mod.isConc_def by (metis message.distinct(3) message.inject)
    moreover from trans assms k_mod.gen_nextState_def have sucx:"x sp mod k = Suc (k_mod.minMsgs ?msgs) mod k" 
    proof (cases "k_mod.ready_level1 k ?msgs ssp | k_mod.ready_level2 k ?msgs ssp")
      case levlup:True
      hence "x ssp mod k = k - 1" using trans
        unfolding k_mod.gen_nextState_def k_mod.ready_level2_def k_mod.ready_level1_def k_mod.isConc_def
        apply (smt ssp conc_ss k_mod.isConc_def loop message.distinct(3) message.inject run sending) done
      moreover have "x sp = 0 | x sp = Suc (k_mod.minMsgs ?msgs)" using levlup trans unfolding k_mod.gen_nextState_def by auto
      ultimately show ?thesis
        by (metis Suc_diff_1 assms(7) k_mod.ready_level1_def k_mod.ready_level2_def less_Suc_eq_0_disj
        less_imp_Suc_add levlup mod_Suc mod_mod_trivial)
    next
      case False
      thus ?thesis using trans unfolding k_mod.gen_nextState_def by auto
    qed
    ultimately have "EX s. rho (Suc r) q = Active s & (Suc (x s)) mod k = x sp mod k"
      using `rho (Suc r) q = Active sq`
      exI[of "%s. rho (Suc r) q = Active s & Suc (x s) mod k = x sp mod k" sq] by (metis mod_Suc_eq)
    moreover from coc have "conc sq" unfolding k_mod.isConc_def
      by (metis `?msgs q = Content sq` message.distinct(3) message.inject)
    hence "rho r q ~= Asleep" using starting[of "Suc r" rho q k HO sq] run Active
      unfolding k_mod.gen_initState_def Active by auto
    then obtain ssq where "rho r q = Active ssq" by (cases "rho r q") auto
    hence transq:"k_mod.gen_nextState k q ssq ?msg sq"
      using Active transition[of rho r q ssq sq k HO] assms by auto
    from sucx xsq have "x sq mod k > 0" using `x sp mod k ~= 1`
      by (metis One_nat_def Suc_lessD assms(7) gr_zeroI less_numeral_extra(4) mod_Suc numeral_2_eq_2)
    hence "k_mod.isConc k ?msg" using transq `conc sq`
      unfolding k_mod.gen_nextState_def k_mod.ready_level1_def k_mod.ready_level2_def by auto
    moreover from transq `x sq mod k > 0` have "~ (k_mod.ready_level1 k ?msg ssq | k_mod.ready_level2 k ?msg ssq)" 
      unfolding k_mod.ready_level2_def k_mod.ready_level1_def k_mod.gen_nextState_def
      by (smt (z3) One_nat_def Suc_1 Suc_diff_1 Suc_lessD assms(7) mod_Suc mod_less neq0_conv)
    from this transq `x sq mod k > 0` assms k_mod.gen_nextState_def
      have "ready sq --> k_mod.isReady ?msg" by auto 
    hence "k_mod.isReady ?msgs --> k_mod.isReady ?msg"
      unfolding k_mod.isReady_def using `?msgs q = Content sq` by auto 
    ultimately show ?thesis using Active by auto
  qed
  thus "k_mod.isConc k ?msg"
    and "k_mod.isReady ?msgs --> k_mod.isReady ?msg"
    and "EX s. rho (Suc r) q = Active s & (Suc (x s)) mod k = x sp mod k" by auto
qed

lemma A1:
assumes path:"k_mod.path HO xi p (t+i) (k-i)"
and loop:"ALL p r. p : HO r p"
and run: "HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A _ _")
and "rho (t+k) p = Active sp"
and "k_mod.isConc k (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+k) p) (rho (t+k-1)))" (is "k_mod.isConc k ?msgs")
and "x sp mod k = 0"
and "k > 2"
and "i < k"
shows "EX sxi. rho (t+i) xi = Active sxi & x sxi mod k = i &
  (k_mod.isReady (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+k) p) (rho (t+k-1))) --> ready sxi)"
proof -
  from path obtain seq where "seq 0 = xi" and "seq (k-i) = p" and
    pat:"ALL j < k-i. seq j : HO (t+i+Suc j) (seq (Suc j))" unfolding k_mod.path_def by auto
  have "ALL j < k-i. let msgs = HOrcvdMsgs ?A (seq (k-i-j)) (HO (t+k-j) (seq (k-i-j))) (rho (t+k-Suc j)) in
      EX s. rho (t+k-j) (seq (k-i-j)) = Active s & x s mod k = (k - j) mod k & k_mod.isConc k msgs & (k_mod.isReady ?msgs --> k_mod.isReady msgs)"
      (is "ALL j. ?recurr_path j")
  proof
    fix j
    let ?msg = "%j. HOrcvdMsgs ?A (seq (k-i-j)) (HO (t+k-j) (seq (k-i-j))) (rho (t+k-Suc j))"
    show "j < k-i --> (let msgs = ?msg j in EX s. rho (t+k-j) (seq (k-i-j)) = Active s &
      x s mod k = (k-j) mod k & k_mod.isConc k msgs & (k_mod.isReady ?msgs --> k_mod.isReady msgs))"
    proof (induction j)
      case 0
      from assms `seq (k-i) = p` have "rho (t+k) (seq (k-i)) = Active sp &
        x sp mod k = (k-0) mod k & k_mod.isConc k ?msgs & (k_mod.isReady ?msgs --> k_mod.isReady ?msgs)" by auto
      thus "0 < k-i --> (let msgs = ?msg 0 in EX s. rho (t+k-0) (seq (k-i-0)) = Active s &
        x s mod k = (k-0) mod k & k_mod.isConc k msgs & (k_mod.isReady ?msgs --> k_mod.isReady msgs))"
        using assms by (simp add:`seq (k-i) = p`)
    next
      case (Suc j)
      show ?case
      proof
        assume "Suc j < k-i"
        hence ineg1:"k-i-Suc j < k-i" and ineg2:"t+i+Suc(k-i-Suc j) = t+k-j" and ineg:"Suc (k-i-Suc j) = k-i-j" and
        ineg3:"t+k >= Suc j" and ineg4:"Suc (t+k-Suc j) = t+k-j" and ineg5:"Suc (k - Suc(i+j)) = k-i-j" by auto
        from this pat have link:"seq (k-i-Suc j) : HO (t+k-j) (seq (k-i-j))" by auto

        from Suc.IH obtain ss where ss:"rho (t+k-j) (seq (k-i-j)) = Active ss"
          and concss:"k_mod.isConc k (?msg j)" and modss:"x ss mod k = (k-j) mod k" and readyss:"k_mod.isReady ?msgs --> k_mod.isReady (?msg j)"
          using `Suc j < k-i` by (meson Suc_lessD)

        have "x ss mod k ~= 1"
        proof
          assume "x ss mod k = 1"
          hence "j = k - 1" using `x ss mod k = (k-j) mod k`
            by (metis One_nat_def `Suc j < k - i` diff_diff_cancel diff_less diff_zero less_Suc_eq_0_disj
            less_iff_Suc_add less_imp_le_nat mod_less mod_self zero_less_diff zero_neq_one)
          thus "False" using `Suc j < k - i` by auto
        qed
        from assms pat this ss concss modss readyss
          obtain s where "rho (t+k-Suc j) (seq (k-i-Suc j)) = Active s & Suc (x s) mod k = x ss mod k"
          and "k_mod.isReady ?msgs --> k_mod.isReady (?msg (Suc j))" and "k_mod.isConc k (?msg (Suc j))"
            using path_conc[of rho "t+k-Suc (Suc j)" "seq (k-i-j)" ss k HO "seq (k-i-Suc j)"]
            by (smt One_nat_def Suc_diff_Suc ineg4 `Suc j < k - i` `Suc j <= t + k` link ineg2
            diff_self_eq_0 ineg le_eq_less_or_eq less_diff_conv not_add_less2 plus_1_eq_Suc)
        thus "let msgs = ?msg (Suc j) in EX s. rho (t+k-Suc j) (seq (k-i-Suc j)) = Active s &
          x s mod k = (k-Suc j) mod k & k_mod.isConc k msgs & (k_mod.isReady ?msgs --> k_mod.isReady msgs)"
          by (smt Suc_diff_Suc add_leD2 diff_Suc_1 diff_le_self ineg le_add_diff_inverse2 le_eq_less_or_eq
          less_Suc_eq_0_disj less_numeral_extra(3) linorder_not_less mod_Suc modss zero_less_diff)
      qed
    qed
  qed
  moreover have "k-i-(k-i-1) = 1" and "t+k-(k-i-1) = t+i+1" and "k-(k-i-1) = i+1" using `i < k` by auto
  ultimately have seq1:"let msgs = HOrcvdMsgs ?A (seq 1) (HO (t+i+1) (seq 1)) (rho (t+i)) in EX ss. 
      rho (t+i+1) (seq 1) = Active ss & x ss mod k = (i+1) mod k & k_mod.isConc k msgs &
      (k_mod.isReady ?msgs --> k_mod.isReady msgs)" using `2 < k` allE[of ?recurr_path "k-i-1" "?recurr_path (k-i-1)"] by auto
  let ?msgxi = "HOrcvdMsgs ?A (seq 1) (HO (t+i+1) (seq 1)) (rho (t+i))"
  have seq1link:"xi : HO (t+i+1) (seq 1)" using pat `seq 0 = xi` `i < k` by fastforce
  from seq1 have concready:"k_mod.isConc k ?msgxi & (k_mod.isReady ?msgs --> k_mod.isReady ?msgxi)" by meson
  have "rho (t+i) xi ~= Asleep"
  proof 
    assume "rho (t+i) xi = Asleep"
    hence "?msgxi xi = Bot" using seq1link unfolding HOrcvdMsgs_def by auto 
    hence "~ k_mod.isConc k ?msgxi" unfolding k_mod.isConc_def by (metis message.distinct(1) message.distinct(5))
    thus "False" using seq1 by auto
  qed
  then obtain sxi where sxi:"rho (t+i) xi = Active sxi" by (cases "rho (t+i) xi") auto
  hence "?msgxi xi = Content sxi" using seq1link unfolding HOrcvdMsgs_def by (simp add: k_mod.gen_HOMachine_def k_mod.gen_sendMsg_def)
  from sxi concready this have "k_mod.isReady ?msgs --> ready sxi" unfolding k_mod.isReady_def by auto
  from concready loop have "rho (t+i) (seq 1) ~= Asleep" unfolding k_mod.isConc_def HOrcvdMsgs_def by fastforce
  then obtain ss1 where ss1:"rho (t+i) (seq 1) = Active ss1" by (cases "rho (t+i) (seq 1)") auto
  from seq1 obtain s1 where s1:"rho (t+i+1) (seq 1) = Active s1" and suci:"x s1 mod k = (i+1) mod k" by meson
  hence trans1:"k_mod.gen_nextState k (seq 1) ss1 ?msgxi s1" using transition assms ss1 s1 by auto
  have "x s1 mod k = Suc (k_mod.minMsgs ?msgxi) mod k"
    using trans1 unfolding k_mod.gen_nextState_def
    by (smt (z3) One_nat_def Suc_1 Suc_diff_1 Suc_lessD assms(7) k_mod.ready_level1_def k_mod.ready_level2_def mod_Suc mod_mod_trivial)
  moreover have "k_mod.minMsgs ?msgxi mod k = x sxi mod k" using concready `?msgxi xi = Content sxi` unfolding k_mod.minMsgs_def k_mod.isConc_def
    by (metis (no_types, lifting) message.distinct(3) message.inject)
  ultimately have "x s1 mod k = Suc (x sxi) mod k" by (metis mod_Suc_eq)
  hence "x sxi mod k = i" using suci by (simp add: assms(8) mod_Suc)
  thus "EX sxi. rho (t+i) xi = Active sxi & x sxi mod k = i & (k_mod.isReady ?msgs --> ready sxi)" using sxi `k_mod.isReady ?msgs --> ready sxi` by auto
qed

lemma A2:
assumes star:"ALL p n. k_mod.path HO xi p n k"
and loop:"ALL p r. p : HO r p"
and run: "HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A _ _")
and "k > 2"
and "i < k"
and ss:"rho i pp = Active ss"
shows "level ss = 0 & x ss <= i & forc ss = 1" using `i < k` ss
proof (induction i arbitrary: pp ss)
  case 0
  thus ?case using starting[of 0 rho pp k HO] assms unfolding k_mod.gen_initState_def by auto
next
case (Suc ii)
  show "level ss = 0 & x ss <= Suc ii & forc ss = 1"
  proof (cases "rho ii pp")
    case Asleep
    thus "level ss = 0 & x ss <= Suc ii & forc ss = 1" using run starting[of "Suc ii" rho pp k HO] Suc
      unfolding k_mod.gen_initState_def by auto
  next
    case (Active sss)
    hence transp:"k_mod.gen_nextState k pp sss (HOrcvdMsgs ?A pp (HO (Suc ii) pp) (rho ii)) ss"
      (is "k_mod.gen_nextState _ _ _ ?msgp _") using assms transition Suc by auto
    from Active have "?msgp pp = Content sss" using loop sending run by presburger
    have "k_mod.forceMsgs (?msgp pp) : k_mod.forceMsgs ` (range ?msgp)" by blast
    moreover have "k_mod.forceMsgs (?msgp pp) = 1" using Suc.IH[of pp sss] Active `?msgp pp = Content sss` by (simp add: Suc_lessD `Suc ii < k` k_mod.forceMsgs.simps(1))
    ultimately have "k_mod.maxForce ?msgp >= 1" unfolding k_mod.maxForce_def by simp
    moreover have a:"ALL p s. ?msgp p = Content s --> x s <= ii & level s = 0 & forc s = 1" using Suc.IH sending_rec by (meson `Suc ii < k` lessI less_trans run)
    hence "ALL p. k_mod.forceMsgs (?msgp p) <= 1" 
      unfolding k_mod.maxForce_def by (metis One_nat_def diff_Suc_1 diff_is_0_eq k_mod.forceMsgs.elims le_SucI le_zero_eq)
    ultimately have forc0:"k_mod.maxForce ?msgp = 1" unfolding k_mod.maxForce_def by (simp add: le_antisym) 

    moreover have "?msgp pp = Content sss" using Active sending run using loop by auto
    ultimately have pp_inf:"?msgp pp = Content sss & forc sss = k_mod.maxForce ?msgp & x sss <= ii" using a by auto
    let ?prop = "%sss pp ii. ?msgp pp = Content sss & forc sss = k_mod.maxForce ?msgp & x sss = ii"
    from pp_inf have "?prop sss pp (x sss)" and "x sss <= ii" by auto
    from pp_inf have "(LEAST i. EX s p. ?prop s p i) <= x sss" using Least_le by (smt (verit, del_insts))
    hence "k_mod.minMsgs ?msgp <= ii" using `x sss <= ii` unfolding k_mod.minMsgs_def by auto
    moreover from this `Suc ii < k` Active have non_levelup:"~ (k_mod.ready_level1 k ?msgp sss | k_mod.ready_level2 k ?msgp sss)"
      unfolding k_mod.ready_level2_def k_mod.ready_level1_def by auto
    ultimately have "x ss <= Suc ii" using transp unfolding k_mod.gen_nextState_def by auto
    moreover from Suc.IH have "level ss = 0" using transp `Suc ii < k` Active unfolding k_mod.gen_nextState_def by (metis non_levelup a pp_inf)
    moreover from forc0 have "forc ss = 1" using non_levelup transp unfolding k_mod.gen_nextState_def by auto
    ultimately show ?thesis by auto
  qed
qed

lemma A2_bis:
assumes loop:"ALL p r. p : HO r p"
and run: "HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A _ _")
and "k > 2"
and "rho r p = Active s"
shows "forc s >= 1 & level s <= 2" using `rho r p = Active s`
proof (induction r arbitrary: p s)
  case 0
  thus ?case using starting[of 0 rho p k HO s] assms unfolding k_mod.gen_initState_def by auto
next
case (Suc rr)
  show ?case
  proof (cases "rho rr p")
    case Asleep
    thus "forc s >= 1 & level s <= 2" using starting[of "Suc rr" rho p k HO s] Suc assms unfolding k_mod.gen_initState_def by auto
  next
    case (Active ss)
    let ?msgp = "HOrcvdMsgs ?A p (HO (Suc rr) p) (rho rr)"
    have "?msgp p = Content ss" using Active loop sending run by presburger
    have "k_mod.forceMsgs (?msgp p) : k_mod.forceMsgs ` (range ?msgp)" by blast
    moreover have "k_mod.forceMsgs (?msgp p) >= 1" using Suc.IH[of p ss] Active `?msgp p = Content ss` by (simp add: k_mod.forceMsgs.simps(1))
    ultimately have "k_mod.maxForce ?msgp >= 1" unfolding k_mod.maxForce_def by (meson Max_ge_iff UNIV_not_empty finite finite_imageI image_is_empty)
    moreover have transp:"k_mod.gen_nextState k p ss ?msgp s" using Active assms transition Suc by auto
    hence "forc s >= k_mod.maxForce ?msgp" unfolding k_mod.gen_nextState_def by auto
    ultimately show "forc s >= 1 & level s <= 2" using transp Suc.IH[of p ss] Active unfolding k_mod.gen_nextState_def by auto
  qed
qed



lemma A3:
assumes star:"ALL p n. k_mod.path HO xi p n k"
and loop:"ALL p r. p : HO r p"
and run: "HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A _ _")
and "k > 2"
and "rho r xi = Active sp"
and "rho (Suc r) xi = Active ssp"
and "level sp = 0"
and "level ssp = 1"
and "rho (r+i) q = Active sq"
and "rho (r+Suc i) q = Active ssq"
and "level sq  < level ssq"
and "i > 0"
shows "i >= k"
proof (rule ccontr)
  assume "~ i >= k"
  have transp:"k_mod.gen_nextState k xi sp (HOrcvdMsgs ?A xi (HO (Suc r) xi) (rho r)) ssp"
    (is "k_mod.gen_nextState _ _ _ ?msgp _") using assms transition by auto
  have "Suc r >= k"
  proof (rule ccontr)
    assume "~ Suc r >= k"
    thus "False" using assms A2 by (metis not_le zero_neq_one)
  qed
  hence lev1p:"k_mod.ready_level1 k ?msgp sp" using assms transp
    unfolding k_mod.gen_nextState_def k_mod.ready_level1_def by (metis k_mod.ready_level2_def zero_neq_one) 
  hence "k_mod.isConc k ?msgp" unfolding k_mod.ready_level1_def by auto
  from loop have self_path:"k_mod.path HO xi xi (Suc r-k+i) (k-i)" unfolding k_mod.path_def by auto
  from transp lev1p have "x ssp mod k = 0"
    unfolding k_mod.gen_nextState_def k_mod.ready_level1_def 
    by (metis (no_types, hide_lams) Suc_diff_1 add.right_neutral assms(4) bits_mod_0 gr_implies_not_zero linorder_neqE_nat mod_Suc_eq mod_add_self1) 
  hence val_xi:"EX sxi. rho (Suc r+i-k) xi = Active sxi & x sxi mod k = i"
    using A1[of HO xi xi "Suc r-k" i k rho ssp] assms `Suc r >= k` `k_mod.isConc k ?msgp` `~ i >= k` self_path by auto
  have transq:"k_mod.gen_nextState k q sq (HOrcvdMsgs ?A q (HO (Suc r+i) q) (rho (r+i))) ssq"
    (is "k_mod.gen_nextState _ _ _ ?msgq _") using assms transition by auto
  hence lev1q:"k_mod.ready_level1 k ?msgq sq | k_mod.ready_level2 k ?msgq sq" using assms transp
    unfolding k_mod.gen_nextState_def k_mod.ready_level1_def k_mod.ready_level2_def zero_neq_one by auto 
  hence "k_mod.isConc k ?msgq" unfolding k_mod.ready_level1_def k_mod.ready_level2_def by auto
  from transq lev1q have "x ssq mod k = 0"
    unfolding k_mod.gen_nextState_def k_mod.ready_level1_def k_mod.ready_level2_def
    by (smt (verit, best) Suc_1 Suc_diff_1 Suc_less_eq2 assms(4) less_Suc_eq_0_disj mod_Suc mod_less) 
  hence "EX sxi. rho (Suc r+i-k) xi = Active sxi & x sxi mod k = 0" using A1[of HO xi q "Suc r-k+i" 0 k rho ssq] assms `Suc r >= k` `k_mod.isConc k ?msgq` by auto
  thus "False" using val_xi `~ i >= k` `i > 0` by auto
qed

definition active_path where 
"active_path rho HO p q n D == EX seq. seq 0 = p & seq D = q &
    (ALL i < D. rho (n+i) (seq (Suc i)) ~= Asleep & seq i : HO (n+Suc i) (seq (Suc i)))"

lemma increasing_force:
assumes star:"ALL p n. k_mod.path HO xi p n k"
and loop:"ALL p r. p : HO r p"
and run: "HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A _ _")
and "k > 2"
and sp:"rho t p = Active sp"
shows "active_path rho HO p q t r --> rho (t+r) q = Active sq --> forc sp <= forc sq"
proof (induction r arbitrary:sq q)
  case 0
  show "active_path rho HO p q t 0 --> rho (t+0) q = Active sq --> forc sp <= forc sq" using sp unfolding active_path_def by fastforce
next
  case (Suc rr)
  show "active_path rho HO p q t (Suc rr) --> rho (t+Suc rr) q = Active sq --> forc sp <= forc sq"
  proof (rule impI)+
    assume "active_path rho HO p q t (Suc rr)" and sq:"rho (t+Suc rr) q = Active sq"
    then obtain seq where seq0:"seq 0 = p" and "seq (Suc rr) = q" and seqSuc:"ALL j < Suc rr. rho (t+j) (seq (Suc j)) ~= Asleep & seq j : HO (t+Suc j) (seq (Suc j))"
      unfolding active_path_def by auto
    have "rho (t+rr) (seq rr) ~= Asleep"
    proof (cases "rr")
      case 0
      thus "rho (t+rr) (seq rr) ~= Asleep" using seq0 sp by auto
    next
      case (Suc rrr)
      hence "rho (t+rr-1) (seq rr) ~= Asleep" using `seq (Suc rr) = q` seqSuc by auto
      thus "rho (t+rr) (seq rr) ~= Asleep" using run nonAsleepAgain
        unfolding HORun_def by (smt (z3) Suc add.commute add_Suc less_add_Suc2 plus_1_eq_Suc proc_state.simps(3) seqSuc)
    qed
    then obtain sqq where sqq:"rho (t+rr) (seq rr) = Active sqq" using run
      unfolding HORun_def by (cases "rho (t+rr) (seq rr)") auto
    have "seq rr : HO (t+Suc rr) q" using seqSuc `seq (Suc rr) = q` by auto
    hence "active_path rho HO p (seq rr) t rr" using seq0 seqSuc unfolding active_path_def by auto
    hence "forc sp <= forc sqq" using sqq Suc.IH by simp
    have "HOrcvdMsgs ?A q (HO (t+Suc rr) q) (rho (t+rr)) (seq rr) = Content sqq" (is "?msgs (seq rr) = _")
      using sending[of rho "t+rr" "seq rr" sqq k HO] assms sqq `seq rr : HO (t+Suc rr) q` by auto
    hence maxf:"k_mod.maxForce ?msgs >= forc sp" using `forc sp <= forc sqq` unfolding k_mod.maxForce_def
      by (smt (verit) Max_ge_iff UNIV_I UNIV_not_empty finite finite_imageI image_eqI image_is_empty k_mod.forceMsgs.simps(1))
    from `seq (Suc rr) = q` seqSuc obtain ssq where "rho (t+rr) q = Active ssq" by (cases "rho (t+rr) q") auto
    hence "k_mod.gen_nextState k q ssq ?msgs sq" using assms sq transition[of _ "t+rr" q ssq sq] by auto
    thus "forc sp <= forc sq" using maxf unfolding k_mod.gen_nextState_def by auto
  qed
qed

lemma path_shrink:
assumes "seq 0 = p"
and "seq k = q"
and "ALL j < k. seq j : HO (n+Suc j) (seq (Suc j))"
and "i <= k"
shows "k_mod.path HO (seq i) q (n+i) (k-i)"
proof  -
  have "ALL j < k-i. seq (i+j) : HO (n+i+Suc j) (seq (i+Suc j))" using assms(3) 
      by (smt (z3) add.commute add.left_commute add_Suc_right less_diff_conv)
  thus ?thesis using assms exI[of _ "%l. seq(i+l)"] unfolding k_mod.path_def by auto
qed

lemma A5:
assumes star:"ALL p n. k_mod.path HO xi p n k"
and loop:"ALL p r. p : HO r p"
and run: "HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A _ _")
and "k > 2"
and sp:"rho r p = Active sp"
and maxf:"k_mod.maxForce (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc r) p) (rho r)) = f"
and minc:"Suc (k_mod.minMsgs (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc r) p) (rho r))) = c" 
shows "EX q sq sqq. rho (Suc r-c) q = Active sqq & level sqq = f-1 & (if f = 1 then c <= r --> rho (r-c) q = Asleep else rho (r-c) q = Active sq & level sq = f-2)"
  using minc sp maxf sp
proof (induction c arbitrary:r p sp)
  case 0
  thus ?case by auto
next
  case cc:(Suc cc)
  define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc r) p) (rho r)"
  have "p : HO (Suc r) p" using loop by auto
  hence "msgp p = Content sp" using sp run sending cc unfolding msgp_def by simp
  have "forc sp >= 1" using A2_bis run cc(5) loop `2 < k` by blast
  hence "k_mod.forceMsgs (msgp p) > 0" using `msgp p = Content sp` by (simp add:k_mod.forceMsgs.simps(1))
  moreover have "k_mod.forceMsgs (msgp p) : k_mod.forceMsgs ` range msgp" by auto
  ultimately have "k_mod.maxForce msgp >= 1" using Max_ge[of "k_mod.forceMsgs ` range msgp" "k_mod.forceMsgs (msgp p)"]
    unfolding k_mod.maxForce_def by (metis One_nat_def finite finite_imageI le0 le_antisym not_le not_less_eq_eq)
  hence "f >= 1" using cc unfolding msgp_def by auto
  obtain q where "k_mod.forceMsgs (msgp q) = f" using Max_in[of "k_mod.forceMsgs ` range msgp"] cc unfolding k_mod.maxForce_def msgp_def by auto
  from this obtain sq where "msgp q = Content sq" using `f >= 1` by (metis One_nat_def k_mod.forceMsgs.elims not_less_eq_eq order_refl)
  hence "EX vv s sq. msgp q = Content sq & forc sq = k_mod.maxForce msgp & x sq = vv"
    using cc `k_mod.forceMsgs (msgp q) = f` unfolding msgp_def by (smt (z3) k_mod.forceMsgs.simps(1))
  from this obtain qq sqq where "msgp qq = Content sqq" and "forc sqq = k_mod.maxForce msgp" and "x sqq = cc"
    using LeastI_ex[of "%cc. EX sqq qq. msgp qq = Content sqq & forc sqq = k_mod.maxForce msgp & x sqq = cc"] cc(2) unfolding k_mod.minMsgs_def msgp_def by auto
  hence sqq:"rho r qq = Active sqq" using sending_rec run unfolding msgp_def by auto
  show ?case
  proof (cases r)
    case rr:(Suc rr)
    show ?thesis
    proof (cases cc)
      case 0
      show ?thesis
      proof (cases "rho (r-1) qq")
        case Asleep
        hence "level sqq = 0" and "forc sqq = 1" using starting[of r rho qq k _ sqq] run sqq unfolding k_mod.gen_initState_def by auto
        thus ?thesis using Asleep `forc sqq = k_mod.maxForce msgp` sqq 0 cc(4) unfolding msgp_def by auto
      next
        case (Active sqqq)
        define msgq where "msgq = HOrcvdMsgs (k_mod.gen_HOMachine k) qq (HO r qq) (rho (r-1))"
        hence transq:"k_mod.gen_nextState k qq sqqq msgq sqq" using `2 < k`
          transition[of rho "r-1" qq sqqq sqq k HO] sqq Active rr run unfolding msgq_def by auto
        hence "k_mod.ready_level1 k msgq sqqq | k_mod.ready_level2 k msgq sqqq" and "forc sqq = Suc (level sqq)"
          using 0 `x sqq = cc` unfolding k_mod.gen_nextState_def by auto
        hence "level sqq = Suc (level sqqq)" using transq unfolding k_mod.gen_nextState_def k_mod.ready_level1_def k_mod.ready_level2_def by auto
        thus ?thesis using Active 0 sqq `forc sqq = Suc (level sqq)` 
          by (metis One_nat_def cc.prems(3) Suc_1 `forc sqq = k_mod.maxForce msgp` diff_Suc_1 diff_Suc_Suc msgp_def nat.simps(3)) 
      qed
    next
      case (Suc ccc)
      define msgq where "msgq = HOrcvdMsgs (k_mod.gen_HOMachine k) qq (HO r qq) (rho (r-1))"
      from Suc obtain sqqq where sqqq:"rho (r-1) qq = Active sqqq" using starting[of r rho qq k HO sqq] `x sqq = cc`
        run sqq unfolding k_mod.gen_initState_def by (cases "rho (r-1) qq") auto
      hence transq:"k_mod.gen_nextState k qq sqqq msgq sqq" using `2 < k` 
        transition[of rho "r-1" qq sqqq sqq k HO] sqq rr run unfolding msgq_def by auto
      hence "x sqq = Suc (k_mod.minMsgs msgq)" using Suc `x sqq = cc` unfolding k_mod.gen_nextState_def by auto
      moreover have "forc sqq = k_mod.maxForce msgq" using transq Suc `x sqq = cc` unfolding k_mod.gen_nextState_def by auto
      hence "k_mod.maxForce msgq = f" using cc(4) `forc sqq = k_mod.maxForce msgp` unfolding msgp_def by auto
      ultimately have postih:"EX tr srr sr. rho (Suc r - Suc cc) tr = Active sr & level sr = f - 1 &
       (if f = 1 then cc <= r - 1 --> rho (r - Suc cc) tr = Asleep else rho (r - Suc cc) tr = Active srr & level srr = f - 2)"
        using cc.IH[of qq "r-1" sqqq] `x sqq = cc` rr sqqq unfolding msgq_def by auto
      thus ?thesis using diff_Suc_1 rr by fastforce
    qed
  next
    case 0
    hence "level sqq = 0" and "forc sqq = 1" and "x sqq = 0" using starting[of r rho qq k _ sqq] run sqq unfolding k_mod.gen_initState_def by auto
    thus ?thesis using sqq `x sqq = cc` `forc sqq = k_mod.maxForce msgp` sqq 0 cc(4) unfolding msgp_def by auto
  qed
qed

lemma level_force:
assumes loop:"ALL p r. p : HO r p"
and run: "HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A _ _")
and "k > 2"
and sp:"rho t p = Active sp"
shows "level sp < forc sp" using sp
proof (induction t arbitrary:sp)
  case 0
  thus ?case using assms starting[of 0 rho p k HO sp] unfolding k_mod.gen_initState_def by auto 
next
  case (Suc tt)
  show ?case
  proof (cases "rho tt p")
    case Asleep
    thus ?thesis using assms Suc starting[of "Suc tt" rho p k HO sp] unfolding k_mod.gen_initState_def by auto 
  next
    case (Active spp)
    define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc tt) p) (rho tt)"
    hence "msgp p = Content spp" using sending assms Active by auto
    hence "k_mod.maxForce msgp >= forc spp" unfolding k_mod.maxForce_def by (metis Max_ge finite_UNIV finite_imageI image_eqI k_mod.forceMsgs.simps(1) rangeI)
    moreover have transp:"k_mod.gen_nextState k p spp msgp sp" using Active assms Suc transition unfolding msgp_def by auto
    ultimately have "forc sp >= forc spp | forc sp = Suc (level sp)" unfolding k_mod.gen_nextState_def by presburger
    thus ?thesis using Suc.IH[of spp] Active transp unfolding k_mod.gen_nextState_def by auto
  qed
qed


lemma A6:
assumes star:"ALL p n. k_mod.path HO xi p n k"
and loop:"ALL p r. p : HO r p"
and run: "HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A _ _")
and "k > 2"
and sp:"rho (t+i) p = Active sp"
and lvup:"ALL sqq. t > 0 --> rho (t-1) q = Active sqq --> level sqq < level sq"
and sq:"rho t q = Active sq"
and path:"active_path rho HO q p t (Suc i)"
and msgp:"msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc t+i) p) (rho (t+i))"
shows "Suc (level sq) < k_mod.maxForce msgp | (Suc (level sq) = k_mod.maxForce msgp & (k_mod.minMsgs msgp) <= i)"
  using path sp msgp
proof (induction i arbitrary:p sp msgp)
  case 0
  hence "q : HO (Suc t) p" unfolding active_path_def by auto
  hence msgq:"msgp q = Content sq" using 0 sending run sq by auto
  thus ?case
  proof (cases "Suc (level sq) < k_mod.maxForce msgp")
    case True
    thus ?thesis by auto
  next
    case False
    have "k_mod.maxForce msgp >= forc sq" using msgq unfolding k_mod.maxForce_def
      by (metis Max_ge finite_UNIV finite_imageI image_eqI k_mod.forceMsgs.simps(1) rangeI)
    hence "forc sq = k_mod.maxForce msgp" and eq:"Suc (level sq) = k_mod.maxForce msgp" and "forc sq = Suc (level sq)"
      using False level_force[of HO k rho t q sq] assms by auto
    hence "k_mod.minMsgs msgp <= x sq" using msgq unfolding k_mod.minMsgs_def by (metis (mono_tags, lifting) Least_le)
    thus ?thesis
    proof (cases "t > 0 --> rho (t-1) q = Asleep")
      case True
      hence "x sq = 0" using run sq starting unfolding k_mod.gen_initState_def by (metis locState.select_convs(1))
      thus ?thesis  using eq `k_mod.minMsgs msgp <= x sq` by auto
    next
      case False
      define msgq where "msgq = HOrcvdMsgs (k_mod.gen_HOMachine k) q (HO t q) (rho (t-1))"
      from False obtain sqq where sqq:"rho (t-1) q = Active sqq" by (cases "rho (t-1) q") auto
      hence transq:"k_mod.gen_nextState k q sqq msgq sq"
        using assms transition[of rho "t-1" q sqq sq k HO] False Suc_diff_1 unfolding msgq_def by fastforce
      hence "level sqq < level sq"  using lvup False sqq by auto
      hence "x sq = 0" using transq `forc sq = Suc (level sq)` unfolding k_mod.gen_nextState_def by auto
      thus ?thesis using `k_mod.minMsgs msgp <= x sq` eq by auto
    qed
  qed
next
  case (Suc ii)
  from Suc(2) obtain seq where "seq 0 = q" and "seq (Suc (Suc ii)) = p" and
    seq:"ALL j < Suc (Suc ii). rho (t+j) (seq (Suc j)) ~= Asleep & seq j : HO (t+Suc j) (seq (Suc j))"
    unfolding active_path_def by auto
  hence "active_path rho HO q (seq (Suc ii)) t (Suc ii)" unfolding active_path_def by auto
  define msgs where "msgs = HOrcvdMsgs (k_mod.gen_HOMachine k) (seq (Suc ii)) (HO (t+Suc ii) (seq (Suc ii))) (rho (t+ii))"
  from seq obtain ss where ss:"rho (t+ii) (seq (Suc ii)) = Active ss" and "seq (Suc ii) : HO (t+Suc (Suc ii)) p"
    using `seq (Suc (Suc ii)) = p` by (cases "rho (t+ii) (seq (Suc ii))") auto
  from ss obtain sss where sss:"rho (t+Suc ii) (seq (Suc ii)) = Active sss"
    using nonAsleepAgain[of rho "t+ii" "seq (Suc ii)" _ _ _ 1] assms unfolding HORun_def by fastforce
  hence transs:"k_mod.gen_nextState k (seq (Suc ii)) ss msgs sss" using ss transition assms unfolding msgs_def by auto
  have ih:"Suc (level sq) < k_mod.maxForce msgs | (Suc (level sq) = k_mod.maxForce msgs & k_mod.minMsgs msgs <= ii)"
    using Suc.IH ss `active_path rho HO q (seq (Suc ii)) t (Suc ii)` msgs_def by auto
  have "k_mod.maxForce msgs <= forc sss" and "x sss <= Suc (k_mod.minMsgs msgs)" using transs unfolding k_mod.gen_nextState_def by auto


  have send:"msgp (seq (Suc ii)) = Content sss" using `seq (Suc ii) : HO (t+Suc (Suc ii)) p` sss
    sending[of rho "t+Suc ii" "seq (Suc ii)"] assms unfolding Suc(4) by auto
  thus ?case
  proof (cases "Suc (level sq) < k_mod.maxForce msgp")
    case True
    thus ?thesis by auto
  next
    case False
    have "Suc (level sq) <= k_mod.maxForce msgs" using ih by auto
    moreover have "k_mod.maxForce msgp >= forc sss" using `msgp (seq (Suc ii)) = Content sss`
      unfolding k_mod.maxForce_def by (metis Max_ge finite_UNIV finite_imageI image_eqI k_mod.forceMsgs.simps(1) rangeI)
    ultimately have "Suc (level sq) = k_mod.maxForce msgp" and "forc sss = k_mod.maxForce msgp"
      using False `k_mod.maxForce msgs <= forc sss` send by auto
    moreover from this have "k_mod.minMsgs msgp <= x sss" using `msgp (seq (Suc ii)) = Content sss`
      unfolding k_mod.minMsgs_def by (metis (mono_tags, lifting) Least_le)
    ultimately show ?thesis using `x sss <= Suc (k_mod.minMsgs msgs)` `k_mod.maxForce msgs <= forc sss` ih by linarith
  qed
qed

lemma extend_path:
assumes star:"ALL p n. k_mod.path HO xi p n k"
and loop:"ALL p r. p : HO r p"
and run: "HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A _ _")
and "k > 2"
and sp:"rho (t+i) p = Active sp"
and ssp:"rho (t+Suc i) p = Active ssp"
and "level sp < level ssp"
and ss:"rho (Suc t) xi = Active ss"
and "i >= k"
shows "active_path rho HO xi p (Suc t) i"
and "forc ss <= k_mod.maxForce (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+Suc i) p) (rho (t+i)))"
proof -
  define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+Suc i) p) (rho (t+i))"
  have transp:"k_mod.gen_nextState k p sp msgp ssp" using assms transition unfolding msgp_def by auto
  hence lev2p:"k_mod.ready_level1 k msgp sp | k_mod.ready_level2 k msgp sp" using assms transp unfolding k_mod.gen_nextState_def by simp 
  hence "k_mod.isConc k msgp" unfolding k_mod.ready_level1_def k_mod.ready_level2_def by auto
  from star obtain seq where "seq 0 = xi" and "seq k = p" and
    pat:"ALL j < k. seq j : HO (Suc t+i-k+Suc j) (seq (Suc j))" (is "ALL j < _. _ : ?HOseq j") unfolding k_mod.path_def by meson
  have nopass:"ALL j < k. rho (Suc t+i-k+j) (seq (Suc j)) ~= Asleep"
  proof (rule+)
    fix j
    assume "j < k" and "rho (Suc t+i-k+j) (seq (Suc j)) = Asleep"
    show "False"
    proof (cases "Suc j = k")
      case True
      thus "False" using `rho (t+i) p = Active sp` `rho (Suc t+i-k+j) (seq (Suc j)) = Asleep` `i >= k` `seq k = p` by fastforce
    next
      case False
      have "k_mod.path HO (seq (Suc j)) p (Suc t+i - k + Suc j) (k - Suc j)"
        using path_shrink[of seq xi k p HO "Suc t+i - k" "Suc j"] `seq k = p` `seq 0 = xi` pat `j < k` by auto
      moreover from transp lev2p have "x ssp mod k = 0" unfolding k_mod.ready_level1_def k_mod.ready_level2_def k_mod.gen_nextState_def
        by (smt (z3) One_nat_def Suc_1 Suc_diff_1 Suc_lessD assms(4) mod_Suc mod_less)
      ultimately obtain ss where ss:"rho (Suc t+i-k+Suc j) (seq (Suc j)) = Active ss & x ss mod k = Suc j"
        using assms `i >= k` `k_mod.isConc k msgp` A1[of HO "seq (Suc j)" p "Suc t+i-k" "Suc j" k rho ssp] `j < k` False unfolding msgp_def by auto
      hence "ss ~= k_mod.gen_initState" using `rho (Suc t+i-k+j) (seq (Suc j)) = Asleep` starting unfolding k_mod.gen_initState_def by auto
      thus "False" using `rho (Suc t+i-k+j) (seq (Suc j)) = Asleep` starting[of "t+i-k+j"] `i >= k` run ss
        by (metis add_Suc_right diff_Suc_1 starting)
    qed
  qed
  hence "rho (t+i-1) (seq (k-1)) ~= Asleep" using `2 < k` `k <= i`
    by (smt (z3) Nat.add_diff_assoc One_nat_def Suc_1 Suc_diff_Suc Suc_lessD diff_Suc_1 group_cancel.add1 le_add1 le_add_diff_inverse2 less_eq_Suc_le plus_1_eq_Suc)
  from this obtain sm where sm:"rho (t+i) (seq (k-1)) = Active sm"
    using nonAsleepAgain[of rho "t+i-1" "seq (k-1)" _ _ _ 1] assms `k <= i` unfolding HORun_def by fastforce
  let ?exseq = "%l. if l <= i-k then xi else seq (l - (i-k))"
  have extrem:"?exseq 0 = xi & ?exseq i = p" using `seq k = p` `k <= i` assms(4) by force 
  moreover have expat:"ALL l < i. rho (Suc t+l) (?exseq (Suc l)) ~= Asleep & ?exseq l : HO (Suc (Suc t)+l) (?exseq (Suc l))"
  proof (rule allI impI)+
    fix l
    assume "l < i"
    show "rho (Suc t+l) (?exseq (Suc l)) ~= Asleep & ?exseq l : HO (Suc (Suc t)+l) (?exseq (Suc l))" 
    proof (cases "l < i-k")
      case True
      hence "rho (Suc t+l) (?exseq (Suc l)) ~= Asleep" using nonAsleepAgain[of rho "Suc t" xi] run
        unfolding HORun_def by (smt (verit) Suc_leI assms(8) proc_state.simps(3))
      thus "rho (Suc t+l) (?exseq (Suc l)) ~= Asleep & ?exseq l : HO (Suc (Suc t)+l) (?exseq (Suc l))" using loop True by auto
    next
      case False
      hence "l-(i-k) < k" using `i >= k` `2 < k` by (metis `l < i` diff_diff_cancel diff_le_self less_diff_iff not_le_imp_less)
      hence "seq (l-(i-k)) : HO (Suc t+i-k+(Suc l-(i-k))) (seq (Suc l-(i-k)))" using pat False Suc_diff_le by auto
      hence "?exseq l : HO (Suc t+Suc l) (?exseq (Suc l))"
        using pat `seq 0 = xi` `l-(i-k) < k` False
        by (smt (z3) Nat.add_diff_assoc `i >= k`  diff_is_0_eq' group_cancel.add1 le_add_diff_inverse nat_less_le not_less_eq)

      moreover have "rho (Suc t+l) (?exseq (Suc l)) ~= Asleep" using `ALL j < k. rho (Suc t+i-k+j) (seq (Suc j)) ~= Asleep` False `l-(i-k) < k` `i >= k`
        by (smt (z3) Nat.add_diff_assoc Suc_eq_plus1 Suc_le_eq add.commute add.left_commute leI le_add_diff_inverse2)
      ultimately show "rho (Suc t+l) (?exseq (Suc l)) ~= Asleep & ?exseq l : HO (Suc (Suc t)+l) (?exseq (Suc l))" by simp
    qed
  qed
  ultimately have patt:"active_path rho HO xi p (Suc t) i" using `seq k = p`
    exI[of "%seqq. seqq 0 = xi & seqq i = p & (ALL j < i. rho (Suc t+j) (seqq (Suc j)) ~= Asleep & seqq j : HO (Suc t+Suc j) (seqq (Suc j)))" ?exseq]
    unfolding active_path_def by auto
  have "ALL j < i-1. rho (Suc t+j) (?exseq (Suc j)) ~= Asleep & ?exseq j : HO (Suc t+Suc j) (?exseq (Suc j))" using expat by auto
  hence "active_path rho HO xi (seq (k-1)) (Suc t) (i - 1)" using `seq k = p`
    exI[of "%seqq. seqq 0 = xi & seqq (i-1) = seq (k-1) &
    (ALL j < i-1. rho (Suc t+j) (seqq (Suc j)) ~= Asleep & seqq j : HO (Suc t+Suc j) (seqq (Suc j)))" ?exseq] extrem expat `k <= i` `seq 0 = xi`
    unfolding active_path_def by auto
  hence "forc sm >= forc ss" using increasing_force[of HO xi k rho "Suc t" xi ss "seq (k-1)" "i-1" sm] sm assms
    by (metis Suc_diff_1 `k <= i` add_Suc_shift dual_order.strict_trans1 less_nat_zero_code neq0_conv)
  have "seq (k-1) : HO (Suc t+i) p" using pat `seq k = p`
    by (smt (verit, del_insts) add_Suc assms(9) assms(4) diff_Suc_1 le_add_diff_inverse2 lessI less_add_Suc2 less_iff_Suc_add nat_less_le order_trans)
  hence "msgp (seq (k-1)) = Content sm" using sm sending run unfolding msgp_def by auto
  hence "k_mod.maxForce msgp >= forc ss" using `forc sm >= forc ss`
    by (metis (mono_tags, hide_lams) Max_ge dual_order.strict_trans1 finite_UNIV
    finite_imageI image_eqI k_mod.forceMsgs.simps(1) k_mod.maxForce_def not_le rangeI)
  thus  "active_path rho HO xi p (Suc t) i"
    and "forc ss <= k_mod.maxForce (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+Suc i) p) (rho (t+i)))"
    using patt unfolding msgp_def by auto
qed


lemma level_growing:
assumes loop:"ALL p r. p : HO r p"
and run: "HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A _ _")
and "k > 2"
and s:"rho r p = Active s"
and "rho (r+i) p = Active ss"
shows "level s <= level ss" using `rho (r+i) p = Active ss`
proof (induction i arbitrary: ss)
  case 0
  thus ?case using starting[of 0 rho p k HO s] assms unfolding k_mod.gen_initState_def by auto
next
  case (Suc rr)
  obtain sss where sss:"rho (r+rr) p = Active sss" using nonAsleepAgain[of rho r p _ _ _ rr] run s unfolding HORun_def by fastforce
  let ?msgp = "HOrcvdMsgs ?A p (HO (r+Suc rr) p) (rho (r+rr))"
  have "?msgp p = Content sss" using sss loop sending[of rho "r+rr" p sss] run by simp
  have "k_mod.forceMsgs (?msgp p) : k_mod.forceMsgs ` (range ?msgp)" by blast
  have transp:"k_mod.gen_nextState k p sss ?msgp ss" using sss assms transition Suc by auto
  hence "level ss >= level sss" unfolding k_mod.ready_level2_def k_mod.ready_level1_def k_mod.gen_nextState_def by auto
  thus "level s <= level ss" using Suc.IH sss by auto
qed

lemma A4:
assumes star:"ALL p n. k_mod.path HO xi p n k"
and loop:"ALL p r. p : HO r p"
and run: "HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A _ _")
and "k > 2"
and sp:"rho (t+i) p = Active sp"
and ssp:"rho (t+Suc i) p = Active ssp"
and "level sp = 1"
and "level ssp = 2"
and s:"rho t xi = Active s"
and ss:"rho (Suc t) xi = Active ss"
and "level s = 0"
and "level ss = 1"
shows "i mod k = 0"
proof (rule ccontr)
  assume "~ i mod k = 0"
  have "level sp < level ssp" using assms by auto
  let ?n = "LEAST nn. EX s. rho nn xi = Active s & level s > 0"
  define j where "j = (LEAST jj. EX q sq ssq. rho (t+jj) q = Active sq &
    rho (t+Suc jj) q = Active ssq & level sq < level ssq & jj mod k ~= 0)" (is "j = (LEAST jj. EX qj sj sjj. ?P jj qj sj sjj)")
  hence "EX i q sq ssq. rho (t+ i) q = Active sq & rho (t+Suc i) q = Active ssq & level sq < level ssq & i mod k ~= 0"
    using `~ i mod k = 0` assms(7) assms(8) sp ssp by fastforce
  from this obtain q sq ssq where sq:"rho (t+j) q = Active sq" and ssq:"rho (t+Suc j) q = Active ssq"
    and levsq:"level sq < level ssq" and "j mod k ~= 0"
    using LeastI_ex[of "%jj. EX qj sj sjj. ?P jj qj sj sjj"] unfolding j_def by blast
  define msgq where "msgq = HOrcvdMsgs (k_mod.gen_HOMachine k) q (HO (t+Suc j) q) (rho (t+j))"
  hence transq:"k_mod.gen_nextState k q sq msgq ssq" using assms transition[of rho "t+j" q sq ssq k HO] 
      sq ssq unfolding msgq_def by auto
  define f where "f = k_mod.maxForce msgq"
  define c where "c = k_mod.minMsgs msgq"
  have "c mod k = k-1" using levsq sq ssq transq
    unfolding c_def msgq_def k_mod.gen_nextState_def k_mod.ready_level1_def k_mod.ready_level2_def by auto
  hence "j-Suc c mod k ~= 0"
    using `j mod k ~= 0` by (metis One_nat_def Suc_1 Suc_lessD Suc_pred assms(4) diff_zero mod_0 mod_Suc)

  have "i >= k" using assms A3[of HO xi k rho t s ss i p sp ssp] by (metis Suc_1 `i mod k ~= 0` bits_mod_0 lessI neq0_conv)
  have "j >= k" using assms sq ssq levsq A3[of HO xi k rho t s ss j q sq ssq] by (metis `j mod k ~= 0` bits_mod_0 neq0_conv)



  obtain h sh shh where shh:"rho (t+j-c) h = Active shh" and "level shh = f-1" and
    sh_pre:"if f = 1 then Suc c <= t+j --> rho (t+j-Suc c) h = Asleep else rho (t+j-Suc c) h = Active sh & level sh = f-2"
    using A5[of HO xi k rho "t+j" q sq f "Suc c"] sq assms unfolding f_def c_def msgq_def by fastforce
  define msgh where "msgh = HOrcvdMsgs (k_mod.gen_HOMachine k) h (HO (t+j-c) h) (rho (t+j-Suc c))"
  have "forc ss <= f" and "active_path rho HO xi q (Suc t) j" using extend_path[of HO xi k rho t j q sq ssq ss]
    assms sq ssq levsq `j >= k` unfolding msgq_def f_def by auto
  hence "1 < f" using level_force[of HO k rho "Suc t" xi ss] sq assms by auto
  hence "t+j >= Suc c" using sh_pre
    `level shh = f-1` by (metis (mono_tags, lifting) One_nat_def Suc_1 Suc_diff_Suc diff_is_0_eq' diff_zero nat_le_linear not_less_eq_eq proc_state.inject shh)
  hence transh:"k_mod.gen_nextState k h sh msgh shh" using assms transition[of rho "t+j-Suc c" h sh shh k HO] sh_pre
    `level shh = f-1` unfolding msgh_def by (metis Suc_diff_le `1 < f` diff_Suc_Suc less_not_refl2 shh)
  hence "k_mod.ready_level1 k msgh sh | k_mod.ready_level2 k msgh sh" using `level shh = f-1` sh_pre `1 < f` transh
    unfolding k_mod.gen_nextState_def by auto
  hence "k_mod.isConc k msgh" and "k_mod.minMsgs msgh mod k = k - 1" and "x shh = 0 | x shh = Suc (k_mod.minMsgs msgh)" using transh
    unfolding k_mod.ready_level1_def k_mod.ready_level2_def k_mod.gen_nextState_def by auto
  hence "x shh mod k = 0" by (metis assms(4) bits_mod_0 diff_Suc_1 less_iff_Suc_add mod_Suc)
  show "False"
  proof (cases "f = 2")
    case True
    have "j-1 >= c" using A6[of HO xi k rho "Suc t" "j-1" q sq xi ss msgq] assms True
      sq `active_path rho HO xi q (Suc t) j` `j >= k` unfolding c_def f_def msgq_def by fastforce
    hence "?P (j-Suc c) h sh shh" using sh_pre True shh `level shh = f-1` `j-Suc c mod k ~= 0`
      by (smt (verit, ccfv_SIG) Nat.add_diff_assoc Suc_diff_1 `1 < f` `c mod k = k - 1` `j mod k \<noteq> 0`
      add_Suc_shift assms(4) cancel_comm_monoid_add_class.diff_cancel diff_diff_left le_add_diff_inverse2
      less_numeral_extra(4) less_trans mod_Suc mod_add_left_eq neq0_conv not_less_eq_eq plus_1_eq_Suc zero_less_one)
    hence "EX qj sj sjj. ?P (j-Suc c) qj sj sjj" by auto
    thus "False" using Least_le[of "%jj. EX qj sj sjj. ?P jj qj sj sjj" "j-Suc c"] by (simp add: j_def)
  next
    case False
    hence "t+j-Suc c >= k" using sh_pre A2[of HO xi k rho "t+j-Suc c" h sh] run loop `2 < k` star
      by (metis One_nat_def Suc_1 Suc_diff_1 Suc_diff_Suc Suc_lessD `1 < f` less_numeral_extra(4) not_le_imp_less)
    hence "EX sss. rho (t+j-c-k) xi = Active sss & (k_mod.isReady msgh --> ready sss) & x sss mod k = 0"
      using `k_mod.isConc k msgh` A1[of HO xi h "t+j-c-k" 0 k rho shh] star loop run shh `2 < k` unfolding msgh_def
      by (smt (z3) Nat.add_0_right Suc_1 Suc_diff_Suc Suc_le_lessD Suc_lessD `Suc c \<le> t + j` `x shh mod k = 0`
      add.commute add_diff_inverse_nat diff_Suc_1 diff_zero less_trans not_le)
    moreover have "level shh = 2" using `level shh = f-1` A2_bis[of HO k rho "t+j-c" h shh] run loop `2 < k` shh False `1 < f` by auto
    hence "k_mod.isReady msgh" using `k_mod.ready_level1 k msgh sh | k_mod.ready_level2 k msgh sh` transh
      unfolding k_mod.gen_nextState_def k_mod.ready_level2_def by auto
    ultimately obtain sss where sss:"rho (t+j-c-k) xi = Active sss" and "x sss mod k = 0" and "ready sss" by auto
    hence "rho (t+j-Suc c-k) xi ~= Asleep" using starting[of "t+j-c-k" rho xi k HO sss] `t+j-Suc c >= k`
      unfolding k_mod.gen_initState_def by (metis Nat.add_0_right One_nat_def add_Suc_shift diff_diff_left locState.select_convs(3) run)
    from this obtain ssss where "rho (t+j-Suc c-k) xi = Active ssss" by (cases "rho (t+j-Suc c-k) xi") auto
    hence transx:"k_mod.gen_nextState k xi ssss (HOrcvdMsgs (k_mod.gen_HOMachine k) xi (HO (t+j-c-k) xi) (rho (t+j-Suc c-k))) sss"
      using sss assms transition[of rho "t+j-Suc c-k" xi ssss sss k HO]
      by (metis Suc_diff_Suc Suc_diff_le Suc_le_lessD `Suc c <= t + j` `k <= t + j - Suc c`)
    hence "level sss > 0" using `x sss mod k = 0` `ready sss` unfolding k_mod.gen_nextState_def by auto
    hence "t+j-c-k >= t" using `level s = 0` level_growing[of HO k rho "t+j-c-k" xi sss _s] s sss
      by (metis add_diff_inverse_nat assms(4) gr_implies_not0 le_less loop run)
    hence "j-Suc c > 0" using `2 < k` Suc_le_lessD `j mod k \<noteq> 0` `k \<le> t + j - Suc c` diff_add_inverse2 diff_le_self by linarith
    hence "?P (j-Suc c) h sh shh" using sh_pre `1 < f` shh `level shh = f-1` `j-Suc c mod k ~= 0`
      by (smt (verit, best) Nat.add_diff_assoc Suc_1 Suc_lessD `c mod k = k - 1` `j mod k \<noteq> 0` `level shh = 2`
      add_Suc_shift diff_Suc_1 diff_is_0_eq' le_add_diff_inverse2 less_iff_Suc_add less_numeral_extra(4)
      mod_Suc mod_add_left_eq nat_le_linear zero_less_diff)
    hence "EX qj sj sjj. ?P (j-Suc c) qj sj sjj" by auto
    thus "False" using Least_le[of "%jj. EX qj sj sjj. ?P jj qj sj sjj" "j-Suc c"] unfolding j_def by auto
  qed
qed


lemma safety:
assumes star:"ALL p n. k_mod.path HO xi p n k"
and loop:"ALL p r. p : HO r p"
and run: "HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A _ _")
and "k > 2"
shows "k_mod.safety k rho"
proof (cases "EX t s ss. rho t xi = Active s & rho (Suc t) xi = Active ss & level s = 0 & level ss = 1")
  case True
  define tt where "tt = (SOME t. EX s ss. rho t xi = Active s & rho (Suc t) xi = Active ss & level s = 0 & level ss = 1)"
    (is "tt = (SOME t. EX s ss. ?P t s ss)")
  obtain t sxt ssxt where "?P t sxt ssxt" using True by auto
  from this obtain sx ssx where "?P tt sx ssx" using someI_ex[of "%t. EX s ss. ?P t s ss"] unfolding tt_def by auto
  have "ALL p r sp ssp. rho r p = Active sp --> level sp < 2 --> rho (Suc r) p = Active ssp --> level ssp = 2 --> r mod k = tt mod k"
  proof (rule+)
    fix p r sp ssp
    assume sp:"rho r p = Active sp" and "level sp < 2" and ssp:"rho (Suc r) p = Active ssp" and "level ssp = 2" 
    define msgs where "msgs = HOrcvdMsgs (k_mod.gen_HOMachine k) xi (HO (Suc r-k) xi) (rho (r-k))"
    define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc r) p) (rho r)"
    hence transp:"k_mod.gen_nextState k p sp msgp ssp" using transition assms sp ssp by auto
    hence lev2:"k_mod.ready_level2 k msgp sp" using `level sp < 2` `level ssp = 2`
      unfolding k_mod.ready_level2_def k_mod.gen_nextState_def by auto
    hence "x ssp mod k = 0" using ssp transp unfolding k_mod.ready_level2_def k_mod.gen_nextState_def
      by (metis One_nat_def Suc_diff_1 Suc_lessD `level sp < 2` assms(4) less_trans mod_Suc mod_less)
    moreover have "r >= k" using A2[of HO xi k rho r p sp] lev2 leI assms sp unfolding k_mod.ready_level2_def by auto
    ultimately obtain sss where sss:"rho (Suc r-k) xi = Active sss" and "ready sss" and "x sss mod k = 0"
      using A1[of HO xi p "Suc r-k" 0 k rho ssp] star lev2 loop run ssp `2 < k` unfolding msgp_def k_mod.ready_level2_def by auto
    hence "rho (r-k) xi ~= Asleep" using starting[of "Suc r-k" rho xi] assms `r >= k` unfolding k_mod.gen_initState_def by fastforce
    from this obtain ss where "rho (r-k) xi = Active ss" by (cases "rho (r-k) xi") auto
    hence trans:"k_mod.gen_nextState k xi ss msgs sss" using transition
      `r >= k` assms sss Suc_diff_le unfolding msgs_def by fastforce
    hence "level sss > 0" using `ready sss` `x sss mod k = 0` unfolding k_mod.gen_nextState_def by auto
    hence "Suc r-k >= tt" using level_growing[of HO k rho "Suc r-k" xi sss "tt-(Suc r-k)" sx]
      sss `?P tt sx ssx` assms by (metis add_diff_inverse_nat le_less not_le)
    hence "(r-tt) mod k = 0" using A4[of HO xi k rho tt "r-tt" p sp ssp sx ssx] sp ssp
      `?P tt sx ssx` assms `level ssp = 2` lev2 unfolding k_mod.ready_level2_def by auto
    thus "r mod k = tt mod k" using `Suc r-k >= tt` mod_add_left_eq[of "r-tt" k tt] 
      by (metis Suc_1 Suc_diff_le `k <= r` add.commute add_cancel_right_left add_diff_inverse_nat assms(4)
      diff_less dual_order.strict_trans dual_order.strict_trans1 less_trans_Suc not_le zero_less_Suc)
  qed
  thus ?thesis unfolding k_mod.safety_def by auto
next
  case False
  have "ALL p r sp ssp. rho r p = Active sp --> level sp < 2 --> rho (Suc r) p = Active ssp --> level ssp = 2 --> r mod k = 0"
  proof (rule+)
    fix p r sp ssp
    assume sp:"rho r p = Active sp" and "level sp < 2" and ssp:"rho (Suc r) p = Active ssp" and "level ssp = 2" 
    define msgs where "msgs = HOrcvdMsgs (k_mod.gen_HOMachine k) xi (HO (Suc r-k) xi) (rho (r-k))"
    define msgp where "msgp = HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc r) p) (rho r)"
    hence transp:"k_mod.gen_nextState k p sp msgp ssp" using transition assms sp ssp by auto
    hence lev2:"k_mod.ready_level2 k msgp sp" using `level sp < 2` `level ssp = 2`
      unfolding k_mod.ready_level2_def k_mod.gen_nextState_def by auto
    hence "x ssp mod k = 0" using ssp transp unfolding k_mod.ready_level2_def k_mod.gen_nextState_def
      by (metis One_nat_def Suc_diff_1 Suc_lessD `level sp < 2` assms(4) less_trans mod_Suc mod_less)
    moreover have "r >= k" using A2[of HO xi k rho r p sp] lev2 leI assms sp unfolding k_mod.ready_level2_def by auto
    ultimately obtain sss where sss:"rho (Suc r-k) xi = Active sss" and "ready sss" and "x sss mod k = 0"
      using A1[of HO xi p "Suc r-k" 0 k rho ssp] star lev2 loop run ssp `2 < k` unfolding msgp_def k_mod.ready_level2_def by auto
    hence "rho (r-k) xi ~= Asleep" using starting[of "Suc r-k" rho xi] assms `r >= k` unfolding k_mod.gen_initState_def by fastforce
    from this obtain ss where "rho (r-k) xi = Active ss" by (cases "rho (r-k) xi") auto
    hence trans:"k_mod.gen_nextState k xi ss msgs sss" using transition
      `r >= k` assms sss Suc_diff_le unfolding msgs_def by fastforce
    hence "level sss > 0" using `ready sss` `x sss mod k = 0` unfolding k_mod.gen_nextState_def by auto
    define jj where "jj = (LEAST j. EX s. rho j xi = Active s & level s > 0)" (is "_ = (LEAST j. EX s. ?Q j s)")
    have "?Q (Suc r-k) sss" using sss `level sss > 0` by auto
    from this obtain s where s:"rho jj xi = Active s" and "level s > 0" using LeastI_ex[of "%j. EX s. ?Q j s"] unfolding jj_def by auto
    hence "rho (jj-1) xi ~= Asleep" using starting[of jj rho xi k HO s] assms unfolding k_mod.gen_initState_def by auto
    from this obtain sx where sx:"rho (jj-1) xi = Active sx" by (cases "rho (jj-1) xi") auto
    have "jj > 0" using starting[of jj rho xi k HO s] `level s > 0` assms s unfolding k_mod.gen_initState_def by fastforce
    define msgs where "msgs = HOrcvdMsgs (k_mod.gen_HOMachine k) xi (HO jj xi) (rho (jj-1))"
    hence transj:"k_mod.gen_nextState k xi sx msgs s" using transition s sx assms `jj > 0` by fastforce
    have "level sx = 0" using Least_le[of "%j. EX s. ?Q j s" "jj-1"] `jj > 0` sx
      unfolding jj_def by (meson diff_less neq0_conv not_le zero_less_one)
    hence "level s = 1" using transj `0 < level s` unfolding k_mod.ready_level2_def k_mod.gen_nextState_def by auto
    thus "r mod k = 0" using False `level sx = 0` s `jj > 0` sx by fastforce
  qed
  thus ?thesis unfolding k_mod.safety_def by auto
qed
