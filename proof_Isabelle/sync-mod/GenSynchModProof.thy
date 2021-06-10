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
      moreover have "x sp = 0" using levlup trans unfolding k_mod.gen_nextState_def by auto
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
    hence "k_mod.isConc k ?msg" using transq `conc sq` unfolding k_mod.gen_nextState_def by auto
    moreover from transq `x sq mod k > 0` assms k_mod.gen_nextState_def
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
  proof (cases "k_mod.ready_level1 k ?msgxi ss1 | k_mod.ready_level2 k ?msgxi ss1")
    case False
    thus ?thesis using trans1 unfolding k_mod.gen_nextState_def by auto
  next
    case True
    hence "k_mod.minMsgs ?msgxi mod k = k - 1" unfolding k_mod.ready_level1_def k_mod.ready_level2_def by auto
    moreover from True have "x s1 = 0" using trans1 unfolding k_mod.gen_nextState_def by auto
    ultimately show ?thesis by (metis Suc_diff_1 assms(8) bits_mod_0 gr_implies_not_zero linorder_neqE_nat mod_Suc)
  qed
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
shows "i < k --> rho i pp = Active ss --> level ss = 0 & x ss <= i & forc ss = 0"
proof (induction i arbitrary: pp ss)
  case 0
  thus ?case using starting[of 0 rho pp k HO ss] assms unfolding k_mod.gen_initState_def by auto
next
  case (Suc ii)
  show ?case
  proof (rule impI)+
    assume "Suc ii < k" and ss:"rho (Suc ii) pp = Active ss"
    show "level ss = 0 & x ss <= Suc ii & forc ss = 0"
    proof (cases "rho ii pp")
      case Asleep
      thus "level ss = 0 & x ss <= Suc ii & forc ss = 0" using ss run starting[of "Suc ii" rho pp k HO]
        unfolding k_mod.gen_initState_def by auto
    next
      case (Active sss)
      hence transp:"k_mod.gen_nextState k pp sss (HOrcvdMsgs ?A pp (HO (Suc ii) pp) (rho ii)) ss"
        (is "k_mod.gen_nextState _ _ _ ?msgp _") using assms transition ss by auto
      have a:"ALL p s. ?msgp p = Content s --> x s <= ii & level s = 0 & forc s = 0"
      proof (rule allI impI)+
        fix p s
        assume "?msgp p = Content s"
        from Suc.IH show "x s <= ii & level s = 0 & forc s = 0" using `?msgp p = Content s` sending_rec by (meson `Suc ii < k` lessI less_trans run)
      qed
      hence "ALL p. k_mod.forceMsgs (?msgp p) = 0" by (metis k_mod.forceMsgs.elims)
      hence "ALL q. q : k_mod.forceMsgs ` range ?msgp --> q = 0" by auto
      moreover from this have "k_mod.forceMsgs (?msgp pp) = 0" by auto
      ultimately have forc0:"k_mod.maxForce ?msgp = 0" unfolding k_mod.maxForce_def by auto
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
      moreover from forc0 have "forc ss = 0" using non_levelup transp unfolding k_mod.gen_nextState_def by auto
      ultimately show ?thesis by auto
    qed
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
and "level sq = 0"
and "level ssq = 1"
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
  from transp lev1p have "x ssp = 0"
    unfolding k_mod.gen_nextState_def k_mod.ready_level1_def by auto 
  hence val_xi:"EX sxi. rho (Suc r+i-k) xi = Active sxi & x sxi mod k = i"
    using A1[of HO xi xi "Suc r-k" i k rho ssp] assms `Suc r >= k` `k_mod.isConc k ?msgp` `~ i >= k` self_path by auto
  have transq:"k_mod.gen_nextState k q sq (HOrcvdMsgs ?A q (HO (Suc r+i) q) (rho (r+i))) ssq"
    (is "k_mod.gen_nextState _ _ _ ?msgq _") using assms transition by auto
  hence lev1q:"k_mod.ready_level1 k ?msgq sq" using assms transp
    unfolding k_mod.gen_nextState_def k_mod.ready_level1_def by (metis k_mod.ready_level2_def zero_neq_one) 
  hence "k_mod.isConc k ?msgq" unfolding k_mod.ready_level1_def by auto
  from transq lev1q have "x ssq = 0"
    unfolding k_mod.gen_nextState_def k_mod.ready_level1_def by auto 
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


lemma A4:
assumes star:"ALL p n. k_mod.path HO xi p n k"
and loop:"ALL p r. p : HO r p"
and run: "HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A _ _")
and "k > 2"
and sp:"rho r p = Active sp"
and ssp:"rho (Suc r) p = Active ssp"
and "level sp = 1"
and "level ssp = 2"
and "k_mod.maxForce (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc r) p) (rho r)) < 2" (is "k_mod.maxForce ?msgp < 2")
shows "EX s ss i. rho (r-i) xi = Active s & rho (Suc r-i) xi = Active ss & level s = 0 & level ss = 1 & x ssp <= i"
proof -
  let ?n = "LEAST nn. EX s. rho nn xi = Active s & level s > 0"
  have "r >= k" using assms A2[of HO xi k rho r p sp] by auto
  have transp:"k_mod.gen_nextState k p sp ?msgp ssp" using assms transition by auto
  hence lev2p:"k_mod.ready_level2 k ?msgp sp" using assms transp unfolding k_mod.gen_nextState_def by simp 
  hence "k_mod.isConc k ?msgp" and "x ssp = 0" using transp unfolding k_mod.ready_level2_def k_mod.gen_nextState_def by auto
  then obtain sxi where sxi:"rho (Suc r-k) xi = Active sxi" and "x sxi mod k = 0" and "k_mod.isReady ?msgp --> ready sxi"
    using assms `r >= k` A1[of HO xi p "Suc r-k" 0 k rho ssp] by auto
  hence "ready sxi" using lev2p unfolding k_mod.ready_level2_def by auto
  from this obtain sxxi where "rho (r-k) xi = Active sxxi"
    using starting[of "Suc r-k" rho xi k HO sxi] assms sxi
    unfolding k_mod.gen_initState_def by (cases "rho (r-k) xi") auto
  hence transxi:"k_mod.gen_nextState k xi sxxi (HOrcvdMsgs ?A xi (HO (Suc r-k) xi) (rho (r-k))) sxi"
    (is "k_mod.gen_nextState _ _ _ ?msgxi _") using assms transition sxi `r >= k` Suc_diff_le by auto
  hence "level sxi > 0" using `ready sxi` `x sxi mod k = 0` unfolding k_mod.gen_nextState_def by auto
  hence "?n <= Suc r-k" using sxi by (simp add:Least_le)
  have "EX s. rho (Suc r-k) xi = Active s & level s > 0" using sxi `level sxi > 0` by auto
  hence "rho ?n xi ~= Asleep" using LeastI[of "%l. EX s. rho l xi = Active s & level s > 0" "Suc r-k"] by auto


  from star obtain seq where "seq 0 = xi" and "seq k = p" and
    pat:"ALL j < k. seq j : HO (Suc r-k+Suc j) (seq (Suc j))" (is "ALL j < _. _ : ?HOseq j") unfolding k_mod.path_def by meson
  have "ALL i < k. rho (Suc r-k+i) (seq (Suc i)) ~= Asleep"
  proof (rule+)
    fix i
    assume "i < k" and "rho (Suc r-k+i) (seq (Suc i)) = Asleep"
    show "False"
    proof (cases "Suc i = k")
      case True
      thus "False" using `rho r p = Active sp` `rho (Suc r-k+i) (seq (Suc i)) = Asleep` `r >= k` `seq k = p` by fastforce
    next
      case False
      have "k_mod.path HO (seq (Suc i)) p (Suc r - k + Suc i) (k - Suc i)"
        using path_shrink[of seq xi k p HO "Suc r - k" "Suc i"] `seq k = p` `seq 0 = xi` pat `i < k` by auto
      moreover from transp lev2p have "x ssp mod k = 0" unfolding k_mod.gen_nextState_def by auto
      ultimately obtain ss where ss:"rho (Suc r-k+Suc i) (seq (Suc i)) = Active ss & x ss mod k = Suc i"
        using assms `r >= k` `k_mod.isConc k ?msgp` A1[of HO "seq (Suc i)" p "Suc r-k" "Suc i" k rho ssp] `i < k` False by auto
      hence "ss ~= k_mod.gen_initState" using `rho (Suc r-k+i) (seq (Suc i)) = Asleep` starting unfolding k_mod.gen_initState_def by auto
      thus "False" using `rho (Suc r-k+i) (seq (Suc i)) = Asleep` starting[of "r-k+i"] `k <= r` run ss
        by (metis add_Suc_right diff_Suc_1 starting)
    qed
  qed
  let ?exseq = "%l. if l <= Suc r - k - ?n then xi else seq (l - (Suc r - k - ?n))"
  have "?exseq 0 = xi & ?exseq (Suc r - ?n) = p" using `seq k = p` `?n <= Suc r - k` `k <= r` assms(4) by force 
  moreover have "ALL l < Suc r - ?n. rho (?n+l) (?exseq (Suc l)) ~= Asleep & ?exseq l : HO (Suc ?n+l) (?exseq (Suc l))"
  proof (rule allI impI)+
    fix l
    assume "l < Suc r - ?n"
    show "rho (?n+l) (?exseq (Suc l)) ~= Asleep & ?exseq l : HO (Suc ?n+l) (?exseq (Suc l))" 
    proof (cases "l < Suc r - k - ?n")
      case True
      hence "rho (?n+l) (?exseq (Suc l)) ~= Asleep" using nonAsleepAgain[of rho ?n xi] `rho ?n xi ~= Asleep` run
        unfolding HORun_def by (smt (verit, best) Suc_leI proc_state.simps(3))
      thus "rho (?n+l) (?exseq (Suc l)) ~= Asleep & ?exseq l : HO (Suc ?n+l) (?exseq (Suc l))" using loop True by auto
    next
      case False
      hence "l-(Suc r-k-?n) < k" using `l < Suc r - ?n` by linarith
      hence "seq (l-(Suc r-k-?n)) : HO (Suc r-k+(Suc l-(Suc r-k-?n))) (seq (Suc l-(Suc r-k-?n)))" using pat False Suc_diff_le by auto
      hence "?exseq l : HO (Suc ?n+l) (?exseq (Suc l))"
        by (smt (z3) False `?n <= Suc r - k` `seq 0 = xi` add_Suc_shift diff_is_0_eq' group_cancel.add1 le_add_diff_inverse nat_le_linear not_le not_less_eq)
      moreover have "rho (?n+l) (?exseq (Suc l)) ~= Asleep" using `ALL i < k. rho (Suc r-k+i) (seq (Suc i)) ~= Asleep` False
        by (smt (z3) Nat.diff_diff_right Suc_diff_le `?n <= Suc r - k` `l - (Suc r - k - ?n) < k` add_diff_inverse_nat diff_add_inverse2
        le_add2 le_add_diff_inverse less_diff_conv less_eq_Suc_le)
      ultimately show "rho (?n+l) (?exseq (Suc l)) ~= Asleep & ?exseq l : HO (Suc ?n+l) (?exseq (Suc l))" by simp
    qed
  qed
  ultimately have "active_path rho HO xi p ?n (Suc r - ?n)" using `seq k = p`
    exI[of "%seqq. seqq 0 = xi & seqq (Suc r - ?n) = p & (ALL i < Suc r - ?n. rho (?n+i) (seqq (Suc i)) ~= Asleep & seqq i : HO (?n+Suc i) (seqq (Suc i)))" ?exseq]
    unfolding active_path_def by auto


(*
  hence "k_mod.path HO xi p ?n (Suc r-?n)" using path_extend[of HO xi k p] `2 < k` star
    by (metis (no_types, lifting) Nat.add_diff_assoc `k <= r` add_Suc_right add_diff_cancel_left' less_nat_zero_code neq0_conv)
  from this obtain seq where "seq 0 = xi" and "seq (Suc r-?n) = p" and
    pat:"ALL j < Suc r-?n. seq j : HO (?n+Suc j) (seq (Suc j))" (is "ALL j < _. _ : ?HOseq j") unfolding k_mod.path_def by auto
  let ?mseq = "%j. HOrcvdMsgs ?A (seq (Suc j)) (?HOseq j) (rho r)"
  have "ALL j s. j < Suc r-?n --> rho (?n+j) (seq j) = Active s --> x s <= j"
  proof (rule allI)+
    fix j s
    show "j < Suc r-?n --> rho (?n+j) (seq j) = Active s --> x s <= j"
    proof (induction j arbitrary:s)
      case 0
      obtain sx where sx:"rho ?n xi = Active sx" and "level sx > 0" using sxi `level sxi > 0` by (smt (verit, ccfv_threshold) LeastI_ex)
      hence n_1:"rho (?n-1) xi ~= Asleep & 0 < ?n" using starting[of ?n rho xi k HO sx] run unfolding k_mod.gen_initState_def by fastforce
      from this obtain sxx where sxx:"rho (?n-1) xi = Active sxx" by (cases "rho (?n-1) xi") auto
      hence transx:"k_mod.gen_nextState k xi sxx (HOrcvdMsgs ?A xi (HO ?n xi) (rho (?n-1))) sx"
        (is "k_mod.gen_nextState _ _ _ ?msgx _") using assms transition[of rho "?n-1" xi sxx sx] sx n_1 by auto
      have "EX s. rho ?n xi = Active s & level s > 0" using `level sx > 0` and sx by blast
      hence "level sxx <= 0" using sxx n_1 Least_def
        by (smt (verit, ccfv_threshold) diff_less dual_order.strict_trans1 less_one not_le_imp_less not_less_Least zero_less_diff zero_less_one)
      hence "k_mod.ready_level1 k ?msgx sxx" using transx sxx sx `level sx > 0` unfolding k_mod.gen_nextState_def
        by (metis (no_types, lifting) bot_nat_0.extremum_uniqueI gr_implies_not_zero k_mod.ready_level2_def zero_neq_one)
      hence "x sx <= 0" using transx sxx unfolding k_mod.gen_nextState_def by auto
      thus "0 < Suc r-?n --> rho (?n+0) (seq 0) = Active s --> x s <= 0" using sx `seq 0 = xi` by fastforce
    next
      case (Suc jj)


and "k_mod.maxForce (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc r) p) (rho r)) < 2" (is "k_mod.maxForce ?msgp < 2")

lemma A5:
assumes star:"ALL p n. k_mod.path HO xi p n (k div 2)"
and loop:"ALL p r. p : HO r p"
and run: "HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A _ _")
and "k > 2"
and sp:"rho r p = Active sp"
shows "EX q ss. rho (r - x sp) q = Active ss &
  (if level sp = 0 then
    (r > x sp --> rho (r - x sp - 1) q = Asleep)
  else
    (EX s. rho (r - x sp - 1) q = Active s & Suc (level s) = level ss & level ss = level sp))"
proof (induction "x sp" arbitrary:p sp r)
  case 0
  show ?case
  proof (cases "level sp = 0")
    case True
    show ?thesis
    proof (cases "r = 0")
      case True
      thus ?thesis using sp `level sp = 0` by auto
    next
      case False
      have "rho (r - 1) p = Asleep"
      proof (rule ccontr)
        assume "rho (r - 1) p ~= Asleep"
        then obtain ssp where "rho (r - 1) p = Active ssp" by (cases "rho (r - 1) p") auto
        hence transp:"k_mod.gen_nextState k p ssp (HOrcvdMsgs ?A p (HO r p) (rho (r-1))) sp" (is "k_mod.gen_nextState _ _ _ ?msgp _")
          using transition assms False by (metis "0.hyps" One_nat_def Suc_diff_Suc diff_zero neq0_conv)
        hence "k_mod.ready_level1 k ?msgp ssp | k_mod.ready_level2 k ?msgp ssp" using `0 = x sp` unfolding k_mod.gen_nextState_def by auto
        thus "False" using transp `level sp = 0` unfolding k_mod.ready_level1_def k_mod.ready_level2_def k_mod.gen_nextState_def by auto
      qed
      thus ?thesis using sp "0.hyps" True by auto
    qed
  next
    case False
    have "r > 0 & rho (r - 1) p ~= Asleep" using starting[of r] assms False
      unfolding k_mod.gen_initState_def by (metis locState.select_convs(5))
    then obtain ssp where ssp:"rho (r - 1) p = Active ssp" by (cases "rho (r - 1) p") auto
    hence transp:"k_mod.gen_nextState k p ssp (HOrcvdMsgs ?A p (HO r p) (rho (r-1))) sp" (is "k_mod.gen_nextState _ _ _ ?msgp _")
      using transition assms False by (metis One_nat_def Suc_diff_Suc `r > 0 & rho (r - 1) p ~= Asleep` diff_zero)
    hence "k_mod.ready_level1 k ?msgp ssp | k_mod.ready_level2 k ?msgp ssp" using `0 = x sp` unfolding k_mod.gen_nextState_def by auto
    hence "Suc (level ssp) = level sp" by (smt One_nat_def Suc_1 k_mod.gen_nextState_def k_mod.ready_level1_def k_mod.ready_level2_def transp)
    hence "EX ss. rho (r-1) p = Active ss & Suc (level ss) = level sp" using ssp by auto
    hence "if level sp = 0 then (r > x sp --> rho (r - x sp - 1) p = Asleep)
      else (EX ssp. rho (r - 1) p = Active ssp & Suc (level ssp) = level sp & level sp = level sp)"
      using `level sp ~= 0` ssp by auto
    hence "rho r p = Active sp & (if level sp = 0 then (r > x sp --> rho (r - x sp - 1) p = Asleep)
      else (EX ssp. rho (r - 1) p = Active ssp & Suc (level ssp) = level sp & level sp = level sp))" using sp by auto
    thus ?thesis using "0.hyps" by auto
  qed
next
  case (Suc v)
  hence "r > 0 & rho (r - 1) p ~= Asleep" using starting[of r] assms 
    unfolding k_mod.gen_initState_def by (metis (no_types, lifting) less_Suc_eq_0_disj less_numeral_extra(3) locState.select_convs(1))
  then obtain ssp where ssp:"rho (r - 1) p = Active ssp" by (cases "rho (r - 1) p") auto
  hence transp:"k_mod.gen_nextState k p ssp (HOrcvdMsgs ?A p (HO r p) (rho (r-1))) sp" (is "k_mod.gen_nextState _ _ _ ?msgp _")
    using transition assms by (metis One_nat_def Suc_diff_Suc `r > 0 & rho (r - 1) p ~= Asleep` diff_zero)
  hence "x sp = Suc (k_mod.minMsgs ?msgp)" and spmaxf:"forc sp = k_mod.maxForce ?msgp" using Suc unfolding k_mod.gen_nextState_def by auto
  hence exLeast:"EX v sq q. ?msgp q = Content sq & forc sq =  k_mod.maxForce ?msgp & x sq = v" (is "EX v q sq. ?getLeast v q sq")
  proof (cases "k_mod.maxForce ?msgp = 0")
    case True
    moreover from loop have "?msgp p = Content ssp"
      using k_mod.gen_HOMachine_def k_mod.gen_sendMsg_def ssp unfolding HOrcvdMsgs_def by force
    ultimately have "forc ssp = 0" using Max_ge[of _ "k_mod.forceMsgs (?msgp p)"] `?msgp p = Content ssp`
      unfolding k_mod.maxForce_def by (metis finite_UNIV finite_imageI image_eqI k_mod.forceMsgs.simps(1) le_zero_eq range_eqI)
    thus "EX v sq q. ?msgp q = Content sq & forc sq =  k_mod.maxForce ?msgp & x sq = v" using True `?msgp p = Content ssp` by auto
  next
    case False
    have "k_mod.maxForce ?msgp : k_mod.forceMsgs ` range ?msgp" using Max_in unfolding k_mod.maxForce_def by auto
    then obtain q where q:"k_mod.maxForce ?msgp = k_mod.forceMsgs (?msgp q)" by auto
    moreover have "EX sq. ?msgp q = Content sq" unfolding k_mod.maxForce_def by (metis False q k_mod.forceMsgs.elims)
    ultimately have "EX sq. ?msgp q = Content sq & k_mod.maxForce ?msgp = k_mod.forceMsgs (?msgp q)" by auto
    thus "EX v sq q. ?msgp q = Content sq & forc sq =  k_mod.maxForce ?msgp & x sq = v" using k_mod.forceMsgs.elims False by metis
  qed
  from exLeast have "EX q sq. ?getLeast (k_mod.minMsgs ?msgp) q sq"
    using LeastI[of "%v. EX q sq. ?getLeast v q sq"] `EX v q sq. ?getLeast v q sq` unfolding k_mod.minMsgs_def by blast
  then obtain q sq where "?msgp q = Content sq" and "Suc (x sq) = x sp" and "forc sq = forc sp"
    using spmaxf `x sp = Suc (k_mod.minMsgs ?msgp)` by auto
  thus ?thesis using Suc.hyps Suc.prems by auto





qed






end *)