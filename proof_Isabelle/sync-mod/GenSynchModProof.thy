theory GenSynchModProof
imports "../HOModel" GenSynchMod
begin

lemma sending:
assumes s:"rho r p = Active s"
  and run: "HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A _ _")
shows "ALL q. HOrcvdMsgs (k_mod.gen_HOMachine k) q (HO (Suc r) q) (rho r) p
    = (if p : HO (Suc r) q then Content s else Void)"
using HOrcvdMsgs_def[of ?A] s by (simp add: k_mod.gen_HOMachine_def k_mod.gen_sendMsg_def)

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
assumes star:"ALL p n. k_mod.path HO xi p n (k div 2)"
and loop:"ALL p r. p : HO r p"
and run: "HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A _ _")
and "rho (t+k) p = Active sp"
and "k_mod.isConc k (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+k) p) (rho (t+k-1)))" (is "k_mod.isConc k ?msgs")
and "x sp mod k = 0"
and "k > 2"
shows "ALL i <= k div 2. EX sxi. rho (t+i) xi = Active sxi & x sxi mod k= i &
  (k_mod.isReady (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+k) p) (rho (t+k-1))) --> ready sxi)"
proof
  fix i
  show "i <= k div 2 --> (EX sxi. rho (t+i) xi = Active sxi & x sxi mod k = i & (k_mod.isReady ?msgs --> ready sxi))"
  proof
    assume "i <= k div 2"
    moreover have "k >= (k div 2) * 2" using `k > 2` using div_times_less_eq_dividend by blast 
    ultimately have "k - i >= k div 2" by auto
    hence "k div 2 + (k-i-k div 2) = k - i" using le_add_diff_inverse by blast 
    hence "k_mod.path HO xi p (t+i) (k-i)"
      using path_extend[of HO xi "k div 2" p] star `k > 2`
      by (metis div_positive less_imp_le_nat zero_less_numeral)
    from this obtain seq where "seq 0 = xi" and "seq (k-i) = p" and
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
    moreover from `2 < k` `k - i >= k div 2 ` have "k - i > 0"  by linarith
    hence "k-i-(k-i-1) = 1" and "t+k-(k-i-1) = t+i+1" and "k-(k-i-1) = i+1" by auto
    ultimately have seq1:"let msgs = HOrcvdMsgs ?A (seq 1) (HO (t+i+1) (seq 1)) (rho (t+i)) in EX ss. 
       rho (t+i+1) (seq 1) = Active ss & x ss mod k = (i+1) mod k & k_mod.isConc k msgs &
       (k_mod.isReady ?msgs --> k_mod.isReady msgs)" using `2 < k` allE[of ?recurr_path "k-i-1" "?recurr_path (k-i-1)"] by auto
    let ?msgxi = "HOrcvdMsgs ?A (seq 1) (HO (t+i+1) (seq 1)) (rho (t+i))"
    have seq1link:"xi : HO (t+i+1) (seq 1)" using pat `seq 0 = xi` `k-i > 0` by fastforce
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
    have "x s1 mod k ~= 0" using suci `i <= k div 2` `2 < k` by simp
    hence "x s1 = Suc (k_mod.minMsgs ?msgxi)" using trans1 concready ss1 unfolding k_mod.gen_nextState_def k_mod.minMsgs_def k_mod.isConc_def by auto
    hence "x s1 mod k = Suc (x sxi) mod k" using concready ss1 unfolding k_mod.gen_nextState_def k_mod.minMsgs_def k_mod.isConc_def
      by (metis (no_types, lifting) `?msgxi xi = Content sxi` message.distinct(3) message.inject mod_Suc_eq)
    hence "x sxi mod k = i" using suci `i <= k div 2`
      by (metis Suc_eq_plus1 `0 < k - i` `x s1 mod k ~= 0` mod_Suc mod_less nat.inject zero_less_diff)
    thus "EX sxi. rho (t+i) xi = Active sxi & x sxi mod k = i & (k_mod.isReady ?msgs --> ready sxi)" using sxi `k_mod.isReady ?msgs --> ready sxi` by auto
  qed
qed

lemma A3:
assumes star:"ALL p n. k_mod.path HO xi p n (k div 2)"
and loop:"ALL p r. p : HO r p"
and run: "HORun (k_mod.gen_HOMachine k) rho HO" (is "HORun ?A _ _")
and "k > 2"
and "rho r p = Active sp"
and "rho (Suc r) p = Active ssp"
and "level sp = 0"
and "level ssp = 1"
and "rho (r+i) q = Active sq"
and "rho (r+Suc i) q = Active ssq"
and "level sq = 0"
and "level ssq = 1"
shows "i > k div 2"
proof (rule ccontr)
  assume "i <= k div 2"
  have transp:"k_mod.gen_nextState k p sp (HOrcvdMsgs ?A p (HO (Suc r) p) (rho r)) ssp"
    (is "k_mod.gen_nextState _ _ _ ?msgp _") using assms transition by auto
  hence "k_mod.ready_level1 k ?msgp sp" using assms
    unfolding k_mod.gen_nextState_def k_mod.ready_level1_def by (metis k_mod.ready_level2_def zero_neq_one)
  have transq:"k_mod.gen_nextState k q sq (HOrcvdMsgs ?A q (HO (Suc r+i) q) (rho (r+i))) ssq" using assms transition by auto





end