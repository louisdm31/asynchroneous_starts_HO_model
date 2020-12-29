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

lemma path_conc:
assumes "rho (Suc r) p = Active sp"
and "(x sp mod k > 0 & conc sp) |
  k_mod.isConc k (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (Suc r) p) (rho r))"
  (is "_ | k_mod.isConc k ?msgs")
and run: "HORun (k_mod.gen_HOMachine k) rho HO" 
and loop:"ALL p r. p : HO r p"
and "q : HO (Suc r) p"
and "k > 2"
shows "EX s. rho r q = Active s & conc s & (Suc (x s)) mod k = x sp mod k & (ready sp --> ready s)"
proof -
  have "~ rho r p = Asleep"
  proof
    assume "rho r p = Asleep"
    hence "sp = k_mod.gen_initState" using starting[of "Suc r" rho p k HO sp] assms by auto
    have "conc sp | k_mod.isConc k ?msgs" using assms by auto
    thus "False"
    proof 
      assume "conc sp"
      thus "False" using `sp = k_mod.gen_initState` unfolding k_mod.gen_initState_def by simp
    next
      assume "k_mod.isConc k ?msgs"
      hence "?msgs p ~= Bot" unfolding k_mod.isConc_def by (metis message.distinct(1) message.distinct(5))
      thus "False" using loop `rho r p = Asleep` unfolding HOrcvdMsgs_def by auto
    qed
  qed
  then obtain ssp where "rho r p = Active ssp" by (cases "rho r p") auto
  hence trans:"k_mod.gen_nextState k p ssp ?msgs sp"
    using transition[of rho r p ssp sp k HO] assms by auto
  show ?thesis
  proof (cases "rho r q")
    case Asleep
    hence "?msgs q = Bot" 
      unfolding HOrcvdMsgs_def using assms by auto
    hence "~ k_mod.isConc k ?msgs" unfolding k_mod.isConc_def by (metis message.distinct(1) message.distinct(5))
    hence "False" using assms trans k_mod.gen_nextState_def by auto
    thus ?thesis by auto
  next
    case (Active sq)
    from sending have "?msgs q = Content sq" using assms `rho r q = Active sq` by auto 
    moreover from trans assms k_mod.gen_nextState_def have coc:"k_mod.isConc k ?msgs" by auto
    ultimately have "x sq mod k = k_mod.minMsgs ?msgs mod k"
      unfolding k_mod.isConc_def by (metis message.distinct(3) message.inject)
    moreover from trans assms k_mod.gen_nextState_def have "x sp = Suc (k_mod.minMsgs ?msgs)" by auto
    ultimately have "Suc (x sq) mod k = x sp mod k" by (metis mod_Suc_eq)
    moreover from coc have "conc sq" unfolding k_mod.isConc_def
      by (metis `?msgs q = Content sq` message.distinct(3) message.inject)
    moreover from trans assms k_mod.gen_nextState_def have "ready sp --> k_mod.isReady ?msgs" by auto 
    hence "ready sp --> ready sq" unfolding k_mod.isReady_def using `?msgs q = Content sq` by auto 
    ultimately show ?thesis using `rho r q = Active sq` by auto
  qed
qed

lemma A1:
assumes star:"ALL p n. k_mod.path HO xi p n (k div 2)"
and loop:"ALL p r. p : HO r p"
and run: "HORun (k_mod.gen_HOMachine k) rho HO" 
and "rho (t+k) p = Active sp"
and "k_mod.isConc k (HOrcvdMsgs (k_mod.gen_HOMachine k) p (HO (t+k) p) (rho (t+k-1)))" (is "k_mod.isConc k ?msgs")
and "x sp mod k = 0"
and "k > 2"
shows "ALL i <= k div 2. EX sxi. rho (t+i) xi = Active sxi & x sxi = i & (ready sp --> ready sxi)"
proof
  fix i
  show "i <= k div 2 --> (EX sxi. rho (t+i) xi = Active sxi & x sxi = i & (ready sp --> ready sxi))"
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
    have "ALL j <= k-i. EX s. rho (t+k-j) (seq (k-i-j)) = Active s &
      conc s & x s mod k = (k - j) mod k & (ready sp --> ready s)"
    proof
      fix j
      show "j <= k-i --> (EX s. rho (t+k-j) (seq (k-i-j)) = Active s &
        conc s & x s mod k = (k - j) mod k & (ready sp --> ready s))"
      proof (induction j)
        case 0
        have "conc sp"
        proof (cases "rho (t+k-1) p")
          case Asleep
          hence "?msgs p = Bot" unfolding HOrcvdMsgs_def using assms by auto
          hence "False" using `k_mod.isConc k ?msgs` unfolding k_mod.isConc_def
            by (metis message.distinct(1) message.distinct(5))
          thus "conc sp" by auto
        next
          case (Active ssp)
          hence "k_mod.gen_nextState k p ssp ?msgs sp"
            using assms transition[of rho "t+k-1" p ssp sp] by auto
          thus "conc sp" unfolding k_mod.gen_nextState_def using assms by auto
        qed
        thus "0 <= k-i --> (EX s. rho (t+k-0) (seq (k-i-0)) = Active s &
          conc s & x s mod k = (k - 0) mod k & (ready sp --> ready s))"
          using assms by (simp add:`seq (k-i) = p`)
      next
        case (Suc j)
        show ?case
        proof
          assume "Suc j <= k-i"
          hence "k-i-Suc j < k-i" and "t+i+Suc(k-i-Suc j) = t+k-j" and ineg:"Suc (k-i-Suc j) = k-i-j" and
          "t+k >= Suc j" and "Suc (t+k-Suc j) = t+k-j" and "Suc (k - Suc(i+j)) = k-i-j" by auto
          from this pat have "seq (k-i-Suc j) : HO (t+k-j) (seq (k-i-j))" by auto

          moreover from Suc.IH obtain ss where "rho (t+k-j) (seq (k-i-j)) = Active ss"
            and "conc ss" and "x ss mod k = (k-j) mod k" and "ready sp --> ready ss"
            using `Suc j <= k-i` by auto

          have "0 < x ss mod k" using `Suc j <= k-i` `x ss mod k = (k-j) mod k` by auto
          from assms pat this
            obtain s where "rho (t+k-Suc j) (seq (k-i-Suc j)) = Active s"
            using path_conc[of rho "t-k-Suc j" "seq (t-k-j)" ss k HO "seq (k-i-Suc j)"]
            by auto
          from `Suc j <= k-i` have "(k-j) mod k > 0" by auto


          moreover from this have "ALL s. Suc (x s) mod k = x ss mod k --> x s mod k = (k - Suc j) mod k"
            using `Suc j <= k-i` by (smt Suc_diff_le add_leD2 add_left_cancel diff_diff_cancel
            diff_le_self le_add_diff_inverse2 less_numeral_extra(3) mod_Suc plus_1_eq_Suc zero_less_Suc)


          ultimately show "EX s. rho (t+k-Suc j) (seq (k-i-Suc j)) = Active s &
            conc s & x s mod k = (k - Suc j) mod k & (ready sp --> ready s)"
            using path_conc[of rho "t-k-Suc j" "seq (t-k-j)" ss k HO "seq (k-i-Suc j)"] assms ineg by 
          proof
          have "seq (k-i-j) : HO "
    show "EX sxi. rho (t+i) xi = Active sxi & x sxi = i"


lemma leq_path:
assumes "rho r p = Active sp"
and "rho (r+i) q = Active sq"
and "forc sp = forc sq"
and path:"k_mod.path HO p q r i"
and run: "HORun (k_mod.gen_HOMachine k) rho HO" 
shows "x sq <= x sp + i"
proof -
  from path obtain seq where "seq 0 = p" and "seq i = q" and
    "ALL j < i. seq j : HO (r+j) (seq (Suc j))" unfolding k_mod.path_def by auto
  have "rho (r+i) q = Active sq ==> seq i = q ==>
    ALL j < i. seq j : HO (r+j) (seq (Suc j)) ==> x sq <= x sp + i"
  proof (induction i arbitrary:seq)
    case 0
    hence "p = q" and "rho r q = Active sq" using path `seq 0 = p` by auto
    hence "sp = sq" using assms by auto
    thus "x sq <= x sp + 0" by auto
  next
    case (Suc i)
    from Suc.IH have 
    thus ?case by sorry
  qed
  thus "x sq <= x sp + i" using assms by auto
qed


end