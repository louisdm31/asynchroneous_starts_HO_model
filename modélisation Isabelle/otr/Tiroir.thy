theory Tiroir
  imports Main
begin

lemma tiroir: assumes fini:"finite {v. E v}" shows "finite {f v | v. E v}"
proof -
  have "card {v. E v} \<ge> 0" (is "?cardens \<ge> 0") by auto
  thus "finite {f v | v. E v}"
  proof (induction ?cardens)
    case 0
    hence "{v. E v} = {}" using fini by auto
    hence "{f v | v. E v} = {}" by auto
    thus "finite {f v | v. E v}"  by auto
  next
    case (Suc crd)
    hence "card {v. E v} > 0" by auto
    hence "\<exists>vv. vv \<in> {v. E v}"
      by (metis less_irrefl sum_bounded_above_strict sum_constant)
    then obtain vv where vvin:"vv \<in> {v. E v}" by auto
    have "\<forall>v. E v = (\<lambda>t. if t = vv then True else E t) v" using vvin by simp
    hence "{v. E v} = {v. (\<lambda>t. if t = vv then True else E t) v}" by blast
    hence dehorsvv:"{v. E v} = {v. (\<lambda>t. if t = vv then False else E t) v} \<union> {vv}" by auto
    hence "finite {v. (\<lambda>t. if t = vv then False else E t) v}" using fini by auto
    hence "finite {f v | v. (\<lambda>t. if t = vv then False else E t) v}" by auto
    hence "finite ({f v | v. (\<lambda>t. if t = vv then False else E t) v} \<union> {f vv})" by auto
    moreover have "{f v | v. E v} = {f v | v. (\<lambda>t. if t = vv then False else E t) v} \<union> {f vv}"
      using vvin by auto
    ultimately show "finite {f v | v. E v}" by simp
  qed
qed


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

end