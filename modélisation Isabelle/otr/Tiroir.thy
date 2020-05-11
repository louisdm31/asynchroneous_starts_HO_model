theory Tiroir
  imports Main
begin

lemma tiroir: assumes fini:"finite {v. E v}" shows "finite {f v | v. E v}"
proof -
  from assms have "finite (f ` {v. E v})" .. (* finite_imageI *)
  thus ?thesis by (simp add: setcompr_eq_image) 
qed

lemma tiroir2: assumes inject:"\<forall>v1 v2. f v1 = f v2 \<longrightarrow> v1 = v2"
  shows "finite {f v | v. E v} \<longrightarrow> finite {v. E v}"
proof
  assume "finite {f v | v. E v}"
  hence "finite (f ` {v . E v})" by (simp add: image_Collect) 
  moreover
  from inject have "inj_on f {v . E v}" by (simp add: inj_onI) 
  ultimately
  show "finite {v . E v}" by (rule finite_imageD)
qed

end