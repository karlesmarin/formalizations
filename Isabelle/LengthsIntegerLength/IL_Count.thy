(*  Title:      IL_Count.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Integer length formula: the least number of integer squares is n + P + (z mod 2) for the graph model (lengths paper)
*)

theory IL_Count
  imports IL_Model
begin

section \<open>Counting\<close>

lemma card_Vc: "card (Vc cs) = (\<Sum>c\<in>{..<length cs}. snd (cs ! c))"
  unfolding Vc_def by (subst card_SigmaI) simp_all

lemma card_hn:
  assumes "1 \<le> m"
  shows "card {k \<in> {..<m}. hn cy m k} = (if cy then m else m - 1)"
proof (cases cy)
  case True
  hence "{k \<in> {..<m}. hn cy m k} = {..<m}" unfolding hn_def by auto
  thus ?thesis using True by simp
next
  case False
  have "{k \<in> {..<m}. hn cy m k} = {..<m - 1}" unfolding hn_def using False by auto
  thus ?thesis using False by simp
qed

lemma nnz_T0:
  assumes ok: "okc cs"
  shows "nnz (T0 cs) = (\<Sum>c\<in>{..<length cs}. if fst (cs ! c) then snd (cs ! c) else snd (cs ! c) - 1)"
proof -
  let ?D = "SIGMA c:{..<length cs}. {k \<in> {..<snd (cs ! c)}. hn (fst (cs ! c)) (snd (cs ! c)) k}"
  let ?g = "\<lambda>x. (x, (fst x, nxt (fst (cs ! fst x)) (snd (cs ! fst x)) (snd x)))"
  have "{p. T0 cs (fst p) (snd p) \<noteq> 0} = ?g ` ?D"
  proof (rule set_eqI)
    fix p :: "(nat \<times> nat) \<times> (nat \<times> nat)"
    obtain a b where p: "p = (a, b)" by (cases p) auto
    show "p \<in> {p. T0 cs (fst p) (snd p) \<noteq> 0} \<longleftrightarrow> p \<in> ?g ` ?D"
    proof
      assume "p \<in> {p. T0 cs (fst p) (snd p) \<noteq> 0}"
      hence x: "T0 cs a b \<noteq> 0" using p by simp
      hence x': "fst a = fst b" "fst a < length cs" "hn (fst (cs ! fst a)) (snd (cs ! fst a)) (snd a)"
        "snd b = nxt (fst (cs ! fst a)) (snd (cs ! fst a)) (snd a)" unfolding T0_nz by auto
      have aD: "a \<in> ?D" using x'(2,3) unfolding hn_def by (cases a) simp
      have "b = (fst a, nxt (fst (cs ! fst a)) (snd (cs ! fst a)) (snd a))"
        using x'(1,4) by (simp add: prod_eq_iff)
      thus "p \<in> ?g ` ?D" using aD p by (auto intro: rev_image_eqI[of a])
    next
      assume "p \<in> ?g ` ?D"
      then obtain x where xD: "x \<in> ?D" and px: "p = ?g x" by blast
      have "T0 cs x (fst x, nxt (fst (cs ! fst x)) (snd (cs ! fst x)) (snd x)) \<noteq> 0"
        using xD unfolding T0_nz by (cases x) auto
      thus "p \<in> {p. T0 cs (fst p) (snd p) \<noteq> 0}" using px by simp
    qed
  qed
  hence "nnz (T0 cs) = card (?g ` ?D)" unfolding nnz_def by simp
  also have "\<dots> = card ?D" by (rule card_image) (auto intro: inj_onI)
  also have "\<dots> = (\<Sum>c\<in>{..<length cs}. card {k \<in> {..<snd (cs ! c)}. hn (fst (cs ! c)) (snd (cs ! c)) k})"
    by (subst card_SigmaI) simp_all
  also have "\<dots> = (\<Sum>c\<in>{..<length cs}. if fst (cs ! c) then snd (cs ! c) else snd (cs ! c) - 1)"
  proof (rule sum.cong[OF refl])
    fix c assume "c \<in> {..<length cs}"
    hence lt: "c < length cs" by simp
    show "card {k \<in> {..<snd (cs ! c)}. hn (fst (cs ! c)) (snd (cs ! c)) k}
        = (if fst (cs ! c) then snd (cs ! c) else snd (cs ! c) - 1)"
      by (rule card_hn[OF okc_pos[OF ok lt]])
  qed
  finally show ?thesis .
qed

lemma n_split:
  assumes ok: "okc cs"
  shows "nnz (T0 cs) + card (Cn cs) = card (Vc cs)"
proof -
  have "card (Cn cs) = (\<Sum>c\<in>{..<length cs}. if \<not> fst (cs ! c) then (1::nat) else 0)"
    unfolding Cn_def by (rule sum_ind[symmetric]) simp
  hence "nnz (T0 cs) + card (Cn cs) = (\<Sum>c\<in>{..<length cs}.
      (if fst (cs ! c) then snd (cs ! c) else snd (cs ! c) - 1) + (if \<not> fst (cs ! c) then 1 else 0))"
    unfolding nnz_T0[OF ok] by (simp add: sum.distrib)
  also have "\<dots> = (\<Sum>c\<in>{..<length cs}. snd (cs ! c))"
  proof (rule sum.cong[OF refl])
    fix c assume "c \<in> {..<length cs}"
    hence "c < length cs" by simp
    from nat_ite[OF okc_pos[OF ok this], of "fst (cs ! c)"]
    show "(if fst (cs ! c) then snd (cs ! c) else snd (cs ! c) - 1) + (if \<not> fst (cs ! c) then 1 else 0)
        = snd (cs ! c)" .
  qed
  finally show ?thesis unfolding card_Vc .
qed

lemma Cn_split:
  assumes ok: "okc cs"
  shows "card (Cn cs) = card (Cp cs) + card (Cz cs)"
proof -
  have "Cn cs = Cp cs \<union> Cz cs"
  proof (rule set_eqI)
    fix c show "c \<in> Cn cs \<longleftrightarrow> c \<in> Cp cs \<union> Cz cs"
    proof (cases "c < length cs")
      case True
      note lt = True
      have p: "1 \<le> snd (cs ! c)" by (rule okc_pos[OF ok lt])
      show ?thesis
      proof (cases "snd (cs ! c) = 1")
        case True
        thus ?thesis using lt unfolding Cn_def Cp_def Cz_def by auto
      next
        case False
        have "2 \<le> snd (cs ! c)" by (rule nat_ge2[OF p False])
        thus ?thesis using lt False unfolding Cn_def Cp_def Cz_def by auto
      qed
    next
      case False
      thus ?thesis unfolding Cn_def Cp_def Cz_def by auto
    qed
  qed
  moreover have "Cp cs \<inter> Cz cs = {}" unfolding Cp_def Cz_def by auto
  moreover have "finite (Cp cs)" "finite (Cz cs)" unfolding Cp_def Cz_def by simp_all
  ultimately show ?thesis by (simp add: card_Un_disjoint)
qed

end
