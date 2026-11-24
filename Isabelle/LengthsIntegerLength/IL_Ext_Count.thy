(*  Title:      IL_Ext_Count.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Integer length formula: the least number of integer squares is n + P + (z mod 2) for the graph model (lengths paper)
*)

theory IL_Ext_Count
  imports IL_Ext_Rep
begin

context lgraph
begin

lemma ext_nnz:
  assumes r: "rep V E T" and i: "i \<in> frs T" and j: "j \<in> frs T" and ne: "i \<noteq> j"
  shows "nnz (ext T i j) = nnz T + 2"
proof -
  have i0: "\<And>k. T i k = 0" and i1: "\<And>k. T k i = 0" using i unfolding frs_def by auto
  have j0: "\<And>k. T j k = 0" and j1: "\<And>k. T k j = 0" using j unfolding frs_def by auto
  note iff = ext_nz_iff[OF ne i0 i1 j0 j1]
  let ?S = "{p. T (fst p) (snd p) \<noteq> 0}"
  let ?P = "{(i, j), (j, i)}"
  have eq: "{p. ext T i j (fst p) (snd p) \<noteq> 0} = ?S \<union> ?P"
  proof (rule set_eqI)
    fix x :: "'v \<times> 'v"
    obtain a b where x: "x = (a, b)" by (cases x) auto
    have l: "x \<in> {p. ext T i j (fst p) (snd p) \<noteq> 0} \<longleftrightarrow> ext T i j a b \<noteq> 0" unfolding x by simp
    have m: "x \<in> ?S \<union> ?P \<longleftrightarrow> T a b \<noteq> 0 \<or> (a = i \<and> b = j) \<or> (a = j \<and> b = i)" unfolding x by auto
    show "x \<in> {p. ext T i j (fst p) (snd p) \<noteq> 0} \<longleftrightarrow> x \<in> ?S \<union> ?P"
      unfolding l m by (rule iff)
  qed
  have fT: "finite ?S" by (rule fin_supp[OF r])
  have fP: "finite ?P" by simp
  have dis: "?S \<inter> ?P = {}"
  proof (rule equals0I)
    fix p assume h: "p \<in> ?S \<inter> ?P"
    hence t: "T (fst p) (snd p) \<noteq> 0" by simp
    have d: "p = (i, j) \<or> p = (j, i)" using h by simp
    from d show False
    proof
      assume "p = (i, j)"
      hence "T (fst p) (snd p) = 0" using i0 by simp
      thus False using t by (rule notE[rotated])
    next
      assume "p = (j, i)"
      hence "T (fst p) (snd p) = 0" using j0 by simp
      thus False using t by (rule notE[rotated])
    qed
  qed
  have c2: "card ?P = 2" using ne by simp
  have "nnz (ext T i j) = card (?S \<union> ?P)" unfolding nnz_def eq ..
  also have "\<dots> = card ?S + card ?P" by (rule card_Un_disjoint[OF fT fP dis])
  also have "\<dots> = nnz T + 2" unfolding c2 nnz_def ..
  finally show ?thesis .
qed

lemma ext_frs:
  assumes r: "rep V E T" and i: "i \<in> frs T" and j: "j \<in> frs T" and ne: "i \<noteq> j"
  shows "frs (ext T i j) = frs T - {i, j}"
proof (rule set_eqI)
  fix a
  show "a \<in> frs (ext T i j) \<longleftrightarrow> a \<in> frs T - {i, j}"
  proof
    assume h: "a \<in> frs (ext T i j)"
    hence aI: "a \<in> isoset" and h1: "\<And>k. ext T i j a k = 0" and h2: "\<And>k. ext T i j k a = 0"
      unfolding frs_def by auto
    have ai: "a \<noteq> i"
    proof
      assume e: "a = i"
      have c: "a = i \<and> j = j" using e by blast
      have "ext T i j a j = 1" by (rule ext_1[OF c])
      thus False using h1[of j] by simp
    qed
    have aj: "a \<noteq> j"
    proof
      assume e: "a = j"
      have c1: "\<not> (a = i \<and> i = j)" using ne by blast
      have c2: "a = j \<and> i = i" using e by blast
      have "ext T i j a i = -1" by (rule ext_2[OF c1 c2])
      thus False using h1[of i] by simp
    qed
    have t1: "T a k = 0" for k
    proof -
      have c1: "\<not> (a = i \<and> k = j)" using ai by blast
      have c2: "\<not> (a = j \<and> k = i)" using aj by blast
      have "T a k = ext T i j a k" by (rule ext_3[OF c1 c2, symmetric])
      also have "\<dots> = 0" by (rule h1)
      finally show "T a k = 0" .
    qed
    have t2: "T k a = 0" for k
    proof -
      have c1: "\<not> (k = i \<and> a = j)" using aj by blast
      have c2: "\<not> (k = j \<and> a = i)" using ai by blast
      have "T k a = ext T i j k a" by (rule ext_3[OF c1 c2, symmetric])
      also have "\<dots> = 0" by (rule h2)
      finally show "T k a = 0" .
    qed
    have "a \<in> frs T" unfolding frs_def using aI t1 t2 by blast
    thus "a \<in> frs T - {i, j}" using ai aj by blast
  next
    assume h: "a \<in> frs T - {i, j}"
    hence aF: "a \<in> frs T" and ai: "a \<noteq> i" and aj: "a \<noteq> j" by auto
    hence aI: "a \<in> isoset" and t1: "\<And>k. T a k = 0" and t2: "\<And>k. T k a = 0"
      unfolding frs_def by auto
    have u1: "ext T i j a k = 0" for k
    proof -
      have c1: "\<not> (a = i \<and> k = j)" using ai by blast
      have c2: "\<not> (a = j \<and> k = i)" using aj by blast
      have "ext T i j a k = T a k" by (rule ext_3[OF c1 c2])
      also have "\<dots> = 0" by (rule t1)
      finally show "ext T i j a k = 0" .
    qed
    have u2: "ext T i j k a = 0" for k
    proof -
      have c1: "\<not> (k = i \<and> a = j)" using aj by blast
      have c2: "\<not> (k = j \<and> a = i)" using ai by blast
      have "ext T i j k a = T k a" by (rule ext_3[OF c1 c2])
      also have "\<dots> = 0" by (rule t2)
      finally show "ext T i j k a = 0" .
    qed
    show "a \<in> frs (ext T i j)" unfolding frs_def using aI u1 u2 by blast
  qed
qed

end

end
