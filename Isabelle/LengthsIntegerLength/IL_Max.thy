(*  Title:      IL_Max.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Integer length formula: the least number of integer squares is n + P + (z mod 2) for the graph model (lengths paper)
*)

theory IL_Max
  imports IL_Ext_Count
begin

context lgraph
begin

lemma extend_many:
  "rep V E T \<Longrightarrow> 2 * k \<le> card (frs T) \<Longrightarrow> \<exists>T'. rep V E T' \<and> nnz T' = nnz T + 2 * k"
proof (induction k arbitrary: T)
  case 0
  thus ?case by (intro exI[of _ T]) simp
next
  case (Suc k)
  have fF: "finite (frs T)" by (rule finite_subset[OF _ fin_isoset]) (auto simp: frs_def)
  have c: "2 * Suc k \<le> card (frs T)" using Suc.prems(2) .
  have "frs T \<noteq> {}"
  proof
    assume "frs T = {}"
    hence "card (frs T) = 0" by simp
    thus False using c by arith
  qed
  then obtain i where i: "i \<in> frs T" by blast
  have "frs T - {i} \<noteq> {}"
  proof
    assume "frs T - {i} = {}"
    hence "card (frs T - {i}) = 0" by (simp only: card.empty)
    moreover have "card (frs T - {i}) = card (frs T) - 1" by (rule card_Diff_singleton[OF i])
    ultimately show False by (rule nat_c[OF _ _ c])
  qed
  then obtain j where j0: "j \<in> frs T - {i}" by blast
  hence j: "j \<in> frs T" and ne: "i \<noteq> j" by auto
  let ?T1 = "ext T i j"
  have r1: "rep V E ?T1" by (rule ext_rep[OF Suc.prems(1) i j ne])
  have n1: "nnz ?T1 = nnz T + 2" by (rule ext_nnz[OF Suc.prems(1) i j ne])
  have f1: "frs ?T1 = frs T - {i, j}" by (rule ext_frs[OF Suc.prems(1) i j ne])
  have "card (frs T - {i, j}) = card (frs T) - card {i, j}"
    by (rule card_Diff_subset) (use i j in auto)
  moreover have "card {i, j} = 2" using ne by simp
  ultimately have "card (frs ?T1) = card (frs T) - 2" using f1 by simp
  hence "2 * k \<le> card (frs ?T1)" using c by arith
  from Suc.IH[OF r1 this] obtain T' where "rep V E T'" "nnz T' = nnz ?T1 + 2 * k" by blast
  thus ?case using n1 by (intro exI[of _ T']) auto
qed

theorem max_nnz:
  assumes r0: "rep V E T0" and sup: "\<And>i j. T0 i j \<noteq> 0 \<Longrightarrow> E i j"
  shows "\<exists>T. rep V E T \<and> nnz T = nnz T0 + 2 * (nz div 2)"
    and "\<And>T. rep V E T \<Longrightarrow> nnz T \<le> nnz T0 + 2 * (nz div 2)"
proof -
  have fr: "frs T0 = isoset"
  proof (rule set_eqI)
    fix i show "i \<in> frs T0 \<longleftrightarrow> i \<in> isoset"
    proof
      assume "i \<in> frs T0" thus "i \<in> isoset" unfolding frs_def by simp
    next
      assume iI: "i \<in> isoset"
      have "\<And>k. T0 i k = 0" using sup iI unfolding isoset_def by auto
      moreover have "\<And>k. T0 k i = 0"
      proof -
        fix k show "T0 k i = 0"
        proof (rule ccontr)
          assume "T0 k i \<noteq> 0"
          hence "E k i" by (rule sup)
          hence "E i k" by (rule Esym)
          thus False using iI unfolding isoset_def by auto
        qed
      qed
      ultimately show "i \<in> frs T0" unfolding frs_def using iI by auto
    qed
  qed
  have "2 * (nz div 2) \<le> card (frs T0)" unfolding fr nz_def by simp
  from extend_many[OF r0 this] show "\<exists>T. rep V E T \<and> nnz T = nnz T0 + 2 * (nz div 2)" .
  fix T assume r: "rep V E T"
  have a: "2 * nnz T0 = ne" by (rule nnz_supported[OF r0 sup])
  have b: "2 * nnz T \<le> ne + 4 * (nz div 2)" by (rule nnz_bound[OF r])
  show "nnz T \<le> nnz T0 + 2 * (nz div 2)" by (rule nat_max[OF a b])
qed

end

end
