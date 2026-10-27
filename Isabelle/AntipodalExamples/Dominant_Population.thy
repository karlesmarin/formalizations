(*  Title:      Dominant_Population.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    A dominant population keeps a state away from orthogonality

    Cut-off inequality of Uffink: a population p_j > 1/2 keeps the autocorrelation at least 2 p_j - 1.
    Lean counterpart: Formalizations.Physics.QuantumMechanics.SpeedLimit.DominantPopulation.

    Main results:
    * two_mul_sub_one_le_norm_suminf: 2 p_j - 1 <= |sum p_k u_k| for p_k >= 0, sum p_k = 1, |u_k| = 1.
    * suminf_ne_zero_of_half_lt: that sum never vanishes when some p_j > 1/2.

    References:
    * M. Andrews, Phys. Rev. A 75, 062112 (2007), Eq. (21).
*)

theory Dominant_Population
  imports "HOL-Analysis.Analysis"
begin

section \<open>Removing one term of a series\<close>

lemma suminf_remove:
  fixes h :: "nat \<Rightarrow> 'a::real_normed_vector"
  assumes "summable h"
  shows "(\<Sum>k. h k) = h j + (\<Sum>k. if k = j then 0 else h k)"
proof -
  have s1: "(\<lambda>k. if k = j then h k else 0) sums h j"
    by (rule sums_single)
  have s2: "summable (\<lambda>k. if k = j then 0 else h k)"
  proof -
    have "summable (\<lambda>k. h k - (if k = j then h k else 0))"
      using assms s1 by (intro summable_diff) (auto simp: sums_iff)
    moreover have "(\<lambda>k. h k - (if k = j then h k else 0)) = (\<lambda>k. if k = j then 0 else h k)"
      by auto
    ultimately show ?thesis by simp
  qed
  have "(\<lambda>k. (if k = j then h k else 0) + (if k = j then 0 else h k)) sums
        (h j + (\<Sum>k. if k = j then 0 else h k))"
    using s1 s2 by (intro sums_add) (auto simp: summable_sums)
  moreover have "(\<lambda>k. (if k = j then h k else 0) + (if k = j then 0 else h k)) = h"
    by auto
  ultimately have "h sums (h j + (\<Sum>k. if k = j then 0 else h k))" by simp
  then show ?thesis by (simp add: sums_iff)
qed

section \<open>The dominant-population floor\<close>

theorem two_mul_sub_one_le_norm_suminf:
  fixes p :: "nat \<Rightarrow> real" and u :: "nat \<Rightarrow> complex"
  assumes hp: "\<And>k. 0 \<le> p k" and hs: "p sums 1" and hu: "\<And>k. norm (u k) = 1"
  shows "2 * p j - 1 \<le> norm (\<Sum>k. of_real (p k) * u k)"
proof -
  have hnorm: "\<And>k. norm (of_real (p k) * u k) = p k"
    using hp hu by (simp add: norm_mult)
  have hsn: "summable (\<lambda>k. norm (of_real (p k) * u k))"
    using hs hnorm by (simp add: sums_iff)
  have hsc: "summable (\<lambda>k. of_real (p k) * u k)"
    by (rule summable_norm_cancel[OF hsn])
  define R where "R = (\<Sum>k. if k = j then 0 else of_real (p k) * u k)"
  have hsplit: "(\<Sum>k. of_real (p k) * u k) = of_real (p j) * u j + R"
    unfolding R_def by (rule suminf_remove[OF hsc])
  have hrest: "(\<Sum>k. if k = j then 0 else p k) = 1 - p j"
  proof -
    have "(\<Sum>k. p k) = p j + (\<Sum>k. if k = j then 0 else p k)"
      by (rule suminf_remove[OF sums_summable[OF hs]])
    then show ?thesis using hs by (simp add: sums_iff)
  qed
  have hsn': "summable (\<lambda>k. norm (if k = j then 0 else of_real (p k) * u k))"
  proof (rule summable_comparison_test[OF _ hsn])
    show "\<exists>N. \<forall>n\<ge>N. norm (norm (if n = j then 0 else of_real (p n) * u n)) \<le>
                       norm (of_real (p n) * u n)"
      by (intro exI[of _ 0]) auto
  qed
  have hRle: "norm R \<le> 1 - p j"
  proof -
    have "norm R \<le> (\<Sum>k. norm (if k = j then 0 else of_real (p k) * u k))"
      unfolding R_def by (rule summable_norm[OF hsn'])
    also have "\<dots> = (\<Sum>k. if k = j then 0 else p k)"
      by (rule suminf_cong) (simp add: hnorm)
    also have "\<dots> = 1 - p j" by (rule hrest)
    finally show ?thesis .
  qed
  have htri: "norm (of_real (p j) * u j) - norm R \<le> norm (of_real (p j) * u j + R)"
    by (rule norm_diff_ineq)
  show ?thesis
    using hsplit hnorm[of j] htri hRle by simp
qed

theorem suminf_ne_zero_of_half_lt:
  fixes p :: "nat \<Rightarrow> real" and u :: "nat \<Rightarrow> complex"
  assumes hp: "\<And>k. 0 \<le> p k" and hs: "p sums 1" and hu: "\<And>k. norm (u k) = 1"
    and hj: "1 / 2 < p j"
  shows "(\<Sum>k. of_real (p k) * u k) \<noteq> 0"
proof
  assume h: "(\<Sum>k. of_real (p k) * u k) = 0"
  have "2 * p j - 1 \<le> norm (\<Sum>k. of_real (p k) * u k)"
    by (rule two_mul_sub_one_le_norm_suminf[OF hp hs hu])
  with h hj show False by simp
qed

end
