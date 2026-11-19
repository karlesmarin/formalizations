(* Title: Exact finite truncation and support-sensitive relative entropy
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Truncation
  imports TAF_Tilt TAF_Secants
begin

definition cut_prob :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real" where
  "cut_prob K p i = (if i\<in>K then p i / sum p K else 0)"

definition finite_kl :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ereal" where
  "finite_kl S p q = (if \<exists>i\<in>S. 0 < p i \<and> q i=0 then \<infinity>
    else ereal (\<Sum>i\<in>S. p i*ln (p i/q i)))"

locale finite_truncation = finite_probability S p for S p +
  fixes K :: "'a set"
  assumes subset: "K \<subseteq> S" and mass_pos: "0 < sum p K"
begin

lemma finite_K: "finite K" using subset finite_S by (rule finite_subset)

lemma mass_le_one: "sum p K \<le> 1"
proof -
  have "sum p K \<le> sum p S"
    by (rule sum_mono2[OF finite_S subset]) (auto intro: p_nonneg)
  then show ?thesis using p_sum by simp
qed

lemma remaining_mass: "sum p (S-K) = 1-sum p K"
  using sum_diff[OF finite_S subset, of p] p_sum by simp

lemma cut_sum: "sum (cut_prob K p) S = 1"
proof -
  have inter: "S\<inter>K=K" using subset by blast
  show ?thesis using mass_pos finite_S
    by (simp add: cut_prob_def sum.If_cases inter sum_divide_distrib[symmetric])
qed

lemma cut_probability: "finite_probability S (cut_prob K p)"
  by (unfold_locales; use finite_S p_nonneg mass_pos cut_sum in
      \<open>auto simp: cut_prob_def intro: divide_nonneg_nonneg\<close>)

lemma truncation_tv: "tv_distance S p (cut_prob K p) = 1-sum p K"
proof -
  let ?t = "sum p K"
  have tp: "0 \<le> (1-?t)/?t" using mass_pos mass_le_one by (intro divide_nonneg_nonneg; linarith)
  have point_eq: "abs (p i-cut_prob K p i) =
    (if i\<in>K then p i*((1-?t)/?t) else p i)" if "i\<in>S" for i
  proof (cases "i\<in>K")
    case True
    have id: "p i-p i/?t = -(p i*((1-?t)/?t))"
      using mass_pos by (simp add: field_simps algebra_simps)
    have rem: "0\<le>1-?t" using mass_le_one by linarith
    show ?thesis using True p_nonneg[OF that] tp mass_pos rem
      by (simp add: cut_prob_def id abs_of_nonneg mult_nonneg_nonneg)
  next
    case False
    show ?thesis using False p_nonneg[OF that] by (simp add: cut_prob_def)
  qed
  have sumpt: "(\<Sum>i\<in>S. abs (p i-cut_prob K p i)) =
    (\<Sum>i\<in>S. if i\<in>K then p i*((1-?t)/?t) else p i)"
    by (rule sum.cong[OF refl]; rule point_eq)
  have eq: "(\<Sum>i\<in>S. abs (p i-cut_prob K p i)) =
    ?t*((1-?t)/?t) + (1-?t)"
    using sumpt subset remaining_mass finite_S mass_pos
    by (simp add: sum.If_cases Int_absorb1 sum_distrib_right[symmetric]
        sum_divide_distrib[symmetric] Diff_eq)
  show ?thesis unfolding tv_distance_def using eq mass_pos by simp
qed

lemma reverse_support:
  "\<not> (\<exists>i\<in>S. 0 < cut_prob K p i \<and> p i=0)"
  by (auto simp: cut_prob_def)

lemma truncation_reverse_kl:
  "finite_kl S (cut_prob K p) p = ereal (-ln (sum p K))"
proof -
  let ?t = "sum p K"
  let ?q = "cut_prob K p"
  have point_eq: "?q i*ln (?q i/p i) = (-ln ?t)*?q i" if "i\<in>S" for i
  proof (cases "i\<in>K \<and> 0 < p i")
    case True
    then have pi: "p i \<noteq> 0" by simp
    have ratio: "(p i/?t)/p i = 1/?t" using pi by simp
    show ?thesis using True mass_pos
      by (simp add: cut_prob_def ratio ln_divide_pos mult.commute)
  next
    case False
    then have "?q i=0" using p_nonneg[OF that] by (auto simp: cut_prob_def)
    then show ?thesis by simp
  qed
  have sumpt: "(\<Sum>i\<in>S. ?q i*ln (?q i/p i)) = (\<Sum>i\<in>S. (-ln ?t)*?q i)"
    by (rule sum.cong[OF refl]; rule point_eq)
  have eq: "(\<Sum>i\<in>S. ?q i*ln (?q i/p i)) = -ln ?t"
    using sumpt
    by (simp add: sum_negf sum_distrib_left[symmetric] cut_sum)
  show ?thesis by (simp add: finite_kl_def reverse_support eq)
qed

lemma truncation_forward_kl:
  assumes "sum p K < 1"
  shows "finite_kl S p (cut_prob K p) = \<infinity>"
proof -
  have "0 < sum p (S-K)" using remaining_mass assms by linarith
  then obtain i where i: "i\<in>S-K" "0 < p i"
    using positive_sum_has_positive_term by blast
  then have "\<exists>i\<in>S. 0 < p i \<and> cut_prob K p i=0"
    by (auto simp: cut_prob_def)
  then show ?thesis by (simp add: finite_kl_def)
qed

end
end
