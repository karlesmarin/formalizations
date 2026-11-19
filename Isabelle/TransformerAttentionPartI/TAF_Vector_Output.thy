(* Title: Convex diameter and frozen attention output bounds
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Vector_Output
  imports TAF_Truncation
begin

definition vector_mean :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'v::real_normed_vector) \<Rightarrow> 'v" where
  "vector_mean S p v = (\<Sum>i\<in>S. p i *\<^sub>R v i)"

lemma vector_mean_add_weights:
  "vector_mean S (\<lambda>i. a*p i+b*q i) v = a *\<^sub>R vector_mean S p v+b *\<^sub>R vector_mean S q v"
  by (simp add: vector_mean_def scaleR_add_left scaleR_scaleR sum.distrib scaleR_sum_right)

lemma convex_diameter:
  assumes p: "finite_probability S p" and q: "finite_probability S q"
    and diam: "\<And>i j. i\<in>S \<Longrightarrow> j\<in>S \<Longrightarrow> norm (v i-v j)\<le>D"
  shows "norm (vector_mean S p v-vector_mean S q v) \<le> D"
proof -
  interpret p: finite_probability S p by (rule p)
  interpret q: finite_probability S q by (rule q)
  have nn: "0\<le>p i*q j" if "i\<in>S" "j\<in>S" for i j
    using p.p_nonneg[OF that(1)] q.p_nonneg[OF that(2)] by (rule mult_nonneg_nonneg)
  have inner: "(\<Sum>j\<in>S. (p i*q j) *\<^sub>R (v i-v j)) =
      p i *\<^sub>R v i-p i *\<^sub>R vector_mean S q v" for i
    by (simp only: scaleR_diff_right sum_subtractf scaleR_scaleR[symmetric]
        scaleR_sum_right[symmetric] scaleR_sum_left[symmetric] q.p_sum scaleR_one vector_mean_def)
  have identity: "(\<Sum>i\<in>S. \<Sum>j\<in>S. (p i*q j) *\<^sub>R (v i-v j)) =
      vector_mean S p v-vector_mean S q v"
    by (simp add: inner sum_subtractf scaleR_sum_left[symmetric] p.p_sum vector_mean_def)
  have n: "norm (vector_mean S p v-vector_mean S q v) \<le>
      (\<Sum>i\<in>S. \<Sum>j\<in>S. norm ((p i*q j) *\<^sub>R (v i-v j)))"
    unfolding identity[symmetric]
    by (rule order_trans[OF norm_sum]; rule sum_mono; rule norm_sum)
  have point: "norm ((p i*q j) *\<^sub>R (v i-v j)) \<le> p i*q j*D"
    if "i\<in>S" "j\<in>S" for i j
    using mult_left_mono[OF diam[OF that] nn[OF that]] nn[OF that]
    by (simp add: norm_scaleR abs_of_nonneg)
  have "(\<Sum>i\<in>S. \<Sum>j\<in>S. norm ((p i*q j) *\<^sub>R (v i-v j))) \<le>
      (\<Sum>i\<in>S. \<Sum>j\<in>S. p i*q j*D)"
    by (intro sum_mono point)
  also have "...=D"
    by (simp add: sum_distrib_left[symmetric] sum_distrib_right[symmetric] p.p_sum q.p_sum)
  finally show ?thesis using n by linarith
qed

lemma bounded_vector_tv:
  assumes p: "finite_probability S p" and q: "finite_probability S q"
    and bound: "\<And>i. i\<in>S \<Longrightarrow> norm (v i)\<le>M"
  shows "norm (vector_mean S p v-vector_mean S q v) \<le> 2*M*tv_distance S p q"
proof -
  have id: "vector_mean S p v-vector_mean S q v = (\<Sum>i\<in>S. (p i-q i) *\<^sub>R v i)"
    by (simp add: vector_mean_def scaleR_diff_left sum_subtractf)
  have "norm (vector_mean S p v-vector_mean S q v) \<le>
      (\<Sum>i\<in>S. abs (p i-q i)*norm (v i))"
    unfolding id using norm_sum[of "\<lambda>i. (p i-q i) *\<^sub>R v i" S]
    by (simp add: norm_scaleR)
  also have "...\<le>(\<Sum>i\<in>S. abs (p i-q i)*M)"
    by (intro sum_mono mult_left_mono bound) auto
  also have "...=2*M*tv_distance S p q"
    by (simp add: tv_distance_def sum_distrib_right[symmetric] sum_distrib_left[symmetric] algebra_simps)
  finally show ?thesis .
qed

context finite_truncation
begin

lemma frozen_output_maxnorm:
  assumes "\<And>i. i\<in>S \<Longrightarrow> norm (v i)\<le>M"
  shows "norm (vector_mean S p v-vector_mean S (cut_prob K p) v) \<le> 2*M*(1-sum p K)"
  using bounded_vector_tv[OF finite_probability_axioms cut_probability assms] truncation_tv by simp

lemma retained_removed_mixture:
  assumes less: "sum p K<1"
  shows "vector_mean S p v = sum p K *\<^sub>R vector_mean S (cut_prob K p) v +
    (1-sum p K) *\<^sub>R vector_mean S (cut_prob (S-K) p) v"
proof -
  have nz: "sum p (S-K)\<noteq>0" using remaining_mass less by linarith
  have pt: "p i = sum p K*cut_prob K p i+(1-sum p K)*cut_prob (S-K) p i"
    if "i\<in>S" for i
    using that mass_pos nz remaining_mass
    by (auto simp: cut_prob_def split: if_splits)
  have eq: "vector_mean S p v = vector_mean S
    (\<lambda>i. sum p K*cut_prob K p i+(1-sum p K)*cut_prob (S-K) p i) v"
    unfolding vector_mean_def by (rule sum.cong[OF refl]; simp only: pt)
  show ?thesis using eq vector_mean_add_weights by metis
qed

lemma frozen_output_exact:
  assumes "sum p K<1"
  shows "norm (vector_mean S p v-vector_mean S (cut_prob K p) v) =
    (1-sum p K)*norm (vector_mean S (cut_prob (S-K) p) v-vector_mean S (cut_prob K p) v)"
proof -
  have id: "vector_mean S p v-vector_mean S (cut_prob K p) v =
    (1-sum p K) *\<^sub>R (vector_mean S (cut_prob (S-K) p) v-vector_mean S (cut_prob K p) v)"
    using retained_removed_mixture[OF assms, where v=v]
    by (simp add: scaleR_diff_right scaleR_diff_left algebra_simps)
  show ?thesis using mass_le_one by (simp add: id norm_scaleR abs_of_nonneg)
qed

lemma frozen_output_diameter_positive:
  assumes less: "sum p K<1"
    and diam: "\<And>i j. i\<in>S \<Longrightarrow> j\<in>S \<Longrightarrow> norm (v i-v j)\<le>D"
  shows "norm (vector_mean S p v-vector_mean S (cut_prob K p) v) \<le> (1-sum p K)*D"
proof -
  interpret r: finite_truncation S p "S-K"
    by (unfold_locales; use finite_S p_nonneg p_sum remaining_mass less in auto)
  have "norm (vector_mean S (cut_prob (S-K) p) v-vector_mean S (cut_prob K p) v)\<le>D"
    by (rule convex_diameter[OF r.cut_probability cut_probability diam])
  then show ?thesis using mass_le_one
    by (simp only: frozen_output_exact[OF less]; intro mult_left_mono; linarith)
qed

end
end
