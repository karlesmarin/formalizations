(*  Title:      Cycle_Utility_Threshold.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    The cycle utility rho(P) of a two-stage cycle: concavity, threshold and the abstract threshold identity.
*)

theory Cycle_Utility_Threshold
  imports "HOL-Analysis.Analysis"
begin

definition rho :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  where "rho gq fq gm fm P = (gq * P + fq * P * (2 - P) + gm * (1 - P) + fm * (1 - P\<^sup>2)) / 3"

text \<open>(5a)\<close>
lemma rho_concave:
  assumes "0 \<le> fq" "0 \<le> fm"
  shows "concave_on {0..1} (rho gq fq gm fm)"
proof (rule concave_on_linorderI)
  fix x y t :: real
  assume t: "0 < t" "t < 1" and xy: "x \<in> {0..1}" "y \<in> {0..1}" "x < y"
  have key: "rho gq fq gm fm ((1 - t) *\<^sub>R x + t *\<^sub>R y)
      - ((1 - t) * rho gq fq gm fm x + t * rho gq fq gm fm y)
      = (fq + fm) / 3 * (t * (1 - t) * (x - y)\<^sup>2)"
    by (simp add: rho_def real_scaleR_def power2_eq_square field_simps)
  have "0 \<le> (fq + fm) / 3 * (t * (1 - t) * (x - y)\<^sup>2)"
    using assms t by (intro mult_nonneg_nonneg) simp_all
  then show "(1 - t) * rho gq fq gm fm x + t * rho gq fq gm fm y
      \<le> rho gq fq gm fm ((1 - t) *\<^sub>R x + t *\<^sub>R y)" using key by linarith
qed (simp add: convex_real_interval)

text \<open>(5b), first part\<close>
lemma rho_ge_rho_one:
  assumes "0 \<le> fq" "0 \<le> fm" "gq + fq \<le> gm + fm" "0 \<le> P" "P \<le> 1"
  shows "rho gq fq gm fm 1 \<le> rho gq fq gm fm P"
proof -
  have "3 * rho gq fq gm fm P - 3 * rho gq fq gm fm 1
      = (1 - P) * ((gm + fm - gq - fq) + (fm + fq) * P)"
    by (simp add: rho_def power2_eq_square field_simps)
  moreover have "0 \<le> (1 - P) * ((gm + fm - gq - fq) + (fm + fq) * P)"
    using assms by (intro mult_nonneg_nonneg add_nonneg_nonneg) simp_all
  ultimately show ?thesis by linarith
qed

text \<open>(5b), second part\<close>
lemma rho_zero_lt:
  assumes "0 \<le> fq" "0 \<le> fm" "gm + fm < gq + fq" "0 < P" "P \<le> 1"
  shows "rho gq fq gm fm 0 < rho gq fq gm fm P"
proof -
  have "3 * rho gq fq gm fm P - 3 * rho gq fq gm fm 0
      = P * (gq + 2 * fq - gm - (fq + fm) * P)"
    by (simp add: rho_def power2_eq_square field_simps)
  moreover have pos: "0 < gq + 2 * fq - gm - (fq + fm) * P"
  proof -
    have "0 \<le> fq * (1 - P)" "0 \<le> fm * (1 - P)" using assms by (simp_all add: mult_nonneg_nonneg)
    then show ?thesis using assms by (simp add: algebra_simps)
  qed
  moreover have "0 < P * (gq + 2 * fq - gm - (fq + fm) * P)"
    using assms(4) pos by (rule mult_pos_pos)
  ultimately show ?thesis by linarith
qed

text \<open>(5c) the abstract threshold identity\<close>
definition F_t :: "(real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  where "F_t A r t \<theta> = A \<theta> + t * r ((cos \<theta>)\<^sup>2)"

lemma F_t_difference:
  assumes "A 0 = 0"
  shows "F_t A r t \<theta> - F_t A r t 0 = A \<theta> - t * (r 1 - r ((cos \<theta>)\<^sup>2))"
  using assms by (simp add: F_t_def algebra_simps)

lemma F_t_ge:
  assumes "A 0 = 0" "0 \<le> A \<theta>" "0 \<le> t" "r 1 - r ((cos \<theta>)\<^sup>2) \<le> 0"
  shows "F_t A r t 0 \<le> F_t A r t \<theta>"
proof -
  have "0 \<le> t * (r ((cos \<theta>)\<^sup>2) - r 1)" using assms(3,4) by (intro mult_nonneg_nonneg) simp_all
  then show ?thesis using assms(1,2) by (simp add: F_t_def algebra_simps)
qed

text \<open>(5d)\<close>
lemma rho_derivative_zero:
  "(rho gq fq gm fm has_real_derivative (gq + 2 * fq - gm) / 3) (at 0)"
proof -
  have "((\<lambda>P. (gq * P + fq * P * (2 - P) + gm * (1 - P) + fm * (1 - P\<^sup>2)) / 3)
        has_real_derivative (gq + 2 * fq - gm) / 3) (at 0)"
    by (rule derivative_eq_intros refl | simp)+
  then show ?thesis by (simp add: rho_def [abs_def])
qed

lemma rho_slope_gt:
  fixes gq fq gm fm :: real
  assumes "0 \<le> fq" "0 \<le> fm" "gm + fm < gq + fq"
  shows "fq + fm < gq + 2 * fq - gm"
  using assms by linarith

end
