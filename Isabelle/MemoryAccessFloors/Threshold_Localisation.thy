(*  Title:      Threshold_Localisation.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Pure inequalities used to localise a threshold.
*)

theory Threshold_Localisation
  imports "HOL-Analysis.Analysis"
begin

lemma amgm_scaled:
  fixes x y h :: real
  assumes "0 < x" "0 < y" "0 < h"
  shows "2 * sqrt (x * y) / h \<le> y + x / h\<^sup>2"
proof -
  let ?s = "sqrt (x * y)"
  have s2: "?s\<^sup>2 = x * y" using assms by simp
  have "0 \<le> y * (h\<^sup>2 * y + x - 2 * h * ?s)"
  proof -
    have "(h * y - ?s)\<^sup>2 = y * (h\<^sup>2 * y + x - 2 * h * ?s)"
      using s2 by (simp add: power2_eq_square algebra_simps)
    then show ?thesis by (metis zero_le_power2)
  qed
  then have "0 \<le> h\<^sup>2 * y + x - 2 * h * ?s" using assms(2) by (simp add: zero_le_mult_iff)
  then have "0 \<le> (h\<^sup>2 * y + x - 2 * h * ?s) / h\<^sup>2" using assms(3) by simp
  moreover have "(h\<^sup>2 * y + x - 2 * h * ?s) / h\<^sup>2 = y + x / h\<^sup>2 - 2 * ?s / h"
    using assms(3) by (simp add: field_simps power2_eq_square)
  ultimately show ?thesis by linarith
qed

text \<open>(2a)\<close>
lemma threshold_lower_bound:
  fixes x y a h r D :: real
  assumes "0 < x" "0 < y" "0 < a" "0 < h" "0 < r" "r = 1 / h\<^sup>2" "0 < D"
    "D \<le> 4 * a * (1 - a / 2)" "a < 2" "a\<^sup>2 \<le> x * y"
  shows "(2 / h) * sqrt (x * y) / (a * (1 - a / 2)) \<le> 4 * (y + r * x) / D"
proof -
  have am: "2 * sqrt (x * y) / h \<le> y + r * x"
    using amgm_scaled[of x y h] assms by simp
  have pos: "0 < a * (1 - a / 2)" using assms by (simp add: mult_pos_pos)
  have "(2 / h) * sqrt (x * y) / (a * (1 - a / 2))
        = 4 * (2 * sqrt (x * y) / h) / (4 * a * (1 - a / 2))"
  proof -
    have h1: "0 < 1 - a / 2" using assms(9) by linarith
    have "a \<noteq> 0" "h \<noteq> 0" "1 - a / 2 \<noteq> 0" using h1 assms(3,4) by simp_all
    then show ?thesis by (simp add: field_simps)
  qed
  also have "\<dots> \<le> 4 * (y + r * x) / (4 * a * (1 - a / 2))"
    using am pos by (intro divide_right_mono) simp_all
  also have "\<dots> \<le> 4 * (y + r * x) / D"
    using assms am pos
    by (intro divide_left_mono) (auto simp: mult_pos_pos intro!: add_nonneg_nonneg mult_nonneg_nonneg)
  finally show ?thesis .
qed

lemma k_identity_aux:
  fixes u v h :: real
  assumes "0 < u" "0 < v" "0 < h"
  shows "(h * (v / u) + 1 / (h * (v / u))) / h = (v\<^sup>2 + u\<^sup>2 / h\<^sup>2) / (u * v)"
  using assms by (simp add: field_simps power2_eq_square)

text \<open>(2b)\<close>
lemma threshold_lower_bound_k:
  fixes x y h r D :: real
  assumes "0 < x" "0 < y" "0 < h" "r = 1 / h\<^sup>2" "0 < D" "D \<le> 4 * sqrt (x * y)"
  shows "((h * sqrt (y / x)) + 1 / (h * sqrt (y / x))) / h \<le> 4 * (y + r * x) / D"
proof -
  let ?s = "sqrt (x * y)"
  have sx: "0 < sqrt x" and sy: "0 < sqrt y" using assms by simp_all
  have s_def: "?s = sqrt x * sqrt y" by (simp add: real_sqrt_mult)
  have yx: "sqrt (y / x) = sqrt y / sqrt x" by (simp add: real_sqrt_divide)
  have eq: "((h * sqrt (y / x)) + 1 / (h * sqrt (y / x))) / h = (y + r * x) / ?s"
  proof -
    have sqx: "(sqrt x)\<^sup>2 = x" and sqy: "(sqrt y)\<^sup>2 = y" using assms by simp_all
    have "((h * sqrt (y / x)) + 1 / (h * sqrt (y / x))) / h
        = ((sqrt y)\<^sup>2 + (sqrt x)\<^sup>2 / h\<^sup>2) / (sqrt x * sqrt y)"
      unfolding yx using k_identity_aux[OF sx sy assms(3)] by simp
    also have "\<dots> = (y + r * x) / ?s" unfolding sqx sqy s_def using assms(4) by simp
    finally show ?thesis .
  qed
  have "0 < ?s" using assms by simp
  have "(y + r * x) / ?s = 4 * (y + r * x) / (4 * ?s)" by (rule sym, rule mult_divide_mult_cancel_left) simp
  also have "\<dots> \<le> 4 * (y + r * x) / D"
    using assms \<open>0 < ?s\<close> by (intro divide_left_mono) (auto simp: mult_pos_pos intro!: add_nonneg_nonneg mult_nonneg_nonneg)
  finally show ?thesis using eq by simp
qed

text \<open>(2c)\<close>
lemma complete_square_bound:
  fixes h L t :: real
  assumes "0 < h" "0 \<le> L"
  shows "- (3 / 2) * L\<^sup>2 * h \<le> t\<^sup>2 / (6 * h) - L * \<bar>t\<bar>"
proof -
  have "0 \<le> (\<bar>t\<bar> - 3 * L * h)\<^sup>2 / (6 * h)" using assms by simp
  moreover have "(\<bar>t\<bar> - 3 * L * h)\<^sup>2 / (6 * h)
      = t\<^sup>2 / (6 * h) - L * \<bar>t\<bar> + (3 / 2) * L\<^sup>2 * h"
    using assms by (simp add: field_simps power2_eq_square)
  ultimately show ?thesis by linarith
qed

end
