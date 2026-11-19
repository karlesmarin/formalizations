(* Title: Finite regression bounds and affine exposure derivatives
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Secants
  imports TAF_Probe
begin

lemma positive_sum_has_positive_term:
  fixes f :: "'a \<Rightarrow> real"
  assumes "0 < sum f S"
  shows "\<exists>i\<in>S. 0 < f i"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "sum f S \<le> 0" by (intro sum_nonpos) auto
  with assms show False by linarith
qed

context finite_probability
begin

lemma positive_sum:
  fixes f :: "'a \<Rightarrow> real"
  assumes nn: "\<And>i. i\<in>S \<Longrightarrow> 0 \<le> f i"
    and ex: "\<exists>i\<in>S. 0 < f i"
  shows "0 < sum f S"
proof -
  have "sum (\<lambda>_. 0::real) S < sum f S"
    by (rule sum_strict_mono_ex1[OF finite_S]) (use nn ex in auto)
  then show ?thesis by simp
qed

lemma covariance_self: "fw_cov S p x x = fw_var S p x"
  unfolding fw_cov_def using variance_moment[of x]
  by (simp add: power2_eq_square)

lemma pair_variance:
  "(\<Sum>i\<in>S. \<Sum>j\<in>S. p i*p j*(x i-x j)^2) = 2*fw_var S p x"
  using covariance_pairwise[of x x] covariance_self[of x]
  by (simp add: power2_eq_square mult.assoc; linarith)

lemma pair_covariance:
  "(\<Sum>i\<in>S. \<Sum>j\<in>S. p i*p j*(x i-x j)*(y i-y j)) = 2*fw_cov S p x y"
  using covariance_pairwise[of x y] by linarith

lemma weighted_secant_bounds:
  assumes v: "0 < fw_var S p x"
    and low: "\<And>i j. i\<in>S \<Longrightarrow> j\<in>S \<Longrightarrow>
       lo*(x i-x j)^2 \<le> (x i-x j)*(y i-y j)"
    and high: "\<And>i j. i\<in>S \<Longrightarrow> j\<in>S \<Longrightarrow>
       (x i-x j)*(y i-y j) \<le> hi*(x i-x j)^2"
  shows "lo \<le> fw_cov S p x y / fw_var S p x"
    "fw_cov S p x y / fw_var S p x \<le> hi"
proof -
  have nn: "0 \<le> p i*p j" if "i\<in>S" "j\<in>S" for i j
    using p_nonneg[OF that(1)] p_nonneg[OF that(2)] by (rule mult_nonneg_nonneg)
  have lpoint: "lo*(p i*p j*(x i-x j)^2) \<le> p i*p j*(x i-x j)*(y i-y j)"
    if "i\<in>S" "j\<in>S" for i j
    using mult_left_mono[OF low[OF that] nn[OF that]] by (simp add: algebra_simps)
  have hpoint: "p i*p j*(x i-x j)*(y i-y j) \<le> hi*(p i*p j*(x i-x j)^2)"
    if "i\<in>S" "j\<in>S" for i j
    using mult_left_mono[OF high[OF that] nn[OF that]] by (simp add: algebra_simps)
  have ls: "(\<Sum>i\<in>S. \<Sum>j\<in>S. lo*(p i*p j*(x i-x j)^2)) \<le>
      (\<Sum>i\<in>S. \<Sum>j\<in>S. p i*p j*(x i-x j)*(y i-y j))"
    by (intro sum_mono lpoint)
  have hs: "(\<Sum>i\<in>S. \<Sum>j\<in>S. p i*p j*(x i-x j)*(y i-y j)) \<le>
      (\<Sum>i\<in>S. \<Sum>j\<in>S. hi*(p i*p j*(x i-x j)^2))"
    by (intro sum_mono hpoint)
  have l: "lo*fw_var S p x \<le> fw_cov S p x y"
    using ls by (simp add: sum_distrib_left[symmetric] pair_variance pair_covariance)
  have h: "fw_cov S p x y \<le> hi*fw_var S p x"
    using hs by (simp add: sum_distrib_left[symmetric] pair_variance pair_covariance)
  show "lo \<le> fw_cov S p x y / fw_var S p x" using l v by (simp add: le_divide_eq)
  show "fw_cov S p x y / fw_var S p x \<le> hi" using h v by (simp add: divide_le_eq mult.commute)
qed

end

definition affine_log :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "affine_log a b x = ln (a*exp x+b)"

lemma affine_log_derivative:
  assumes "0 < a" "0 < b"
  shows "((\<lambda>x. affine_log a b x) has_real_derivative
      (a*exp t/(a*exp t+b))) (at t)"
  unfolding affine_log_def using assms
  by (auto intro!: derivative_eq_intros simp: field_simps add_pos_pos mult_pos_pos)

lemma affine_log_offset_derivative:
  assumes "0 < a" "0 < b"
  shows "((\<lambda>b. affine_log a b x) has_real_derivative
      (1/(a*exp x+b))) (at b)"
  unfolding affine_log_def using assms
  by (auto intro!: derivative_eq_intros simp: field_simps add_pos_pos mult_pos_pos)

lemma affine_log_scale_derivative:
  assumes "0 < a" "0 < b" "0 < l"
  shows "((\<lambda>l. ln (a*l*exp x+b)) has_real_derivative
      (a*exp x/(a*l*exp x+b))) (at l)"
  using assms by (auto intro!: derivative_eq_intros
      simp: field_simps algebra_simps add_pos_pos mult_pos_pos)

lemma affine_elasticity_increasing:
  fixes a b x y :: real
  assumes "0 < a" "0 < b" "x < y"
  shows "a*exp x/(a*exp x+b) < a*exp y/(a*exp y+b)"
proof -
  have ex: "exp x < exp y" using assms by simp
  have ax: "0 < a*exp x+b" and ay: "0 < a*exp y+b"
    using assms by (simp_all add: add_pos_pos mult_pos_pos)
  have prod: "a*b*exp x < a*b*exp y"
    using assms ex by (intro mult_strict_left_mono) (auto intro: mult_pos_pos)
  have cross: "a*exp x*(a*exp y+b) < a*exp y*(a*exp x+b)"
    using prod by (simp add: algebra_simps)
  show ?thesis using cross
    by (simp only: pos_divide_less_eq[OF ax] times_divide_eq_left pos_less_divide_eq[OF ay])
qed

end
