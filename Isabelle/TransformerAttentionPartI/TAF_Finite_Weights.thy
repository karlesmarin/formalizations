(* Title: Finite weighted expectations for the attention audit
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Finite_Weights
  imports "HOL-Analysis.Analysis"
begin

definition fw_mean :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real" where
  "fw_mean S p x = (\<Sum>i\<in>S. p i * x i)"

definition fw_var :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real" where
  "fw_var S p x = (\<Sum>i\<in>S. p i * (x i - fw_mean S p x)^2)"

definition fw_cov :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real" where
  "fw_cov S p x y = fw_mean S p (\<lambda>i. x i*y i) - fw_mean S p x * fw_mean S p y"

locale finite_probability =
  fixes S :: "'a set" and p :: "'a \<Rightarrow> real"
  assumes finite_S: "finite S"
    and p_nonneg: "\<And>i. i\<in>S \<Longrightarrow> 0 \<le> p i"
    and p_sum: "sum p S = 1"
begin

lemma nonempty_S: "S \<noteq> {}" using p_sum by auto

lemma mean_const: "fw_mean S p (\<lambda>_. c) = c"
  by (simp add: fw_mean_def sum_distrib_right[symmetric] p_sum)

lemma mean_add:
  "fw_mean S p (\<lambda>i. x i+y i) = fw_mean S p x+fw_mean S p y"
  by (simp add: fw_mean_def algebra_simps sum.distrib)

lemma mean_diff:
  "fw_mean S p (\<lambda>i. x i-y i) = fw_mean S p x-fw_mean S p y"
  by (simp add: fw_mean_def algebra_simps sum_subtractf)

lemma mean_scale: "fw_mean S p (\<lambda>i. c*x i) = c*fw_mean S p x"
  by (simp add: fw_mean_def sum_distrib_left algebra_simps)

lemma mean_mono:
  assumes "\<And>i. i\<in>S \<Longrightarrow> x i \<le> y i"
  shows "fw_mean S p x \<le> fw_mean S p y"
  unfolding fw_mean_def using assms p_nonneg by (intro sum_mono mult_left_mono) auto

lemma mean_bounds:
  assumes "\<And>i. i\<in>S \<Longrightarrow> a \<le> x i" "\<And>i. i\<in>S \<Longrightarrow> x i \<le> b"
  shows "a \<le> fw_mean S p x" "fw_mean S p x \<le> b"
  using mean_mono[of "\<lambda>_. a" x] mean_mono[of x "\<lambda>_. b"] assms
  by (simp_all add: mean_const)

lemma variance_moment:
  "fw_var S p x = fw_mean S p (\<lambda>i. (x i)^2) - (fw_mean S p x)^2"
proof -
  have e: "p i*(x i-fw_mean S p x)^2 =
      p i*(x i)^2 - 2*fw_mean S p x*(p i*x i) + (fw_mean S p x)^2*p i" for i
    by (simp add: algebra_simps power2_eq_square)
  show ?thesis unfolding fw_var_def e
    by (simp add: fw_mean_def sum.distrib sum_subtractf
        sum_distrib_left[symmetric] sum_distrib_right[symmetric] p_sum;
        simp add: algebra_simps power2_eq_square)
qed

lemma variance_nonneg: "0 \<le> fw_var S p x"
  unfolding fw_var_def using p_nonneg by (intro sum_nonneg mult_nonneg_nonneg) auto

lemma variance_bounded:
  assumes L: "0 \<le> L" and x: "\<And>i. i\<in>S \<Longrightarrow> 0 \<le> x i"
    and xL: "\<And>i. i\<in>S \<Longrightarrow> x i \<le> L"
  shows "fw_var S p x \<le> L^2/4"
proof -
  have point: "(x i)^2 \<le> L*x i" if "i\<in>S" for i
    using x[OF that] xL[OF that] by (simp add: power2_eq_square mult_right_mono)
  have second: "fw_mean S p (\<lambda>i. (x i)^2) \<le> L*fw_mean S p x"
    using mean_mono[OF point] by (simp add: mean_scale)
  have square: "0 \<le> (fw_mean S p x-L/2)^2" by simp
  have expand: "(fw_mean S p x-L/2)^2 =
      (fw_mean S p x)^2 - L*fw_mean S p x + L^2/4"
    by (simp add: algebra_simps power2_eq_square)
  show ?thesis using second square expand variance_moment[of x] by linarith
qed

lemma covariance_pairwise:
  "fw_cov S p x y = (\<Sum>i\<in>S. \<Sum>j\<in>S.
      p i*p j*(x i-x j)*(y i-y j))/2"
proof -
  have e: "p i*p j*(x i-x j)*(y i-y j) =
      p i*x i*y i*p j - p i*x i*(p j*y j) - p i*y i*(p j*x j) + p i*(p j*x j*y j)" for i j
    by (simp add: algebra_simps)
  show ?thesis unfolding fw_cov_def fw_mean_def e
    by (simp add: sum.distrib sum_subtractf sum_distrib_left[symmetric]
        sum_distrib_right[symmetric] p_sum; simp add: algebra_simps)
qed

lemma covariance_comonotone:
  assumes order: "\<And>i j. i\<in>S \<Longrightarrow> j\<in>S \<Longrightarrow> 0 \<le> (x i-x j)*(y i-y j)"
  shows "0 \<le> fw_cov S p x y"
  unfolding covariance_pairwise using p_nonneg order
  by (intro divide_nonneg_nonneg sum_nonneg;
      auto simp: mult.assoc intro: mult_nonneg_nonneg)

end
end
