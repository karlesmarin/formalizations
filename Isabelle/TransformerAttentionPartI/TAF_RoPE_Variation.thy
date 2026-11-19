(* Title: The absolute-sine quadrature bound for the logarithmic cosine grid
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_RoPE_Variation
  imports TAF_Cosine_Variation
begin

definition cosine_variation :: "real \<Rightarrow> real" where
  "cosine_variation x=integral {0..x} (\<lambda>t. abs (sin t))"

lemma cosine_variation_difference:
  assumes b: "0\<le>b" and ba: "b\<le>a"
  shows "cosine_variation a-cosine_variation b=integral {b..a} (\<lambda>t. abs (sin t))"
proof -
  have int: "(\<lambda>t. abs (sin t)) integrable_on {0..a}"
    by (intro integrable_continuous_real continuous_intros)
  show ?thesis using Henstock_Kurzweil_Integration.integral_combine[OF b ba int]
    by (simp add: cosine_variation_def; linarith)
qed

lemma cosine_primitive_variation_bound:
  assumes b: "0\<le>b" and ba: "b\<le>a"
  shows "abs (cos a-cos b)\<le>cosine_variation a-cosine_variation b"
proof -
  have vd: "(cos has_vector_derivative (-sin x)) (at x)" for x::real
    using DERIV_cos[of x] by (simp only: has_real_derivative_iff_has_vector_derivative)
  have ftc: "((\<lambda>t. -sin t) has_integral (cos a-cos b)) {b..a}"
  proof (rule fundamental_theorem_of_calculus[OF ba])
    fix x assume "x\<in>{b..a}"
    show "(cos has_vector_derivative (-sin x)) (at x within {b..a})"
      by (rule has_vector_derivative_at_within[OF vd])
  qed
  have int: "(\<lambda>t. abs (sin t)) integrable_on {b..a}"
    by (intro integrable_continuous_real continuous_intros)
  have bound: "norm (integral {b..a} (\<lambda>t. -sin t))\<le>integral {b..a} (\<lambda>t. abs (sin t))"
    by (rule integral_norm_bound_integral[OF has_integral_integrable[OF ftc] int]; simp)
  show ?thesis using bound integral_unique[OF ftc] cosine_variation_difference[OF b ba] by simp
qed

lemma positive_phase_cosine_cap:
  assumes pos: "\<And>x. 0\<le>P x" and mono: "antimono P"
    and ab: "a\<le>b" and t: "t\<in>{a..b}"
  shows "abs (cos (P a)-cos (P t))\<le>cosine_variation (P a)-cosine_variation (P b)"
proof -
  have pa: "P t\<le>P a" and pb: "P b\<le>P t" using mono t by (auto simp: antimono_def)
  have first: "abs (cos (P a)-cos (P t))\<le>cosine_variation (P a)-cosine_variation (P t)"
    by (rule cosine_primitive_variation_bound[OF pos pa])
  have second: "abs (cos (P t)-cos (P b))\<le>cosine_variation (P t)-cosine_variation (P b)"
    by (rule cosine_primitive_variation_bound[OF pos pb])
  have nonneg: "0\<le>abs (cos (P t)-cos (P b))" by simp
  show ?thesis using first second nonneg by linarith
qed

lemma rope_grid_absolute_sine_error:
  assumes m: "0<m" and theta: "1<theta" and d: "0<d"
  shows "abs (rope_cosine_sum m theta d-rope_cosine_integral m theta d)\<le>
    integral {d/theta..d} (\<lambda>u. abs (sin u))"
proof -
  let ?P="\<lambda>t. d*exp (-ln theta*t)"
  have th: "0<theta" using theta by linarith
  have L: "0\<le>ln theta" using theta by simp
  have pos: "0\<le>?P t" for t using d by (intro mult_nonneg_nonneg) auto
  have mono: "antimono ?P" by (rule exponential_phase_antimono[OF less_imp_le[OF d] L])
  have cont: "continuous_on UNIV (\<lambda>t. cos (?P t))" by (rule logarithmic_cosine_continuous)
  have err: "abs ((\<Sum>i<m. cos (?P (real i/real m)))-real m*integral {0..1} (\<lambda>t. cos (?P t)))\<le>
      cosine_variation (?P 0)-cosine_variation (?P 1)"
    by (rule variation_riemann_error[OF m cont]; rule positive_phase_cosine_cap[OF pos mono]; assumption)
  have ends: "?P 0=d" "?P 1=d/theta" using th by (simp_all add: exp_minus')
  have da: "d\<le>theta*d"
    using mult_right_mono[OF less_imp_le[OF theta] less_imp_le[OF d]] by simp
  have db: "d/theta\<le>d" using da th by (simp add: pos_divide_le_eq mult.commute)
  have dp: "0\<le>d/theta" using d th by simp
  show ?thesis using err cosine_variation_difference[OF dp db]
    by (simp only: ends rope_cosine_sum_def rope_cosine_integral_def)
qed

lemma absolute_sine_interval_length:
  assumes "a\<le>b"
  shows "integral {a..b} (\<lambda>u::real. abs (sin u))\<le>b-a"
proof -
  have int: "(\<lambda>u::real. abs (sin u)) integrable_on {a..b}"
    by (intro integrable_continuous_real continuous_intros)
  have "integral {a..b} (\<lambda>u::real. abs (sin u))\<le>integral {a..b} (\<lambda>_. 1::real)"
    by (rule integral_le[OF int integrable_const_ivl]; simp add: abs_sin_le_one)
  then show ?thesis using assms by simp
qed

end
