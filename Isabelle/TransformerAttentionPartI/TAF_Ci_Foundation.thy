(* Title: Cosine integral normalized by the standard Euler constant
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Ci_Foundation
  imports "Exp_Log_Integral.Exp_Log_Integral" TAF_RoPE_Grid
begin

definition ci_entire_real :: "real \<Rightarrow> real" where
  "ci_entire_real x=Re (Ein (\<i>* of_real x))"

definition cosine_integral :: "real \<Rightarrow> real" where
  "cosine_integral x=euler_mascheroni+ln x-ci_entire_real x"

lemma ci_entire_real_zero [simp]: "ci_entire_real 0=0"
  by (simp add: ci_entire_real_def)

lemma ci_entire_real_derivative:
  "(ci_entire_real has_real_derivative ((1-cos x)/x)) (at x within A)"
proof -
  have d: "((\<lambda>z::complex. Ein (\<i>*z)) has_field_derivative
      ((if \<i>* of_real x=0 then 1 else
        (1-exp (- (\<i>* of_real x)))/(\<i>* of_real x))*\<i>)) (at (of_real x))"
    by (auto intro!: derivative_eq_intros)
  have v: "((\<lambda>t. Ein (\<i>* of_real t)) has_vector_derivative
      ((if \<i>* of_real x=0 then 1 else
        (1-exp (- (\<i>* of_real x)))/(\<i>* of_real x))*\<i>)) (at x within A)"
    by (rule has_vector_derivative_real_field[OF d])
  note r=bounded_linear.has_vector_derivative[OF bounded_linear_Re v]
  have alg: "z/(\<i>* of_real x)*\<i>=z/of_real x" for z :: complex
    by (simp add: divide_inverse mult_ac)
  show ?thesis using r
    by (cases "x=0"; simp add: ci_entire_real_def[abs_def] alg Re_exp
      has_real_derivative_iff_has_vector_derivative)
qed

lemma cosine_integral_derivative:
  assumes "0<x"
  shows "(cosine_integral has_real_derivative (cos x/x)) (at x)"
proof -
  have ld: "(ln has_real_derivative (1/x)) (at x)"
    using assms by (auto intro!: derivative_eq_intros)
  have cd: "((\<lambda>t::real. euler_mascheroni) has_real_derivative 0) (at x)"
    by (rule DERIV_const)
  have ad: "((\<lambda>t. euler_mascheroni+ln t) has_real_derivative (1/x)) (at x)"
    using DERIV_add[OF cd ld] by simp
  have d: "((\<lambda>t. euler_mascheroni+ln t-ci_entire_real t) has_real_derivative
    (1/x-(1-cos x)/x)) (at x)"
    by (rule DERIV_diff[OF ad ci_entire_real_derivative])
  show ?thesis using d by (simp add: cosine_integral_def[abs_def] diff_divide_distrib)
qed

lemma cosine_integral_gamma_bridge:
  assumes xp: "0<x"
  shows "cosine_integral x= -Re (Gamma_incu 0 (\<i>* of_real x))"
proof -
  have outside: "(\<i>* of_real x::complex)\<notin>\<real>\<^sub>\<le>\<^sub>0"
    using xp by (auto simp: complex_nonpos_Reals_iff)
  have nz: "(\<i>* of_real x::complex)\<noteq>0" using xp by simp
  have norm: "norm (\<i>* of_real x::complex)=x" using xp by (simp add: norm_mult)
  note eq=Gamma_incu_0_conv_Ei_complex[OF outside]
  note re=arg_cong[where f=Re, OF eq]
  show ?thesis using re Re_Ln[OF nz] norm
    by (simp add: cosine_integral_def ci_entire_real_def; linarith)
qed

lemma ci_entire_real_integral:
  assumes "0\<le>y"
  shows "((\<lambda>x. (1-cos x)/x) has_integral ci_entire_real y) {0..y}"
proof -
  have "((\<lambda>x. (1-cos x)/x) has_integral (ci_entire_real y-ci_entire_real 0)) {0..y}"
    by (rule fundamental_theorem_of_calculus[OF assms];
        simp add: has_real_derivative_iff_has_vector_derivative[symmetric]
          ci_entire_real_derivative)
  then show ?thesis by simp
qed

lemma ci_entire_real_small_bound:
  assumes yp: "0\<le>y"
  shows "abs (ci_entire_real y)\<le>y^2/4"
proof -
  have int: "(\<lambda>x. (1-cos x)/x) integrable_on {0..y}"
    by (rule has_integral_integrable[OF ci_entire_real_integral[OF yp]])
  have point: "norm ((1-cos x)/x)\<le>x/2" if "x\<in>{0..y}" for x
  proof (cases "x=0")
    case True then show ?thesis by simp
  next
    case False
    have xp: "0<x" using that False by auto
    show ?thesis using small_cosine_integrand[OF xp]
      by (simp add: abs_minus_commute)
  qed
  have intg: "(\<lambda>x::real. x/2) integrable_on {0..y}"
    by (intro integrable_continuous_real continuous_intros; simp)
  have bound: "norm (integral {0..y} (\<lambda>x. (1-cos x)/x))\<le>
      integral {0..y} (\<lambda>x. x/2)"
    by (rule integral_norm_bound_integral[OF int intg point])
  have value_eq: "integral {0..y} (\<lambda>x. x/2)=y^2/4"
    using yp by simp
  have val: "integral {0..y} (\<lambda>x. (1-cos x)/x)=ci_entire_real y"
    by (rule integral_unique[OF ci_entire_real_integral[OF yp]])
  show ?thesis using bound by (simp only: val value_eq real_norm_def)
qed

lemma cosine_integral_small_remainder:
  assumes "0<y"
  shows "abs (cosine_integral y-euler_mascheroni-ln y)\<le>y^2/4"
  using ci_entire_real_small_bound[of y] assms by (simp add: cosine_integral_def algebra_simps)

end
