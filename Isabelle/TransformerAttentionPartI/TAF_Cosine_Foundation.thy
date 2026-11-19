(* Title: Elementary analytic ingredients for the logarithmic cosine grid
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Cosine_Foundation
  imports TAF_Finite_Weights
begin

lemma cosine_lipschitz:
  fixes x y :: real
  shows "abs (cos x-cos y)\<le>abs (x-y)"
proof -
  have ordered: "abs (cos b-cos a)\<le>abs (b-a)" if ab: "a<b" for a b :: real
  proof -
    obtain z where z: "cos b-cos a=(b-a)*(-sin z)"
      using MVT2[OF ab, where f=cos and f'="\<lambda>x. -sin x"] DERIV_cos by blast
    have "abs (cos b-cos a)=abs (b-a)*abs (sin z)" by (simp add: z abs_mult)
    also have "...\<le>abs (b-a)*1" by (intro mult_left_mono abs_sin_le_one) auto
    finally show ?thesis by simp
  qed
  show ?thesis using ordered[of x y] ordered[of y x]
    by (cases "x=y"; cases "x<y"; auto simp: abs_minus_commute)
qed

lemma cosine_quadratic_remainder:
  fixes x :: real
  shows "abs (cos x-1)\<le>x^2/2"
proof -
  have bound: "abs (sin (x/2))^2\<le>abs (x/2)^2"
    by (rule power_mono[OF abs_sin_x_le_abs_x]) simp
  have sq: "(sin (x/2))^2\<le>x^2/4" using bound by (simp add: power_divide)
  have co: "cos x=1-2*(sin (x/2))^2" using cos_double_sin[of "x/2"] by simp
  have absid: "abs (cos x-1)=2*(sin (x/2))^2" by (simp add: co)
  show ?thesis using absid sq by linarith
qed

lemma small_cosine_integrand:
  fixes x :: real
  assumes "0<x"
  shows "abs ((cos x-1)/x)\<le>x/2"
proof -
  have "abs (cos x-1)/x\<le>(x^2/2)/x"
    by (rule divide_right_mono[OF cosine_quadratic_remainder]) (use assms in linarith)
  then show ?thesis using assms by (simp add: abs_divide power2_eq_square)
qed

lemma logarithmic_cosine_derivative:
  fixes d L t :: real
  shows "((\<lambda>x. cos (d*exp (-L*x))) has_real_derivative
    (d*L*exp (-L*t) * sin (d*exp (-L*t)))) (at t)"
  by (auto intro!: derivative_eq_intros simp: algebra_simps)

lemma logarithmic_cosine_continuous:
  "continuous_on S (\<lambda>t::real. cos (d*exp (-L*t)))"
  by (intro continuous_intros)

lemma cell_integral_error:
  fixes f :: "real \<Rightarrow> real"
  assumes ab: "a\<le>b" and int: "f integrable_on {a..b}"
    and bound: "\<And>t. t\<in>{a..b} \<Longrightarrow> abs (f a-f t)\<le>B"
  shows "abs ((b-a)*f a-integral {a..b} f)\<le>(b-a)*B"
proof -
  have ii: "(\<lambda>t. f a-f t) integrable_on {a..b}"
    by (intro integrable_diff integrable_const_ivl int)
  have id: "integral {a..b} (\<lambda>t. f a-f t)=(b-a)*f a-integral {a..b} f"
    using Henstock_Kurzweil_Integration.integral_diff[where f="\<lambda>_. f a" and g=f and S="{a..b}",
      OF integrable_const_ivl int]
      ab by simp
  have "norm (integral {a..b} (\<lambda>t. f a-f t))\<le>integral {a..b} (\<lambda>_. B)"
    by (rule integral_norm_bound_integral[OF ii integrable_const_ivl]; simp add: bound)
  then show ?thesis using ab by (simp add: id)
qed

end
