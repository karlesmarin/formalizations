(* Title: Derivative bounds imply bounds for weighted regression
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Regression_Calculus
  imports TAF_Secants TAF_Mixture_Entropy
begin

lemma derivative_secant_bounds:
  fixes F F' :: "real \<Rightarrow> real"
  assumes d: "\<And>x. (F has_real_derivative F' x) (at x)"
    and low: "\<And>x. a\<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> lo\<le>F' x"
    and high: "\<And>x. a\<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> F' x\<le>hi"
    and u: "a\<le>u" "u\<le>b" and v: "a\<le>v" "v\<le>b"
  shows "lo*(u-v)^2\<le>(u-v)*(F u-F v)"
    "(u-v)*(F u-F v)\<le>hi*(u-v)^2"
proof -
  have ordered: "lo*(y-x)^2\<le>(y-x)*(F y-F x) \<and>
    (y-x)*(F y-F x)\<le>hi*(y-x)^2"
    if xy: "x<y" and range: "a\<le>x" "y\<le>b" for x y
  proof -
    obtain z where z: "x<z" "z<y" "F y-F x=(y-x)*F' z"
      using MVT2[OF xy, where f=F and f'=F'] d by blast
    have l: "lo\<le>F' z" and h: "F' z\<le>hi" using low high z range by auto
    have ll: "(y-x)^2*lo\<le>(y-x)^2*F' z"
      by (rule mult_left_mono[OF l]) simp
    have hh: "(y-x)^2*F' z\<le>(y-x)^2*hi"
      by (rule mult_left_mono[OF h]) simp
    show ?thesis using ll hh by (simp add: z(3) power2_eq_square mult.commute mult.left_commute mult.assoc)
  qed
  show "lo*(u-v)^2\<le>(u-v)*(F u-F v)"
    "(u-v)*(F u-F v)\<le>hi*(u-v)^2"
    using ordered[of u v] ordered[of v u] u v
    by (cases "u=v"; cases "u<v"; auto simp: power2_eq_square algebra_simps)+
qed

context finite_probability
begin

lemma regression_derivative_bounds:
  assumes var: "0<fw_var S p x"
    and d: "\<And>t. (F has_real_derivative F' t) (at t)"
    and low: "\<And>t. a\<le>t \<Longrightarrow> t\<le>b \<Longrightarrow> lo\<le>F' t"
    and high: "\<And>t. a\<le>t \<Longrightarrow> t\<le>b \<Longrightarrow> F' t\<le>hi"
    and range: "\<And>i. i\<in>S \<Longrightarrow> a\<le>x i" "\<And>i. i\<in>S \<Longrightarrow> x i\<le>b"
  shows "lo\<le>fw_cov S p x (\<lambda>i. F (x i))/fw_var S p x"
    "fw_cov S p x (\<lambda>i. F (x i))/fw_var S p x\<le>hi"
proof -
  have pl: "lo*(x i-x j)^2\<le>(x i-x j)*(F (x i)-F (x j))" if "i\<in>S" "j\<in>S" for i j
    by (rule derivative_secant_bounds(1)[where F=F and F'=F' and a=a and b=b and lo=lo and hi=hi,
        OF d low high]; use that range in auto)
  have ph: "(x i-x j)*(F (x i)-F (x j))\<le>hi*(x i-x j)^2" if "i\<in>S" "j\<in>S" for i j
    by (rule derivative_secant_bounds(2)[where F=F and F'=F' and a=a and b=b and lo=lo and hi=hi,
        OF d low high]; use that range in auto)
  show "lo\<le>fw_cov S p x (\<lambda>i. F (x i))/fw_var S p x"
    by (rule weighted_secant_bounds(1)[where x=x and y="\<lambda>i. F (x i)", OF var pl ph])
  show "fw_cov S p x (\<lambda>i. F (x i))/fw_var S p x\<le>hi"
    by (rule weighted_secant_bounds(2)[where x=x and y="\<lambda>i. F (x i)", OF var pl ph])
qed

end

context finite_exp_family
begin

lemma mixture_regression_bounds:
  assumes p: "finite_probability I w" and var: "0<fw_var I w x"
    and range: "\<And>i. i\<in>I \<Longrightarrow> l\<le>x i" "\<And>i. i\<in>I \<Longrightarrow> x i\<le>u"
  shows "emean u\<le>log_slope I w x (\<lambda>i. mom 0 (x i))"
    "log_slope I w x (\<lambda>i. mom 0 (x i))\<le>emean l"
proof -
  interpret p: finite_probability I w by (rule p)
  have deriv: "((\<lambda>x. -ln (mom 0 x)) has_real_derivative emean t) (at t)" for t
    using DERIV_minus[OF log_partition_derivative[of t]] by simp
  have bounds: "emean u\<le>fw_cov I w x (\<lambda>i. -ln (mom 0 (x i)))/fw_var I w x"
    "fw_cov I w x (\<lambda>i. -ln (mom 0 (x i)))/fw_var I w x\<le>emean l"
    by (rule p.regression_derivative_bounds[OF var deriv];
        auto intro: mean_nonincreasing range)+
  have sign: "fw_cov I w x (\<lambda>i. -ln (mom 0 (x i))) =
    -fw_cov I w x (\<lambda>i. ln (mom 0 (x i)))"
    by (simp add: fw_cov_def fw_mean_def sum_negf)
  show "emean u\<le>log_slope I w x (\<lambda>i. mom 0 (x i))"
    "log_slope I w x (\<lambda>i. mom 0 (x i))\<le>emean l"
    using bounds sign p.slope_covariance[where A="\<lambda>i. mom 0 (x i)" and x=x] by simp_all
qed

end
end
