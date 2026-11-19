(* Title: Strict weighted-regression bounds for affine exposure
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Affine_Bounds
  imports TAF_Regression_Calculus TAF_Strict_Covariance
begin

context finite_probability
begin

lemma covariance_diff_y:
  "fw_cov S p x (\<lambda>i. y i-z i)=fw_cov S p x y-fw_cov S p x z"
  by (simp add: fw_cov_def fw_mean_def algebra_simps sum_subtractf)

lemma covariance_scale_y:
  "fw_cov S p x (\<lambda>i. c*y i)=c*fw_cov S p x y"
  by (simp add: fw_cov_def fw_mean_def algebra_simps sum_distrib_left[symmetric])

lemma ordered_covariance_positive:
  assumes var: "0<fw_var S p x"
    and order: "\<And>i j. i\<in>S \<Longrightarrow> j\<in>S \<Longrightarrow> x i<x j \<Longrightarrow> y i<y j"
  shows "0<fw_cov S p x y"
proof (rule strictly_comonotone_covariance[OF var])
  fix i j assume i: "i\<in>S" and j: "j\<in>S" and neq: "x i\<noteq>x j"
  show "0<(x i-x j)*(y i-y j)"
  proof (cases "x i<x j")
    case True
    have yy: "y i<y j" by (rule order[OF i j True])
    show ?thesis by (intro mult_neg_neg; use True yy in linarith)
  next
    case False
    have xx: "x j<x i" using False neq by auto
    have yy: "y j<y i" by (rule order[OF j i xx])
    show ?thesis by (intro mult_pos_pos; use xx yy in linarith)
  qed
qed

lemma regression_strict_lower:
  assumes var: "0<fw_var S p x"
    and d: "\<And>t. (F has_real_derivative F' t) (at t)"
    and low: "\<And>t. a<t \<Longrightarrow> t<b \<Longrightarrow> lo<F' t"
    and range: "\<And>i. i\<in>S \<Longrightarrow> a\<le>x i" "\<And>i. i\<in>S \<Longrightarrow> x i\<le>b"
  shows "lo<fw_cov S p x (\<lambda>i. F (x i))/fw_var S p x"
proof -
  let ?G = "\<lambda>t. F t-lo*t"
  have dg: "(?G has_real_derivative (F' t-lo)) (at t)" for t
    using d[of t] by (auto intro!: derivative_eq_intros)
  have order: "?G (x i)<?G (x j)" if ij: "i\<in>S" "j\<in>S" "x i<x j" for i j
  proof -
    obtain z where z: "x i<z" "z<x j" "?G (x j)-?G (x i)=(x j-x i)*(F' z-lo)"
      using MVT2[OF ij(3), where f="?G" and f'="\<lambda>t. F' t-lo"] dg by blast
    have zr: "a<z" "z<b" using range[OF ij(1)] range[OF ij(2)] z by auto
    have zp: "0<F' z-lo" using low[OF zr] by linarith
    have "0<(x j-x i)*(F' z-lo)" by (intro mult_pos_pos zp; use ij in linarith)
    then show ?thesis using z(3) by linarith
  qed
  have cv: "0<fw_cov S p x (\<lambda>i. F (x i)-lo*x i)"
    by (rule ordered_covariance_positive[OF var order])
  have id: "fw_cov S p x (\<lambda>i. F (x i)-lo*x i)=
      fw_cov S p x (\<lambda>i. F (x i))-lo*fw_var S p x"
    by (simp only: covariance_diff_y covariance_scale_y covariance_self)
  show ?thesis using cv id var by (simp add: less_divide_eq)
qed

lemma regression_strict_upper:
  assumes var: "0<fw_var S p x"
    and d: "\<And>t. (F has_real_derivative F' t) (at t)"
    and high: "\<And>t. a<t \<Longrightarrow> t<b \<Longrightarrow> F' t<hi"
    and range: "\<And>i. i\<in>S \<Longrightarrow> a\<le>x i" "\<And>i. i\<in>S \<Longrightarrow> x i\<le>b"
  shows "fw_cov S p x (\<lambda>i. F (x i))/fw_var S p x<hi"
proof -
  have dn: "((\<lambda>t. -F t) has_real_derivative (-F' t)) (at t)" for t
    by (rule DERIV_minus[OF d])
  have neglo: "-hi < -F' t" if "a<t" "t<b" for t using high[OF that] by linarith
  have res: "-hi<fw_cov S p x (\<lambda>i. -F (x i))/fw_var S p x"
    by (rule regression_strict_lower[where F="\<lambda>t. -F t" and F'="\<lambda>t. -F' t" and a=a and b=b,
        OF var dn neglo range])
  have neg: "fw_cov S p x (\<lambda>i. -F (x i))=-fw_cov S p x (\<lambda>i. F (x i))"
    using covariance_scale_y[where c="-1" and y="\<lambda>i. F (x i)" and x=x] by simp
  show ?thesis using res by (simp add: neg)
qed

lemma affine_regression_strict_bounds:
  assumes var: "0<fw_var S p x" and a: "0<a" and b: "0<b"
    and range: "\<And>i. i\<in>S \<Longrightarrow> l\<le>x i" "\<And>i. i\<in>S \<Longrightarrow> x i\<le>u"
  shows "a*exp l/(a*exp l+b)<fw_cov S p x (\<lambda>i. affine_log a b (x i))/fw_var S p x"
    "fw_cov S p x (\<lambda>i. affine_log a b (x i))/fw_var S p x<a*exp u/(a*exp u+b)"
proof -
  have d: "((\<lambda>t. affine_log a b t) has_real_derivative (a*exp t/(a*exp t+b))) (at t)" for t
    by (rule affine_log_derivative[OF a b])
  have low: "a*exp l/(a*exp l+b)<a*exp t/(a*exp t+b)" if "l<t" "t<u" for t
    by (rule affine_elasticity_increasing[OF a b that(1)])
  have high: "a*exp t/(a*exp t+b)<a*exp u/(a*exp u+b)" if "l<t" "t<u" for t
    by (rule affine_elasticity_increasing[OF a b that(2)])
  show "a*exp l/(a*exp l+b)<fw_cov S p x (\<lambda>i. affine_log a b (x i))/fw_var S p x"
    by (rule regression_strict_lower[where F="affine_log a b" and F'="\<lambda>t. a*exp t/(a*exp t+b)"
        and a=l and b=u and lo="a*exp l/(a*exp l+b)", OF var d low range])
  show "fw_cov S p x (\<lambda>i. affine_log a b (x i))/fw_var S p x<a*exp u/(a*exp u+b)"
    by (rule regression_strict_upper[where F="affine_log a b" and F'="\<lambda>t. a*exp t/(a*exp t+b)"
        and a=l and b=u and hi="a*exp u/(a*exp u+b)", OF var d high range])
qed

end
end
