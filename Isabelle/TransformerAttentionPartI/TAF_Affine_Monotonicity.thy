(* Title: Strict parameter response of the affine instrumental slope
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Affine_Monotonicity
  imports TAF_Affine_Bounds
begin

definition affine_slope where
  "affine_slope S p x a b l = fw_cov S p x (\<lambda>i. ln (a*l*exp (x i)+b))/fw_var S p x"

context finite_probability
begin

lemma regression_has_derivative:
  assumes d: "\<And>i. i\<in>S \<Longrightarrow> ((\<lambda>t. F t i) has_real_derivative (D i)) (at t)"
  shows "((\<lambda>t. fw_cov S p x (F t)/fw_var S p x) has_real_derivative
    (fw_cov S p x D/fw_var S p x)) (at t)"
proof -
  have ds: "((\<lambda>t. \<Sum>i\<in>S. p i*(x i-fw_mean S p x)*F t i) has_real_derivative
      (\<Sum>i\<in>S. p i*(x i-fw_mean S p x)*D i)) (at t)"
    by (intro DERIV_sum DERIV_cmult; rule d)
  have cf: "(\<lambda>t. fw_cov S p x (F t))=(\<lambda>t. \<Sum>i\<in>S. p i*(x i-fw_mean S p x)*F t i)"
    by (rule ext; rule covariance_centered)
  have cd: "fw_cov S p x D=(\<Sum>i\<in>S. p i*(x i-fw_mean S p x)*D i)"
    by (rule covariance_centered)
  show ?thesis using DERIV_cdivide[OF ds, where c="fw_var S p x"]
    by (simp only: covariance_centered)
qed

lemma affine_offset_derivative:
  assumes a: "0<a" and b: "0<b" and l: "0<l"
  shows "((\<lambda>b. affine_slope S p x a b l) has_real_derivative
    (fw_cov S p x (\<lambda>i. 1/(a*l*exp (x i)+b))/fw_var S p x)) (at b)"
proof -
  have al: "0<a*l" by (rule mult_pos_pos[OF a l])
  have di: "((\<lambda>b. ln (a*l*exp (x i)+b)) has_real_derivative (1/(a*l*exp (x i)+b))) (at b)" for i
    using affine_log_offset_derivative[OF al b, where x="x i"] by (simp only: affine_log_def)
  show ?thesis unfolding affine_slope_def by (rule regression_has_derivative; rule di)
qed

lemma affine_scale_derivative:
  assumes a: "0<a" and b: "0<b" and l: "0<l"
  shows "((\<lambda>l. affine_slope S p x a b l) has_real_derivative
    (fw_cov S p x (\<lambda>i. a*exp (x i)/(a*l*exp (x i)+b))/fw_var S p x)) (at l)"
  unfolding affine_slope_def
  by (rule regression_has_derivative; rule affine_log_scale_derivative[OF a b l])

lemma affine_offset_derivative_negative:
  assumes var: "0<fw_var S p x" and a: "0<a" and b: "0<b" and l: "0<l"
  shows "fw_cov S p x (\<lambda>i. 1/(a*l*exp (x i)+b))/fw_var S p x<0"
proof -
  have al: "0<a*l" by (rule mult_pos_pos[OF a l])
  have pos: "0<a*l*exp z+b" for z using a b l by (intro add_pos_pos mult_pos_pos) auto
  have order: "-(1/(a*l*exp (x i)+b)) < -(1/(a*l*exp (x j)+b))"
    if "i\<in>S" "j\<in>S" "x i<x j" for i j
  proof -
    have ex: "exp (x i)<exp (x j)" using that(3) by simp
    have dd: "a*l*exp (x i)+b<a*l*exp (x j)+b"
      using mult_strict_left_mono[OF ex al] by linarith
    have recip: "1/(a*l*exp (x j)+b)<1/(a*l*exp (x i)+b)"
      using dd by (simp only: pos_divide_less_eq[OF pos[of "x j"]] times_divide_eq_left
          pos_less_divide_eq[OF pos[of "x i"]] mult_1_left)
    then show ?thesis by linarith
  qed
  have cv: "0<fw_cov S p x (\<lambda>i. -(1/(a*l*exp (x i)+b)))"
    by (rule ordered_covariance_positive[OF var order])
  have neg: "fw_cov S p x (\<lambda>i. -(1/(a*l*exp (x i)+b))) =
    -fw_cov S p x (\<lambda>i. 1/(a*l*exp (x i)+b))"
    using covariance_scale_y[where c="-1" and x=x and y="\<lambda>i. 1/(a*l*exp (x i)+b)"] by simp
  have "fw_cov S p x (\<lambda>i. 1/(a*l*exp (x i)+b))<0" using cv neg by linarith
  then show ?thesis by (rule divide_neg_pos[OF _ var])
qed

lemma affine_scale_derivative_positive:
  assumes var: "0<fw_var S p x" and a: "0<a" and b: "0<b" and l: "0<l"
  shows "0<fw_cov S p x (\<lambda>i. a*exp (x i)/(a*l*exp (x i)+b))/fw_var S p x"
proof -
  have al: "0<a*l" by (rule mult_pos_pos[OF a l])
  have pos: "0<a*l*exp z+b" for z using a b l by (intro add_pos_pos mult_pos_pos) auto
  have numerator: "a*l*exp z=(a*exp z)*l" for z
    by (simp add: mult.commute mult.left_commute mult.assoc)
  have id: "a*exp z/(a*l*exp z+b)=(a*l*exp z/(a*l*exp z+b))/l" for z
    using l by (simp only: divide_divide_eq_left numerator; simp)
  have order: "a*exp (x i)/(a*l*exp (x i)+b)<a*exp (x j)/(a*l*exp (x j)+b)"
    if "i\<in>S" "j\<in>S" "x i<x j" for i j
    by (simp only: id; rule divide_strict_right_mono[OF affine_elasticity_increasing[OF al b that(3)] l])
  have cv: "0<fw_cov S p x (\<lambda>i. a*exp (x i)/(a*l*exp (x i)+b))"
    by (rule ordered_covariance_positive[OF var order])
  show ?thesis by (rule divide_pos_pos[OF cv var])
qed

lemma affine_offset_strict_decrease:
  assumes var: "0<fw_var S p x" and a: "0<a" and b: "0<b1" and l: "0<l" and order: "b1<b2"
  shows "affine_slope S p x a b2 l<affine_slope S p x a b1 l"
proof (rule DERIV_neg_imp_decreasing[OF order])
  fix t assume t: "b1\<le>t" "t\<le>b2"
  have tp: "0<t" using b t by linarith
  show "\<exists>y. ((\<lambda>b. affine_slope S p x a b l) has_real_derivative y) (at t) \<and> y<0"
    using affine_offset_derivative[OF a tp l] affine_offset_derivative_negative[OF var a tp l] by blast
qed

lemma affine_scale_strict_increase:
  assumes var: "0<fw_var S p x" and a: "0<a" and b: "0<b" and l: "0<l1" and order: "l1<l2"
  shows "affine_slope S p x a b l1<affine_slope S p x a b l2"
proof (rule DERIV_pos_imp_increasing[OF order])
  fix t assume t: "l1\<le>t" "t\<le>l2"
  have tp: "0<t" using l t by linarith
  show "\<exists>y. ((\<lambda>l. affine_slope S p x a b l) has_real_derivative y) (at t) \<and> 0<y"
    using affine_scale_derivative[OF a b tp] affine_scale_derivative_positive[OF var a b tp] by blast
qed

end
end
