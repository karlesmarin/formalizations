(* Title: Endpoint limits and amplitude invariance of affine exposure
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Affine_Limits
  imports TAF_Affine_Monotonicity
begin

definition affine_elasticity where
  "affine_elasticity a b r z=a*r*exp z/(a*r*exp z+b)"

lemma affine_elasticity_ratio:
  fixes a b r z :: real
  assumes a: "0<a"
  shows "affine_elasticity a b r z=r/(r+b/(a*exp z))"
proof -
  have q: "a*exp z\<noteq>0" using a by simp
  have num: "a*r*exp z=(a*exp z)*r" by (simp add: algebra_simps)
  have den: "a*r*exp z+b=(a*exp z)*(r+b/(a*exp z))"
    using q by (simp add: algebra_simps)
  have eq: "a*r*exp z/(a*r*exp z+b)=((a*exp z)*r)/((a*exp z)*(r+b/(a*exp z)))"
    by (rule arg_cong2[where f="\<lambda>u v::real. u/v", OF num den])
  show ?thesis unfolding affine_elasticity_def
    by (simp only: eq; use q in simp)
qed

lemma affine_elasticity_limit_zero:
  fixes a b z :: real
  assumes a: "0<a" and b: "0<b"
  shows "((\<lambda>r. affine_elasticity a b r z) \<longlongrightarrow> 0) (at_right 0)"
proof -
  have bp: "0<b/(a*exp z)" using a b by (intro divide_pos_pos mult_pos_pos) auto
  have "((\<lambda>r::real. r/(r+b/(a*exp z))) \<longlongrightarrow> 0/(0+b/(a*exp z))) (at_right 0)"
    by (intro tendsto_intros; use bp in auto)
  then show ?thesis by (simp only: affine_elasticity_ratio[OF a]) simp
qed

lemma affine_elasticity_limit_infinity:
  fixes a b z :: real
  assumes a: "0<a"
  shows "((\<lambda>r. affine_elasticity a b r z) \<longlongrightarrow> 1) at_top"
proof -
  let ?c = "b/(a*exp z)"
  have small: "((\<lambda>r::real. ?c/r) \<longlongrightarrow> 0) at_top"
    by (rule tendsto_divide_0[OF tendsto_const];
        rule filterlim_at_top_imp_at_infinity; rule filterlim_ident)
  have inv: "((\<lambda>r::real. 1/(1+?c/r)) \<longlongrightarrow> 1/(1+0)) at_top"
    by (intro tendsto_intros small; simp)
  have eq: "\<forall>\<^sub>F r::real in at_top. affine_elasticity a b r z=1/(1+?c/r)"
  proof (rule eventually_mono[OF eventually_gt_at_top[of "0::real"]])
    fix r :: real assume rp: "0<r"
    have den: "r+?c=r*(1+?c/r)" using rp by (simp add: algebra_simps)
    have quotient: "r/(r+?c)=1/(1+?c/r)"
      by (simp only: den; use rp in simp)
    show "affine_elasticity a b r z=1/(1+?c/r)"
      by (simp only: affine_elasticity_ratio[OF a]; rule quotient)
  qed
  show ?thesis by (subst tendsto_cong[OF eq]; use inv in simp)
qed

context finite_probability
begin

lemma covariance_constant_y: "fw_cov S p x (\<lambda>_. c)=0"
proof -
  have point: "(\<lambda>i. x i*c)=(\<lambda>i. c*x i)" by (rule ext; simp add: mult.commute)
  show ?thesis unfolding fw_cov_def
    by (simp only: point mean_const mean_scale; simp add: mult.commute)
qed

lemma affine_profile_slope:
  assumes a: "0<a" and b: "0<b" and c: "0<c" and r: "0<r"
  shows "log_slope S p x (\<lambda>i. c/(a*r*exp (x i)+b))=affine_slope S p x a b r"
proof -
  have den: "0<a*r*exp (x i)+b" for i using a b r
    by (intro add_pos_pos mult_pos_pos) auto
  have ratio: "log_slope S p x (\<lambda>i. c/(a*r*exp (x i)+b))=
    log_slope S p x (\<lambda>_. c)-log_slope S p x (\<lambda>i. a*r*exp (x i)+b)"
    by (rule log_slope_ratio; use c den in auto)
  show ?thesis using ratio constant_log_slope[where c=c and x=x]
    slope_covariance[where x=x and A="\<lambda>i. a*r*exp (x i)+b"]
    by (simp only: affine_slope_def)
qed

lemma affine_slope_endpoint_bounds:
  assumes var: "0<fw_var S p x" and a: "0<a" and b: "0<b" and r: "0<r"
    and range: "\<And>i. i\<in>S \<Longrightarrow> l\<le>x i" "\<And>i. i\<in>S \<Longrightarrow> x i\<le>u"
  shows "affine_elasticity a b r l<affine_slope S p x a b r"
    "affine_slope S p x a b r<affine_elasticity a b r u"
proof -
  have ar: "0<a*r" by (rule mult_pos_pos[OF a r])
  show "affine_elasticity a b r l<affine_slope S p x a b r"
    using affine_regression_strict_bounds(1)[where a="a*r" and b=b and x=x and l=l and u=u,
      OF var ar b range] by (simp only: affine_elasticity_def affine_slope_def affine_log_def)
  show "affine_slope S p x a b r<affine_elasticity a b r u"
    using affine_regression_strict_bounds(2)[where a="a*r" and b=b and x=x and l=l and u=u,
      OF var ar b range] by (simp only: affine_elasticity_def affine_slope_def affine_log_def)
qed

lemma affine_slope_limits:
  assumes var: "0<fw_var S p x" and a: "0<a" and b: "0<b"
    and range: "\<And>i. i\<in>S \<Longrightarrow> l\<le>x i" "\<And>i. i\<in>S \<Longrightarrow> x i\<le>u"
  shows "((\<lambda>r. affine_slope S p x a b r) \<longlongrightarrow> 0) (at_right 0)"
    "((\<lambda>r. affine_slope S p x a b r) \<longlongrightarrow> 1) at_top"
proof -
  have bounds: "affine_elasticity a b r l\<le>affine_slope S p x a b r \<and>
    affine_slope S p x a b r\<le>affine_elasticity a b r u" if "0<r" for r
    using affine_slope_endpoint_bounds[where x=x and a=a and b=b and r=r and l=l and u=u,
      OF var a b that range] by auto
  have ev0: "\<forall>\<^sub>F r::real in at_right 0. affine_elasticity a b r l\<le>affine_slope S p x a b r \<and>
    affine_slope S p x a b r\<le>affine_elasticity a b r u"
    using bounds by (auto simp: eventually_at_filter)
  have evinf: "\<forall>\<^sub>F r::real in at_top. affine_elasticity a b r l\<le>affine_slope S p x a b r \<and>
    affine_slope S p x a b r\<le>affine_elasticity a b r u"
    by (rule eventually_mono[OF eventually_gt_at_top[of "0::real"]]; rule bounds; assumption)
  have low0: "\<forall>\<^sub>F r::real in at_right 0. affine_elasticity a b r l\<le>affine_slope S p x a b r"
    by (rule eventually_mono[OF ev0]; blast)
  have high0: "\<forall>\<^sub>F r::real in at_right 0. affine_slope S p x a b r\<le>affine_elasticity a b r u"
    by (rule eventually_mono[OF ev0]; blast)
  have lowinf: "\<forall>\<^sub>F r::real in at_top. affine_elasticity a b r l\<le>affine_slope S p x a b r"
    by (rule eventually_mono[OF evinf]; blast)
  have highinf: "\<forall>\<^sub>F r::real in at_top. affine_slope S p x a b r\<le>affine_elasticity a b r u"
    by (rule eventually_mono[OF evinf]; blast)
  show "((\<lambda>r. affine_slope S p x a b r) \<longlongrightarrow> 0) (at_right 0)"
    by (rule tendsto_sandwich[OF low0 high0 affine_elasticity_limit_zero[OF a b] affine_elasticity_limit_zero[OF a b]])
  show "((\<lambda>r. affine_slope S p x a b r) \<longlongrightarrow> 1) at_top"
    by (rule tendsto_sandwich[OF lowinf highinf affine_elasticity_limit_infinity[OF a] affine_elasticity_limit_infinity[OF a]])
qed

end
end
