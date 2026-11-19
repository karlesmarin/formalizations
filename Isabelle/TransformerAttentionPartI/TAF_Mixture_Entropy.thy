(* Title: Strict mixture curvature and finite entropy identities
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Mixture_Entropy
  imports TAF_Exponential_Family TAF_Truncation
begin

context finite_exp_family
begin

lemma variance_zero_forces_constant:
  assumes z: "evar t=0" and i: "i\<in>S"
  shows "E i=emean t"
proof -
  have nn: "0 \<le> ep t j*(E j-fw_mean S (ep t) E)^2" if "j\<in>S" for j
    using ep_positive[OF that, of t] by (intro mult_nonneg_nonneg) auto
  have total: "(\<Sum>j\<in>S. ep t j*(E j-fw_mean S (ep t) E)^2)=0"
    using z ep_variance[of t] by (simp add: fw_var_def)
  have "ep t i*(E i-fw_mean S (ep t) E)^2=0"
    by (rule sum_nonneg_0[OF finite_S nn total i])
  then show ?thesis using ep_positive[OF i, of t] by (simp add: ep_mean)
qed

lemma strict_variance:
  assumes i: "i\<in>S" and j: "j\<in>S" and diff: "E i\<noteq>E j"
  shows "0 < evar t"
proof -
  have "evar t\<noteq>0"
  proof
    assume z: "evar t=0"
    have ei: "E i=emean t" by (rule variance_zero_forces_constant[OF z i])
    have ej: "E j=emean t" by (rule variance_zero_forces_constant[OF z j])
    show False using ei ej diff by simp
  qed
  then show ?thesis using evar_nonnegative[of t] by linarith
qed

lemma strict_mean_decrease:
  assumes i: "i\<in>S" and j: "j\<in>S" and diff: "E i\<noteq>E j" and uv: "u<v"
  shows "emean v < emean u"
proof (rule DERIV_neg_imp_decreasing[OF uv])
  fix x assume "u\<le>x" "x\<le>v"
  have pos: "0<evar x" by (rule strict_variance[OF i j diff])
  show "\<exists>y. (emean has_real_derivative y) (at x) \<and> y<0"
    by (intro exI[where x="-evar x"] conjI mean_derivative; use pos in linarith)
qed

lemma mean_energy_bounds:
  assumes lo: "\<And>i. i\<in>S \<Longrightarrow> l\<le>E i"
    and hi: "\<And>i. i\<in>S \<Longrightarrow> E i\<le>u"
  shows "l\<le>emean t" "emean t\<le>u"
proof -
  interpret p: finite_probability S "ep t" by (rule ep_probability)
  show "l\<le>emean t" using p.mean_bounds(1)[where x=E and a=l and b=u, OF lo hi] ep_mean[of t] by simp
  show "emean t\<le>u" using p.mean_bounds(2)[where x=E and a=l and b=u, OF lo hi] ep_mean[of t] by simp
qed

lemma log_probability:
  assumes "i\<in>S"
  shows "ln (ep t i) = ln (a i)-t*E i-ln (mom 0 t)"
  using a_pos[OF assms] mom0_positive[of t]
  by (simp add: ep_def ew_def ln_divide_pos ln_mult_pos)

lemma kl_partition_identity:
  "finite_kl S (ep g) (ep h) = ereal ((h-g)*emean g+ln (mom 0 h)-ln (mom 0 g))"
proof -
  interpret p: finite_probability S "ep g" by (rule ep_probability)
  have support: "\<not> (\<exists>i\<in>S. 0 < ep g i \<and> ep h i=0)"
  proof
    assume "\<exists>i\<in>S. 0 < ep g i \<and> ep h i=0"
    then obtain i where i: "i\<in>S" "ep h i=0" by blast
    have "0<ep h i" by (rule ep_positive[OF i(1)])
    then show False using i(2) by simp
  qed
  have point_eq: "ep g i*ln (ep g i/ep h i) =
    (h-g)*(ep g i*E i)+(ln (mom 0 h)-ln (mom 0 g))*ep g i" if "i\<in>S" for i
    using ep_positive[OF that, of g] ep_positive[OF that, of h]
    by (simp add: ln_divide_pos log_probability[OF that] algebra_simps)
  have sumpt: "(\<Sum>i\<in>S. ep g i*ln (ep g i/ep h i)) =
    (\<Sum>i\<in>S. (h-g)*(ep g i*E i)+(ln (mom 0 h)-ln (mom 0 g))*ep g i)"
    by (rule sum.cong[OF refl]; rule point_eq)
  have eq: "(\<Sum>i\<in>S. ep g i*ln (ep g i/ep h i)) =
    (h-g)*emean g+ln (mom 0 h)-ln (mom 0 g)"
    using sumpt
    by (simp add: sum.distrib sum_distrib_left[symmetric] ep_sum fw_mean_def[symmetric] ep_mean)
  show ?thesis by (simp add: finite_kl_def support eq)
qed

definition canonical_entropy :: "real \<Rightarrow> real" where
  "canonical_entropy t = ln (mom 0 t)+t*emean t"

lemma entropy_identity:
  assumes unit: "\<And>i. i\<in>S \<Longrightarrow> a i=1"
  shows "-(\<Sum>i\<in>S. ep t i*ln (ep t i)) = canonical_entropy t"
proof -
  have point_eq: "ep t i*ln (ep t i) = -t*(ep t i*E i)-ln (mom 0 t)*ep t i" if "i\<in>S" for i
    by (simp add: log_probability[OF that] unit[OF that] algebra_simps)
  have sumpt: "(\<Sum>i\<in>S. ep t i*ln (ep t i)) =
    (\<Sum>i\<in>S. -t*(ep t i*E i)-ln (mom 0 t)*ep t i)"
    by (rule sum.cong[OF refl]; rule point_eq)
  show ?thesis using sumpt
    by (simp add: canonical_entropy_def sum_subtractf sum_negf sum_distrib_left[symmetric]
        ep_sum fw_mean_def[symmetric] ep_mean)
qed

lemma entropy_derivative:
  "(canonical_entropy has_real_derivative (-t*evar t)) (at t)"
proof -
  have prod: "((\<lambda>u. u*emean u) has_real_derivative (emean t-evar t*t)) (at t)"
    using DERIV_mult[OF DERIV_ident mean_derivative[of t]] by simp
  have "((\<lambda>u. ln (mom 0 u)+u*emean u) has_real_derivative (-t*evar t)) (at t)"
    using DERIV_add[OF log_partition_derivative[of t] prod]
    by (simp add: algebra_simps)
  then show ?thesis unfolding canonical_entropy_def[abs_def] .
qed

lemma entropy_decreasing_positive:
  assumes "0\<le>u" "u\<le>v"
  shows "canonical_entropy v\<le>canonical_entropy u"
proof (rule DERIV_nonpos_imp_nonincreasing[OF assms(2)])
  fix x assume x: "u\<le>x" "x\<le>v"
  have xp: "0\<le>x" using x assms by linarith
  have nn: "0\<le>x*evar x" by (rule mult_nonneg_nonneg[OF xp evar_nonnegative])
  have sign: "-x*evar x\<le>0" using nn by simp
  show "\<exists>y. (canonical_entropy has_real_derivative y) (at x) \<and> y\<le>0"
    using entropy_derivative[of x] sign by blast
qed

lemma entropy_increasing_negative:
  assumes "u\<le>v" "v\<le>0"
  shows "canonical_entropy u\<le>canonical_entropy v"
proof (rule DERIV_nonneg_imp_nondecreasing[OF assms(1)])
  fix x assume x: "u\<le>x" "x\<le>v"
  have xp: "0\<le>-x" using x assms by linarith
  have sign: "0\<le>-x*evar x" by (rule mult_nonneg_nonneg[OF xp evar_nonnegative])
  show "\<exists>y. (canonical_entropy has_real_derivative y) (at x) \<and> 0\<le>y"
    using entropy_derivative[of x] sign by blast
qed

lemma heat_capacity_bound:
  assumes "0\<le>L" "\<And>i. i\<in>S \<Longrightarrow> 0\<le>E i"
    "\<And>i. i\<in>S \<Longrightarrow> E i\<le>L"
  shows "0\<le>t^2*evar t" "t^2*evar t\<le>t^2*L^2/4"
  using evar_nonnegative[of t] mult_left_mono[OF variance_bound[OF assms, of t], of "t^2"]
  by (auto intro: mult_nonneg_nonneg simp: divide_simps)

end
end
