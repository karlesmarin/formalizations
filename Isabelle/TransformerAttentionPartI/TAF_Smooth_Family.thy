(* Title: All orders of continuous differentiability of the finite family
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Smooth_Family
  imports TAF_KL_Bound "HOL-Analysis.Higher_Differentiability_Multi"
begin

lemma real_derivative_global_differentiable:
  assumes d: "\<And>x::real. (f has_real_derivative D x) (at x)"
  shows "f differentiable_on UNIV"
proof -
  have "f field_differentiable (at x)" for x
    unfolding field_differentiable_def using d[of x] by blast
  then show ?thesis using field_differentiable_imp_differentiable
    by (auto simp: differentiable_on_eq_differentiable_at)
qed

context finite_exp_family
begin

lemma moment_deriv_function:
  "deriv (mom j)=(\<lambda>t. -mom (Suc j) t)"
  by (rule ext; rule DERIV_imp_deriv[OF moment_derivative])

lemma moment_Ck: "Ck_on n (mom j) UNIV"
proof (induction n arbitrary: j)
  case 0
  show ?case by (auto simp: Ck_on_0_iff intro: continuous_at_imp_continuous_on moment_continuous)
next
  case (Suc n)
  have diff: "(mom j) differentiable_on UNIV"
    by (rule real_derivative_global_differentiable; rule moment_derivative)
  have dC: "Ck_on n (deriv (mom j)) UNIV"
    by (simp only: moment_deriv_function; rule Ck_on_neg[OF Suc.IH])
  show ?case using diff dC by (simp add: Ck_on_real_iff C_k_on_Suc_iff)
qed

lemma smooth_mom0_nonzero: "mom 0 t\<noteq>0"
  using mom0_positive[of t] by linarith

lemma mean_Ck: "Ck_on n emean UNIV"
  unfolding emean_def[abs_def]
  by (intro Ck_on_divide moment_Ck; simp add: smooth_mom0_nonzero)

lemma variance_Ck: "Ck_on n evar UNIV"
  unfolding evar_def[abs_def]
  by (intro Ck_on_sub Ck_on_divide Ck_on_pow moment_Ck mean_Ck;
      simp add: smooth_mom0_nonzero)

lemma log_partition_deriv_function:
  "deriv (\<lambda>t. ln (mom 0 t))=(\<lambda>t. -emean t)"
  by (rule ext; rule DERIV_imp_deriv[OF log_partition_derivative])

lemma log_partition_Ck: "Ck_on n (\<lambda>t. ln (mom 0 t)) UNIV"
proof (cases n)
  case 0
  have cont: "isCont (\<lambda>t. ln (mom 0 t)) x" for x
    using log_partition_derivative[of x] by (rule DERIV_isCont)
  show ?thesis using 0
    by (auto simp: Ck_on_0_iff intro: continuous_at_imp_continuous_on cont)
next
  case (Suc k)
  have diff: "(\<lambda>t. ln (mom 0 t)) differentiable_on UNIV"
    by (rule real_derivative_global_differentiable; rule log_partition_derivative)
  have dC: "Ck_on k (deriv (\<lambda>t. ln (mom 0 t))) UNIV"
    by (simp only: log_partition_deriv_function; rule Ck_on_neg[OF mean_Ck])
  show ?thesis using diff dC Suc by (simp add: Ck_on_real_iff C_k_on_Suc_iff)
qed

lemma entropy_Ck: "Ck_on n canonical_entropy UNIV"
  unfolding canonical_entropy_def[abs_def]
  by (intro Ck_on_add log_partition_Ck Ck_on_mult Ck_on_id mean_Ck; simp)

lemma heat_capacity_Ck: "Ck_on n (\<lambda>t. t^2*evar t) UNIV"
  by (intro Ck_on_mult Ck_on_pow Ck_on_id variance_Ck; simp)

lemma weight_Ck:
  assumes i: "i\<in>S"
  shows "Ck_on n (\<lambda>t. ew t i) UNIV"
proof -
  interpret single: finite_exp_family "{i}" a E
    by (unfold_locales; use a_pos[OF i] in auto)
  show ?thesis using single.moment_Ck[where j=0 and n=n]
    by (simp add: single.mom_def[abs_def] ew_def[abs_def])
qed

lemma probability_Ck:
  assumes "i\<in>S"
  shows "Ck_on n (\<lambda>t. ep t i) UNIV"
  unfolding ep_def
  by (intro Ck_on_divide weight_Ck[OF assms] moment_Ck; simp add: smooth_mom0_nonzero)

lemma finite_family_all_orders:
  "\<forall>n. Ck_on n (mom 0) UNIV \<and> Ck_on n (\<lambda>t. ln (mom 0 t)) UNIV \<and>
    Ck_on n emean UNIV \<and> Ck_on n evar UNIV \<and> Ck_on n canonical_entropy UNIV \<and>
    Ck_on n (\<lambda>t. t^2*evar t) UNIV"
  by (intro allI conjI moment_Ck log_partition_Ck mean_Ck variance_Ck entropy_Ck heat_capacity_Ck)

end
end
