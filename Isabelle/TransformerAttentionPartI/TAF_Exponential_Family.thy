(* Title: Differentiation of a finite exponential family
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Exponential_Family
  imports TAF_Finite_Weights
begin

locale finite_exp_family =
  fixes S :: "'a set" and a E :: "'a \<Rightarrow> real"
  assumes finite_S: "finite S" and nonempty_S: "S \<noteq> {}"
    and a_pos: "\<And>i. i\<in>S \<Longrightarrow> 0 < a i"
begin

definition ew :: "real \<Rightarrow> 'a \<Rightarrow> real" where
  "ew t i = a i * exp (-t*E i)"

definition mom :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "mom k t = (\<Sum>i\<in>S. a i * (E i)^k * exp (-t*E i))"

definition ep :: "real \<Rightarrow> 'a \<Rightarrow> real" where
  "ep t i = ew t i / mom 0 t"

definition emean :: "real \<Rightarrow> real" where
  "emean t = mom 1 t / mom 0 t"

definition evar :: "real \<Rightarrow> real" where
  "evar t = mom 2 t / mom 0 t - (emean t)^2"

lemma ew_positive: "i\<in>S \<Longrightarrow> 0 < ew t i"
  by (simp add: ew_def a_pos)

lemma mom0_as_sum: "mom 0 t = sum (ew t) S"
  by (simp add: mom_def ew_def)

lemma mom0_positive: "0 < mom 0 t"
proof -
  have "sum (\<lambda>_. 0::real) S < sum (ew t) S"
    by (intro sum_strict_mono[OF finite_S nonempty_S]) (rule ew_positive)
  then show ?thesis by (simp add: mom0_as_sum)
qed

lemma ep_positive: "i\<in>S \<Longrightarrow> 0 < ep t i"
  by (simp add: ep_def divide_pos_pos ew_positive mom0_positive)

lemma ep_sum: "sum (ep t) S = 1"
  using mom0_positive[of t]
  by (simp add: ep_def sum_divide_distrib[symmetric] mom0_as_sum[symmetric])

lemma ep_probability: "finite_probability S (ep t)"
  by (unfold_locales; auto intro: finite_S less_imp_le[OF ep_positive] ep_sum)

lemma ep_moment:
  "fw_mean S (ep t) (\<lambda>i. (E i)^k) = mom k t / mom 0 t"
proof -
  have point_eq: "ep t i*(E i)^k =
      (a i*(E i)^k*exp (-t*E i))/mom 0 t" for i
    by (simp add: ep_def ew_def algebra_simps)
  show ?thesis by (simp add: fw_mean_def point_eq sum_divide_distrib[symmetric] mom_def)
qed

lemma ep_mean: "fw_mean S (ep t) E = emean t"
  using ep_moment[of t 1] by (simp add: emean_def)

lemma ep_variance: "fw_var S (ep t) E = evar t"
proof -
  interpret p: finite_probability S "ep t" by (rule ep_probability)
  show ?thesis using p.variance_moment[of E]
    by (simp add: ep_moment ep_mean evar_def)
qed

lemma evar_nonnegative: "0 \<le> evar t"
proof -
  interpret p: finite_probability S "ep t" by (rule ep_probability)
  show ?thesis using p.variance_nonneg[of E] by (simp add: ep_variance)
qed

lemma moment_derivative:
  "((\<lambda>u. mom k u) has_real_derivative (-mom (Suc k) t)) (at t)"
proof -
  have d: "((\<lambda>u. a i*(E i)^k*exp (-u*E i)) has_real_derivative
      (-a i*(E i)^(Suc k)*exp (-t*E i))) (at t)" for i
    by (auto intro!: derivative_eq_intros simp: algebra_simps power_Suc)
  have ds: "((\<lambda>u. \<Sum>i\<in>S. a i*(E i)^k*exp (-u*E i)) has_real_derivative
      (\<Sum>i\<in>S. -a i*(E i)^(Suc k)*exp (-t*E i))) (at t)"
    by (intro DERIV_sum) (rule d)
  show ?thesis using ds by (simp add: mom_def sum_negf)
qed

lemma mean_derivative:
  "(emean has_real_derivative (-evar t)) (at t)"
proof -
  have d0: "((\<lambda>u. mom 0 u) has_real_derivative (-mom 1 t)) (at t)"
    using moment_derivative[of 0 t] by simp
  have d1: "((\<lambda>u. mom 1 u) has_real_derivative (-mom 2 t)) (at t)"
    using moment_derivative[of 1 t] by (simp add: numeral_2_eq_2)
  have dz: "mom 0 t \<noteq> 0" using mom0_positive[of t] by simp
  have d: "((\<lambda>u. mom 1 u / mom 0 u) has_real_derivative
      ((-mom 2 t*mom 0 t-mom 1 t*(-mom 1 t))/(mom 0 t)^2)) (at t)"
    using d0 d1 dz by (auto intro!: derivative_eq_intros simp: power2_eq_square)
  have eq: "(-mom 2 t*mom 0 t-mom 1 t*(-mom 1 t))/(mom 0 t)^2 = -evar t"
    unfolding evar_def emean_def using dz
    by (simp add: divide_simps algebra_simps power2_eq_square)
  have hfun: "emean = (\<lambda>u. mom 1 u / mom 0 u)"
    by (simp add: fun_eq_iff emean_def)
  show ?thesis using d by (simp only: hfun eq)
qed

lemma log_partition_derivative:
  "((\<lambda>u. ln (mom 0 u)) has_real_derivative (-emean t)) (at t)"
proof -
  have d0: "((\<lambda>u. mom 0 u) has_real_derivative (-mom 1 t)) (at t)"
    using moment_derivative[of 0 t] by simp
  show ?thesis unfolding emean_def
    using d0 mom0_positive[of t] by (auto intro!: derivative_eq_intros simp: field_simps)
qed

lemma probability_derivative:
  "((\<lambda>u. ep u i) has_real_derivative (ep t i*(emean t-E i))) (at t)"
proof -
  have dw: "((\<lambda>u. ew u i) has_real_derivative (-E i*ew t i)) (at t)"
    unfolding ew_def by (auto intro!: derivative_eq_intros simp: algebra_simps)
  have d0: "((\<lambda>u. mom 0 u) has_real_derivative (-mom 1 t)) (at t)"
    using moment_derivative[of 0 t] by simp
  have dz: "mom 0 t \<noteq> 0" using mom0_positive[of t] by simp
  have d: "((\<lambda>u. ew u i / mom 0 u) has_real_derivative
      ((-E i*ew t i*mom 0 t-ew t i*(-mom 1 t))/(mom 0 t)^2)) (at t)"
    using dw d0 dz by (auto intro!: derivative_eq_intros simp: power2_eq_square)
  have eq: "(-E i*ew t i*mom 0 t-ew t i*(-mom 1 t))/(mom 0 t)^2 = ep t i*(emean t-E i)"
    unfolding ep_def emean_def using dz
    by (simp add: divide_simps algebra_simps power2_eq_square)
  have hfun: "(\<lambda>u. ep u i) = (\<lambda>u. ew u i / mom 0 u)"
    by (simp only: ep_def)
  show ?thesis using d by (simp only: hfun eq)
qed

lemma mean_nonincreasing:
  assumes "u \<le> v"
  shows "emean v \<le> emean u"
  by (rule deriv_nonpos_imp_antimono[where g'="\<lambda>t. -evar t"];
      auto intro: mean_derivative simp: evar_nonnegative assms)

lemma variance_bound:
  assumes "0 \<le> L" "\<And>i. i\<in>S \<Longrightarrow> 0 \<le> E i"
    "\<And>i. i\<in>S \<Longrightarrow> E i \<le> L"
  shows "evar t \<le> L^2/4"
proof -
  interpret p: finite_probability S "ep t" by (rule ep_probability)
  have b: "fw_var S (ep t) E \<le> L^2/4"
    by (rule p.variance_bounded[where x=E and L=L]) (use assms in auto)
  show ?thesis using b ep_variance[of t] by simp
qed

end
end
