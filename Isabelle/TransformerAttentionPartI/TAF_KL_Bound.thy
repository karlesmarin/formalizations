(* Title: Global quadratic relative-entropy bound for finite energies
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_KL_Bound
  imports TAF_KL_Remainder
begin

context finite_exp_family
begin

lemma moment_continuous: "isCont (mom k) t"
  using moment_derivative[of k t] by (rule DERIV_isCont)

lemma mean_continuous: "isCont emean t"
  using mean_derivative[of t] by (rule DERIV_isCont)

lemma variance_continuous: "isCont evar t"
  unfolding evar_def[abs_def]
  using mom0_positive[of t]
  by (intro continuous_intros moment_continuous mean_continuous) auto

lemma log_partition_second_derivative:
  "((\<lambda>t. -emean t) has_real_derivative evar g) (at g)"
  using DERIV_minus[OF mean_derivative[of g]] by simp

lemma kl_quadratic_bound:
  assumes L: "0\<le>L" and lo: "\<And>i. i\<in>S \<Longrightarrow> 0\<le>E i"
    and hi: "\<And>i. i\<in>S \<Longrightarrow> E i\<le>L"
  shows "finite_kl S (ep g) (ep h)\<le>ereal ((h-g)^2*L^2/8)"
proof -
  let ?F = "\<lambda>t. (1-t)*evar (g+t*(h-g))"
  have vpath: "isCont (\<lambda>t. evar (g+t*(h-g))) x" for x
    by (rule isCont_o2; intro variance_continuous continuous_intros)
  have cont: "continuous_on {0..1} ?F"
    by (intro continuous_at_imp_continuous_on ballI continuous_intros vpath)
  have int: "?F integrable_on {0..1}" by (rule integrable_continuous_real[OF cont])
  have intg: "(\<lambda>t::real. (1-t)*(L^2/4)) integrable_on {0..1}"
    by (intro integrable_continuous_real continuous_intros)
  have point: "?F t\<le>(1-t)*(L^2/4)" if "t\<in>{0..1}" for t
    by (intro mult_left_mono[OF variance_bound[OF L lo hi]]; use that in auto)
  have b: "integral {0..1} ?F\<le>integral {0..1} (\<lambda>t::real. (1-t)*(L^2/4))"
    by (rule integral_le[OF int intg point])
  have ilinear: "integral {0..1} (\<lambda>t::real. 1-t)=1/2"
    using Henstock_Kurzweil_Integration.integral_diff[where S="{0..1::real}" and f="\<lambda>_. 1" and g="\<lambda>t. t",
      OF integrable_const_ivl ident_integrable_on] by simp
  have eqfun: "(\<lambda>t::real. (1-t)*(L^2/4))=(\<lambda>t. (L^2/4) *\<^sub>R (1-t))"
    by (rule ext; simp add: real_scaleR_def mult.commute)
  have ivalue: "integral {0..1} (\<lambda>t::real. (1-t)*(L^2/4))=L^2/8"
    by (simp only: eqfun Henstock_Kurzweil_Integration.integral_cmul ilinear; simp)
  have bsmall: "integral {0..1} ?F\<le>L^2/8" using b by (simp only: ivalue)
  have main: "(h-g)^2*integral {0..1} ?F\<le>(h-g)^2*L^2/8"
    using mult_left_mono[OF bsmall, where c="(h-g)^2"] by simp
  show ?thesis by (simp only: kl_integral_remainder ereal_less_eq) (rule main)
qed

end
end
