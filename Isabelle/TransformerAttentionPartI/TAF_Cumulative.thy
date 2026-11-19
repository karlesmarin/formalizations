(* Title: Strict stochastic ordering for finite exponential families
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Cumulative
  imports TAF_Mixture_Entropy
begin

context finite_exp_family
begin

definition subset_probability :: "'a set \<Rightarrow> real \<Rightarrow> real" where
  "subset_probability K t = sum (ep t) K"

lemma subset_probability_derivative:
  "((\<lambda>t. subset_probability K t) has_real_derivative
    (\<Sum>i\<in>K. ep t i*(emean t-E i))) (at t)"
  unfolding subset_probability_def by (intro DERIV_sum probability_derivative)

lemma subset_derivative_cross:
  assumes sub: "K\<subseteq>S"
  shows "(\<Sum>i\<in>K. ep t i*(emean t-E i)) =
    (\<Sum>i\<in>K. \<Sum>j\<in>S-K. ep t i*ep t j*(E j-E i))"
proof -
  have fin: "finite K" using sub finite_S by (rule finite_subset)
  have ps: "sum (ep t) (S-K) = 1-sum (ep t) K"
    using sum_diff[OF finite_S sub, of "ep t"] ep_sum[of t] by simp
  have es: "(\<Sum>i\<in>S-K. ep t i*E i) = emean t-(\<Sum>i\<in>K. ep t i*E i)"
    using sum_diff[OF finite_S sub, of "\<lambda>i. ep t i*E i"] ep_mean[of t]
    by (simp add: fw_mean_def)
  have point: "ep t i*ep t j*(E j-E i) = ep t i*(ep t j*E j)-(ep t i*E i)*ep t j" for i j
    by (simp add: algebra_simps)
  have inner: "(\<Sum>j\<in>S-K. ep t i*ep t j*(E j-E i)) =
    ep t i*(\<Sum>j\<in>S-K. ep t j*E j)-(ep t i*E i) * sum (ep t) (S-K)" for i
    by (simp only: point sum_subtractf sum_distrib_left[symmetric])
  have right: "(\<Sum>i\<in>K. \<Sum>j\<in>S-K. ep t i*ep t j*(E j-E i)) =
    sum (ep t) K*emean t-(\<Sum>i\<in>K. ep t i*E i)"
    by (simp only: inner sum_subtractf sum_distrib_right[symmetric] ps es;
        simp add: algebra_simps)
  have point2: "ep t i*(emean t-E i)=ep t i*emean t-ep t i*E i" for i
    by (simp add: algebra_simps)
  show ?thesis by (simp only: right point2 sum_subtractf sum_distrib_right[symmetric])
qed

lemma ordered_subset_strict_derivative:
  assumes sub: "K\<subseteq>S" and ne: "K\<noteq>{}" and comp: "S-K\<noteq>{}"
    and order: "\<And>i j. i\<in>K \<Longrightarrow> j\<in>S-K \<Longrightarrow> E i<E j"
  shows "0<(\<Sum>i\<in>K. ep t i*(emean t-E i))"
proof -
  have fin: "finite K" using sub finite_S by (rule finite_subset)
  have finc: "finite (S-K)" using finite_S by simp
  have inner: "0<(\<Sum>j\<in>S-K. ep t i*ep t j*(E j-E i))" if "i\<in>K" for i
  proof -
    have ip: "0<ep t i" using ep_positive sub that by blast
    have "sum (\<lambda>_. 0::real) (S-K) < (\<Sum>j\<in>S-K. ep t i*ep t j*(E j-E i))"
      by (rule sum_strict_mono[OF finc comp];
          use ip order[OF that] ep_positive in \<open>auto intro!: mult_pos_pos\<close>)
    then show ?thesis by simp
  qed
  have "sum (\<lambda>_. 0::real) K < (\<Sum>i\<in>K. \<Sum>j\<in>S-K. ep t i*ep t j*(E j-E i))"
    by (rule sum_strict_mono[OF fin ne]; rule inner)
  then show ?thesis by (simp add: subset_derivative_cross[OF sub])
qed

lemma ordered_subset_strict_increase:
  assumes sub: "K\<subseteq>S" and ne: "K\<noteq>{}" and comp: "S-K\<noteq>{}"
    and order: "\<And>i j. i\<in>K \<Longrightarrow> j\<in>S-K \<Longrightarrow> E i<E j"
    and gh: "g<h"
  shows "subset_probability K g<subset_probability K h"
proof (rule DERIV_pos_imp_increasing[OF gh])
  fix x assume "g\<le>x" "x\<le>h"
  show "\<exists>y. ((\<lambda>t. subset_probability K t) has_real_derivative y) (at x) \<and> 0<y"
    using subset_probability_derivative[of K x]
      ordered_subset_strict_derivative[OF sub ne comp order, of x] by blast
qed

end

definition finite_quantile :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> nat" where
  "finite_quantile N F f = Min {k\<in>{1..N}. f\<le>F k}"

lemma finite_quantile_valid:
  assumes "1\<le>N" "f\<le>F N"
  shows "finite_quantile N F f\<in>{1..N}" "f\<le>F (finite_quantile N F f)"
proof -
  have fin: "finite {k\<in>{1..N}. f\<le>F k}" by simp
  have ne: "{k\<in>{1..N}. f\<le>F k}\<noteq>{}" using assms by auto
  have "Min {k\<in>{1..N}. f\<le>F k}\<in>{k\<in>{1..N}. f\<le>F k}"
    by (rule Min_in[OF fin ne])
  then show "finite_quantile N F f\<in>{1..N}" "f\<le>F (finite_quantile N F f)"
    by (auto simp: finite_quantile_def)
qed

lemma quantile_order_from_cdf:
  assumes N: "1\<le>N" and endF: "f\<le>F N"
    and cdf: "\<And>k. k\<in>{1..N} \<Longrightarrow> F k\<le>G k"
  shows "finite_quantile N G f\<le>finite_quantile N F f"
proof -
  have mem: "finite_quantile N F f\<in>{1..N}" and atq: "f\<le>F (finite_quantile N F f)"
    using finite_quantile_valid[where N=N and F=F and f=f, OF N endF] by auto
  have "finite_quantile N F f\<in>{k\<in>{1..N}. f\<le>G k}"
    using mem atq cdf[OF mem] by auto
  then show ?thesis unfolding finite_quantile_def by (intro Min_le) auto
qed

end
