(* Title: Finite power family, prefix and quantile ordering
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Power_Family
  imports TAF_Cumulative
begin

locale finite_power_family =
  fixes N :: nat
  assumes N2: "2\<le>N"
begin

sublocale f: finite_exp_family "{1..N}" "\<lambda>_. 1" "\<lambda>i. ln (real i)"
  by (unfold_locales; use N2 in auto)

definition cdf :: "real \<Rightarrow> nat \<Rightarrow> real" where
  "cdf g k = sum (f.ep g) {1..min N k}"

definition quantile :: "real \<Rightarrow> real \<Rightarrow> nat" where
  "quantile g fract = finite_quantile N (cdf g) fract"

lemma cdf_end: "cdf g N=1"
  unfolding cdf_def by (simp only: min.idem; rule f.ep_sum)

lemma cdf_as_subset:
  assumes "k\<le>N"
  shows "cdf g k=f.subset_probability {1..k} g"
proof -
  have mn: "min N k=k" using assms by simp
  show ?thesis by (simp only: cdf_def f.subset_probability_def mn)
qed

lemma cdf_strict_increase:
  assumes k: "1\<le>k" "k<N" and gh: "g<h"
  shows "cdf g k<cdf h k"
proof -
  have sub: "{1..k}\<subseteq>{1..N}" using k by auto
  have ne: "{1..k}\<noteq>{}" using k by auto
  have comp: "{1..N}-{1..k}\<noteq>{}" using k by auto
  have order: "ln (real i)<ln (real j)" if "i\<in>{1..k}" "j\<in>{1..N}-{1..k}" for i j
    using that by (auto simp: ln_less_cancel_iff)
  have "f.subset_probability {1..k} g<f.subset_probability {1..k} h"
    by (rule f.ordered_subset_strict_increase[OF sub ne comp order gh])
  then show ?thesis using k by (simp add: cdf_as_subset)
qed

lemma cdf_nondecreasing:
  assumes k: "k\<in>{1..N}" and gh: "g\<le>h"
  shows "cdf g k\<le>cdf h k"
  using cdf_strict_increase[of k g h] k gh cdf_end[of g] cdf_end[of h]
  by (cases "g=h"; cases "k=N"; auto)

lemma quantile_nonincreasing:
  assumes fract: "fract\<le>1" and gh: "g\<le>h"
  shows "quantile h fract\<le>quantile g fract"
  unfolding quantile_def
  by (rule quantile_order_from_cdf; use N2 fract gh cdf_end cdf_nondecreasing in auto)

lemma energy_range:
  assumes "i\<in>{1..N}"
  shows "0\<le>ln (real i)" "ln (real i)\<le>ln (real N)"
  using assms by (auto simp: ln_le_cancel_iff)

lemma finite_power_variance_positive: "0<f.evar g"
  by (rule f.strict_variance[where i=1 and j=2]; use N2 in auto)

lemma finite_power_variance_bound: "f.evar g\<le>(ln (real N))^2/4"
  by (rule f.variance_bound; use N2 energy_range in auto)

end
end
