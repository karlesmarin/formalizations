(*  Title:      Correlation_Monotone.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Monotonicity of the polynomial 6 Delta(C) in the correlation C.
*)

theory Correlation_Monotone
  imports "HOL-Analysis.Analysis"
begin

definition six_delta :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  where "six_delta sq sm z0 A0 C u x y =
    2 * (sq + sm - 2 * C) * (u\<^sup>2 - z0\<^sup>2) + 2 * A0 * ((sq + C) * x + (sm + C) * y)
    + sq * x\<^sup>2 + 2 * C * x * y + sm * y\<^sup>2"

definition delta_fn :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  where "delta_fn sq sm z0 A0 C u x y = six_delta sq sm z0 A0 C u x y / 6"

text \<open>(3a)\<close>
lemma six_delta_difference:
  "six_delta sq sm z0 A0 C2 u x y - six_delta sq sm z0 A0 C1 u x y
   = (C2 - C1) * (4 * (z0\<^sup>2 - u\<^sup>2) + 2 * (A0 * (x + y) + x * y))"
  by (simp add: six_delta_def algebra_simps)

text \<open>(3b)\<close>
lemma delta_monotone_in_C:
  assumes "0 \<le> u" "u \<le> z0" "0 \<le> x" "0 \<le> y" "0 \<le> A0" "C1 \<le> C2"
  shows "delta_fn sq sm z0 A0 C1 u x y \<le> delta_fn sq sm z0 A0 C2 u x y"
proof -
  have u2: "u\<^sup>2 \<le> z0\<^sup>2" using assms(1,2) by (intro power_mono) simp_all
  have "0 \<le> A0 * (x + y) + x * y" using assms by (simp add: mult_nonneg_nonneg add_nonneg_nonneg)
  then have "0 \<le> 4 * (z0\<^sup>2 - u\<^sup>2) + 2 * (A0 * (x + y) + x * y)" using u2 by simp
  then have "0 \<le> (C2 - C1) * (4 * (z0\<^sup>2 - u\<^sup>2) + 2 * (A0 * (x + y) + x * y))"
    using assms(6) by (simp add: mult_nonneg_nonneg)
  moreover have "six_delta sq sm z0 A0 C2 u x y - six_delta sq sm z0 A0 C1 u x y
      = (C2 - C1) * (4 * (z0\<^sup>2 - u\<^sup>2) + 2 * (A0 * (x + y) + x * y))"
    by (rule six_delta_difference)
  ultimately show ?thesis unfolding delta_fn_def by linarith
qed

text \<open>(3c)\<close>
lemma delta_nonneg_transfer:
  assumes "0 \<le> u" "u \<le> z0" "0 \<le> x" "0 \<le> y" "0 \<le> A0" "C1 \<le> C2"
    "0 \<le> delta_fn sq sm z0 A0 C1 u x y"
  shows "0 \<le> delta_fn sq sm z0 A0 C2 u x y"
  using delta_monotone_in_C[OF assms(1-6), where sq = sq and sm = sm] assms(7) by linarith

end
