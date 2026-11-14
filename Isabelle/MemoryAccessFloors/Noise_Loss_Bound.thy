(*  Title:      Noise_Loss_Bound.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    The lower bound behind the error of a transfer with slow noise on the qubit and a decay rate of the memory:
    the arithmetic--geometric mean estimate on the product of the excess exposures, its minimisation over the
    leakage, the combined bound for the error J = sigma^2 (2 z^2 + A^2) / 6 + gamma B / 3, and the case of
    large leakage. Everything is stated over the reals; the dynamics is not formalised.
*)

theory Noise_Loss_Bound
  imports "HOL-Analysis.Analysis"
begin

text \<open>Notation: @{text "\<sigma>2"} is the second moment of the offset, @{text "gm"} the decay rate of the memory,
  @{text "A0"} the exposure of the square pulse, @{text "z0"} its leakage, @{text "z"} the leakage of the pulse,
  @{text "x = A - A0"} and @{text "y = B - A0"} the excess exposures, constrained by @{text "x y \<ge> (z0 - z)\<^sup>2"}.\<close>

section \<open>A. Arithmetic--geometric mean estimate\<close>

lemma noiseloss_lower_core:
  fixes sigma2 gm A0 z0 z x y :: real
  assumes "0 \<le> sigma2" and "0 < gm" and "0 < A0" and "0 < z0" and "0 \<le> z" and "z \<le> z0"
    and "0 \<le> x" and "0 \<le> y" and "(z0 - z)\<^sup>2 \<le> x * y"
  shows "(2 / 3) * (z0 - z) * sqrt (sigma2 * A0 * gm) \<le> sigma2 * A0 * x / 3 + gm * y / 3"
proof -
  define P where "P = sqrt (sigma2 * A0 * gm)"
  define d where "d = z0 - z"
  define u where "u = sigma2 * A0 * x"
  define v where "v = gm * y"
  have a0: "0 \<le> sigma2 * A0 * gm" by (intro mult_nonneg_nonneg) (use assms in auto)
  have P0: "0 \<le> P" unfolding P_def by (rule real_sqrt_ge_zero) (rule a0)
  have P2: "P\<^sup>2 = sigma2 * A0 * gm" unfolding P_def using a0 by simp
  have d0: "0 \<le> d" unfolding d_def using assms(6) by simp
  have u0: "0 \<le> u" unfolding u_def using assms(1,3,7) by simp
  have v0: "0 \<le> v" unfolding v_def using assms(2,8) by simp
  have uv: "u * v = P\<^sup>2 * (x * y)" unfolding u_def v_def P2 by (simp add: algebra_simps)
  have h1: "P\<^sup>2 * d\<^sup>2 \<le> P\<^sup>2 * (x * y)"
    using assms(9) unfolding d_def by (intro mult_left_mono) simp_all
  have h2: "(2 * (P * d))\<^sup>2 \<le> (u + v)\<^sup>2"
  proof -
    have sq: "0 \<le> (u - v)\<^sup>2" by simp
    have e1: "(u + v)\<^sup>2 = (u - v)\<^sup>2 + 4 * (u * v)" by (simp add: power2_eq_square algebra_simps)
    have e2: "(2 * (P * d))\<^sup>2 = 4 * (P\<^sup>2 * d\<^sup>2)" by (simp add: power2_eq_square algebra_simps)
    show ?thesis using sq e1 e2 h1 uv by linarith
  qed
  have h3: "2 * (P * d) \<le> u + v"
    by (rule power2_le_imp_le[OF h2]) (use u0 v0 in simp)
  have h5: "2 * (sqrt (sigma2 * A0 * gm) * (z0 - z)) \<le> sigma2 * A0 * x + gm * y"
    using h3 unfolding P_def d_def u_def v_def .
  have e: "(sigma2 * A0 * x / 3 + gm * y / 3) - (2 / 3) * (z0 - z) * sqrt (sigma2 * A0 * gm)
           = ((sigma2 * A0 * x + gm * y) - 2 * (sqrt (sigma2 * A0 * gm) * (z0 - z))) / 3"
    by (simp add: field_simps)
  have "0 \<le> (sigma2 * A0 * x / 3 + gm * y / 3) - (2 / 3) * (z0 - z) * sqrt (sigma2 * A0 * gm)"
    by (subst e) (use h5 in simp)
  thus ?thesis by simp
qed

lemma noiseloss_lower:
  fixes sigma2 gm A0 z0 z x y :: real
  assumes "0 \<le> sigma2" and "0 < gm" and "0 < A0" and "0 < z0" and "0 \<le> z" and "z \<le> z0"
    and "0 \<le> x" and "0 \<le> y" and "(z0 - z)\<^sup>2 \<le> x * y"
  shows "(2 / 3) * (z0 - z) * sqrt (sigma2 * A0 * gm)
         \<le> sigma2 * z\<^sup>2 / 3 + sigma2 * A0 * x / 3 + gm * y / 3"
proof -
  have c: "(2 / 3) * (z0 - z) * sqrt (sigma2 * A0 * gm) \<le> sigma2 * A0 * x / 3 + gm * y / 3"
    using assms by (rule noiseloss_lower_core)
  have h4: "0 \<le> sigma2 * z\<^sup>2 / 3" using assms(1) by simp
  show ?thesis using c h4 by linarith
qed

section \<open>B. Minimising over the leakage\<close>

lemma noiseloss_minimise_z:
  fixes sigma2 A0 gm z0 z s :: real
  assumes "0 < sigma2" and "0 < A0" and "0 < gm" and "0 < z0" and "0 \<le> z" and "z \<le> z0"
    and "s = sqrt sigma2"
  shows "(2 / 3) * z0 * s * sqrt (A0 * gm) - A0 * gm / 3
         \<le> sigma2 * z\<^sup>2 / 3 + (2 / 3) * (z0 - z) * s * sqrt (A0 * gm)"
proof -
  define c where "c = sqrt (A0 * gm)"
  have s2: "s\<^sup>2 = sigma2" unfolding assms(7) using assms(1) by simp
  have c2: "c\<^sup>2 = A0 * gm" unfolding c_def using assms(2,3) by simp
  have h: "0 \<le> (s * z - c)\<^sup>2" by simp
  have e: "(s * z - c)\<^sup>2 = s\<^sup>2 * z\<^sup>2 - 2 * z * (s * c) + c\<^sup>2"
    by (simp add: power2_eq_square algebra_simps)
  have h': "0 \<le> sigma2 * z\<^sup>2 - 2 * z * (s * c) + A0 * gm" using h e s2 c2 by simp
  have e2: "sigma2 * z\<^sup>2 / 3 + (2 / 3) * (z0 - z) * s * c - ((2 / 3) * z0 * s * c - A0 * gm / 3)
            = (sigma2 * z\<^sup>2 - 2 * z * (s * c) + A0 * gm) / 3"
    by (simp add: field_simps)
  have h'': "0 \<le> sigma2 * z\<^sup>2 / 3 + (2 / 3) * (z0 - z) * s * c - ((2 / 3) * z0 * s * c - A0 * gm / 3)"
    by (subst e2) (use h' in simp)
  show ?thesis unfolding c_def[symmetric] using h'' by simp
qed

section \<open>C. The combined bound\<close>

text \<open>The paper's sentence has the constant @{text "- A0 gm / 3"} in the final bound; the term
  @{text "gm B / 3 = gm A0 / 3 + gm y / 3"} cancels it, and @{text "sigma2 x\<^sup>2 / 6 \<ge> 0"} is dropped, so the
  correct bound has no such correction. The version with the correction follows as a corollary.\<close>

lemma noiseloss_combined:
  fixes sigma2 gm A0 z0 z x y A B :: real
  assumes "0 < sigma2" and "0 < gm" and "0 < A0" and "0 < z0" and "0 \<le> z" and "z \<le> z0"
    and "0 \<le> x" and "0 \<le> y" and "(z0 - z)\<^sup>2 \<le> x * y" and "A = A0 + x" and "B = A0 + y"
  shows "sigma2 * A0\<^sup>2 / 6 + (2 / 3) * z0 * sqrt sigma2 * sqrt (A0 * gm)
         \<le> sigma2 * (2 * z\<^sup>2 + A\<^sup>2) / 6 + gm * B / 3"
proof -
  have l1: "(2 / 3) * (z0 - z) * sqrt (sigma2 * A0 * gm) \<le> sigma2 * A0 * x / 3 + gm * y / 3"
    using assms(1-9) by (intro noiseloss_lower_core) simp_all
  have sq: "sqrt (sigma2 * A0 * gm) = sqrt sigma2 * sqrt (A0 * gm)"
    by (simp add: mult.assoc real_sqrt_mult)
  have l2: "(2 / 3) * z0 * sqrt sigma2 * sqrt (A0 * gm) - A0 * gm / 3
            \<le> sigma2 * z\<^sup>2 / 3 + (2 / 3) * (z0 - z) * sqrt sigma2 * sqrt (A0 * gm)"
    using assms(1-6) by (intro noiseloss_minimise_z) simp_all
  have l3: "0 \<le> sigma2 * x\<^sup>2 / 6" using assms(1) by simp
  have ex: "sigma2 * (2 * z\<^sup>2 + A\<^sup>2) / 6 + gm * B / 3
          = sigma2 * z\<^sup>2 / 3 + sigma2 * A0\<^sup>2 / 6 + sigma2 * A0 * x / 3 + sigma2 * x\<^sup>2 / 6
            + A0 * gm / 3 + gm * y / 3"
    unfolding assms(10,11) by (simp add: power2_eq_square field_simps)
  have l1': "(2 / 3) * (z0 - z) * (sqrt sigma2 * sqrt (A0 * gm))
             \<le> sigma2 * A0 * x / 3 + gm * y / 3"
    using l1 unfolding sq .
  have t1: "(2 / 3) * z0 * sqrt sigma2 * sqrt (A0 * gm) = (2 / 3) * z0 * (sqrt sigma2 * sqrt (A0 * gm))"
    by (simp add: algebra_simps)
  have t2: "(2 / 3) * (z0 - z) * sqrt sigma2 * sqrt (A0 * gm)
            = (2 / 3) * (z0 - z) * (sqrt sigma2 * sqrt (A0 * gm))"
    by (simp add: algebra_simps)
  show ?thesis using l1' l2 l3 ex t1 t2 by linarith
qed

corollary noiseloss_combined_paper:
  fixes sigma2 gm A0 z0 z x y A B :: real
  assumes "0 < sigma2" and "0 < gm" and "0 < A0" and "0 < z0" and "0 \<le> z" and "z \<le> z0"
    and "0 \<le> x" and "0 \<le> y" and "(z0 - z)\<^sup>2 \<le> x * y" and "A = A0 + x" and "B = A0 + y"
  shows "sigma2 * A0\<^sup>2 / 6 + (2 / 3) * z0 * sqrt sigma2 * sqrt (A0 * gm) - A0 * gm / 3
         \<le> sigma2 * (2 * z\<^sup>2 + A\<^sup>2) / 6 + gm * B / 3"
proof -
  have "0 \<le> A0 * gm / 3" using assms(2,3) by simp
  thus ?thesis using noiseloss_combined[OF assms] by linarith
qed

section \<open>D. Large leakage\<close>

lemma noiseloss_large_zeta:
  fixes sigma2 gm A0 z0 z A B :: real
  assumes "0 \<le> sigma2" and "0 \<le> gm" and "0 < A0" and "0 < z0" and "z0 \<le> z"
    and "A0 \<le> A" and "A0 \<le> B"
  shows "sigma2 * (A0\<^sup>2 + 2 * z0\<^sup>2) / 6 \<le> sigma2 * (2 * z\<^sup>2 + A\<^sup>2) / 6 + gm * B / 3"
proof -
  have z2: "z0\<^sup>2 \<le> z\<^sup>2" using assms(4,5) by (intro power_mono) simp_all
  have a2: "A0\<^sup>2 \<le> A\<^sup>2" using assms(3,6) by (intro power_mono) simp_all
  have m1: "sigma2 * (A0\<^sup>2 + 2 * z0\<^sup>2) \<le> sigma2 * (2 * z\<^sup>2 + A\<^sup>2)"
    using z2 a2 assms(1) by (intro mult_left_mono) simp_all
  have m2: "0 \<le> gm * B / 3" using assms(2,3,7) by simp
  show ?thesis using m1 m2 by linarith
qed

end
