(*  Title:      Noise_Loss_Relax.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License: BSD

    Lower bound for the error J = s (2 z^2 + A^2) / 6 + (gq A + gm B) / 3 of a transfer when the qubit also relaxes
    (rate gq >= 0), with s the second moment of the slow offset, under the constraints A >= A0, B >= A0 and
    (z - z0)^2 <= (A - A0) (B - A0). With a = s A0 + gq the bound is
    s A0^2 / 6 + (gq + gm) A0 / 3 + (2/3) z0 sqrt (a gm) - a gm / (3 s).
    For gq = 0 it is the bound of Noise_Loss_Bound. Everything is over the reals; the dynamics is not formalised.
*)

theory Noise_Loss_Relax
  imports Noise_Loss_Bound
begin

section \<open>A. Completing the square in the leakage\<close>

text \<open>With @{text "c"} standing for @{text "sqrt (a gm)"}: the leakage term @{text "s z\<^sup>2 / 3"} pays for
  the linear gain @{text "(2/3) (z0 - z) c"} up to the correction @{text "c\<^sup>2 / (3 s)"}.\<close>

lemma relax_square:
  fixes s c z0 z :: real
  assumes "0 < s"
  shows "(2 / 3) * z0 * c - c\<^sup>2 / (3 * s) \<le> s * z\<^sup>2 / 3 + (2 / 3) * (z0 - z) * c"
proof -
  have e: "s * z\<^sup>2 / 3 + (2 / 3) * (z0 - z) * c - ((2 / 3) * z0 * c - c\<^sup>2 / (3 * s))
           = (s * z - c)\<^sup>2 / (3 * s)"
    using assms by (simp add: field_simps power2_eq_square)
  have "0 \<le> (s * z - c)\<^sup>2 / (3 * s)" using assms by simp
  thus ?thesis using e by linarith
qed

section \<open>B. The case of large leakage\<close>

text \<open>For @{text "z \<ge> z0"} the margin is explicit: with @{text "r = sqrt s"}, it is at least
  @{text "(r z0 - c / r)\<^sup>2 / 3"}, which is non-negative.\<close>

lemma relax_large_zeta_margin:
  fixes s c z0 z :: real
  assumes "0 < s" and "0 \<le> z0" and "z0 \<le> z"
  shows "(sqrt s * z0 - c / sqrt s)\<^sup>2 / 3
         \<le> s * z\<^sup>2 / 3 - ((2 / 3) * z0 * c - c\<^sup>2 / (3 * s))"
proof -
  define r where "r = sqrt s"
  have r0: "0 < r" unfolding r_def using assms(1) by simp
  have r2: "r\<^sup>2 = s" unfolding r_def using assms(1) by simp
  have e: "(r * z0 - c / r)\<^sup>2 / 3 = r\<^sup>2 * z0\<^sup>2 / 3 - (2 / 3) * z0 * c + c\<^sup>2 / (3 * r\<^sup>2)"
    using r0 by (simp add: field_simps power2_eq_square)
  have e': "(r * z0 - c / r)\<^sup>2 / 3 = s * z0\<^sup>2 / 3 - (2 / 3) * z0 * c + c\<^sup>2 / (3 * s)"
    using e r2 by simp
  have z2: "z0\<^sup>2 \<le> z\<^sup>2" using assms(2,3) by (intro power_mono) simp_all
  have "s * z0\<^sup>2 \<le> s * z\<^sup>2" using z2 assms(1) by (intro mult_left_mono) simp_all
  hence "s * z0\<^sup>2 / 3 \<le> s * z\<^sup>2 / 3" by simp
  thus ?thesis unfolding r_def[symmetric] using e' by linarith
qed

corollary relax_large_zeta_margin_nonneg:
  fixes s c z0 z :: real
  assumes "0 < s" and "0 \<le> z0" and "z0 \<le> z"
  shows "(2 / 3) * z0 * c - c\<^sup>2 / (3 * s) \<le> s * z\<^sup>2 / 3"
proof -
  have "0 \<le> (sqrt s * z0 - c / sqrt s)\<^sup>2 / 3" by simp
  thus ?thesis using relax_large_zeta_margin[where c = c, OF assms] by linarith
qed

section \<open>C. The bound for every pulse\<close>

text \<open>The constraint of Theorem 13 of the paper is @{text "(z - z0)\<^sup>2 \<le> (A - A0) (B - A0)"}, with @{text "z"}
  the modulus of the leakage; the theorem below does not use the sign of @{text "z0 - z"}.\<close>

theorem relax_bound:
  fixes s g gm A0 z0 z A B :: real
  assumes "0 < s" and "0 \<le> g" and "0 < gm" and "0 < A0" and "0 < z0" and "0 \<le> z"
    and "A0 \<le> A" and "A0 \<le> B" and "(z - z0)\<^sup>2 \<le> (A - A0) * (B - A0)"
  shows "s * A0\<^sup>2 / 6 + (g + gm) * A0 / 3 + (2 / 3) * z0 * sqrt ((s * A0 + g) * gm)
           - (s * A0 + g) * gm / (3 * s)
         \<le> s * (2 * z\<^sup>2 + A\<^sup>2) / 6 + (g * A + gm * B) / 3"
proof -
  define a where "a = s * A0 + g"
  define c where "c = sqrt (a * gm)"
  define x where "x = A - A0"
  define y where "y = B - A0"
  have a0: "0 < a" unfolding a_def using assms(1,2,4) by (intro add_pos_nonneg) simp_all
  have c2: "c\<^sup>2 = a * gm" unfolding c_def using a0 assms(3) by simp
  have x0: "0 \<le> x" unfolding x_def using assms(7) by simp
  have y0: "0 \<le> y" unfolding y_def using assms(8) by simp
  have ex: "s * (2 * z\<^sup>2 + A\<^sup>2) / 6 + (g * A + gm * B) / 3
          = s * A0\<^sup>2 / 6 + (g + gm) * A0 / 3 + s * z\<^sup>2 / 3 + s * x\<^sup>2 / 6 + a * x / 3 + gm * y / 3"
    unfolding a_def x_def y_def by (simp add: power2_eq_square field_simps)
  have l3: "0 \<le> s * x\<^sup>2 / 6" using assms(1) by simp
  have goal: "(2 / 3) * z0 * c - c\<^sup>2 / (3 * s)
              \<le> s * z\<^sup>2 / 3 + a * x / 3 + gm * y / 3"
  proof (cases "z \<le> z0")
    case True
    have h: "(z0 - z)\<^sup>2 \<le> x * y"
      using assms(9) unfolding x_def y_def by (simp add: power2_commute)
    have l1: "(2 / 3) * (z0 - z) * sqrt (a * 1 * gm) \<le> a * 1 * x / 3 + gm * y / 3"
      using a0 assms(3,5,6) True x0 y0 h by (intro noiseloss_lower_core) simp_all
    hence l1': "(2 / 3) * (z0 - z) * c \<le> a * x / 3 + gm * y / 3" unfolding c_def by simp
    have l2: "(2 / 3) * z0 * c - c\<^sup>2 / (3 * s) \<le> s * z\<^sup>2 / 3 + (2 / 3) * (z0 - z) * c"
      by (rule relax_square) (rule assms(1))
    show ?thesis using l1' l2 by linarith
  next
    case False
    hence zz: "z0 \<le> z" by simp
    have l2: "(2 / 3) * z0 * c - c\<^sup>2 / (3 * s) \<le> s * z\<^sup>2 / 3"
      using assms(1,5) zz by (intro relax_large_zeta_margin_nonneg) simp_all
    have l4: "0 \<le> a * x / 3" using a0 x0 by simp
    have l5: "0 \<le> gm * y / 3" using assms(3) y0 by simp
    show ?thesis using l2 l4 l5 by linarith
  qed
  have c2': "c\<^sup>2 / (3 * s) = a * gm / (3 * s)" using c2 by simp
  have m: "s * A0\<^sup>2 / 6 + (g + gm) * A0 / 3 + (2 / 3) * z0 * c - a * gm / (3 * s)
           \<le> s * (2 * z\<^sup>2 + A\<^sup>2) / 6 + (g * A + gm * B) / 3"
    using goal c2' ex l3 by linarith
  have m': "s * A0\<^sup>2 / 6 + (g + gm) * A0 / 3 + (2 / 3) * z0 * sqrt ((s * A0 + g) * gm)
           - (s * A0 + g) * gm / (3 * s)
           \<le> s * (2 * z\<^sup>2 + A\<^sup>2) / 6 + (g * A + gm * B) / 3"
    using m unfolding c_def a_def .
  show ?thesis using m' .
qed

text \<open>The same statement in the notation of the paper, @{text "A0 = \<pi> / (4 G)"}, @{text "z0 = 1 / (2 G)"}.\<close>

corollary relax_bound_G:
  fixes s g gm G z A B :: real
  assumes "0 < G" and "0 < s" and "0 \<le> g" and "0 < gm" and "0 \<le> z"
    and "pi / (4 * G) \<le> A" and "pi / (4 * G) \<le> B"
    and "(z - 1 / (2 * G))\<^sup>2 \<le> (A - pi / (4 * G)) * (B - pi / (4 * G))"
  shows "s * (pi / (4 * G))\<^sup>2 / 6 + (g + gm) * (pi / (4 * G)) / 3
           + (2 / 3) * (1 / (2 * G)) * sqrt ((s * (pi / (4 * G)) + g) * gm)
           - (s * (pi / (4 * G)) + g) * gm / (3 * s)
         \<le> s * (2 * z\<^sup>2 + A\<^sup>2) / 6 + (g * A + gm * B) / 3"
  using assms by (intro relax_bound) simp_all

section \<open>D. Relation with the case without relaxation of the qubit\<close>

lemma relax_bound_gq0_eq:
  fixes s gm A0 z0 :: real
  assumes "0 < s" and "0 < gm" and "0 < A0"
  shows "s * A0\<^sup>2 / 6 + (0 + gm) * A0 / 3 + (2 / 3) * z0 * sqrt ((s * A0 + 0) * gm)
           - (s * A0 + 0) * gm / (3 * s)
         = s * A0\<^sup>2 / 6 + (2 / 3) * z0 * sqrt s * sqrt (A0 * gm)"
proof -
  have sq: "sqrt ((s * A0 + 0) * gm) = sqrt s * sqrt (A0 * gm)"
    by (simp add: mult.assoc real_sqrt_mult)
  have "(s * A0 + 0) * gm / (3 * s) = A0 * gm / 3" using assms(1) by (simp add: field_simps)
  moreover have "(2 / 3) * z0 * (sqrt s * sqrt (A0 * gm)) = (2 / 3) * z0 * sqrt s * sqrt (A0 * gm)"
    by simp
  ultimately show ?thesis unfolding sq by (simp add: algebra_simps)
qed

text \<open>For @{text "g = 0"} the bound of @{text "relax_bound"} is exactly the one of @{text "noiseloss_combined"},
  and that theorem is recovered from it (here without the hypothesis @{text "z \<le> z0"}).\<close>

corollary relax_recovers_noiseloss:
  fixes sigma2 gm A0 z0 z A B :: real
  assumes "0 < sigma2" and "0 < gm" and "0 < A0" and "0 < z0" and "0 \<le> z"
    and "A0 \<le> A" and "A0 \<le> B" and "(z0 - z)\<^sup>2 \<le> (A - A0) * (B - A0)"
  shows "sigma2 * A0\<^sup>2 / 6 + (2 / 3) * z0 * sqrt sigma2 * sqrt (A0 * gm)
         \<le> sigma2 * (2 * z\<^sup>2 + A\<^sup>2) / 6 + gm * B / 3"
proof -
  have h: "(z - z0)\<^sup>2 \<le> (A - A0) * (B - A0)" using assms(8) by (simp add: power2_commute)
  have "sigma2 * A0\<^sup>2 / 6 + (0 + gm) * A0 / 3 + (2 / 3) * z0 * sqrt ((sigma2 * A0 + 0) * gm)
          - (sigma2 * A0 + 0) * gm / (3 * sigma2)
        \<le> sigma2 * (2 * z\<^sup>2 + A\<^sup>2) / 6 + (0 * A + gm * B) / 3"
    using assms(1-7) h by (intro relax_bound) simp_all
  thus ?thesis unfolding relax_bound_gq0_eq[OF assms(1-3)] by simp
qed

end
