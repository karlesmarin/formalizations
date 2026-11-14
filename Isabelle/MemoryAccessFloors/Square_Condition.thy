(*  Title:      Square_Condition.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License: BSD

    Sufficient condition for the optimality of the square pulse in the transfer with a relaxing qubit. With
    J = s (2 z^2 + A^2) / 6 + (g A + gm B) / 3 under A >= A0, B >= A0 and (z - z0)^2 <= (A - A0) (B - A0), and
    a = s A0 + g, the square pulse (z = z0, A = B = A0) has the value s (2 z0^2 + A0^2) / 6 + (g + gm) A0 / 3, and
    it is optimal as soon as sqrt (a gm) >= s z0. Everything is over the reals; the dynamics is not formalised.
*)

theory Square_Condition
  imports Noise_Loss_Relax
begin

section \<open>A. The one-variable inequality\<close>

text \<open>For @{text "0 \<le> z \<le> z0"} and @{text "s z0 \<le> c"} the function
  @{text "s z\<^sup>2 / 3 + (2/3) (z0 - z) c"} is at least its value at @{text "z0"}.\<close>

lemma square_cond_scalar:
  fixes s c z0 z :: real
  assumes "0 < s" and "0 \<le> z" and "z \<le> z0" and "s * z0 \<le> c"
  shows "s * z0\<^sup>2 / 3 \<le> s * z\<^sup>2 / 3 + (2 / 3) * (z0 - z) * c"
proof -
  have e: "s * z\<^sup>2 / 3 + (2 / 3) * (z0 - z) * c - s * z0\<^sup>2 / 3
           = (z0 - z) * (2 * c - s * (z + z0)) / 3"
    by (simp add: field_simps power2_eq_square)
  have p1: "0 \<le> z0 - z" using assms(3) by simp
  have sz: "s * (z + z0) \<le> s * (2 * z0)"
    using assms(1,3) by (intro mult_left_mono) simp_all
  have p2: "0 \<le> 2 * c - s * (z + z0)" using sz assms(4) by simp
  have "0 \<le> (z0 - z) * (2 * c - s * (z + z0)) / 3" using p1 p2 by simp
  thus ?thesis using e by linarith
qed

section \<open>B. The sufficient condition\<close>

theorem square_pulse_optimal:
  fixes s g gm A0 z0 z A B :: real
  assumes "0 < s" and "0 \<le> g" and "0 < gm" and "0 < A0" and "0 < z0" and "0 \<le> z"
    and "A0 \<le> A" and "A0 \<le> B" and "(z - z0)\<^sup>2 \<le> (A - A0) * (B - A0)"
    and "s * z0 \<le> sqrt ((s * A0 + g) * gm)"
  shows "s * (2 * z0\<^sup>2 + A0\<^sup>2) / 6 + (g + gm) * A0 / 3
         \<le> s * (2 * z\<^sup>2 + A\<^sup>2) / 6 + (g * A + gm * B) / 3"
proof -
  define a where "a = s * A0 + g"
  define c where "c = sqrt (a * gm)"
  define x where "x = A - A0"
  define y where "y = B - A0"
  have a0: "0 < a" unfolding a_def using assms(1,2,4) by (intro add_pos_nonneg) simp_all
  have x0: "0 \<le> x" unfolding x_def using assms(7) by simp
  have y0: "0 \<le> y" unfolding y_def using assms(8) by simp
  have hc: "s * z0 \<le> c" unfolding c_def a_def using assms(10) .
  have ex: "s * (2 * z\<^sup>2 + A\<^sup>2) / 6 + (g * A + gm * B) / 3
          = s * A0\<^sup>2 / 6 + (g + gm) * A0 / 3 + s * z\<^sup>2 / 3 + s * x\<^sup>2 / 6 + a * x / 3 + gm * y / 3"
    unfolding a_def x_def y_def by (simp add: power2_eq_square field_simps)
  have bs: "s * (2 * z0\<^sup>2 + A0\<^sup>2) / 6 + (g + gm) * A0 / 3
          = s * A0\<^sup>2 / 6 + (g + gm) * A0 / 3 + s * z0\<^sup>2 / 3"
    by (simp add: field_simps)
  have l3: "0 \<le> s * x\<^sup>2 / 6" using assms(1) by simp
  have goal: "s * z0\<^sup>2 / 3 \<le> s * z\<^sup>2 / 3 + a * x / 3 + gm * y / 3"
  proof (cases "z \<le> z0")
    case True
    have h: "(z0 - z)\<^sup>2 \<le> x * y"
      using assms(9) unfolding x_def y_def by (simp add: power2_commute)
    have l1: "(2 / 3) * (z0 - z) * sqrt (a * 1 * gm) \<le> a * 1 * x / 3 + gm * y / 3"
      using a0 assms(3,5,6) True x0 y0 h by (intro noiseloss_lower_core) simp_all
    hence l1': "(2 / 3) * (z0 - z) * c \<le> a * x / 3 + gm * y / 3" unfolding c_def by simp
    have l2: "s * z0\<^sup>2 / 3 \<le> s * z\<^sup>2 / 3 + (2 / 3) * (z0 - z) * c"
      using assms(1,6) True hc by (intro square_cond_scalar) simp_all
    show ?thesis using l1' l2 by linarith
  next
    case False
    hence zz: "z0 \<le> z" by simp
    have z2: "z0\<^sup>2 \<le> z\<^sup>2" using assms(5) zz by (intro power_mono) simp_all
    have "s * z0\<^sup>2 \<le> s * z\<^sup>2" using z2 assms(1) by (intro mult_left_mono) simp_all
    hence l2: "s * z0\<^sup>2 / 3 \<le> s * z\<^sup>2 / 3" by simp
    have l4: "0 \<le> a * x / 3" using a0 x0 by simp
    have l5: "0 \<le> gm * y / 3" using assms(3) y0 by simp
    show ?thesis using l2 l4 l5 by linarith
  qed
  show ?thesis using goal ex bs l3 by linarith
qed

section \<open>C. The case without relaxation, in the notation of the paper\<close>

text \<open>For @{text "g = 0"}, @{text "A0 = \<pi> / (4 G)"}, @{text "z0 = 1 / (2 G)"} the condition
  @{text "sqrt (a gm) \<ge> s z0"} follows from @{text "s / (gm G) \<le> \<pi>"}.\<close>

lemma square_cond_Lambda:
  fixes s gm G :: real
  assumes "0 < G" and "0 < s" and "0 < gm" and "s / (gm * G) \<le> pi"
  shows "s * (1 / (2 * G)) \<le> sqrt ((s * (pi / (4 * G)) + 0) * gm)"
proof -
  have h: "s \<le> pi * (gm * G)" using assms(1,3,4) by (simp add: field_simps divide_le_eq)
  have "(s * (1 / (2 * G)))\<^sup>2 \<le> (s * (pi / (4 * G)) + 0) * gm"
  proof -
    have e: "(s * (1 / (2 * G)))\<^sup>2 = s * s / (4 * G\<^sup>2)"
      by (simp add: field_simps power2_eq_square)
    have e': "(s * (pi / (4 * G)) + 0) * gm = s * (pi * gm * G) / (4 * G\<^sup>2)"
      using assms(1) by (simp add: field_simps power2_eq_square)
    have "s * s \<le> s * (pi * gm * G)"
      using h assms(2) by (intro mult_left_mono) (simp_all add: algebra_simps)
    thus ?thesis unfolding e e' using assms(1) by (intro divide_right_mono) simp_all
  qed
  moreover have "0 \<le> s * (1 / (2 * G))" using assms(1,2) by simp
  ultimately show ?thesis by (intro real_le_rsqrt) (simp add: power2_eq_square)
qed

corollary square_pulse_optimal_G:
  fixes s gm G z A B :: real
  assumes "0 < G" and "0 < s" and "0 < gm" and "0 \<le> z"
    and "pi / (4 * G) \<le> A" and "pi / (4 * G) \<le> B"
    and "(z - 1 / (2 * G))\<^sup>2 \<le> (A - pi / (4 * G)) * (B - pi / (4 * G))"
    and "s / (gm * G) \<le> pi"
  shows "s * (2 * (1 / (2 * G))\<^sup>2 + (pi / (4 * G))\<^sup>2) / 6 + (0 + gm) * (pi / (4 * G)) / 3
         \<le> s * (2 * z\<^sup>2 + A\<^sup>2) / 6 + (0 * A + gm * B) / 3"
  using assms square_cond_Lambda[OF assms(1-3,8)] by (intro square_pulse_optimal) simp_all

end
