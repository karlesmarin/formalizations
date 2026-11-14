(*  Title:      Memory_Robust.thy
    Author:     Carles Marín Muñoz
    Copyright:  Carles Marín Muñoz
    License:    BSD-3-Clause

    encaje: sesion 187; piezas del Teorema "Robustness costs time and exposure" de "Exact limits for writing a
    quantum memory" (memory-floors.tex, thm:robust y su corolario); modelo de estilo: sesion 186; no es herramienta.
*)

theory Memory_Robust
  imports "HOL-Analysis.Analysis"
begin

text \<open>Notation throughout: @{text "G > 0"}, @{text "\<nu> = 2G"}, @{text "T\<^sub>0 = \<pi>/(2G)"},
  @{text "A\<^sub>0 = \<pi>/(4G)"}, @{text "z\<^sub>0 = 1/(2G)"}.\<close>

section \<open>A. Concavity step of (b)\<close>

lemma concavity_step:
  fixes s a :: real
  assumes "0 \<le> s" and "s \<le> pi" and "0 \<le> a" and "a \<le> s"
  shows "1 + cos (s / 2) \<le> cos (a / 2) + cos ((s - a) / 2)"
proof -
  define u where "u = a / 4"
  define v where "v = (s - a) / 4"
  have u0: "0 \<le> u" and v0: "0 \<le> v" using assms by (auto simp: u_def v_def)
  have uvs: "u + v = s / 4" by (simp add: u_def v_def field_simps)
  have uv: "u + v \<le> pi / 2" using uvs assms(2) pi_gt_zero by linarith
  have su: "0 \<le> sin u" by (rule sin_ge_zero[OF u0]) (use uv v0 pi_gt_zero in linarith)
  have sv: "0 \<le> sin v" by (rule sin_ge_zero[OF v0]) (use uv u0 pi_gt_zero in linarith)
  have cuv: "0 \<le> cos (u + v)" using u0 v0 uv by (intro cos_ge_zero) auto
  have p: "0 \<le> cos u * cos v - sin u * sin v" using cuv by (simp add: cos_add)
  have x: "a / 2 = 2 * u" by (simp add: u_def)
  have y: "(s - a) / 2 = 2 * v" by (simp add: v_def)
  have z: "s / 2 = 2 * u + 2 * v" by (simp add: u_def v_def field_simps)
  have cx: "cos (2 * u) = 1 - 2 * (sin u)\<^sup>2" by (rule cos_double_sin)
  have cy: "cos (2 * v) = 1 - 2 * (sin v)\<^sup>2" by (rule cos_double_sin)
  have sx: "sin (2 * u) = 2 * sin u * cos u" by (rule sin_double)
  have sy: "sin (2 * v) = 2 * sin v * cos v" by (rule sin_double)
  have key: "cos (2 * u) + cos (2 * v) - 1 - cos (2 * u + 2 * v)
      = 4 * (sin u * sin v) * (cos u * cos v - sin u * sin v)"
    unfolding cos_add cx cy sx sy by (simp add: power2_eq_square algebra_simps)
  have nn: "0 \<le> 4 * (sin u * sin v) * (cos u * cos v - sin u * sin v)"
    using su sv p by (intro mult_nonneg_nonneg) auto
  show ?thesis unfolding z x y using key nn by linarith
qed

section \<open>B. Integral of the tent\<close>

lemma tent_integral:
  fixes nu a ts :: real
  assumes "0 < nu" and "0 \<le> a" and "ts = (pi / 2 + a) / nu"
  shows "((\<lambda>t. cos (min (nu * (ts - t)) (pi / 2 + nu * t))) has_integral
           (2 * cos (a / 2) - 1) / nu) {0..ts}"
proof -
  define tc where "tc = a / (2 * nu)"
  have nu: "nu \<noteq> 0" using assms(1) by simp
  have ts: "nu * ts = pi / 2 + a" using assms(3) nu by (simp add: field_simps)
  have tc0: "0 \<le> tc" using assms by (simp add: tc_def)
  have nutc: "nu * tc = a / 2" using nu by (simp add: tc_def field_simps)
  have tcts: "tc \<le> ts"
  proof -
    have "nu * tc \<le> nu * ts" using nutc ts assms(2) pi_gt_zero by linarith
    then show ?thesis using assms(1) by simp
  qed
  have I1: "((\<lambda>t. cos (pi / 2 + nu * t)) has_integral
        (sin (pi / 2 + nu * tc) / nu - sin (pi / 2 + nu * 0) / nu)) {0..tc}"
  proof (rule fundamental_theorem_of_calculus)
    show "0 \<le> tc" by fact
    fix x :: real
    assume "x \<in> {0..tc}"
    have "((\<lambda>t. sin (pi / 2 + nu * t) / nu) has_real_derivative cos (pi / 2 + nu * x)) (at x)"
      by (rule derivative_eq_intros refl | simp add: nu)+
    then have hd: "((\<lambda>t. sin (pi / 2 + nu * t) / nu) has_vector_derivative cos (pi / 2 + nu * x)) (at x)"
      by (simp add: has_real_derivative_iff_has_vector_derivative)
    show "((\<lambda>t. sin (pi / 2 + nu * t) / nu) has_vector_derivative cos (pi / 2 + nu * x))
        (at x within {0..tc})"
      by (rule has_vector_derivative_at_within[OF hd])
  qed
  have I2: "((\<lambda>t. cos (nu * (ts - t))) has_integral
        (- sin (nu * (ts - ts)) / nu - (- sin (nu * (ts - tc)) / nu))) {tc..ts}"
  proof (rule fundamental_theorem_of_calculus)
    show "tc \<le> ts" by fact
    fix x :: real
    assume "x \<in> {tc..ts}"
    have "((\<lambda>t. - sin (nu * (ts - t)) / nu) has_real_derivative cos (nu * (ts - x))) (at x)"
      by (rule derivative_eq_intros refl | simp add: nu)+
    then have hd: "((\<lambda>t. - sin (nu * (ts - t)) / nu) has_vector_derivative cos (nu * (ts - x))) (at x)"
      by (simp add: has_real_derivative_iff_has_vector_derivative)
    show "((\<lambda>t. - sin (nu * (ts - t)) / nu) has_vector_derivative cos (nu * (ts - x)))
        (at x within {tc..ts})"
      by (rule has_vector_derivative_at_within[OF hd])
  qed
  have v1: "sin (pi / 2 + nu * tc) / nu - sin (pi / 2 + nu * 0) / nu = (cos (a / 2) - 1) / nu"
  proof -
    have s1: "sin (pi / 2 + nu * tc) = cos (a / 2)" by (simp add: sin_add nutc)
    show ?thesis by (simp add: s1 diff_divide_distrib)
  qed
  have v2: "- sin (nu * (ts - ts)) / nu - (- sin (nu * (ts - tc)) / nu) = cos (a / 2) / nu"
  proof -
    have e0: "nu * (ts - tc) = nu * ts - nu * tc" by (simp add: right_diff_distrib)
    have e1: "nu * (ts - tc) = pi / 2 + a / 2" using e0 ts nutc by linarith
    have s2: "sin (nu * (ts - tc)) = cos (a / 2)" by (simp add: e1 sin_add)
    show ?thesis by (simp add: s2)
  qed
  have J1: "((\<lambda>t. cos (min (nu * (ts - t)) (pi / 2 + nu * t))) has_integral (cos (a / 2) - 1) / nu) {0..tc}"
  proof (rule has_integral_eq[OF _ I1[unfolded v1]])
    fix x :: real
    assume "x \<in> {0..tc}"
    then have "x \<le> tc" by simp
    then have "nu * x \<le> nu * tc" using assms(1) by simp
    then have "pi / 2 + nu * x \<le> nu * (ts - x)" using ts nutc by (simp add: algebra_simps)
    then show "cos (pi / 2 + nu * x) = cos (min (nu * (ts - x)) (pi / 2 + nu * x))"
      by (simp add: min_def)
  qed
  have J2: "((\<lambda>t. cos (min (nu * (ts - t)) (pi / 2 + nu * t))) has_integral cos (a / 2) / nu) {tc..ts}"
  proof (rule has_integral_eq[OF _ I2[unfolded v2]])
    fix x :: real
    assume "x \<in> {tc..ts}"
    then have "tc \<le> x" by simp
    then have "nu * tc \<le> nu * x" using assms(1) by simp
    then have "nu * (ts - x) \<le> pi / 2 + nu * x" using ts nutc by (simp add: algebra_simps)
    then show "cos (nu * (ts - x)) = cos (min (nu * (ts - x)) (pi / 2 + nu * x))"
      by (simp add: min_def)
  qed
  have "((\<lambda>t. cos (min (nu * (ts - t)) (pi / 2 + nu * t))) has_integral
      ((cos (a / 2) - 1) / nu + cos (a / 2) / nu)) {0..ts}"
    by (rule has_integral_combine[OF tc0 tcts J1 J2])
  moreover have "(cos (a / 2) - 1) / nu + cos (a / 2) / nu = (2 * cos (a / 2) - 1) / nu"
    using nu by (simp add: field_simps)
  ultimately show ?thesis by simp
qed

corollary tent_integral_value:
  fixes nu a ts :: real
  assumes "0 < nu" and "0 \<le> a" and "ts = (pi / 2 + a) / nu"
  shows "integral {0..ts} (\<lambda>t. cos (min (nu * (ts - t)) (pi / 2 + nu * t))) = (2 * cos (a / 2) - 1) / nu"
  using tent_integral[OF assms] by (rule integral_unique)

section \<open>C. Last step of (b)\<close>

lemma frontier_step:
  fixes G nu s zeta z0 T T0 :: real
  assumes "0 < G" and "nu = 2 * G" and "T0 = pi / (2 * G)" and "z0 = 1 / (2 * G)"
    and "0 \<le> s" and "s \<le> pi" and "0 \<le> zeta" and "zeta \<le> z0"
    and "T = (pi + s) / nu" and "cos (s / 2) \<le> zeta / z0"
  shows "T0 + arccos (zeta / z0) / G \<le> T"
proof -
  have z0: "0 < z0" using assms(1,4) by simp
  have r0: "0 \<le> zeta / z0" using assms(7) z0 by simp
  have r1: "zeta / z0 \<le> 1" using assms(8) z0 by (simp add: divide_le_eq)
  have c0: "- 1 \<le> cos (s / 2)" by simp
  have c1: "cos (s / 2) \<le> 1" by simp
  have "arccos (zeta / z0) \<le> arccos (cos (s / 2))"
    using assms(10) r0 r1 c0 c1 by (subst arccos_le_mono) auto
  also have "arccos (cos (s / 2)) = s / 2"
    using assms(5,6) by (intro arccos_cos) auto
  finally have ac: "arccos (zeta / z0) \<le> s / 2" .
  have "arccos (zeta / z0) / G \<le> (s / 2) / G"
    using ac assms(1) by (intro divide_right_mono) auto
  then have "T0 + arccos (zeta / z0) / G \<le> pi / (2 * G) + (s / 2) / G"
    using assms(3) by simp
  also have "\<dots> = T" using assms(1,2,9) by (simp add: field_simps)
  finally show ?thesis .
qed

section \<open>D. Last step of (a)\<close>

lemma disk_from_two_bounds:
  fixes G nu zeta z0 Q X Y :: real
  assumes "0 < G" and "nu = 2 * G" and "z0 = 1 / (2 * G)"
    and "\<bar>2 * zeta - 2 / nu\<bar> \<le> Q - 2 / nu" and "Q - 2 / nu \<le> 2 * sqrt (X * Y)"
    and "0 \<le> X" and "0 \<le> Y"
  shows "(zeta - z0)\<^sup>2 \<le> X * Y"
proof -
  have e: "2 * zeta - 2 / nu = 2 * (zeta - z0)" using assms(1,2,3) by (simp add: field_simps)
  have "\<bar>2 * (zeta - z0)\<bar> \<le> 2 * sqrt (X * Y)" using assms(4,5) e by simp
  then have "\<bar>zeta - z0\<bar> \<le> sqrt (X * Y)" by (simp add: abs_mult)
  then have "\<bar>zeta - z0\<bar>\<^sup>2 \<le> (sqrt (X * Y))\<^sup>2"
    by (intro power_mono) auto
  then show ?thesis using assms(6,7) by simp
qed

section \<open>E. Equality cases\<close>

lemma bang_bang_equality:
  fixes G d T T0 A0 z0 zeta A B :: real
  assumes "0 < G" and "0 \<le> d" and "d \<le> pi / 2"
    and "T0 = pi / (2 * G)" and "A0 = pi / (4 * G)" and "z0 = 1 / (2 * G)"
    and "T = (pi + 2 * d) / (2 * G)" and "zeta = cos d / (2 * G)"
    and "A = A0 + (d - sin d) / (2 * G)" and "B = A0 + (d + sin d) / (2 * G)"
  shows "A + B = T"
    and "T = T0 + arccos (zeta / z0) / G"
    and "(zeta - z0)\<^sup>2 \<le> (A - A0) * (B - A0)"
proof -
  have G: "G \<noteq> 0" using assms(1) by simp
  show "A + B = T"
    unfolding assms(7,9,10,5) using G by (simp add: field_simps)
  have r: "zeta / z0 = cos d" unfolding assms(6,8) using G by (simp add: field_simps)
  have "arccos (cos d) = d" using assms(2,3) by (intro arccos_cos) auto
  then show "T = T0 + arccos (zeta / z0) / G" using r assms(4,7) G by (simp add: field_simps)
  have sh: "0 \<le> sin (d / 2)" using assms(2,3) by (intro sin_ge_zero) auto
  have sh2: "sin (d / 2) \<le> d / 2" using assms(2) by (intro sin_x_le_x) simp
  have "(sin (d / 2))\<^sup>2 \<le> (d / 2)\<^sup>2" using sh sh2 by (intro power_mono) auto
  then have cd: "2 - 2 * cos d \<le> d\<^sup>2"
    using cos_double_sin[of "d / 2"] by (simp add: power2_eq_square field_simps)
  have sc: "(sin d)\<^sup>2 + (cos d)\<^sup>2 = 1" by simp
  have key: "(1 - cos d)\<^sup>2 \<le> d\<^sup>2 - (sin d)\<^sup>2"
    using cd sc by (simp add: power2_eq_square algebra_simps)
  have e1: "zeta - z0 = (cos d - 1) * z0" unfolding assms(6,8) using G by (simp add: field_simps)
  have e2: "A - A0 = (d - sin d) * z0" unfolding assms(6,9) using G by (simp add: field_simps)
  have e3: "B - A0 = (d + sin d) * z0" unfolding assms(6,10) using G by (simp add: field_simps)
  have "(zeta - z0)\<^sup>2 = (1 - cos d)\<^sup>2 * z0\<^sup>2" by (simp add: e1 power2_eq_square algebra_simps)
  also have "\<dots> \<le> (d\<^sup>2 - (sin d)\<^sup>2) * z0\<^sup>2" using key by (intro mult_right_mono) auto
  also have "\<dots> = (A - A0) * (B - A0)" by (simp add: e2 e3 power2_eq_square algebra_simps)
  finally show "(zeta - z0)\<^sup>2 \<le> (A - A0) * (B - A0)" .
qed

lemma turn_wait_turn_equality:
  fixes G L alpha z0 A0 zeta A B :: real
  assumes "0 \<le> L" and "z0 = 1 / (2 * G)" and "A0 = pi / (4 * G)"
    and "zeta = z0 + L * sin alpha / 2"
    and "A = A0 + L * (1 + cos alpha) / 2" and "B = A0 + L * (1 - cos alpha) / 2"
  shows "(zeta - z0)\<^sup>2 = (A - A0) * (B - A0)" and "A + B = 2 * A0 + L"
proof -
  have sc: "(sin alpha)\<^sup>2 = 1 - (cos alpha)\<^sup>2" using sin_cos_squared_add[of alpha] by linarith
  have "(zeta - z0)\<^sup>2 = L\<^sup>2 * (sin alpha)\<^sup>2 / 4" using assms(4) by (simp add: power2_eq_square algebra_simps)
  also have "\<dots> = L\<^sup>2 * (1 - (cos alpha)\<^sup>2) / 4" using sc by simp
  also have "\<dots> = (A - A0) * (B - A0)" using assms(5,6) by (simp add: power2_eq_square algebra_simps)
  finally show "(zeta - z0)\<^sup>2 = (A - A0) * (B - A0)" .
  show "A + B = 2 * A0 + L" unfolding assms(5,6) by (simp add: field_simps)
qed

section \<open>F. Cost of robustness\<close>

lemma robust_cost_amgm:
  fixes G gq gm x y :: real
  assumes "0 < G" and "0 \<le> gq" and "0 \<le> gm" and "0 \<le> x" and "0 \<le> y"
    and "1 / (4 * G\<^sup>2) \<le> x * y"
  shows "sqrt (gq * gm) / G \<le> gq * x + gm * y"
proof -
  define r where "r = sqrt (gq * gm)"
  have gg: "0 \<le> gq * gm" by (rule mult_nonneg_nonneg[OF assms(2,3)])
  have r0: "0 \<le> r" using gg by (simp add: r_def)
  have r2: "r\<^sup>2 = gq * gm" using gg by (simp add: r_def)
  have h: "(r / G)\<^sup>2 = gq * gm * (1 / G\<^sup>2)" using r2 by (simp add: power_divide)
  have hq: "gq * gm * (4 * (1 / (4 * G\<^sup>2))) = (r / G)\<^sup>2" using h assms(1) by (simp add: field_simps)
  have "gq * gm * (4 * (1 / (4 * G\<^sup>2))) \<le> gq * gm * (4 * (x * y))"
    by (intro mult_left_mono) (use gg assms(6) in auto)
  then have "(r / G)\<^sup>2 \<le> 4 * (gq * gm) * (x * y)" using hq by (simp add: algebra_simps)
  also have "\<dots> \<le> (gq * x + gm * y)\<^sup>2"
  proof -
    have "(gq * x + gm * y)\<^sup>2 - 4 * (gq * gm) * (x * y) = (gq * x - gm * y)\<^sup>2"
      by (simp add: power2_eq_square algebra_simps)
    then show ?thesis by (metis diff_ge_0_iff_ge zero_le_power2)
  qed
  finally have "(r / G)\<^sup>2 \<le> (gq * x + gm * y)\<^sup>2" .
  moreover have "0 \<le> gq * x + gm * y" using assms(2-5) by (intro add_nonneg_nonneg mult_nonneg_nonneg)
  ultimately show ?thesis unfolding r_def[symmetric] by (rule power2_le_imp_le)
qed

lemma min_robust_A:
  fixes G d A A0 zeta :: real
  assumes "0 < G" and "d = pi / 2" and "A0 = pi / (4 * G)"
    and "A = A0 + (d - sin d) / (2 * G)" and "zeta = cos d / (2 * G)"
  shows "A = (pi - 1) / (2 * G)" and "zeta = 0"
proof -
  have G: "G \<noteq> 0" using assms(1) by simp
  have "A = pi / (4 * G) + (pi / 2 - sin (pi / 2)) / (2 * G)"
    unfolding assms(4,3,2) by simp
  also have "\<dots> = pi / (4 * G) + (pi / 2 - 1) / (2 * G)" by simp
  also have "\<dots> = (pi - 1) / (2 * G)" using G by (simp add: field_simps)
  finally show "A = (pi - 1) / (2 * G)" .
  show "zeta = 0" unfolding assms(5,2) by simp
qed

end
