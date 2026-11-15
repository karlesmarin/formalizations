(*  Title:      Symmetric_Branch.thy
    Author:     Carles Marin
    Copyright:  Carles Marin
    License:    BSD-3-Clause

    The symmetric branch of the turn-wait-turn family never beats the square pulse (memory-floor notes, slow noise
    with memory loss above the threshold, case 3 of the argument): in units z0 = 1, 2 A0 = pi, for a turn of phi in
    (0, pi/2] and a wait w >= 0, with s = sin phi, c = cos phi, z = c - w s / 2 and y = phi + s + w (1 + c) / 2,
        Q_m = 2 (z^2 - 1) + y (pi + y) >= pi phi + s (pi - 2 s) > 0.
    Only the inequality is formalised; the reduction of the cost to Q_m is a written argument.
*)

theory Symmetric_Branch
  imports "HOL-Analysis.Analysis"
begin

lemma one_minus_z_sq:
  fixes p w :: real
  assumes "0 \<le> w" "0 \<le> sin p" "cos p \<le> 1"
  shows "1 - (cos p - w * sin p / 2)\<^sup>2 \<le> (sin p)\<^sup>2 + (1 + cos p) * w * sin p / 2"
proof -
  define s c z where "s = sin p" and "c = cos p" and "z = c - w * s / 2"
  have ws: "0 \<le> w * s" using assms(1,2) by (simp add: s_def)
  have zc: "z \<le> c" using ws by (simp add: z_def)
  have c1: "c \<le> 1" using assms(3) by (simp add: c_def)
  have omz: "0 \<le> 1 - z" using zc c1 by linarith
  have "(1 - z) * (1 + z) \<le> (1 - z) * (1 + c)" by (rule mult_left_mono) (use zc omz in auto)
  moreover have "(1 - z) * (1 + c) = s\<^sup>2 + (1 + c) * w * s / 2"
  proof -
    have "s\<^sup>2 = 1 - c\<^sup>2" by (simp add: s_def c_def sin_squared_eq)
    then show ?thesis by (simp add: z_def algebra_simps power2_eq_square)
  qed
  moreover have "1 - z\<^sup>2 = (1 - z) * (1 + z)" by (simp add: power2_eq_square algebra_simps)
  ultimately have "1 - z\<^sup>2 \<le> s\<^sup>2 + (1 + c) * w * s / 2" by linarith
  then show ?thesis by (simp add: s_def c_def z_def)
qed

theorem symmetric_branch_bound:
  fixes p w :: real
  assumes p0: "0 < p" and p1: "p \<le> pi / 2" and w0: "0 \<le> w"
  shows "pi * p + sin p * (pi - 2 * sin p)
           \<le> 2 * ((cos p - w * sin p / 2)\<^sup>2 - 1)
              + (p + sin p + w * (1 + cos p) / 2) * (pi + (p + sin p + w * (1 + cos p) / 2))"
proof -
  define s c y where "s = sin p" and "c = cos p" and "y = p + sin p + w * (1 + cos p) / 2"
  have s0: "0 \<le> s" unfolding s_def using p0 p1 by (intro sin_ge_zero) auto
  have s1: "s \<le> 1" by (simp add: s_def)
  have c0: "0 \<le> c" unfolding c_def using p0 p1 by (intro cos_ge_zero) auto
  have c1: "c \<le> 1" by (simp add: c_def)
  have y0: "0 \<le> y" using p0 s0 c0 w0 by (simp add: y_def s_def c_def)
  have sp: "0 \<le> sin p" using s0 by (simp add: s_def)
  have h1: "1 - (cos p - w * sin p / 2)\<^sup>2 \<le> (sin p)\<^sup>2 + (1 + cos p) * w * sin p / 2"
    by (rule one_minus_z_sq[OF w0 sp cos_le_one])
  have h2: "2 * (1 - (cos p - w * sin p / 2)\<^sup>2) \<le> 2 * ((sin p)\<^sup>2 + (1 + cos p) * w * sin p / 2)"
    by (rule mult_left_mono[OF h1]) simp
  have h3: "2 * ((sin p)\<^sup>2 + (1 + cos p) * w * sin p / 2) = 2 * s\<^sup>2 + (1 + c) * w * s"
    by (simp add: s_def c_def algebra_simps)
  have step1: "2 * (1 - (cos p - w * sin p / 2)\<^sup>2) \<le> 2 * s\<^sup>2 + (1 + c) * w * s"
    using h2 h3 by linarith
  have half: "s \<le> pi / 2" using s1 pi_gt3 by linarith
  have wterm: "0 \<le> w * (1 + c) * (pi / 2 - s)"
    using w0 c0 half by (intro mult_nonneg_nonneg) auto
  have a1: "y * (pi + y) \<ge> pi * y" using y0 by (simp add: algebra_simps)
  have a2: "pi * y = pi * (p + s) + w * (1 + c) * (pi / 2)"
    by (simp add: y_def s_def c_def algebra_simps)
  have a3: "w * (1 + c) * (pi / 2 - s) = w * (1 + c) * (pi / 2) - (1 + c) * w * s"
    by (simp add: algebra_simps)
  have a4: "pi * (p + s) - 2 * s\<^sup>2 = pi * p + s * (pi - 2 * s)"
    by (simp add: algebra_simps power2_eq_square)
  have main: "y * (pi + y) - 2 * (1 - (cos p - w * sin p / 2)\<^sup>2) \<ge> pi * p + s * (pi - 2 * s)"
    using a1 a2 a3 a4 step1 wterm by linarith
  have rhs: "2 * ((cos p - w * sin p / 2)\<^sup>2 - 1) + y * (pi + y)
             = y * (pi + y) - 2 * (1 - (cos p - w * sin p / 2)\<^sup>2)"
    by (simp add: algebra_simps)
  show ?thesis using main rhs by (simp add: y_def s_def)
qed

corollary symmetric_branch_positive:
  fixes p w :: real
  assumes "0 < p" "p \<le> pi / 2" "0 \<le> w"
  shows "0 < 2 * ((cos p - w * sin p / 2)\<^sup>2 - 1)
              + (p + sin p + w * (1 + cos p) / 2) * (pi + (p + sin p + w * (1 + cos p) / 2))"
proof -
  have s0: "0 \<le> sin p" using assms by (intro sin_ge_zero) auto
  have s1: "sin p \<le> 1" by simp
  have "0 \<le> pi - 2 * sin p" using s1 pi_gt3 by linarith
  then have "0 \<le> sin p * (pi - 2 * sin p)" using s0 by (rule mult_nonneg_nonneg[rotated])
  moreover have "0 < pi * p" using assms(1) by simp
  ultimately show ?thesis using symmetric_branch_bound[OF assms] by linarith
qed

end
