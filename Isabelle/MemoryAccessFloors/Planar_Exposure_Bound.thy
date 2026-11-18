(*  Title:      Planar_Exposure_Bound.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    The planar exposure bound (Lemma "planar exposure bound" of the memory-floor note B, sec_robust.tex),
    from the step that is elementary onwards.

    What is formalised.  With z in [0,1), d = arccos z, a_z(phi) = phi - (1+z) tan(phi/2),
    b_z(phi) = phi + (1-z) cot(phi/2) and, for the normalised exposures a, b of a pulse and
    theta = (a+b)/2, the arc of type (1,0,-1)
        x_3 = -2 sin(phi) - 2 (theta-phi) cos(phi),   y_3 = 2 cos(phi) - 2 (theta-phi) sin(phi):
    - the exposures along the arc: a = phi - sin(phi) + (theta-phi)(1-cos phi), b = phi + sin(phi) + (theta-phi)(1+cos phi);
    - steps (3) and (4) of the proof: from y_3 <= 2z get theta >= theta_z(phi) = phi + (cos phi - z)/sin phi, hence
      a >= a_z(phi); a_z is strictly increasing, theta_z is non-increasing on (0,d]; so for beta = a_z^{-1}(a)
      one has b >= b_z(beta)   (theorems planar_exposure_bound_inner and planar_exposure_bound);
    - the statement about the range: a_z maps (0,d] into (0,d - sin d] (and onto it: Memory_Floors_Pieces.a_z_range);
    - equality is attained by the arc with the non-negative wait (arc_attains);
    - step (1): odd turns k >= 1 give exposures k*pi, larger than the bang-bang values d -+ sin d
      (multi_turn_dominated; the integral inequality itself is Memory_Floors_Pieces.odd_turns_integral).

    What is NOT formalised, and enters as a hypothesis (named in the theorem statements).  Step (2) of the proof is the
    classification of the section of the reachable set of a planar Dubins car at heading pi by Patsko and Fedotov
    (Lemma 3.1 and Theorem 11.1 of their paper), which is dynamics (extremal controls, Cases 1-3) and is an
    external result.  Its consequence enters as the hypothesis "on the arc": every pulse in the strict sector
    a < d - sin d lies above the point of the arc x_3, y_3 at the same x, with 0 < phi < d, i.e. a - b = x_3 and
    y_3 <= 2z.  The case a = d - sin d needs only theta >= d, which is part (b) of the robust theorem of B
    and is also a hypothesis.  The reduction of the pulse to a Dubins car (the Bloch direction on a meridian) is not
    formalised either.  The symmetric statement (a and b exchanged) is the same theorem applied to the time-reversed
    pulse and is not repeated.
*)
theory Planar_Exposure_Bound
  imports Memory_Floors_Pieces
begin

section \<open>The arc and the closed forms\<close>

definition x3 :: "real \<Rightarrow> real \<Rightarrow> real" where
  "x3 theta phi = - 2 * sin phi - 2 * (theta - phi) * cos phi"

definition y3 :: "real \<Rightarrow> real \<Rightarrow> real" where
  "y3 theta phi = 2 * cos phi - 2 * (theta - phi) * sin phi"

definition theta_z :: "real \<Rightarrow> real \<Rightarrow> real" where
  "theta_z z phi = phi + (cos phi - z) / sin phi"

text \<open>Exposures along the arc: the points a = theta + x_3/2 and b = theta - x_3/2 (since a + b = 2 theta
and a - b = x_3) are the closed forms of the remark of B, with G w = theta - phi.\<close>

theorem arc_exposures:
  fixes theta phi :: real
  shows "theta + x3 theta phi / 2 = phi - sin phi + (theta - phi) * (1 - cos phi)"
    and "theta - x3 theta phi / 2 = phi + sin phi + (theta - phi) * (1 + cos phi)"
  unfolding x3_def by (simp_all add: field_simps)

lemma alg_a:
  fixes s c z :: real
  assumes s: "0 < s" and c: "0 < c" and e: "s\<^sup>2 + c\<^sup>2 = 1"
  shows "- ((1 + z) * (s / c)) = - (2 * s * c) + ((c\<^sup>2 - s\<^sup>2 - z) / (2 * s * c)) * (1 - (c\<^sup>2 - s\<^sup>2))"
proof -
  have o: "1 - (c\<^sup>2 - s\<^sup>2) = 2 * s\<^sup>2" using e by linarith
  have n: "(- (2 * s * c) * c + (c\<^sup>2 - s\<^sup>2 - z) * s) = - s * (c\<^sup>2 + s\<^sup>2) - z * s"
    by (simp add: algebra_simps power2_eq_square)
  have "- (2 * s * c) + ((c\<^sup>2 - s\<^sup>2 - z) / (2 * s * c)) * (2 * s\<^sup>2)
        = (- (2 * s * c) * c + (c\<^sup>2 - s\<^sup>2 - z) * s) / c"
    using s c by (simp add: field_simps power2_eq_square)
  also have "\<dots> = (- s * (c\<^sup>2 + s\<^sup>2) - z * s) / c" using n by simp
  also have "\<dots> = (- s - z * s) / c" using e by (simp add: add.commute)
  also have "\<dots> = - ((1 + z) * (s / c))" using c by (simp add: field_simps)
  finally show ?thesis unfolding o by simp
qed

lemma alg_b:
  fixes s c z :: real
  assumes s: "0 < s" and c: "0 < c" and e: "s\<^sup>2 + c\<^sup>2 = 1"
  shows "(1 - z) * (c / s) = 2 * s * c + ((c\<^sup>2 - s\<^sup>2 - z) / (2 * s * c)) * (1 + (c\<^sup>2 - s\<^sup>2))"
proof -
  have o: "1 + (c\<^sup>2 - s\<^sup>2) = 2 * c\<^sup>2" using e by linarith
  have n: "(2 * s * c * s + (c\<^sup>2 - s\<^sup>2 - z) * c) = c * (c\<^sup>2 + s\<^sup>2) - z * c"
    by (simp add: algebra_simps power2_eq_square)
  have "2 * s * c + ((c\<^sup>2 - s\<^sup>2 - z) / (2 * s * c)) * (2 * c\<^sup>2)
        = (2 * s * c * s + (c\<^sup>2 - s\<^sup>2 - z) * c) / s"
    using s c by (simp add: field_simps power2_eq_square)
  also have "\<dots> = (c * (c\<^sup>2 + s\<^sup>2) - z * c) / s" using n by simp
  also have "\<dots> = (c - z * c) / s" using e by (simp add: add.commute)
  also have "\<dots> = (1 - z) * (c / s)" using s by (simp add: field_simps)
  finally show ?thesis unfolding o by simp
qed

lemma half_angle_data:
  fixes phi :: real
  assumes "0 < phi" and "phi < pi"
  shows "0 < sin (phi / 2)" and "0 < cos (phi / 2)"
    and "sin phi = 2 * sin (phi / 2) * cos (phi / 2)"
    and "cos phi = (cos (phi / 2))\<^sup>2 - (sin (phi / 2))\<^sup>2"
    and "(sin (phi / 2))\<^sup>2 + (cos (phi / 2))\<^sup>2 = 1"
proof -
  show "0 < sin (phi / 2)" using assms by (intro sin_gt_zero) simp_all
  show "0 < cos (phi / 2)" using assms by (intro cos_gt_zero_pi) simp_all
  have "sin phi = sin (2 * (phi / 2))" by simp
  then show "sin phi = 2 * sin (phi / 2) * cos (phi / 2)" by (simp only: sin_double)
  have "cos phi = cos (2 * (phi / 2))" by simp
  then show "cos phi = (cos (phi / 2))\<^sup>2 - (sin (phi / 2))\<^sup>2"
    by (simp only: cos_double power2_eq_square)
  show "(sin (phi / 2))\<^sup>2 + (cos (phi / 2))\<^sup>2 = 1" by simp
qed

theorem a_z_arc:
  fixes z phi :: real
  assumes "0 < phi" and "phi < pi"
  shows "a_z z phi = phi - sin phi + (theta_z z phi - phi) * (1 - cos phi)"
proof -
  define s where "s = sin (phi / 2)"
  define c where "c = cos (phi / 2)"
  have sp: "0 < s" and cp: "0 < c" and sn: "sin phi = 2 * s * c"
    and cs: "cos phi = c\<^sup>2 - s\<^sup>2" and e: "s\<^sup>2 + c\<^sup>2 = 1"
    unfolding s_def c_def using half_angle_data[OF assms] by simp_all
  have "tan (phi / 2) = s / c" unfolding s_def c_def tan_def by simp
  then have "a_z z phi = phi - (1 + z) * (s / c)" unfolding a_z_def by simp
  moreover have "phi - sin phi + (theta_z z phi - phi) * (1 - cos phi)
                 = phi - (2 * s * c) + ((c\<^sup>2 - s\<^sup>2 - z) / (2 * s * c)) * (1 - (c\<^sup>2 - s\<^sup>2))"
    unfolding theta_z_def sn cs by simp
  ultimately show ?thesis using alg_a[OF sp cp e, of z] by simp
qed

theorem b_z_arc:
  fixes z phi :: real
  assumes "0 < phi" and "phi < pi"
  shows "b_z z phi = phi + sin phi + (theta_z z phi - phi) * (1 + cos phi)"
proof -
  define s where "s = sin (phi / 2)"
  define c where "c = cos (phi / 2)"
  have sp: "0 < s" and cp: "0 < c" and sn: "sin phi = 2 * s * c"
    and cs: "cos phi = c\<^sup>2 - s\<^sup>2" and e: "s\<^sup>2 + c\<^sup>2 = 1"
    unfolding s_def c_def using half_angle_data[OF assms] by simp_all
  have "cot (phi / 2) = c / s" unfolding s_def c_def cot_def by simp
  then have "b_z z phi = phi + (1 - z) * (c / s)" unfolding b_z_def by simp
  moreover have "phi + sin phi + (theta_z z phi - phi) * (1 + cos phi)
                 = phi + (2 * s * c) + ((c\<^sup>2 - s\<^sup>2 - z) / (2 * s * c)) * (1 + (c\<^sup>2 - s\<^sup>2))"
    unfolding theta_z_def sn cs by simp
  ultimately show ?thesis using alg_b[OF sp cp e, of z] by simp
qed

theorem theta_z_avg:
  fixes z phi :: real
  assumes "0 < phi" and "phi < pi"
  shows "theta_z z phi = (a_z z phi + b_z z phi) / 2"
  using a_z_arc[OF assms, of z] b_z_arc[OF assms, of z] by (simp add: algebra_simps)

theorem b_z_from_theta:
  fixes z phi :: real
  assumes "0 < phi" and "phi < pi"
  shows "b_z z phi = 2 * theta_z z phi - a_z z phi"
  using theta_z_avg[OF assms, of z] by simp

section \<open>Monotonicity: a_z strictly increasing, theta_z non-increasing\<close>

lemma cos_gt_z:
  fixes z phi :: real
  assumes "0 \<le> z" and "z < 1" and "0 < phi" and "phi < arccos z"
  shows "z < cos phi"
proof -
  have d2: "arccos z \<le> pi / 2" by (rule arccos_facts(2)[OF assms(1,2)])
  have "cos (arccos z) < cos phi"
    using assms(3,4) d2 pi_gt_zero by (intro cos_monotone_0_pi) linarith+
  then show ?thesis using arccos_facts(3)[OF assms(1,2)] by simp
qed

lemma cos_ge_z:
  fixes z phi :: real
  assumes "0 \<le> z" and "z < 1" and "0 < phi" and "phi \<le> arccos z"
  shows "z \<le> cos phi"
proof (cases "phi = arccos z")
  case True
  then show ?thesis using arccos_facts(3)[OF assms(1,2)] by simp
next
  case False
  then show ?thesis using cos_gt_z[OF assms(1,2,3)] assms(4) by simp
qed

theorem a_z_strict_mono:
  fixes z p1 p2 :: real
  assumes "0 \<le> z" and "z < 1" and "0 < p1" and "p1 < p2" and "p2 \<le> arccos z"
  shows "a_z z p1 < a_z z p2"
proof -
  have d2: "arccos z \<le> pi / 2" by (rule arccos_facts(2)[OF assms(1,2)])
  have dr: "(a_z z has_real_derivative (cos x - z) / (1 + cos x)) (at x)" if "p1 \<le> x" "x \<le> p2" for x
  proof -
    have "- pi < x" "x < pi" using that assms(3,5) d2 pi_gt_zero by linarith+
    then show ?thesis by (rule a_z_deriv)
  qed
  have D: "\<exists>y. DERIV (a_z z) x :> y \<and> 0 < y" if x1: "p1 < x" and x2: "x < p2" for x
  proof -
    have cz: "z < cos x" using cos_gt_z[OF assms(1,2)] x1 x2 assms(3,5) by simp
    have "0 < (cos x - z) / (1 + cos x)" using cz assms(1) by (intro divide_pos_pos) linarith+
    then show ?thesis using dr[of x] x1 x2 by auto
  qed
  have C: "continuous_on {p1..p2} (a_z z)"
    by (intro continuous_at_imp_continuous_on ballI DERIV_isCont) (use dr in auto)
  show ?thesis by (rule DERIV_pos_imp_increasing_open[OF assms(4) D C]) (use D in blast)
qed

theorem a_z_inj:
  fixes z p1 p2 :: real
  assumes "0 \<le> z" and "z < 1" and "0 < p1" and "p1 \<le> arccos z" and "0 < p2" and "p2 \<le> arccos z"
    and "a_z z p1 = a_z z p2"
  shows "p1 = p2"
proof (rule ccontr)
  assume ne: "p1 \<noteq> p2"
  then consider "p1 < p2" | "p2 < p1" by linarith
  then show False
  proof cases
    case 1 then show ?thesis using a_z_strict_mono[OF assms(1,2,3) 1 assms(6)] assms(7) by simp
  next
    case 2 then show ?thesis using a_z_strict_mono[OF assms(1,2,5) 2 assms(4)] assms(7) by simp
  qed
qed

theorem theta_z_antimono:
  fixes z p1 p2 :: real
  assumes "0 \<le> z" and "z < 1" and "0 < p1" and "p1 \<le> p2" and "p2 \<le> arccos z"
  shows "theta_z z p2 \<le> theta_z z p1"
proof -
  have d2: "arccos z \<le> pi / 2" by (rule arccos_facts(2)[OF assms(1,2)])
  define f where "f = (\<lambda>x. (a_z z x + b_z z x) / 2)"
  have fe: "f x = theta_z z x" if "0 < x" "x \<le> p2" for x
    unfolding f_def using theta_z_avg[of x z] that assms(5) d2 pi_gt_zero by simp
  have D: "\<exists>y. DERIV f x :> y \<and> y \<le> 0" if x1: "p1 \<le> x" and x2: "x \<le> p2" for x
  proof -
    have x0: "0 < x" and xp: "x < pi" using x1 x2 assms(3,5) d2 pi_gt_zero by linarith+
    have da: "(a_z z has_real_derivative (cos x - z) / (1 + cos x)) (at x)"
      using x0 xp by (intro a_z_deriv) linarith+
    have db: "(b_z z has_real_derivative (z - cos x) / (1 - cos x)) (at x)"
      using x0 xp by (intro b_z_deriv)
    have dd: "(f has_real_derivative ((cos x - z) / (1 + cos x) + (z - cos x) / (1 - cos x)) / 2) (at x)"
      unfolding f_def by (rule DERIV_cdivide[OF DERIV_add[OF da db]])
    have cge: "z \<le> cos x" using cos_ge_z[OF assms(1,2)] x1 x2 assms(3,5) by simp
    have c0: "0 \<le> cos x" using cge assms(1) by linarith
    have c1: "cos x < 1"
    proof -
      have "1 - cos x = 2 * (sin (x / 2))\<^sup>2" by (rule one_minus_cos)
      moreover have "0 < (sin (x / 2))\<^sup>2"
        using x0 xp by (intro zero_less_power sin_gt_zero) simp_all
      ultimately show ?thesis by linarith
    qed
    have n1: "1 + cos x \<noteq> 0" using c0 by linarith
    have n2: "1 - cos x \<noteq> 0" using c1 by linarith
    have n3: "1 - cos x * cos x \<noteq> 0"
    proof -
      have "1 - cos x * cos x = (1 + cos x) * (1 - cos x)" by (simp add: algebra_simps)
      then show ?thesis using n1 n2 by simp
    qed
    have n4: "2 - cos x * (cos x * 2) \<noteq> 0" using n3 by (simp add: algebra_simps)
    have "((cos x - z) / (1 + cos x) + (z - cos x) / (1 - cos x)) / 2
          = - (cos x * (cos x - z)) / ((1 + cos x) * (1 - cos x))"
      using n1 n2 n3 n4 by (simp add: field_simps)
    moreover have "- (cos x * (cos x - z)) / ((1 + cos x) * (1 - cos x)) \<le> 0"
    proof -
      have "0 \<le> cos x * (cos x - z)" using c0 cge by (intro mult_nonneg_nonneg) linarith+
      moreover have "0 < (1 + cos x) * (1 - cos x)" using c0 c1 by (intro mult_pos_pos) linarith+
      ultimately show ?thesis by (simp add: divide_nonpos_pos)
    qed
    ultimately show ?thesis using dd by auto
  qed
  have "f p2 \<le> f p1" by (rule DERIV_nonpos_imp_nonincreasing[OF assms(4)]) (blast intro: D)
  then show ?thesis using fe assms(3,4,5) by simp
qed

theorem theta_z_ge_phi:
  fixes z phi :: real
  assumes "0 \<le> z" and "z < 1" and "0 < phi" and "phi \<le> arccos z"
  shows "phi \<le> theta_z z phi"
proof -
  have d2: "arccos z \<le> pi / 2" by (rule arccos_facts(2)[OF assms(1,2)])
  have "0 < sin phi" using assms(3,4) d2 pi_gt_zero by (intro sin_gt_zero) linarith+
  moreover have "0 \<le> cos phi - z" using cos_ge_z[OF assms] by simp
  ultimately show ?thesis unfolding theta_z_def by simp
qed

section \<open>The range of a_z and the wait of the arc\<close>

lemma sin_lt_self:
  fixes x :: real
  assumes "0 < x" and "x < pi"
  shows "sin x < x"
proof -
  define f where "f = (\<lambda>t::real. t - sin t)"
  have D: "\<exists>y. DERIV f t :> y \<and> 0 < y" if t0: "0 < t" and t1: "t < x" for t
  proof -
    have "(f has_real_derivative 1 - cos t) (at t)" unfolding f_def
      by (auto intro!: derivative_eq_intros)
    moreover have "0 < 1 - cos t"
    proof -
      have "1 - cos t = 2 * (sin (t / 2))\<^sup>2" by (rule one_minus_cos)
      moreover have "0 < (sin (t / 2))\<^sup>2"
        using t0 t1 assms(2) by (intro zero_less_power sin_gt_zero) simp_all
      ultimately show ?thesis by linarith
    qed
    ultimately show ?thesis by blast
  qed
  have C: "continuous_on {0..x} f" unfolding f_def by (intro continuous_intros)
  have "f 0 < f x" by (rule DERIV_pos_imp_increasing_open[OF assms(1) D C]) (use D in blast)
  then show ?thesis unfolding f_def by simp
qed

theorem a_z_image:
  fixes z phi :: real
  assumes "0 \<le> z" and "z < 1" and "0 < phi" and "phi \<le> arccos z"
  shows "0 < a_z z phi" and "a_z z phi \<le> arccos z - sin (arccos z)"
proof -
  have d2: "arccos z \<le> pi / 2" by (rule arccos_facts(2)[OF assms(1,2)])
  have pp: "phi < pi" using assms(4) d2 pi_gt_zero by linarith
  have "0 < sin phi" using assms(3) pp by (intro sin_gt_zero)
  have "phi - sin phi < a_z z phi \<or> phi - sin phi = a_z z phi"
  proof -
    have w: "0 \<le> theta_z z phi - phi" using theta_z_ge_phi[OF assms] by simp
    have "0 \<le> 1 - cos phi" by simp
    then have "0 \<le> (theta_z z phi - phi) * (1 - cos phi)" using w by (intro mult_nonneg_nonneg)
    then show ?thesis using a_z_arc[OF assms(3) pp, of z] by linarith
  qed
  moreover have "sin phi < phi" using assms(3) pp by (rule sin_lt_self)
  ultimately show "0 < a_z z phi" by linarith
  show "a_z z phi \<le> arccos z - sin (arccos z)"
  proof -
    have "a_z z phi \<le> a_z z (arccos z)"
    proof (cases "phi = arccos z")
      case True then show ?thesis by simp
    next
      case False then show ?thesis using a_z_strict_mono[OF assms(1,2,3) _ order_refl] assms(4) by simp
    qed
    then show ?thesis using a_z_at_d[OF assms(1,2)] by simp
  qed
qed

theorem arc_attains:
  fixes z phi :: real
  assumes "0 \<le> z" and "z < 1" and "0 < phi" and "phi \<le> arccos z"
  defines "th \<equiv> theta_z z phi"
  shows "th + x3 th phi / 2 = a_z z phi" and "th - x3 th phi / 2 = b_z z phi"
    and "y3 th phi = 2 * z" and "0 \<le> th - phi"
proof -
  have d2: "arccos z \<le> pi / 2" by (rule arccos_facts(2)[OF assms(1,2)])
  have pp: "phi < pi" using assms(4) d2 pi_gt_zero by linarith
  have sp: "0 < sin phi" using assms(3) pp by (intro sin_gt_zero)
  show "th + x3 th phi / 2 = a_z z phi"
    unfolding th_def using arc_exposures(1)[of "theta_z z phi" phi] a_z_arc[OF assms(3) pp, of z] by simp
  show "th - x3 th phi / 2 = b_z z phi"
    unfolding th_def using arc_exposures(2)[of "theta_z z phi" phi] b_z_arc[OF assms(3) pp, of z] by simp
  show "y3 th phi = 2 * z" unfolding th_def y3_def theta_z_def using sp by (simp add: field_simps)
  show "0 \<le> th - phi" unfolding th_def using theta_z_ge_phi[OF assms(1-4)] by simp
qed

section \<open>The bound\<close>

text \<open>Step (3): on the arc, the lateral constraint $y_3 \le 2z$ gives $\theta \ge \theta_z(\varphi)$, and then
the exposure $a \ge a_z(\varphi)$.\<close>

theorem arc_bounds:
  fixes z phi theta :: real
  assumes "0 < phi" and "phi < pi" and "y3 theta phi \<le> 2 * z"
  shows "theta_z z phi \<le> theta" and "a_z z phi \<le> theta + x3 theta phi / 2"
proof -
  have sp: "0 < sin phi" using assms(1,2) by (intro sin_gt_zero)
  have "(cos phi - z) \<le> (theta - phi) * sin phi" using assms(3) unfolding y3_def by linarith
  then have "(cos phi - z) / sin phi \<le> theta - phi" using sp by (simp add: pos_divide_le_eq)
  then show th: "theta_z z phi \<le> theta" unfolding theta_z_def by linarith
  have "0 \<le> 1 - cos phi" by simp
  then have "(theta_z z phi - phi) * (1 - cos phi) \<le> (theta - phi) * (1 - cos phi)"
    using th by (intro mult_right_mono) linarith+
  then show "a_z z phi \<le> theta + x3 theta phi / 2"
    using a_z_arc[OF assms(1,2), of z] arc_exposures(1)[of theta phi] by linarith
qed

lemma lin_mid:
  fixes th a b :: real
  assumes "th = (a + b) / 2"
  shows "2 * th - a = b"
  using assms by (simp add: field_simps)

lemma lin_end:
  fixes a b d s bz :: real
  assumes "a = d - s" and "d \<le> (a + b) / 2" and "bz = d + s"
  shows "bz \<le> b"
proof -
  have h: "2 * d \<le> a + b" using assms(2) by (simp add: field_simps)
  have e: "bz = b - (a + b - 2 * d)" using assms(1,3) by (simp add: algebra_simps)
  have "0 \<le> a + b - 2 * d" using h by simp
  then show ?thesis using e by simp
qed

theorem planar_exposure_bound_inner:
  fixes z a b :: real
  assumes z: "0 \<le> z" "z < 1" and a: "0 < a" "a < arccos z - sin (arccos z)"
    and arc: "\<exists>phi. 0 < phi \<and> phi < arccos z \<and> a - b = x3 ((a + b) / 2) phi
                      \<and> y3 ((a + b) / 2) phi \<le> 2 * z"
  shows "\<exists>beta. 0 < beta \<and> beta \<le> arccos z \<and> a_z z beta = a
                \<and> (\<forall>beta'. 0 < beta' \<longrightarrow> beta' \<le> arccos z \<longrightarrow> a_z z beta' = a \<longrightarrow> beta' = beta)
                \<and> b_z z beta \<le> b"
proof -
  obtain beta where be: "0 < beta" "beta \<le> arccos z" "a_z z beta = a"
    using a_z_range[OF z a(1) less_imp_le[OF a(2)]] by blast
  obtain phi where ph: "0 < phi" "phi < arccos z" and xe: "a - b = x3 ((a + b) / 2) phi"
    and ye: "y3 ((a + b) / 2) phi \<le> 2 * z" using arc by blast
  define th where "th = (a + b) / 2"
  have d2: "arccos z \<le> pi / 2" by (rule arccos_facts(2)[OF z])
  have pp: "phi < pi" using ph(2) d2 pi_gt_zero by linarith
  have bd: "theta_z z phi \<le> th" and ad: "a_z z phi \<le> th + x3 th phi / 2"
    using arc_bounds[OF ph(1) pp ye[folded th_def]] by simp_all
  have xe': "a - b = x3 th phi" unfolding th_def by (rule xe)
  have h: "x3 th phi = a - b" using xe' by simp
  have aeq: "th + x3 th phi / 2 = a"
    by (subst h, subst th_def) (simp add: field_simps)
  have pb: "phi \<le> beta"
  proof (rule ccontr)
    assume "\<not> phi \<le> beta"
    then have "beta < phi" by simp
    then have "a_z z beta < a_z z phi" using a_z_strict_mono[OF z be(1) _ _] ph(2) by simp
    then show False using ad aeq be(3) by linarith
  qed
  have "theta_z z beta \<le> theta_z z phi"
    using theta_z_antimono[OF z ph(1) pb be(2)] .
  then have "theta_z z beta \<le> th" using bd by linarith
  moreover have bpp: "beta < pi" using be(2) d2 pi_gt_zero by linarith
  ultimately have "b_z z beta \<le> 2 * th - a"
    using b_z_from_theta[OF be(1) bpp, of z] be(3) by linarith
  moreover have "2 * th - a = b" by (rule lin_mid[OF th_def])
  ultimately have "b_z z beta \<le> b" by simp
  moreover have "\<forall>beta'. 0 < beta' \<longrightarrow> beta' \<le> arccos z \<longrightarrow> a_z z beta' = a \<longrightarrow> beta' = beta"
    using a_z_inj[OF z be(1,2)] be(3) by auto
  ultimately show ?thesis using be by blast
qed

theorem planar_exposure_bound:
  fixes z a b :: real
  assumes z: "0 \<le> z" "z < 1" and a: "0 < a" "a \<le> arccos z - sin (arccos z)"
    and th: "arccos z \<le> (a + b) / 2"
    and arc: "a < arccos z - sin (arccos z) \<Longrightarrow>
              \<exists>phi. 0 < phi \<and> phi < arccos z \<and> a - b = x3 ((a + b) / 2) phi
                      \<and> y3 ((a + b) / 2) phi \<le> 2 * z"
  shows "\<exists>beta. 0 < beta \<and> beta \<le> arccos z \<and> a_z z beta = a
                \<and> (\<forall>beta'. 0 < beta' \<longrightarrow> beta' \<le> arccos z \<longrightarrow> a_z z beta' = a \<longrightarrow> beta' = beta)
                \<and> b_z z beta \<le> b"
proof (cases "a < arccos z - sin (arccos z)")
  case True
  from planar_exposure_bound_inner[OF z a(1) True arc[OF True]] show ?thesis .
next
  case False
  then have ae: "a = arccos z - sin (arccos z)" using a(2) by simp
  have d0: "0 < arccos z" by (rule arccos_facts(1)[OF z])
  have ad: "a_z z (arccos z) = a" using a_z_at_d[OF z] ae by simp
  have bd: "b_z z (arccos z) \<le> b" by (rule lin_end[OF ae th b_z_at_d[OF z]])
  have uq: "\<forall>beta'. 0 < beta' \<longrightarrow> beta' \<le> arccos z \<longrightarrow> a_z z beta' = a \<longrightarrow> beta' = arccos z"
  proof (intro allI impI)
    fix beta' assume h1: "0 < beta'" and h2: "beta' \<le> arccos z" and h3: "a_z z beta' = a"
    have "a_z z beta' = a_z z (arccos z)" using h3 ad by simp
    then show "beta' = arccos z" by (rule a_z_inj[OF z(1) z(2) h1 h2 d0 order_refl])
  qed
  show ?thesis using d0 ad bd uq by (intro exI[of _ "arccos z"]) simp
qed

section \<open>Step (1): odd turns beyond the first are dominated\<close>

theorem multi_turn_dominated:
  fixes z :: real and k :: nat
  assumes "0 \<le> z" and "z < 1" and "1 \<le> k"
  shows "arccos z - sin (arccos z) < real k * pi" and "arccos z + sin (arccos z) < real k * pi"
proof -
  have d2: "arccos z \<le> pi / 2" by (rule arccos_facts(2)[OF assms(1,2)])
  have d0: "0 < arccos z" by (rule arccos_facts(1)[OF assms(1,2)])
  have s1: "sin (arccos z) \<le> 1" by simp
  have s0: "- 1 \<le> sin (arccos z)" by simp
  have k1: "(1::real) \<le> real k" using assms(3) by simp
  have "pi \<le> real k * pi" using k1 pi_gt_zero by (simp add: mult_le_cancel_right1)
  moreover have "2 < pi" using pi_gt3 by simp
  ultimately show "arccos z - sin (arccos z) < real k * pi" and "arccos z + sin (arccos z) < real k * pi"
    using d2 s1 s0 by linarith+
qed

end
