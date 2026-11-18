(*  Title:      Square_Unified_Condition.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    One sufficient condition for the optimality of the square pulse in the qubit-memory transfer under slow
    (quasi-static) offsets with second moments sq, sm and covariance C, and relaxation of the qubit (gq) and of the
    memory (gm), at second order in the offsets: with V = sq + sm - 2 C and A0 = pi z0 / 2, the error of every pulse
    is at least the error of the square pulse as soon as
        V z0 <= sqrt (((sq + C) A0 + gq) ((sm + C) A0 + gm)).
    The exposures x = A - A0, y = B - A0 and the residual u = |zeta| enter through the disk inequality
    (z0 - u)^2 <= x y (proved in Robust_Disk). Everything is over the reals; the dynamics is not formalised.
*)

theory Square_Unified_Condition
  imports "HOL-Analysis.Analysis"
begin

section \<open>The unified condition under which the square pulse minimises the error\<close>

text \<open>
  With slow noise on both elements (variances @{text sq}, @{text sm}, covariance @{text C})
  and relaxation rates @{text gq}, @{text gm}, the error difference (times 6) between an
  arbitrary pulse and the square pulse is the expression in the conclusion below.  It is
  nonnegative whenever @{text "V * z0 \<le> sqrt (a * b)"}, with @{text "V = sq + sm - 2*C"}.
\<close>

lemma amgm_disk:
  fixes a b x y t s :: real
  assumes "0 \<le> a" "0 \<le> b" "0 \<le> x" "0 \<le> y" "0 \<le> t" "t^2 \<le> x*y" "s = sqrt (a*b)"
  shows "2 * s * t \<le> a*x + b*y"
proof -
  have ab: "0 \<le> a*b" by (rule mult_nonneg_nonneg[OF assms(1,2)])
  have s2: "s^2 = a*b" unfolding assms(7) by (rule real_sqrt_pow2[OF ab])
  have T0: "0 \<le> a*x + b*y"
    using mult_nonneg_nonneg[OF assms(1,3)] mult_nonneg_nonneg[OF assms(2,4)] by linarith
  have "(2 * s * t)^2 = 4*(a*b)*t^2" using s2 by (simp add: power_mult_distrib)
  also have "\<dots> \<le> 4*(a*b)*(x*y)" using assms(1,2,6) by (intro mult_left_mono) simp_all
  also have "\<dots> \<le> (a*x + b*y)^2" using zero_le_power2[of "a*x - b*y"] by (simp add: power2_eq_square algebra_simps)
  finally have H: "(2 * s * t)^2 \<le> (a*x + b*y)^2" .
  show ?thesis
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have lt: "a*x + b*y < 2 * s * t" by simp
    have "0 < (2 * s * t - (a*x + b*y)) * (2 * s * t + (a*x + b*y))"
      using lt T0 by (intro mult_pos_pos) linarith+
    then have "(a*x + b*y)^2 < (2 * s * t)^2" by (simp add: power2_eq_square algebra_simps)
    with H show False by simp
  qed
qed

theorem square_unified:
  fixes z0 A0 sq sm C gq gm x y u :: real
  assumes "0 < z0" "A0 = pi/2 * z0" "0 \<le> sq" "0 \<le> sm" "0 \<le> C" "0 \<le> gq" "0 \<le> gm"
      "0 \<le> sq + sm - 2*C" "0 \<le> x" "0 \<le> y" "0 \<le> u"
      "u \<le> z0 \<Longrightarrow> (z0 - u)^2 \<le> x*y"
      "(sq + sm - 2*C) * z0 \<le> sqrt (((sq + C)*A0 + gq) * ((sm + C)*A0 + gm))"
  shows "0 \<le> 2*(sq + sm - 2*C)*(u^2 - z0^2)
            + 2*(((sq + C)*A0 + gq)*x + ((sm + C)*A0 + gm)*y)
            + sq*x^2 + 2*C*x*y + sm*y^2"
proof -
  have A0: "0 \<le> A0"
  proof -
    have "0 < pi/2 * z0" using pi_gt_zero assms(1) by (intro mult_pos_pos) simp_all
    then show ?thesis using assms(2) by simp
  qed
  have a0: "0 \<le> (sq + C)*A0 + gq"
    using mult_nonneg_nonneg[of "sq + C" A0] assms(3,5,6) A0 by linarith
  have b0: "0 \<le> (sm + C)*A0 + gm"
    using mult_nonneg_nonneg[of "sm + C" A0] assms(4,5,7) A0 by linarith
  define V where "V = sq + sm - 2*C"
  have e: "2*(sq + sm - 2*C)*(u^2 - z0^2) = 2*V*(u^2 - z0^2)" by (simp add: V_def)
  define s where "s = sqrt (((sq + C)*A0 + gq) * ((sm + C)*A0 + gm))"
  have V0: "0 \<le> V" using assms(8) V_def by simp
  have quad: "0 \<le> sq*x^2 + 2*C*x*y + sm*y^2"
  proof -
    have "0 \<le> sq*x^2" "0 \<le> sm*y^2" using assms(3,4) by simp_all
    moreover have "0 \<le> C*x*y" using assms(5,9,10) by (intro mult_nonneg_nonneg) simp_all
    ultimately show ?thesis by linarith
  qed
  have lin: "0 \<le> 2*(((sq + C)*A0 + gq)*x + ((sm + C)*A0 + gm)*y)"
  proof -
    have h1: "0 \<le> ((sq + C)*A0 + gq)*x" by (rule mult_nonneg_nonneg[OF a0 assms(9)])
    have h2: "0 \<le> ((sm + C)*A0 + gm)*y" by (rule mult_nonneg_nonneg[OF b0 assms(10)])
    show ?thesis by (intro mult_nonneg_nonneg add_nonneg_nonneg h1 h2) simp
  qed
  have hs: "V * z0 \<le> s" using assms(13) V_def s_def by simp
  show ?thesis
  proof (cases "u \<le> z0")
    case True
    have d0: "0 \<le> z0 - u" using True by simp
    have key: "2 * s * (z0 - u) \<le> ((sq + C)*A0 + gq)*x + ((sm + C)*A0 + gm)*y"
      by (rule amgm_disk[OF a0 b0 assms(9,10) d0 assms(12)[OF True] s_def])
    have "0 \<le> (z0 - u) * (s - V*z0)" using d0 hs by (intro mult_nonneg_nonneg) simp_all
    moreover have "0 \<le> V * (z0 - u) * (z0 - u)"
      using V0 d0 by (intro mult_nonneg_nonneg) simp_all
    ultimately have "0 \<le> (z0 - u)*(s - V*z0) * 4 + 2 * (V * (z0 - u) * (z0 - u))" by linarith
    then have t1: "0 \<le> 2*V*(u^2 - z0^2) + 4 * s * (z0 - u)"
      by (simp add: algebra_simps power2_eq_square)
    have t2: "0 \<le> 2 * (((sq + C)*A0 + gq)*x + ((sm + C)*A0 + gm)*y - 2 * s * (z0 - u))"
      using key by simp
    have f: "0 \<le> (2*V*(u^2 - z0^2) + 4 * s * (z0 - u))
        + 2 * (((sq + C)*A0 + gq)*x + ((sm + C)*A0 + gm)*y - 2 * s * (z0 - u))
        + (sq*x^2 + 2*C*x*y + sm*y^2)"
      by (rule add_nonneg_nonneg[OF add_nonneg_nonneg[OF t1 t2] quad])
    have g: "(2*V*(u^2 - z0^2) + 4 * s * (z0 - u))
        + 2 * (((sq + C)*A0 + gq)*x + ((sm + C)*A0 + gm)*y - 2 * s * (z0 - u))
        + (sq*x^2 + 2*C*x*y + sm*y^2)
        = 2*(sq + sm - 2*C)*(u^2 - z0^2)
            + 2*(((sq + C)*A0 + gq)*x + ((sm + C)*A0 + gm)*y)
            + sq*x^2 + 2*C*x*y + sm*y^2"
      by (simp add: V_def algebra_simps)
    show ?thesis using f by (subst (asm) g) assumption
  next
    case False
    then have "z0 \<le> u" by simp
    then have "z0^2 \<le> u^2" using assms(1) by (simp add: power_mono)
    then have "0 \<le> 2*V*(u^2 - z0^2)" using V0 by (intro mult_nonneg_nonneg) simp_all
    then show ?thesis using quad lin e by linarith
  qed
qed

corollary square_unified_no_relax:
  fixes z0 A0 sq sm C x y u :: real
  assumes "0 < z0" "A0 = pi/2 * z0" "0 \<le> sq" "0 \<le> sm" "0 \<le> C"
      "0 \<le> sq + sm - 2*C" "0 \<le> x" "0 \<le> y" "0 \<le> u"
      "u \<le> z0 \<Longrightarrow> (z0 - u)^2 \<le> x*y"
      "(sq + sm - 2*C) * z0 \<le> A0 * sqrt ((sq + C) * (sm + C))"
  shows "0 \<le> 2*(sq + sm - 2*C)*(u^2 - z0^2)
            + 2*((sq + C)*A0*x + (sm + C)*A0*y) + sq*x^2 + 2*C*x*y + sm*y^2"
proof -
  have A0: "0 \<le> A0"
  proof -
    have "0 < pi/2 * z0" using pi_gt_zero assms(1) by (intro mult_pos_pos) simp_all
    then show ?thesis using assms(2) by simp
  qed
  have "sqrt (((sq + C)*A0) * ((sm + C)*A0)) = A0 * sqrt ((sq + C) * (sm + C))"
  proof -
    have "((sq + C)*A0) * ((sm + C)*A0) = A0^2 * ((sq + C) * (sm + C))"
      by (simp add: power2_eq_square algebra_simps)
    then show ?thesis using A0 by (simp add: real_sqrt_mult)
  qed
  then have "(sq + sm - 2*C) * z0
      \<le> sqrt (((sq + C)*A0 + 0) * ((sm + C)*A0 + 0))" using assms(11) by simp
  from square_unified[OF assms(1,2,3,4,5) order_refl order_refl assms(6,7,8,9,10) this]
  show ?thesis by simp
qed

corollary square_unified_qubit_only:
  fixes z0 A0 sq gq gm x y u :: real
  assumes "0 < z0" "A0 = pi/2 * z0" "0 \<le> sq" "0 \<le> gq" "0 \<le> gm"
      "0 \<le> x" "0 \<le> y" "0 \<le> u"
      "u \<le> z0 \<Longrightarrow> (z0 - u)^2 \<le> x*y"
      "sq * z0 \<le> sqrt ((sq*A0 + gq) * gm)"
  shows "0 \<le> 2 * sq * (u^2 - z0^2) + 2*((sq*A0 + gq)*x + gm*y) + sq*x^2"
proof -
  have "(sq + 0 - 2*0) * z0 \<le> sqrt (((sq + 0)*A0 + gq) * ((0 + 0)*A0 + gm))"
    using assms(10) by simp
  from square_unified[OF assms(1,2,3) order_refl order_refl assms(4,5) _ assms(6,7,8,9) this]
  show ?thesis using assms(3) by simp
qed

corollary square_unified_uncorrelated_needs_relax:
  fixes z0 A0 sq sm :: real
  assumes "0 < z0" "A0 = pi/2 * z0" "0 \<le> sq" "0 \<le> sm" "0 < sq + sm"
  shows "\<not> ((sq + sm - 2*0) * z0 \<le> sqrt (((sq + 0)*A0 + 0) * ((sm + 0)*A0 + 0)))"
proof
  assume H: "(sq + sm - 2*0) * z0 \<le> sqrt (((sq + 0)*A0 + 0) * ((sm + 0)*A0 + 0))"
  define Q where "Q = pi/4 * z0 * (sq + sm)"
  have Q0: "0 \<le> Q" using assms unfolding Q_def by simp
  have "sq*A0 * (sm*A0) = A0^2 * (sq * sm)" by (simp add: power2_eq_square algebra_simps)
  also have "\<dots> \<le> A0^2 * ((sq + sm)^2/4)"    using zero_le_power2[of "sq - sm"]
    by (intro mult_left_mono) (simp_all add: power2_eq_square algebra_simps)
  also have "\<dots> = Q^2" unfolding Q_def assms(2) by (simp add: power2_eq_square algebra_simps)
  finally have P: "sq*A0 * (sm*A0) \<le> Q^2" .
  have "sqrt (sq*A0 * (sm*A0)) \<le> Q" using real_sqrt_le_mono[OF P] Q0 by simp
  with H have "(sq + sm) * z0 \<le> Q" by simp
  moreover have "Q < (sq + sm) * z0"
  proof -
    have "pi/4 < 1" using pi_less_4 by simp
    then have "pi/4 * ((sq + sm) * z0) < 1 * ((sq + sm) * z0)"
      using assms(1,5) by (intro mult_strict_right_mono) simp_all
    then show ?thesis unfolding Q_def by (simp add: algebra_simps)
  qed
  ultimately show False by simp
qed

end
