(*  Title:      Memory_Access_Extras.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    From "Exact limits for writing a quantum memory" (C. Marín, draft, November 2026): the familiar estimate
    exp(-pi (gq + gm)/(4G)) is a rigorous lower bound for the maximum, and an exact slow-noise counterexample.
*)

theory Memory_Access_Extras
  imports Memory_Access_Floors Memory_Access_All_Pulses Memory_Access_Dephasing
begin

section \<open>1. The folk-number inequality\<close>

lemma sin_half_pi_ge:
  fixes x :: real
  assumes "0 \<le> x" and "x \<le> 1"
  shows "x \<le> sin (pi / 2 * x)"
proof -
  define f where "f = (\<lambda>x::real. x - sin (pi / 2 * x))"
  define f' where "f' = (\<lambda>x::real. 1 - cos (pi / 2 * x) * (pi / 2))"
  have cv: "convex_on {0..1} f"
  proof (rule convex_on_realI[where f' = f'])
    show "connected {0..1::real}" by simp
  next
    fix x :: real
    assume "x \<in> {0..1}"
    have "(f has_real_derivative 1 - cos (pi / 2 * x) * (pi / 2 * 1)) (at x)"
      unfolding f_def by (auto intro!: derivative_eq_intros)
    then show "(f has_real_derivative f' x) (at x)" unfolding f'_def by simp
  next
    fix x y :: real
    assume xy: "x \<in> {0..1}" "y \<in> {0..1}" "x \<le> y"
    have "cos (pi / 2 * y) \<le> cos (pi / 2 * x)"
      using xy by (intro cos_monotone_0_pi_le) (auto simp: field_simps)
    then show "f' x \<le> f' y" unfolding f'_def using pi_gt_zero by (simp add: mult_right_mono)
  qed
  have "f ((1 - x) * 0 + x * 1) \<le> (1 - x) * f 0 + x * f 1"
    using convex_onD[OF cv, of x 0 1] assms by (simp add: real_scaleR_def)
  then show ?thesis unfolding f_def by simp
qed

lemma folk_aux:
  fixes G x :: real
  assumes "0 < G" and "0 < x"
  shows "G\<^sup>2 / (G * x)\<^sup>2 * x\<^sup>2 = 1"
proof -
  have "G \<noteq> 0" "x \<noteq> 0" using assms by simp_all
  then show ?thesis by (simp add: power_mult_distrib field_simps)
qed

lemma folk_stopped_pulse:
  fixes G gq gm gb d \<Omega> :: real
  assumes "0 < G" and "0 \<le> gq" and "0 \<le> gm" and "gb = (gq + gm) / 2"
    and "d = gq - gm" and "G\<^sup>2 > d\<^sup>2 / 16" and "\<Omega> = sqrt (G\<^sup>2 - d\<^sup>2 / 16)"
  shows "exp (- pi * (gq + gm) / (4 * G))
         \<le> G\<^sup>2 / \<Omega>\<^sup>2 * exp (- gb * (pi / (2 * G))) * (sin (\<Omega> * (pi / (2 * G))))\<^sup>2"
proof -
  have om2: "\<Omega>\<^sup>2 = G\<^sup>2 - d\<^sup>2 / 16" using assms(6,7) by (simp add: real_sqrt_pow2)
  have om: "0 < \<Omega>" using assms(6,7) by simp
  have omG: "\<Omega> \<le> G"
  proof -
    have h: "\<Omega>\<^sup>2 \<le> G\<^sup>2" using om2 by simp
    have g0: "0 \<le> G" using assms(1) by simp
    show ?thesis by (rule power2_le_imp_le[OF h g0])
  qed
  let ?x = "\<Omega> / G"
  have x0: "0 \<le> ?x" and x1: "?x \<le> 1" using om omG assms(1) by (simp_all add: field_simps)
  have arg: "\<Omega> * (pi / (2 * G)) = pi / 2 * ?x" using assms(1) by (simp add: field_simps)
  have s: "?x \<le> sin (\<Omega> * (pi / (2 * G)))" unfolding arg by (rule sin_half_pi_ge[OF x0 x1])
  have s2: "?x\<^sup>2 \<le> (sin (\<Omega> * (pi / (2 * G))))\<^sup>2"
    using s x0 by (simp add: power_mono)
  have e: "- gb * (pi / (2 * G)) = - pi * (gq + gm) / (4 * G)"
    using assms(1,4) by (simp add: field_simps)
  have Gne: "G \<noteq> 0" using assms(1) by simp
  have Ome: "\<Omega> \<noteq> 0" using om by simp
  have xpos: "0 < \<Omega> / G" using om assms(1) by simp
  have fa: "G\<^sup>2 / (G * (\<Omega> / G))\<^sup>2 * (\<Omega> / G)\<^sup>2 = 1" by (rule folk_aux[OF assms(1) xpos])
  have Gx: "G * (\<Omega> / G) = \<Omega>" using Gne by simp
  have key: "G\<^sup>2 / \<Omega>\<^sup>2 * ?x\<^sup>2 = 1" using fa unfolding Gx .
  have "exp (- pi * (gq + gm) / (4 * G)) = G\<^sup>2 / \<Omega>\<^sup>2 * ?x\<^sup>2 * exp (- pi * (gq + gm) / (4 * G))"
    by (simp only: key mult_1_left)
  also have "\<dots> \<le> G\<^sup>2 / \<Omega>\<^sup>2 * (sin (\<Omega> * (pi / (2 * G))))\<^sup>2 * exp (- pi * (gq + gm) / (4 * G))"
    using s2 om by (intro mult_right_mono mult_left_mono) simp_all
  also have "\<dots> = G\<^sup>2 / \<Omega>\<^sup>2 * exp (- gb * (pi / (2 * G))) * (sin (\<Omega> * (pi / (2 * G))))\<^sup>2"
    unfolding e by (simp add: mult.commute mult.left_commute)
  finally show ?thesis .
qed

theorem folk_number_bound:
  fixes G gq gm gb d \<Omega> :: real
  assumes "0 < G" and "0 \<le> gq" and "0 \<le> gm" and "gb = (gq + gm) / 2" and "0 < gb"
    and "d = gq - gm" and "G\<^sup>2 > d\<^sup>2 / 16" and "\<Omega> = sqrt (G\<^sup>2 - d\<^sup>2 / 16)"
  shows "exp (- pi * (gq + gm) / (4 * G))
         \<le> 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- (gb / \<Omega>) * arctan (2 * \<Omega> / gb))"
proof -
  have t: "0 \<le> pi / (2 * G)" using assms(1) by simp
  have "exp (- pi * (gq + gm) / (4 * G)) \<le> G\<^sup>2 / \<Omega>\<^sup>2 * exp (- gb * (pi / (2 * G))) * (sin (\<Omega> * (pi / (2 * G))))\<^sup>2"
    by (rule folk_stopped_pulse[OF assms(1,2,3,4,6,7,8)])
  also have "\<dots> \<le> 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- (gb / \<Omega>) * arctan (2 * \<Omega> / gb))"
    by (rule resonant_pulse_max_bound[OF assms(1,2,3,4,5,6,7,8) t])
  finally show ?thesis .
qed

corollary folk_number_max_population:
  fixes G gq gm :: real
  assumes "0 < G" and "0 \<le> gq" and "0 \<le> gm" and "0 < (gq + gm) / 2"
    and "G\<^sup>2 > (gq - gm)\<^sup>2 / 16"
  shows "exp (- pi * (gq + gm) / (4 * G)) \<le> max_population G gq gm"
  unfolding max_population_def
  by (rule folk_number_bound[OF assms(1,2,3) refl assms(4) refl assms(5) refl])

section \<open>2. Slow noise: an exact counterexample\<close>

text \<open>Lossless model: amplitudes @{text "(a, b)"} with @{text "i a' = D a + g b"}, @{text "i b' = g a"},
  constant unknown detuning @{text "D = +-1"}, control @{text "g"} piecewise constant.\<close>

subsection \<open>One segment with constant g and D\<close>

definition Om :: "real \<Rightarrow> real \<Rightarrow> real" where
  "Om g D = sqrt (g\<^sup>2 + D\<^sup>2 / 4)"

definition sm :: "complex \<Rightarrow> complex \<times> complex \<Rightarrow> complex \<times> complex" where
  "sm z ab = (z * fst ab, z * snd ab)"

text \<open>@{text "Umat D g C S"} is @{text "C I - i S (H - D/2 I)"} with @{text "H = [[D, g], [g, 0]]"}.\<close>

definition Umat :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex \<times> complex \<Rightarrow> complex \<times> complex" where
  "Umat D g C S ab =
     ((of_real C - \<i> * of_real (D / 2) * of_real S) * fst ab - \<i> * of_real g * of_real S * snd ab,
      - (\<i> * of_real g * of_real S) * fst ab + (of_real C + \<i> * of_real (D / 2) * of_real S) * snd ab)"

text \<open>The closed propagator: @{text "e^{-iHt} = e^{-iDt/2} [cos(Om t) I - i (sin(Om t)/Om) (H - D/2 I)]"}.\<close>

definition seg :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex \<times> complex \<Rightarrow> complex \<times> complex" where
  "seg D g t ab = sm (cis (- D * t / 2)) (Umat D g (cos (Om g D * t)) (sin (Om g D * t) / Om g D) ab)"

lemma sm_sm: "sm z (sm w ab) = sm (z * w) ab"
  by (simp add: sm_def mult.assoc)

lemma Umat_sm: "Umat D g C S (sm z ab) = sm z (Umat D g C S ab)"
  by (simp add: Umat_def sm_def algebra_simps)

lemma seg_zero: "seg D g 0 ab = ab"
  by (cases ab) (simp add: seg_def Umat_def sm_def)

subsubsection \<open>(i) The segment solves the equations\<close>

definition Af :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex" where
  "Af Dc gc Wc u a0 b0 z =
     a0 * (exp (- \<i> * Dc / 2 * z) * cos (Wc * z))
     + (- \<i> * (Dc / 2) * a0 - \<i> * gc * b0) * u * (exp (- \<i> * Dc / 2 * z) * sin (Wc * z))"

definition Bf :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex" where
  "Bf Dc gc Wc u a0 b0 z =
     b0 * (exp (- \<i> * Dc / 2 * z) * cos (Wc * z))
     + (- \<i> * gc * a0 + \<i> * (Dc / 2) * b0) * u * (exp (- \<i> * Dc / 2 * z) * sin (Wc * z))"

lemma dE1:
  fixes cc Wc z :: complex
  shows "((\<lambda>z. exp (cc * z) * cos (Wc * z)) has_field_derivative
          cc * (exp (cc * z) * cos (Wc * z)) - Wc * (exp (cc * z) * sin (Wc * z))) (at z)"
proof -
  have "((\<lambda>z. exp (cc * z) * cos (Wc * z)) has_field_derivative
        exp (cc * z) * cc * cos (Wc * z) + exp (cc * z) * (- sin (Wc * z) * Wc)) (at z)"
    by (auto intro!: derivative_eq_intros)
  then show ?thesis by (rule DERIV_cong) (simp add: algebra_simps)
qed

lemma dE3:
  fixes cc Wc z :: complex
  shows "((\<lambda>z. exp (cc * z) * sin (Wc * z)) has_field_derivative
          cc * (exp (cc * z) * sin (Wc * z)) + Wc * (exp (cc * z) * cos (Wc * z))) (at z)"
proof -
  have "((\<lambda>z. exp (cc * z) * sin (Wc * z)) has_field_derivative
        exp (cc * z) * cc * sin (Wc * z) + exp (cc * z) * (cos (Wc * z) * Wc)) (at z)"
    by (auto intro!: derivative_eq_intros)
  then show ?thesis by (rule DERIV_cong) (simp add: algebra_simps)
qed

lemma alg_A:
  fixes Dc gc Wc u a0 b0 E1 E3 :: complex
  assumes W2: "Wc * Wc = gc * gc + Dc * Dc / 4" and Wu: "Wc * u = 1"
    and ka: "ka = - \<i> * (Dc / 2) * a0 - \<i> * gc * b0" and kb: "kb = - \<i> * gc * a0 + \<i> * (Dc / 2) * b0"
  shows "a0 * ((- \<i> * Dc / 2) * E1 - Wc * E3) + ka * u * ((- \<i> * Dc / 2) * E3 + Wc * E1)
         = - \<i> * (Dc * (a0 * E1 + ka * u * E3) + gc * (b0 * E1 + kb * u * E3))"
proof -
  have ii: "\<i> * \<i> = (-1 :: complex)" by simp
  have h: "Wc * Wc * u = Wc" by (simp add: mult.assoc Wu)
  have diff: "(a0 * ((- \<i> * Dc / 2) * E1 - Wc * E3) + ka * u * ((- \<i> * Dc / 2) * E3 + Wc * E1))
              - (- \<i> * (Dc * (a0 * E1 + ka * u * E3) + gc * (b0 * E1 + kb * u * E3)))
            = E1 * (a0 * (- \<i> * Dc / 2) + ka * u * Wc + \<i> * (Dc * a0 + gc * b0))
              + E3 * (- a0 * Wc + u * (ka * \<i> * Dc / 2 + \<i> * gc * kb))"
    by (simp add: algebra_simps)
  have alpha: "a0 * (- \<i> * Dc / 2) + ka * u * Wc + \<i> * (Dc * a0 + gc * b0) = 0"
  proof -
    have f: "ka * u * Wc = ka"
    proof -
      have "ka * u * Wc = ka * (Wc * u)" by (simp add: algebra_simps)
      then show ?thesis using Wu by simp
    qed
    have "a0 * (- \<i> * Dc / 2) + ka * u * Wc + \<i> * (Dc * a0 + gc * b0)
          = a0 * (- \<i> * Dc / 2) + ka + \<i> * (Dc * a0 + gc * b0)" by (simp only: f)
    also have "\<dots> = 0" by (simp add: ka algebra_simps)
    finally show ?thesis .
  qed
  have beta: "- a0 * Wc + u * (ka * \<i> * Dc / 2 + \<i> * gc * kb) = 0"
  proof -
    have e: "- a0 * Wc = - a0 * ((gc * gc + Dc * Dc / 4) * u)"
    proof -
      have "- a0 * Wc = - a0 * (Wc * Wc * u)" using h by simp
      also have "\<dots> = - a0 * ((gc * gc + Dc * Dc / 4) * u)" using W2 by simp
      finally show ?thesis .
    qed
    have T: "- a0 * (gc * gc + Dc * Dc / 4) + ka * \<i> * Dc / 2 + \<i> * gc * kb
             = - (\<i> * \<i> + 1) * (a0 * gc * gc + a0 * Dc * Dc / 4)"
      by (simp add: ka kb algebra_simps)
    then have T0: "- a0 * (gc * gc + Dc * Dc / 4) + ka * \<i> * Dc / 2 + \<i> * gc * kb = 0" using ii by simp
    have "- a0 * Wc + u * (ka * \<i> * Dc / 2 + \<i> * gc * kb)
          = u * (- a0 * (gc * gc + Dc * Dc / 4) + ka * \<i> * Dc / 2 + \<i> * gc * kb)"
      using e by (simp add: algebra_simps)
    then show ?thesis using T0 by simp
  qed
  have "(a0 * ((- \<i> * Dc / 2) * E1 - Wc * E3) + ka * u * ((- \<i> * Dc / 2) * E3 + Wc * E1))
        - (- \<i> * (Dc * (a0 * E1 + ka * u * E3) + gc * (b0 * E1 + kb * u * E3))) = 0"
    unfolding diff alpha beta by simp
  then show ?thesis by (rule iffD1[OF right_minus_eq])
qed

lemma alg_B:
  fixes Dc gc Wc u a0 b0 E1 E3 :: complex
  assumes W2: "Wc * Wc = gc * gc + Dc * Dc / 4" and Wu: "Wc * u = 1"
    and ka: "ka = - \<i> * (Dc / 2) * a0 - \<i> * gc * b0" and kb: "kb = - \<i> * gc * a0 + \<i> * (Dc / 2) * b0"
  shows "b0 * ((- \<i> * Dc / 2) * E1 - Wc * E3) + kb * u * ((- \<i> * Dc / 2) * E3 + Wc * E1)
         = - \<i> * gc * (a0 * E1 + ka * u * E3)"
proof -
  have ii: "\<i> * \<i> = (-1 :: complex)" by simp
  have h: "Wc * Wc * u = Wc" by (simp add: mult.assoc Wu)
  have diff: "(b0 * ((- \<i> * Dc / 2) * E1 - Wc * E3) + kb * u * ((- \<i> * Dc / 2) * E3 + Wc * E1))
              - (- \<i> * gc * (a0 * E1 + ka * u * E3))
            = E1 * (b0 * (- \<i> * Dc / 2) + kb * u * Wc + \<i> * gc * a0)
              + E3 * (- b0 * Wc + u * (kb * (- \<i> * Dc / 2) + \<i> * gc * ka))"
    by (simp add: algebra_simps)
  have alpha: "b0 * (- \<i> * Dc / 2) + kb * u * Wc + \<i> * gc * a0 = 0"
  proof -
    have f: "kb * u * Wc = kb"
    proof -
      have "kb * u * Wc = kb * (Wc * u)" by (simp add: algebra_simps)
      then show ?thesis using Wu by simp
    qed
    have "b0 * (- \<i> * Dc / 2) + kb * u * Wc + \<i> * gc * a0
          = b0 * (- \<i> * Dc / 2) + kb + \<i> * gc * a0" by (simp only: f)
    also have "\<dots> = 0" by (simp add: kb algebra_simps)
    finally show ?thesis .
  qed
  have beta: "- b0 * Wc + u * (kb * (- \<i> * Dc / 2) + \<i> * gc * ka) = 0"
  proof -
    have e: "- b0 * Wc = - b0 * ((gc * gc + Dc * Dc / 4) * u)"
    proof -
      have "- b0 * Wc = - b0 * (Wc * Wc * u)" using h by simp
      also have "\<dots> = - b0 * ((gc * gc + Dc * Dc / 4) * u)" using W2 by simp
      finally show ?thesis .
    qed
    have T: "- b0 * (gc * gc + Dc * Dc / 4) + kb * (- \<i> * Dc / 2) + \<i> * gc * ka
             = - (\<i> * \<i> + 1) * (b0 * gc * gc + b0 * Dc * Dc / 4)"
      by (simp add: ka kb algebra_simps)
    then have T0: "- b0 * (gc * gc + Dc * Dc / 4) + kb * (- \<i> * Dc / 2) + \<i> * gc * ka = 0" using ii by simp
    have "- b0 * Wc + u * (kb * (- \<i> * Dc / 2) + \<i> * gc * ka)
          = u * (- b0 * (gc * gc + Dc * Dc / 4) + kb * (- \<i> * Dc / 2) + \<i> * gc * ka)"
      using e by (simp add: algebra_simps)
    then show ?thesis using T0 by simp
  qed
  have "(b0 * ((- \<i> * Dc / 2) * E1 - Wc * E3) + kb * u * ((- \<i> * Dc / 2) * E3 + Wc * E1))
        - (- \<i> * gc * (a0 * E1 + ka * u * E3)) = 0"
    unfolding diff alpha beta by simp
  then show ?thesis by (rule iffD1[OF right_minus_eq])
qed

lemma ode_complex:
  fixes Dc gc Wc u a0 b0 :: complex
  assumes W2: "Wc * Wc = gc * gc + Dc * Dc / 4" and Wu: "Wc * u = 1"
  shows "(Af Dc gc Wc u a0 b0 has_field_derivative
            - \<i> * (Dc * Af Dc gc Wc u a0 b0 z + gc * Bf Dc gc Wc u a0 b0 z)) (at z)"
    and "(Bf Dc gc Wc u a0 b0 has_field_derivative - \<i> * gc * Af Dc gc Wc u a0 b0 z) (at z)"
proof -
  have d1: "((\<lambda>z. exp ((- \<i> * Dc / 2) * z) * cos (Wc * z)) has_field_derivative
             (- \<i> * Dc / 2) * (exp ((- \<i> * Dc / 2) * z) * cos (Wc * z)) - Wc * (exp ((- \<i> * Dc / 2) * z) * sin (Wc * z))) (at z)"
    by (rule dE1)
  have d3: "((\<lambda>z. exp ((- \<i> * Dc / 2) * z) * sin (Wc * z)) has_field_derivative
             (- \<i> * Dc / 2) * (exp ((- \<i> * Dc / 2) * z) * sin (Wc * z)) + Wc * (exp ((- \<i> * Dc / 2) * z) * cos (Wc * z))) (at z)"
    by (rule dE3)
  have dA: "(Af Dc gc Wc u a0 b0 has_field_derivative
        a0 * ((- \<i> * Dc / 2) * (exp ((- \<i> * Dc / 2) * z) * cos (Wc * z)) - Wc * (exp ((- \<i> * Dc / 2) * z) * sin (Wc * z)))
        + (- \<i> * (Dc / 2) * a0 - \<i> * gc * b0) * u
          * ((- \<i> * Dc / 2) * (exp ((- \<i> * Dc / 2) * z) * sin (Wc * z)) + Wc * (exp ((- \<i> * Dc / 2) * z) * cos (Wc * z)))) (at z)"
    unfolding Af_def by (rule DERIV_add[OF DERIV_cmult[OF d1] DERIV_cmult[OF d3]])
  have dB: "(Bf Dc gc Wc u a0 b0 has_field_derivative
        b0 * ((- \<i> * Dc / 2) * (exp ((- \<i> * Dc / 2) * z) * cos (Wc * z)) - Wc * (exp ((- \<i> * Dc / 2) * z) * sin (Wc * z)))
        + (- \<i> * gc * a0 + \<i> * (Dc / 2) * b0) * u
          * ((- \<i> * Dc / 2) * (exp ((- \<i> * Dc / 2) * z) * sin (Wc * z)) + Wc * (exp ((- \<i> * Dc / 2) * z) * cos (Wc * z)))) (at z)"
    unfolding Bf_def by (rule DERIV_add[OF DERIV_cmult[OF d1] DERIV_cmult[OF d3]])
  show "(Af Dc gc Wc u a0 b0 has_field_derivative
            - \<i> * (Dc * Af Dc gc Wc u a0 b0 z + gc * Bf Dc gc Wc u a0 b0 z)) (at z)"
    by (rule DERIV_cong[OF dA]) (unfold Af_def Bf_def, rule alg_A[OF W2 Wu refl refl])
  show "(Bf Dc gc Wc u a0 b0 has_field_derivative - \<i> * gc * Af Dc gc Wc u a0 b0 z) (at z)"
    by (rule DERIV_cong[OF dB]) (unfold Af_def, rule alg_B[OF W2 Wu refl refl])
qed

lemma seg_alg1:
  fixes E C S u Dc gc a0 b0 :: complex
  shows "E * ((C - \<i> * (Dc / 2) * (S * u)) * a0 - \<i> * gc * (S * u) * b0)
         = a0 * (E * C) + (- \<i> * (Dc / 2) * a0 - \<i> * gc * b0) * u * (E * S)"
  by (simp add: algebra_simps)

lemma seg_alg2:
  fixes E C S u Dc gc a0 b0 :: complex
  shows "E * (- (\<i> * gc * (S * u)) * a0 + (C + \<i> * (Dc / 2) * (S * u)) * b0)
         = b0 * (E * C) + (- \<i> * gc * a0 + \<i> * (Dc / 2) * b0) * u * (E * S)"
  by (simp add: algebra_simps)

lemma seg_fst_snd:
  fixes D g t :: real and a0 b0 :: complex
  assumes "0 < Om g D"
  shows "fst (seg D g t (a0, b0)) = Af (of_real D) (of_real g) (of_real (Om g D)) (of_real (1 / Om g D)) a0 b0 (of_real t)"
    and "snd (seg D g t (a0, b0)) = Bf (of_real D) (of_real g) (of_real (Om g D)) (of_real (1 / Om g D)) a0 b0 (of_real t)"
proof -
  have ex: "cis (- D * t / 2) = exp (- \<i> * of_real D / 2 * of_real t)"
    unfolding cis_conv_exp by (rule arg_cong[of _ _ exp]) (simp add: field_simps)
  have c1: "(of_real (cos (Om g D * t)) :: complex) = cos (of_real (Om g D) * of_real t)"
    by (simp only: of_real_mult[symmetric] cos_of_real)
  have s1: "(of_real (sin (Om g D * t)) :: complex) = sin (of_real (Om g D) * of_real t)"
    by (simp only: of_real_mult[symmetric] sin_of_real)
  have u0: "sin (Om g D * t) / Om g D = sin (Om g D * t) * (1 / Om g D)" by simp
  have u1: "(of_real (sin (Om g D * t) / Om g D) :: complex)
            = of_real (sin (Om g D * t)) * of_real (1 / Om g D)"
    using arg_cong[of _ _ "of_real :: real \<Rightarrow> complex", OF u0] by (simp only: of_real_mult)
  have hd: "(of_real (D / 2) :: complex) = of_real D / 2" by simp
  have S1: "fst (seg D g t (a0, b0))
            = a0 * (cis (- D * t / 2) * of_real (cos (Om g D * t)))
              + (- \<i> * (of_real D / 2) * a0 - \<i> * of_real g * b0) * of_real (1 / Om g D)
                * (cis (- D * t / 2) * of_real (sin (Om g D * t)))"
  proof -
    have f1: "fst (seg D g t (a0, b0))
              = cis (- D * t / 2) * ((of_real (cos (Om g D * t))
                  - \<i> * (of_real D / 2) * (of_real (sin (Om g D * t)) * of_real (1 / Om g D))) * a0
                  - \<i> * of_real g * (of_real (sin (Om g D * t)) * of_real (1 / Om g D)) * b0)"
      unfolding seg_def Umat_def sm_def by (simp only: fst_conv snd_conv u1 hd)
    show ?thesis by (simp only: f1 seg_alg1)
  qed
  have S2: "snd (seg D g t (a0, b0))
            = b0 * (cis (- D * t / 2) * of_real (cos (Om g D * t)))
              + (- \<i> * of_real g * a0 + \<i> * (of_real D / 2) * b0) * of_real (1 / Om g D)
                * (cis (- D * t / 2) * of_real (sin (Om g D * t)))"
  proof -
    have f2: "snd (seg D g t (a0, b0))
              = cis (- D * t / 2) * (- (\<i> * of_real g * (of_real (sin (Om g D * t)) * of_real (1 / Om g D))) * a0
                  + (of_real (cos (Om g D * t))
                  + \<i> * (of_real D / 2) * (of_real (sin (Om g D * t)) * of_real (1 / Om g D))) * b0)"
      unfolding seg_def Umat_def sm_def by (simp only: fst_conv snd_conv u1 hd)
    show ?thesis by (simp only: f2 seg_alg2)
  qed
  show "fst (seg D g t (a0, b0)) = Af (of_real D) (of_real g) (of_real (Om g D)) (of_real (1 / Om g D)) a0 b0 (of_real t)"
    by (simp only: S1 Af_def ex c1 s1)
  show "snd (seg D g t (a0, b0)) = Bf (of_real D) (of_real g) (of_real (Om g D)) (of_real (1 / Om g D)) a0 b0 (of_real t)"
    by (simp only: S2 Bf_def ex c1 s1)
qed

theorem seg_ode:
  fixes D g t :: real and a0 b0 :: complex
  assumes "0 < Om g D"
  shows "((\<lambda>t. fst (seg D g t (a0, b0))) has_vector_derivative
            - \<i> * (of_real D * fst (seg D g t (a0, b0)) + of_real g * snd (seg D g t (a0, b0)))) (at t)"
    and "((\<lambda>t. snd (seg D g t (a0, b0))) has_vector_derivative
            - \<i> * of_real g * fst (seg D g t (a0, b0))) (at t)"
proof -
  have W2r: "Om g D * Om g D = g * g + D * D / 4"
    using assms by (simp add: Om_def real_sqrt_mult_self power2_eq_square)
  have W2: "(of_real (Om g D) :: complex) * of_real (Om g D) = of_real g * of_real g + of_real D * of_real D / 4"
  proof -
    have "of_real (Om g D * Om g D) = (of_real (g * g + D * D / 4) :: complex)" using W2r by simp
    then show ?thesis by simp
  qed
  have Wu: "(of_real (Om g D) :: complex) * of_real (1 / Om g D) = 1" using assms by simp
  note oc = ode_complex[OF W2 Wu, of a0 b0 "of_real t"]
  have fe: "(\<lambda>t. fst (seg D g t (a0, b0))) =
            (\<lambda>t. Af (of_real D) (of_real g) (of_real (Om g D)) (of_real (1 / Om g D)) a0 b0 (of_real t))"
    by (rule ext) (rule seg_fst_snd(1)[OF assms])
  have ge: "(\<lambda>t. snd (seg D g t (a0, b0))) =
            (\<lambda>t. Bf (of_real D) (of_real g) (of_real (Om g D)) (of_real (1 / Om g D)) a0 b0 (of_real t))"
    by (rule ext) (rule seg_fst_snd(2)[OF assms])
  show "((\<lambda>t. fst (seg D g t (a0, b0))) has_vector_derivative
            - \<i> * (of_real D * fst (seg D g t (a0, b0)) + of_real g * snd (seg D g t (a0, b0)))) (at t)"
    unfolding fe seg_fst_snd(1)[OF assms] seg_fst_snd(2)[OF assms]
    by (rule has_vector_derivative_real_field[OF oc(1)])
  show "((\<lambda>t. snd (seg D g t (a0, b0))) has_vector_derivative
            - \<i> * of_real g * fst (seg D g t (a0, b0))) (at t)"
    unfolding ge seg_fst_snd(1)[OF assms]
    by (rule has_vector_derivative_real_field[OF oc(2)])
qed

subsubsection \<open>(ii) The four-segment sequence\<close>

definition Os :: real where "Os = sqrt 5 / 2"
definition u0 :: real where "u0 = arccos (3 / 8) / 2"
definition ta :: real where "ta = u0 / Os"
definition tb :: real where "tb = (pi - u0) / Os"
definition w0 :: real where "w0 = pi - (2 * ta + tb) / 2"

lemma Os_sq: "Os\<^sup>2 = 5 / 4" unfolding Os_def by (simp add: power_divide)

lemma Os_pos: "0 < Os" unfolding Os_def by simp

lemma Om_Os:
  assumes "g\<^sup>2 = 1" and "D\<^sup>2 = 1"
  shows "Om g D = Os"
proof -
  have nn: "0 \<le> g\<^sup>2 + D\<^sup>2 / 4"
    by (rule add_nonneg_nonneg[OF zero_le_power2 divide_nonneg_nonneg[OF zero_le_power2]]) simp
  have h1: "0 \<le> Om g D" unfolding Om_def by (rule real_sqrt_ge_zero[OF nn])
  have h2: "0 \<le> Os" using Os_pos by simp
  have "(Om g D)\<^sup>2 = g\<^sup>2 + D\<^sup>2 / 4" unfolding Om_def by (rule real_sqrt_pow2[OF nn])
  then have h3: "(Om g D)\<^sup>2 = Os\<^sup>2" using assms Os_sq by simp
  show ?thesis by (rule power2_eq_imp_eq[OF h3 h1 h2])
qed

lemma Om_free:
  assumes "D\<^sup>2 = 1"
  shows "Om 0 D = 1 / 2"
proof -
  have nn: "0 \<le> (0::real)\<^sup>2 + D\<^sup>2 / 4"
    by (rule add_nonneg_nonneg[OF zero_le_power2 divide_nonneg_nonneg[OF zero_le_power2]]) simp
  have h1: "0 \<le> Om 0 D" unfolding Om_def by (rule real_sqrt_ge_zero[OF nn])
  have h2: "0 \<le> (1 / 2 :: real)" by simp
  have "(Om 0 D)\<^sup>2 = 0\<^sup>2 + D\<^sup>2 / 4" unfolding Om_def by (rule real_sqrt_pow2[OF nn])
  then have h3: "(Om 0 D)\<^sup>2 = (1 / 2)\<^sup>2" using assms by (simp add: power_divide)
  show ?thesis by (rule power2_eq_imp_eq[OF h3 h1 h2])
qed

lemma cos_u0_sq: "(cos u0)\<^sup>2 = 11 / 16"
proof -
  have "cos (2 * u0) = 3 / 8" unfolding u0_def by (simp add: cos_arccos)
  moreover have "cos (2 * u0) = 2 * (cos u0)\<^sup>2 - 1" by (rule cos_double_cos)
  ultimately show ?thesis by simp
qed

lemma u0_range: "0 < u0" "u0 \<le> pi / 2"
proof -
  have a0: "0 \<le> arccos (3 / 8)" and a1: "arccos (3 / 8) \<le> pi" by (simp_all add: arccos_lbound arccos_ubound)
  have "arccos (3 / 8) \<noteq> 0"
  proof
    assume "arccos (3 / 8) = 0"
    then have "cos (arccos (3 / 8)) = 1" by simp
    then show False by simp
  qed
  then show "0 < u0" "u0 \<le> pi / 2" unfolding u0_def using a0 a1 by simp_all
qed

lemma sin_u0: "sin u0 = Os / 2"
proof -
  have "(sin u0)\<^sup>2 = 5 / 16"
  proof -
    have "(sin u0)\<^sup>2 = 1 - (cos u0)\<^sup>2" by (rule sin_squared_eq)
    then show ?thesis using cos_u0_sq by simp
  qed
  moreover have "(Os / 2)\<^sup>2 = 5 / 16" using Os_sq by (simp add: power_divide)
  ultimately have e: "(sin u0)\<^sup>2 = (Os / 2)\<^sup>2" by simp
  have "0 \<le> sin u0" by (rule sin_ge_zero) (use u0_range pi_gt_zero in auto)
  moreover have "0 \<le> Os / 2" using Os_pos by simp
  ultimately show ?thesis by (rule power2_eq_imp_eq[OF e])
qed

lemma Os_ta: "Os * ta = u0" unfolding ta_def using Os_pos by simp
lemma Os_tb: "Os * tb = pi - u0" unfolding tb_def using Os_pos by simp

lemma seg_ta:
  assumes "D\<^sup>2 = 1"
  shows "seg D 1 ta v = sm (cis (- D * ta / 2)) (Umat D 1 (cos u0) (1 / 2) v)"
proof -
  have om: "Om 1 D = Os" by (rule Om_Os) (use assms in simp_all)
  have hs: "sin u0 / Os = 1 / 2" using sin_u0 Os_pos by simp
  show ?thesis unfolding seg_def by (simp only: om Os_ta hs)
qed

lemma seg_tb:
  assumes "D\<^sup>2 = 1"
  shows "seg D (- 1) tb v = sm (cis (- D * tb / 2)) (Umat D (- 1) (- cos u0) (1 / 2) v)"
proof -
  have om: "Om (- 1) D = Os" by (rule Om_Os) (use assms in simp_all)
  have hs: "sin u0 / Os = 1 / 2" using sin_u0 Os_pos by simp
  show ?thesis unfolding seg_def by (simp only: om Os_tb cos_pi_minus sin_pi_minus hs)
qed

lemma seg_free:
  assumes "D = 1 \<or> D = - 1"
  shows "seg D 0 t (1, 0) = sm (cis (- D * t)) (1, 0)"
proof -
  have D2: "D\<^sup>2 = 1" using assms by auto
  have om: "Om 0 D = 1 / 2" by (rule Om_free[OF D2])
  have "cis (- D * t / 2) * cis (- D * t / 2) = cis (- D * t)"
    by (simp only: cis_mult) (rule arg_cong[of _ _ cis], simp)
  moreover have "(of_real (cos (t / 2)) - \<i> * of_real (D / 2) * of_real (sin (t / 2) / (1 / 2)) :: complex)
                 = cis (- D * t / 2)"
    using assms by (elim disjE) (simp_all add: complex_eq_iff)
  ultimately show ?thesis
    unfolding seg_def om Umat_def sm_def by (simp add: field_simps)
qed

definition Ucx :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<times> complex" where
  "Ucx dh g C S a b = ((C - \<i> * dh * S) * a - \<i> * g * S * b, - (\<i> * g * S) * a + (C + \<i> * dh * S) * b)"

lemma Umat_Ucx:
  "Umat D g C S (a, b) = Ucx (of_real (D / 2)) (of_real g) (of_real C) (of_real S) a b"
  by (simp add: Umat_def Ucx_def)

lemma eq_via_zero:
  fixes A T R :: complex
  assumes "A - T = R" and "R = 0"
  shows "A = T"
proof -
  have "A - T = 0" using assms by simp
  then show ?thesis by (rule iffD1[OF right_minus_eq])
qed

lemma Ucx_s1:
  fixes ch dd :: complex
  shows "Ucx (dd / 2) 1 ch (1 / 2) 1 0 = (ch - \<i> * dd / 4, - \<i> / 2)"
  unfolding Ucx_def by (simp add: algebra_simps field_simps)

lemma Ucx_s2:
  fixes ch dd :: complex
  assumes c2: "ch * ch = 11 / 16" and d2: "dd * dd = 1"
  shows "Ucx (dd / 2) (- 1) (- ch) (1 / 2) (ch - \<i> * dd / 4) (- \<i> / 2) = (- 1 / 2, \<i> * ch + dd / 4)"
proof -
  have ii: "\<i> * \<i> = (-1 :: complex)" by simp
  have e1: "((- ch) - \<i> * (dd / 2) * (1 / 2)) * (ch - \<i> * dd / 4) - \<i> * (- 1) * (1 / 2) * (- \<i> / 2) - (- 1 / 2)
            = - (ch * ch - 11 / 16) + (\<i> * \<i> + 1) * (dd * dd / 16 - 1 / 4) - (dd * dd - 1) / 16"
    by (simp add: algebra_simps field_simps)
  have e1': "- (ch * ch - 11 / 16) + (\<i> * \<i> + 1) * (dd * dd / 16 - 1 / 4) - (dd * dd - 1) / 16 = 0"
    by (simp add: c2 d2 ii)
  have e2: "- (\<i> * (- 1) * (1 / 2)) * (ch - \<i> * dd / 4) + ((- ch) + \<i> * (dd / 2) * (1 / 2)) * (- \<i> / 2)
            - (\<i> * ch + dd / 4) = - (\<i> * \<i> + 1) * (dd / 4)"
    by (simp add: algebra_simps field_simps)
  have e2': "- (\<i> * \<i> + 1) * (dd / 4) = 0" by (simp add: ii)
  show ?thesis unfolding Ucx_def
    apply (rule prod_eqI)
     apply (simp only: fst_conv)
     apply (rule eq_via_zero[OF e1 e1'])
    apply (simp only: snd_conv)
    apply (rule eq_via_zero[OF e2 e2'])
    done
qed

lemma Ucx_s3:
  fixes ch dd :: complex
  assumes c2: "ch * ch = 11 / 16" and d2: "dd * dd = 1"
  shows "Ucx (dd / 2) 1 ch (1 / 2) (- 1 / 2) (\<i> * ch + dd / 4) = (0, \<i>)"
proof -
  have ii: "\<i> * \<i> = (-1 :: complex)" by simp
  have e1: "(ch - \<i> * (dd / 2) * (1 / 2)) * (- 1 / 2) - \<i> * 1 * (1 / 2) * (\<i> * ch + dd / 4) - 0
            = - (ch / 2) * (\<i> * \<i> + 1)"
    by (simp add: algebra_simps field_simps)
  have e1': "- (ch / 2) * (\<i> * \<i> + 1) = 0" by (simp add: ii)
  have e2: "- (\<i> * 1 * (1 / 2)) * (- 1 / 2) + (ch + \<i> * (dd / 2) * (1 / 2)) * (\<i> * ch + dd / 4) - \<i>
            = \<i> * (ch * ch - 11 / 16) + \<i> * (dd * dd - 1) / 16 + (ch * dd / 4) * (\<i> * \<i> + 1)"
    by (simp add: algebra_simps field_simps)
  have e2': "\<i> * (ch * ch - 11 / 16) + \<i> * (dd * dd - 1) / 16 + (ch * dd / 4) * (\<i> * \<i> + 1) = 0"
    by (simp add: c2 d2 ii)
  show ?thesis unfolding Ucx_def
    apply (rule prod_eqI)
     apply (simp only: fst_conv)
     apply (rule eq_via_zero[OF e1 e1'])
    apply (simp only: snd_conv)
    apply (rule eq_via_zero[OF e2 e2'])
    done
qed

lemma alg4:
  fixes c D :: real
  assumes c2: "c\<^sup>2 = 11 / 16" and D2: "D\<^sup>2 = 1"
  shows "Umat D 1 c (1 / 2) (Umat D (- 1) (- c) (1 / 2) (Umat D 1 c (1 / 2) (1, 0))) = (0, \<i>)"
proof -
  have c2c: "(of_real c :: complex) * of_real c = 11 / 16"
  proof -
    have "(of_real c :: complex) * of_real c = of_real (c * c)" by (simp only: of_real_mult)
    also have "\<dots> = of_real (11 / 16)"
      by (rule arg_cong[of _ _ of_real]) (use c2 in \<open>simp add: power2_eq_square\<close>)
    also have "\<dots> = (11 / 16 :: complex)" by simp
    finally show ?thesis .
  qed
  have D2c: "(of_real D :: complex) * of_real D = 1"
  proof -
    have "(of_real D :: complex) * of_real D = of_real (D * D)" by (simp only: of_real_mult)
    also have "\<dots> = of_real 1"
      by (rule arg_cong[of _ _ of_real]) (use D2 in \<open>simp add: power2_eq_square\<close>)
    also have "\<dots> = (1 :: complex)" by simp
    finally show ?thesis .
  qed
  have hd: "(of_real (D / 2) :: complex) = of_real D / 2" by simp
  have h12: "(of_real (1 / 2) :: complex) = 1 / 2" by simp
  have hm1: "(of_real (- 1) :: complex) = - 1" by simp
  have hmc: "(of_real (- c) :: complex) = - of_real c" by simp
  have hone: "(of_real 1 :: complex) = 1" by simp
  have s1: "Umat D 1 c (1 / 2) (1, 0) = (of_real c - \<i> * of_real D / 4, - \<i> / 2)"
    by (simp only: Umat_Ucx hd h12 hone Ucx_s1)
  have s2: "Umat D (- 1) (- c) (1 / 2) (of_real c - \<i> * of_real D / 4, - \<i> / 2)
            = (- 1 / 2, \<i> * of_real c + of_real D / 4)"
    by (simp only: Umat_Ucx hd h12 hm1 hmc Ucx_s2[OF c2c D2c])
  have s3: "Umat D 1 c (1 / 2) (- 1 / 2, \<i> * of_real c + of_real D / 4) = (0, \<i>)"
    by (simp only: Umat_Ucx hd h12 hone Ucx_s3[OF c2c D2c])
  show ?thesis by (simp only: s1 s2 s3)
qed

theorem slow_noise_counterexample:
  assumes "D = 1 \<or> D = - 1"
  shows "seg D 1 ta (seg D (- 1) tb (seg D 1 ta (seg D 0 w0 (1, 0)))) = (0, - \<i>)"
proof -
  have D2: "D\<^sup>2 = 1" using assms by auto
  have ph: "cis (- D * ta / 2) * (cis (- D * tb / 2) * (cis (- D * ta / 2) * cis (- D * w0))) = - 1"
  proof -
    have "cis (- D * ta / 2) * (cis (- D * tb / 2) * (cis (- D * ta / 2) * cis (- D * w0)))
          = cis (- D * ta / 2 + (- D * tb / 2 + (- D * ta / 2 + - D * w0)))" by (simp add: cis_mult)
    also have "- D * ta / 2 + (- D * tb / 2 + (- D * ta / 2 + - D * w0)) = - D * pi"
    proof -
      have "ta + tb / 2 + w0 = pi" unfolding w0_def by argo
      have e1: "- D * ta / 2 + (- D * tb / 2 + (- D * ta / 2 + - D * w0)) = - D * (ta + tb / 2 + w0)"
        by (simp add: algebra_simps)
      show ?thesis by (subst e1) (simp only: \<open>ta + tb / 2 + w0 = pi\<close>)
    qed
    also have "cis (- D * pi) = - 1" using assms by (auto simp: complex_eq_iff)
    finally show ?thesis .
  qed
  have "seg D 1 ta (seg D (- 1) tb (seg D 1 ta (seg D 0 w0 (1, 0))))
        = sm (cis (- D * ta / 2) * (cis (- D * tb / 2) * (cis (- D * ta / 2) * cis (- D * w0))))
             (Umat D 1 (cos u0) (1 / 2) (Umat D (- 1) (- cos u0) (1 / 2) (Umat D 1 (cos u0) (1 / 2) (1, 0))))"
    by (simp add: seg_free[OF assms] seg_ta[OF D2] seg_tb[OF D2] Umat_sm sm_sm)
  also have "\<dots> = sm (- 1) (0, \<i>)" using ph alg4[OF cos_u0_sq D2] by simp
  also have "\<dots> = (0, - \<i>)" by (simp add: sm_def)
  finally show ?thesis .
qed

subsubsection \<open>(iii) The plain resonant pulse\<close>

theorem resonant_plain_pulse:
  assumes "D = 1 \<or> D = - 1"
  shows "(norm (snd (seg D 1 t (1, 0))))\<^sup>2 = 4 / 5 * (sin (Os * t))\<^sup>2"
    and "(norm (snd (seg D 1 t (1, 0))))\<^sup>2 \<le> 4 / 5"
proof -
  have D2: "D\<^sup>2 = 1" using assms by auto
  have om: "Om 1 D = Os" by (rule Om_Os) (use D2 in simp_all)
  have "snd (seg D 1 t (1, 0)) = - (cis (- D * t / 2) * (\<i> * of_real (sin (Os * t) / Os)))"
    unfolding seg_def om Umat_def sm_def by simp
  then have "norm (snd (seg D 1 t (1, 0))) = \<bar>sin (Os * t) / Os\<bar>" by (simp add: norm_mult norm_divide)
  then have "(norm (snd (seg D 1 t (1, 0))))\<^sup>2 = (sin (Os * t))\<^sup>2 / Os\<^sup>2" by (simp add: power_divide)
  then show e: "(norm (snd (seg D 1 t (1, 0))))\<^sup>2 = 4 / 5 * (sin (Os * t))\<^sup>2" using Os_sq by simp
  show "(norm (snd (seg D 1 t (1, 0))))\<^sup>2 \<le> 4 / 5"
  proof -
    have "(sin (Os * t))\<^sup>2 \<le> 1" by (simp add: sin_squared_eq)
    then show ?thesis unfolding e by simp
  qed
qed

section \<open>3. P2 without the slit hypothesis\<close>

text \<open>Argument. Let @{text "tau"} be the first time the trajectory touches the closed slit
  @{text "{y = 0, X <= 0}"}. Before @{text "tau"} the Lyapunov argument applies (@{text "P2_gen"}); by closedness
  the bound @{text "min_{[0,tau]} Xr <= X tau"} survives at @{text "tau"}. After @{text "tau"}, the radius is
  non-increasing (P1), and at @{text "tau"} it equals @{text "-X tau"}, so @{text "X t >= X tau"}.\<close>

context dephasing
begin

lemma rho2_mono:
  assumes "0 \<le> a" and "a \<le> b" and "b \<le> T"
  shows "rho2 b \<le> rho2 a"
proof (rule mono_nonpos[OF assms(2)])
  show "continuous_on {a..b} rho2" by (rule continuous_on_subset[OF contr2]) (use assms in auto)
  fix x assume x: "a < x" "x < b"
  have "(y x)\<^sup>2 \<ge> 0" by simp
  then show "\<exists>D. (rho2 has_real_derivative D) (at x) \<and> D \<le> 0"
    using rho2_deriv[of x] x assms Ph0
    by (intro exI[of _ "- 2 * \<Phi> * (y x)\<^sup>2"] conjI) (auto intro: mult_nonneg_nonneg)
qed

lemma X_free:
  assumes t: "t \<in> {0..T}"
  shows "0 \<le> X t \<or> (\<exists>s. 0 \<le> s \<and> s \<le> t \<and> Xr s \<le> X t \<and> Xr s \<le> 0)"
proof (cases "\<forall>s\<in>{0..t}. y s \<noteq> 0 \<or> 0 < X s")
  case True
  show ?thesis by (rule P2_gen[OF t]) (use True in blast)
next
  case False
  have tT: "t \<le> T" and t0: "0 \<le> t" using t by simp_all
  have sub: "{0..t} \<subseteq> {0..T}" using tT by auto
  have cy: "continuous_on {0..t} y" by (rule continuous_on_subset[OF conty sub])
  have cX: "continuous_on {0..t} X" by (rule continuous_on_subset[OF contX sub])
  define S where "S = {s \<in> {0..t}. y s = 0 \<and> X s \<le> 0}"
  have Sne: "S \<noteq> {}" using False unfolding S_def by auto
  have Sbd: "bdd_below S" unfolding S_def by (intro bdd_belowI[of _ 0]) auto
  have Scl: "closed S"
  proof -
    have c1: "closed {s \<in> {0..t}. y s \<le> (\<lambda>_. 0) s}"
      by (rule continuous_on_closed_Collect_le[OF cy continuous_on_const closed_atLeastAtMost])
    have c2: "closed {s \<in> {0..t}. (\<lambda>_. 0) s \<le> y s}"
      by (rule continuous_on_closed_Collect_le[OF continuous_on_const cy closed_atLeastAtMost])
    have c3: "closed {s \<in> {0..t}. X s \<le> (\<lambda>_. 0) s}"
      by (rule continuous_on_closed_Collect_le[OF cX continuous_on_const closed_atLeastAtMost])
    have "S = {s \<in> {0..t}. y s \<le> (\<lambda>_. 0) s} \<inter> {s \<in> {0..t}. (\<lambda>_. 0) s \<le> y s}
              \<inter> {s \<in> {0..t}. X s \<le> (\<lambda>_. 0) s}" unfolding S_def by auto
    then show ?thesis using c1 c2 c3 by (simp only: closed_Int)
  qed
  define tau where "tau = Inf S"
  have tauS: "tau \<in> S" unfolding tau_def by (rule closed_contains_Inf[OF Sne Sbd Scl])
  have tau_t: "tau \<le> t" and tau0: "0 \<le> tau" and yt: "y tau = 0" and Xt: "X tau \<le> 0"
    using tauS unfolding S_def by auto
  have tau_low: "\<And>r. r \<in> S \<Longrightarrow> tau \<le> r" unfolding tau_def by (rule cInf_lower[OF _ Sbd])
  have thalf_tau: "t_half \<le> tau"
  proof (rule ccontr)
    assume "\<not> t_half \<le> tau"
    then have lt: "tau < t_half" by simp
    have "0 < X tau" by (rule X_pos[OF _ lt]) (use tau0 tau_t tT in auto)
    then show False using Xt by simp
  qed
  have tau_pos: "0 < tau" using thalf_tau t_half_pos by simp
  have tauT: "tau \<in> {0..T}" using tau0 tau_t tT by auto
  have sub2: "{0..tau} \<subseteq> {0..T}" using tau_t tT by auto
  have compt: "compact {0..tau}" by simp
  have ne: "{0..tau} \<noteq> {}" using tau0 by simp
  obtain sx where sx: "sx \<in> {0..tau}" and smin: "\<And>s. s \<in> {0..tau} \<Longrightarrow> Xr sx \<le> Xr s"
    using continuous_attains_inf[OF compt ne continuous_on_subset[OF contXr sub2]] by blast
  have m0: "Xr sx \<le> 0"
  proof -
    have "t_half \<in> {0..tau}" using thalf_tau t_half_pos by auto
    then show ?thesis using smin[of t_half] Xr_half by simp
  qed
  have Xtau: "Xr sx \<le> X tau"
  proof -
    define K where "K = {s \<in> {0..tau}. (\<lambda>_. Xr sx) s \<le> X s}"
    have cXt: "continuous_on {0..tau} X" by (rule continuous_on_subset[OF contX sub2])
    have Kcl: "closed K" unfolding K_def
      by (rule continuous_on_closed_Collect_le[OF continuous_on_const cXt closed_atLeastAtMost])
    have subK: "{0..<tau} \<subseteq> K"
    proof
      fix s assume s: "s \<in> {0..<tau}"
      have sT: "s \<in> {0..T}" using s tau_t tT by auto
      have sl: "\<And>r. r \<in> {0..s} \<Longrightarrow> y r \<noteq> 0 \<or> 0 < X r"
      proof -
        fix r assume r: "r \<in> {0..s}"
        have "r < tau" using r s by auto
        have "r \<notin> S"
        proof
          assume "r \<in> S"
          then have "tau \<le> r" by (rule tau_low)
          then show False using \<open>r < tau\<close> by simp
        qed
        moreover have "r \<in> {0..t}" using r s tau_t by auto
        ultimately show "y r \<noteq> 0 \<or> 0 < X r" unfolding S_def by auto
      qed
      have "Xr sx \<le> X s"
        using P2_gen[OF sT sl]
      proof
        assume "0 \<le> X s" then show ?thesis using m0 by simp
      next
        assume "\<exists>s'. 0 \<le> s' \<and> s' \<le> s \<and> Xr s' \<le> X s \<and> Xr s' \<le> 0"
        then obtain s' where s': "0 \<le> s'" "s' \<le> s" "Xr s' \<le> X s" by blast
        have "s' \<in> {0..tau}" using s' s by auto
        then show ?thesis using smin[of s'] s'(3) by simp
      qed
      then show "s \<in> K" unfolding K_def using s by auto
    qed
    have "tau \<in> closure {0..<tau}" using tau_pos by (simp add: closure_atLeastLessThan)
    then have "tau \<in> K" using closure_minimal[OF subK Kcl] by auto
    then show ?thesis unfolding K_def by simp
  qed
  have Xt_ge: "X tau \<le> X t"
  proof -
    have "rho2 t \<le> rho2 tau" by (rule rho2_mono[OF tau0 tau_t tT])
    then have "(X t)\<^sup>2 \<le> (X tau)\<^sup>2"
    proof -
      have yt2: "(y tau)\<^sup>2 = 0" using yt by simp
      show ?thesis using \<open>rho2 t \<le> rho2 tau\<close> yt2 zero_le_power2[of "y t"] unfolding rho2_def by argo
    qed
    then have "\<bar>X t\<bar> \<le> \<bar>X tau\<bar>" by (simp add: abs_le_square_iff)
    moreover have "\<bar>X tau\<bar> = - X tau" using Xt by (rule abs_of_nonpos)
    moreover have "- X t \<le> \<bar>X t\<bar>" by simp
    ultimately show ?thesis by linarith
  qed
  have "Xr sx \<le> X t" using Xtau Xt_ge by simp
  moreover have "sx \<le> t" using sx tau_t by auto
  moreover have "0 \<le> sx" using sx by auto
  ultimately show ?thesis using m0 by blast
qed

theorem P2_free:
  fixes \<gamma> :: real
  assumes g: "0 \<le> \<gamma>" and t: "t \<in> {0..T}"
  shows "\<exists>s. 0 \<le> s \<and> exp (- \<gamma> * t) * (1 - X t) / 2 \<le> exp (- \<gamma> * s) * (1 - dp_Xr G \<Phi> s) / 2"
proof (cases "t \<le> t_half")
  case True
  then show ?thesis using P3_population[OF t True, of \<gamma>] t by (intro exI[of _ t]) simp
next
  case False
  have th: "t_half \<le> t" using False by simp
  from X_free[OF t] show ?thesis
  proof
    assume X0': "0 \<le> X t"
    have "exp (- \<gamma> * t) * (1 - X t) / 2 \<le> exp (- \<gamma> * t) * 1 / 2"
      using X0' by (intro divide_right_mono mult_left_mono) simp_all
    also have "\<dots> \<le> exp (- \<gamma> * t_half) * 1 / 2"
      using g th by (intro divide_right_mono mult_right_mono) (simp_all add: mult_left_mono)
    also have "\<dots> = exp (- \<gamma> * t_half) * (1 - dp_Xr G \<Phi> t_half) / 2" using Xr_half by simp
    finally show ?thesis using t_half_pos by (intro exI[of _ t_half]) simp
  next
    assume "\<exists>s. 0 \<le> s \<and> s \<le> t \<and> Xr s \<le> X t \<and> Xr s \<le> 0"
    then obtain s where s: "0 \<le> s" "s \<le> t" "Xr s \<le> X t" "Xr s \<le> 0" by blast
    have "exp (- \<gamma> * t) * (1 - X t) / 2 \<le> exp (- \<gamma> * t) * (1 - Xr s) / 2"
      using s(3) by (intro divide_right_mono mult_left_mono) simp_all
    also have "\<dots> \<le> exp (- \<gamma> * s) * (1 - Xr s) / 2"
    proof (rule divide_right_mono)
      have "exp (- \<gamma> * t) \<le> exp (- \<gamma> * s)" using g s(2) by (simp add: mult_left_mono)
      then show "exp (- \<gamma> * t) * (1 - Xr s) \<le> exp (- \<gamma> * s) * (1 - Xr s)"
        using s(4) by (intro mult_right_mono) simp_all
    qed simp
    finally show ?thesis using s(1) by (intro exI[of _ s]) simp
  qed
qed

end

theorem memory_dephasing_equal_rates_free:
  fixes G \<Phi> \<gamma> T t :: real and X y w :: "real \<Rightarrow> real"
  assumes G: "0 < G" and Ph0: "0 \<le> \<Phi>" and Ph4: "\<Phi> < 4 * G" and g: "0 \<le> \<gamma>" and T: "0 \<le> T"
    and dX: "\<And>t. t \<in> {0..T} \<Longrightarrow> (X has_real_derivative - 2 * w t * y t) (at t within {0..T})"
    and dy: "\<And>t. t \<in> {0..T} \<Longrightarrow> (y has_real_derivative - \<Phi> * y t + 2 * w t * X t) (at t within {0..T})"
    and wb: "\<And>t. t \<in> {0..T} \<Longrightarrow> \<bar>w t\<bar> \<le> G"
    and X0: "X 0 = 1" and y0: "y 0 = 0" and t: "t \<in> {0..T}"
  shows "\<exists>s. 0 \<le> s \<and> exp (- \<gamma> * t) * (1 - X t) / 2 \<le> exp (- \<gamma> * s) * (1 - dp_Xr G \<Phi> s) / 2"
proof -
  interpret dephasing G \<Phi> T X y w
    by unfold_locales (use assms in \<open>blast+\<close>)
  show ?thesis by (rule P2_free[OF g t])
qed

end
