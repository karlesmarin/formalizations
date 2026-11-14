(*  Title:      Memory_Access_Floors.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Part of the formalisation of "Exact limits for writing a quantum memory" (C. Marín, draft, November 2026): the maximum of the damped
    vacuum-Rabi transfer, the write-channel identities, the worst-case fidelity and the alignment lemma.
*)

theory Memory_Access_Floors
  imports "HOL-Analysis.Analysis"
begin

section \<open>A. Write channel (algebra)\<close>

lemma write_channel_infidelity:
  fixes p c :: real
  defines "Fe \<equiv> (1 + p + 2 * c) / 4"
  defines "F \<equiv> (2 * Fe + 1) / 3"
  shows "1 - F = (1 - p) / 6 + (1 - c) / 3"
    and "1 - Fe = (3 / 2) * (1 - F)"
  unfolding F_def Fe_def by (simp_all add: field_simps)

lemma write_channel_monotone:
  fixes p c P C :: real
  assumes "p \<le> P" and "c \<le> C"
  shows "(1 - P) / 6 + (1 - C) / 3 \<le> (1 - p) / 6 + (1 - c) / 3"
  using assms by argo

section \<open>B. Worst case over pure states\<close>

definition wc_poly :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "wc_poly p c x = 1 - (1 + p - 2 * c) * x + 2 * (p - c) * x\<^sup>2"

lemma worst_case_case_one:
  fixes p c x :: real
  assumes "0 \<le> p" and "p \<le> 1" and "0 \<le> c" and "c\<^sup>2 \<le> p"
    and "3 * p - 2 * c \<le> 1" and "0 \<le> x" and "x \<le> 1"
  shows "p \<le> wc_poly p c x" and "wc_poly p c 1 = p"
proof -
  have fac: "wc_poly p c x - p = (1 - x) * ((1 - p) - 2 * (p - c) * x)"
    unfolding wc_poly_def by (simp add: algebra_simps power2_eq_square)
  have "0 \<le> (1 - p) - 2 * (p - c) * x"
  proof (cases "p \<le> c")
    case True
    then have "0 \<le> 2 * (c - p) * x" using assms(6) by simp
    with assms(2) show ?thesis by (simp add: algebra_simps)
  next
    case False
    then have "0 \<le> p - c" by simp
    have "2 * (p - c) * x \<le> 2 * (p - c) * 1"
      using \<open>0 \<le> p - c\<close> assms(7) by (intro mult_left_mono) auto
    with assms(5) show ?thesis by argo
  qed
  then have "0 \<le> (1 - x) * ((1 - p) - 2 * (p - c) * x)"
    using assms(7) by (intro mult_nonneg_nonneg) auto
  with fac show "p \<le> wc_poly p c x" by argo
  show "wc_poly p c 1 = p" unfolding wc_poly_def by (simp add: algebra_simps power2_eq_square)
qed

lemma worst_case_case_two:
  fixes p c x :: real
  assumes "0 \<le> p" and "p \<le> 1" and "0 \<le> c" and "c\<^sup>2 \<le> p"
    and "3 * p - 2 * c > 1"
  defines "q \<equiv> p - c" and "b \<equiv> 1 + p - 2 * c"
  shows "c < p"
    and "0 \<le> b / (4 * q)" and "b / (4 * q) \<le> 1"
    and "wc_poly p c x = 1 - b\<^sup>2 / (8 * q) + 2 * q * (x - b / (4 * q))\<^sup>2"
    and "0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 1 - b\<^sup>2 / (8 * q) \<le> wc_poly p c x"
    and "wc_poly p c (b / (4 * q)) = 1 - b\<^sup>2 / (8 * q)"
proof -
  show cp: "c < p" using assms(2,5) by argo
  then have q: "0 < q" unfolding q_def by simp
  have b0: "0 \<le> b"
  proof -
    have "0 \<le> (1 - c)\<^sup>2" by simp
    then show ?thesis unfolding b_def using assms(4) by (simp add: power2_eq_square algebra_simps)
  qed
  show "0 \<le> b / (4 * q)" using b0 q by simp
  have "b \<le> 4 * q" unfolding b_def q_def using assms(5) by argo
  then show "b / (4 * q) \<le> 1" using q by (simp add: divide_le_eq)
  have eqall: "wc_poly p c y = 1 - b\<^sup>2 / (8 * q) + 2 * q * (y - b / (4 * q))\<^sup>2" for y
    unfolding wc_poly_def b_def[symmetric] q_def[symmetric]
    using q by (simp add: field_simps power2_eq_square)
  show "wc_poly p c x = 1 - b\<^sup>2 / (8 * q) + 2 * q * (x - b / (4 * q))\<^sup>2" by (rule eqall)
  show "0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 1 - b\<^sup>2 / (8 * q) \<le> wc_poly p c x"
    using eqall[of x] q by simp
  show "wc_poly p c (b / (4 * q)) = 1 - b\<^sup>2 / (8 * q)" using eqall[of "b / (4 * q)"] by simp
qed

section \<open>D. Alignment lemma\<close>

lemma alignment_lemma:
  fixes z :: complex
  assumes "\<forall>\<phi>::real. Re (exp (- (\<i> * of_real \<phi>)) * z) \<le> Re z"
  shows "Im z = 0" and "Re z = norm z" and "0 \<le> Re z"
proof -
  have e: "exp (- (\<i> * of_real \<phi>)) = Complex (cos \<phi>) (- sin \<phi>)" for \<phi> :: real
  proof -
    have "- (\<i> * of_real \<phi>) = \<i> * of_real (- \<phi>)" by simp
    then show ?thesis
      by (simp only: exp_Euler) (simp add: complex_eq_iff cos_of_real sin_of_real)
  qed
  have key: "Re (exp (- (\<i> * of_real \<phi>)) * z) = Re z * cos \<phi> + Im z * sin \<phi>" for \<phi> :: real
    by (simp add: e)
  obtain A where zA: "z = rcis (norm z) A" using rcis_cmod_Arg by metis
  have re: "Re z = norm z * cos A" and im: "Im z = norm z * sin A"
    using zA Re_rcis Im_rcis by metis+
  have h: "Re z * cos A + Im z * sin A \<le> Re z" using assms key by metis
  have lhs: "Re z * cos A + Im z * sin A = norm z"
  proof -
    have "Re z * cos A + Im z * sin A = norm z * (cos A * cos A + sin A * sin A)"
      by (subst re, subst im) (simp only: algebra_simps)
    also have "\<dots> = norm z"
    proof -
      have "cos A * cos A + sin A * sin A = 1"
        using sin_cos_squared_add[of A] by (simp add: power2_eq_square add.commute)
      then show ?thesis by simp
    qed
    finally show ?thesis .
  qed
  have main: "Im z = 0 \<and> Re z = norm z"
  proof (cases "z = 0")
    case True
    then show ?thesis by simp
  next
    case False
    then have r: "0 < norm z" by simp
    have "norm z \<le> norm z * cos A" using h lhs re by simp
    then have "1 \<le> cos A" using r by (metis mult_le_cancel_left_pos mult.right_neutral)
    then have c1: "cos A = 1" using cos_le_one[of A] by argo
    then have "sin A = 0" using sin_cos_squared_add[of A] by simp
    then show ?thesis using re im c1 by simp
  qed
  then show "Im z = 0" and "Re z = norm z" by simp_all
  show "0 \<le> Re z" using main by simp
qed

section \<open>C. Closed form of the resonant-pulse maximum\<close>

lemma resonant_omega_identity:
  fixes G gq gm gb d \<Omega> :: real
  assumes "gb = (gq + gm) / 2" and "d = gq - gm" and "G\<^sup>2 > d\<^sup>2 / 16"
    and "\<Omega> = sqrt (G\<^sup>2 - d\<^sup>2 / 16)"
  shows "4 * \<Omega>\<^sup>2 + gb\<^sup>2 = 4 * G\<^sup>2 + gq * gm"
proof -
  have "\<Omega>\<^sup>2 = G\<^sup>2 - (gq - gm)\<^sup>2 / 16"
    using assms(2,3,4) by (simp add: real_sqrt_pow2)
  then show ?thesis by (simp add: assms(1) power2_eq_square algebra_simps; argo)
qed

definition max_population :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "max_population G gq gm =
     4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) *
     exp (- (((gq + gm) / 2) / sqrt (G\<^sup>2 - (gq - gm)\<^sup>2 / 16)) *
          arctan (2 * sqrt (G\<^sup>2 - (gq - gm)\<^sup>2 / 16) / ((gq + gm) / 2)))"

subsection \<open>The normalised damped sine\<close>

definition damped_sine :: "real \<Rightarrow> real \<Rightarrow> real" where
  "damped_sine k u = exp (- k * u) * (sin u)\<^sup>2"

lemma damped_sine_deriv:
  "DERIV (damped_sine k) x :> exp (- k * x) * sin x * (2 * cos x - k * sin x)"
proof -
  have "((\<lambda>x. exp (- k * x) * (sin x)\<^sup>2) has_real_derivative
        (exp (- k * x) * (- k)) * (sin x)\<^sup>2 + exp (- k * x) * (2 * sin x * cos x)) (at x)"
    by (auto intro!: derivative_eq_intros)
  then show ?thesis
    unfolding damped_sine_def[abs_def] by (simp add: algebra_simps power2_eq_square)
qed

lemma damped_sine_peak_facts:
  fixes k :: real
  assumes "0 < k"
  defines "u0 \<equiv> arctan (2 / k)"
  shows "0 \<le> u0" and "u0 < pi / 2" and "0 < cos u0" and "k * sin u0 = 2 * cos u0"
    and "damped_sine k u0 = 4 / (4 + k\<^sup>2) * exp (- k * arctan (2 / k))"
proof -
  show u0nn: "0 \<le> u0"
  proof -
    have "arctan 0 \<le> arctan (2 / k)" using assms by (intro arctan_monotone') simp
    then show ?thesis unfolding u0_def by simp
  qed
  show u0lt: "u0 < pi / 2" unfolding u0_def by (rule arctan_ubound)
  show cpos: "0 < cos u0" using u0nn u0lt by (intro cos_gt_zero_pi) auto
  have "tan u0 = 2 / k" unfolding u0_def by (rule tan_arctan)
  then have "sin u0 / cos u0 = 2 / k" by (simp add: tan_def)
  then show ks: "k * sin u0 = 2 * cos u0" using cpos assms by (simp add: field_simps)
  have e1: "k\<^sup>2 * (sin u0)\<^sup>2 = 4 * (cos u0)\<^sup>2"
  proof -
    have "(k * sin u0)\<^sup>2 = (2 * cos u0)\<^sup>2" using ks by simp
    then show ?thesis by (simp add: power_mult_distrib)
  qed
  have e2: "(sin u0)\<^sup>2 + (cos u0)\<^sup>2 = 1" by simp
  have h4: "(sin u0)\<^sup>2 * (4 + k\<^sup>2) = 4 * ((sin u0)\<^sup>2 + (cos u0)\<^sup>2)"
  proof -
    have "(sin u0)\<^sup>2 * (4 + k\<^sup>2) = 4 * (sin u0)\<^sup>2 + k\<^sup>2 * (sin u0)\<^sup>2"
      by (simp add: algebra_simps)
    also have "\<dots> = 4 * (sin u0)\<^sup>2 + 4 * (cos u0)\<^sup>2" by (simp only: e1)
    also have "\<dots> = 4 * ((sin u0)\<^sup>2 + (cos u0)\<^sup>2)" by (rule distrib_left[symmetric])
    finally show ?thesis .
  qed
  have P: "(sin u0)\<^sup>2 * (4 + k\<^sup>2) = 4" by (simp only: h4 e2 mult_1_right)
  have s2: "(sin u0)\<^sup>2 = 4 / (4 + k\<^sup>2)"
  proof -
    have pos: "0 < 4 + k\<^sup>2" by (rule add_pos_nonneg) simp_all
    have n0: "4 + k\<^sup>2 \<noteq> 0" using pos by simp
    show ?thesis using n0 P by (rule eq_divide_imp)
  qed
  show "damped_sine k u0 = 4 / (4 + k\<^sup>2) * exp (- k * arctan (2 / k))"
    unfolding damped_sine_def using s2 u0_def by simp
qed

lemma damped_sine_le_peak_on_period:
  fixes k u :: real
  assumes "0 < k" and "0 \<le> u" and "u \<le> pi"
  shows "damped_sine k u \<le> damped_sine k (arctan (2 / k))"
proof -
  define u0 where "u0 = arctan (2 / k)"
  have u0nn: "0 \<le> u0" and u0lt: "u0 < pi / 2" and cpos: "0 < cos u0"
    and ks: "k * sin u0 = 2 * cos u0"
    using damped_sine_peak_facts[OF assms(1)] unfolding u0_def by simp_all
  have rel: "k * sin (u0 - x) = cos u0 * (2 * cos x - k * sin x)" for x
  proof -
    have "k * sin (u0 - x) = k * sin u0 * cos x - k * cos u0 * sin x"
      by (simp add: sin_diff algebra_simps)
    also have "\<dots> = 2 * cos u0 * cos x - k * cos u0 * sin x" using ks by simp
    finally show ?thesis by (simp add: algebra_simps)
  qed
  have E: "2 * cos x - k * sin x = k * sin (u0 - x) / cos u0" for x
    using rel cpos by (simp add: field_simps)
  have sinx: "0 \<le> sin x" if "0 \<le> x" "x \<le> pi" for x using that by (rule sin_ge_zero)
  show ?thesis
  proof (cases "u \<le> u0")
    case True
    have "damped_sine k u \<le> damped_sine k u0"
    proof (rule DERIV_nonneg_imp_nondecreasing[OF True])
      fix x assume x: "u \<le> x" "x \<le> u0"
      have "0 \<le> sin (u0 - x)" using x u0lt assms(2) by (intro sin_ge_zero) auto
      then have "0 \<le> 2 * cos x - k * sin x" using E[of x] cpos assms(1) by simp
      moreover have "0 \<le> sin x" using x u0lt assms(2) by (intro sinx) auto
      ultimately have "0 \<le> exp (- k * x) * sin x * (2 * cos x - k * sin x)" by simp
      then show "\<exists>y. DERIV (damped_sine k) x :> y \<and> 0 \<le> y"
        using damped_sine_deriv by blast
    qed
    then show ?thesis unfolding u0_def .
  next
    case False
    then have le: "u0 \<le> u" by simp
    have "damped_sine k u \<le> damped_sine k u0"
    proof (rule DERIV_nonpos_imp_nonincreasing[OF le])
      fix x assume x: "u0 \<le> x" "x \<le> u"
      have "0 \<le> sin (x - u0)" using x u0nn assms(3) u0lt by (intro sin_ge_zero) auto
      moreover have "sin (u0 - x) = - sin (x - u0)" by (metis minus_diff_eq sin_minus)
      ultimately have "sin (u0 - x) \<le> 0" by simp
      then have "2 * cos x - k * sin x \<le> 0"
        using E[of x] cpos assms(1) by (simp add: divide_nonpos_pos mult_nonneg_nonpos)
      moreover have "0 \<le> sin x" using x u0nn assms(3) by (intro sinx) auto
      ultimately have "exp (- k * x) * sin x * (2 * cos x - k * sin x) \<le> 0"
        by (simp add: mult_nonneg_nonpos)
      then show "\<exists>y. DERIV (damped_sine k) x :> y \<and> y \<le> 0"
        using damped_sine_deriv by blast
    qed
    then show ?thesis unfolding u0_def .
  qed
qed

lemma damped_sine_step:
  fixes k u :: real
  assumes "0 < k" and "0 \<le> u"
  shows "damped_sine k (u + pi) \<le> damped_sine k u"
proof -
  have st: "damped_sine k (u + pi) = exp (- k * pi) * damped_sine k u"
  proof -
    have e1: "- k * (u + pi) = - k * u + - k * pi" by (simp add: algebra_simps)
    have a: "exp (- k * (u + pi)) = exp (- k * pi) * exp (- k * u)"
      by (subst e1, subst exp_add, rule mult.commute)
    have sq: "(sin (u + pi))\<^sup>2 = (sin u)\<^sup>2" by (simp add: sin_add)
    show ?thesis unfolding damped_sine_def by (simp only: a sq mult.assoc)
  qed
  moreover have "exp (- k * pi) \<le> 1" using assms(1) by simp
  moreover have "0 \<le> damped_sine k u" unfolding damped_sine_def by simp
  ultimately have "exp (- k * pi) * damped_sine k u \<le> 1 * damped_sine k u"
    by (intro mult_right_mono) simp_all
  then show ?thesis using st by simp
qed

lemma damped_sine_le_peak:
  fixes k u :: real
  assumes "0 < k" and "0 \<le> u"
  shows "damped_sine k u \<le> 4 / (4 + k\<^sup>2) * exp (- k * arctan (2 / k))"
proof -
  have iter: "damped_sine k (v + real n * pi) \<le> damped_sine k v" if "0 \<le> v" for v n
  proof (induction n)
    case 0 then show ?case by simp
  next
    case (Suc n)
    have "damped_sine k (v + real (Suc n) * pi) = damped_sine k ((v + real n * pi) + pi)"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> damped_sine k (v + real n * pi)"
      using damped_sine_step[OF assms(1)] that by (simp add: add_nonneg_nonneg)
    finally show ?case using Suc.IH by simp
  qed
  define n where "n = nat (floor (u / pi))"
  have pipos: "0 < pi" by simp
  have fl0: "0 \<le> floor (u / pi)" using assms(2) pipos by (simp add: zero_le_floor)
  have nR: "real n = of_int (floor (u / pi))" unfolding n_def using fl0 by simp
  have a1: "real n * pi \<le> u"
  proof -
    have "of_int (floor (u / pi)) \<le> u / pi" by (rule of_int_floor_le)
    then show ?thesis unfolding nR using pipos by (simp add: le_divide_eq)
  qed
  have a2: "u < real n * pi + pi"
  proof -
    have "u / pi < of_int (floor (u / pi)) + 1" using floor_correct[of "u / pi"] by (simp add: of_int_add)
    then show ?thesis unfolding nR using pipos by (simp add: divide_less_eq algebra_simps)
  qed
  define v where "v = u - real n * pi"
  have v0: "0 \<le> v" and v1: "v \<le> pi" using a1 a2 unfolding v_def by simp_all
  have "damped_sine k u = damped_sine k (v + real n * pi)" unfolding v_def by simp
  also have "\<dots> \<le> damped_sine k v" using iter v0 by blast
  also have "\<dots> \<le> damped_sine k (arctan (2 / k))"
    using damped_sine_le_peak_on_period[OF assms(1) v0 v1] .
  also have "\<dots> = 4 / (4 + k\<^sup>2) * exp (- k * arctan (2 / k))"
    using damped_sine_peak_facts(5)[OF assms(1)] .
  finally show ?thesis .
qed

subsection \<open>Rescaling to the normalised form and the two statements\<close>

lemma pulse_rescale:
  fixes G gb \<Omega> t :: real
  assumes "0 < \<Omega>" and "0 < gb"
  shows "G\<^sup>2 / \<Omega>\<^sup>2 * exp (- gb * t) * (sin (\<Omega> * t))\<^sup>2
         = G\<^sup>2 / \<Omega>\<^sup>2 * damped_sine (gb / \<Omega>) (\<Omega> * t)"
proof -
  have "- (gb / \<Omega>) * (\<Omega> * t) = - gb * t" using assms(1) by (simp add: field_simps)
  then show ?thesis unfolding damped_sine_def by (simp add: mult.assoc)
qed

lemma pulse_peak_constant:
  fixes G gb \<Omega> :: real
  assumes "0 < \<Omega>" and "0 < gb"
  shows "G\<^sup>2 / \<Omega>\<^sup>2 * (4 / (4 + (gb / \<Omega>)\<^sup>2) * exp (- (gb / \<Omega>) * arctan (2 / (gb / \<Omega>))))
         = 4 * G\<^sup>2 / (4 * \<Omega>\<^sup>2 + gb\<^sup>2) * exp (- (gb / \<Omega>) * arctan (2 * \<Omega> / gb))"
proof -
  have a: "2 / (gb / \<Omega>) = 2 * \<Omega> / gb" using assms by (simp add: field_simps)
  have p1: "0 < \<Omega>\<^sup>2" using assms(1) by simp
  have p2: "0 < 4 * \<Omega>\<^sup>2 + gb\<^sup>2" using p1 by (intro add_pos_nonneg) simp_all
  have h: "G\<^sup>2 / \<Omega>\<^sup>2 * (4 / (4 + (gb / \<Omega>)\<^sup>2)) = 4 * G\<^sup>2 / (4 * \<Omega>\<^sup>2 + gb\<^sup>2)"
    using p1 p2 by (simp add: field_simps power_divide)
  show ?thesis unfolding a by (simp only: mult.assoc[symmetric] h)
qed

theorem resonant_pulse_max_bound:
  fixes G gq gm gb d \<Omega> t :: real
  assumes "0 < G" and "0 \<le> gq" and "0 \<le> gm" and "gb = (gq + gm) / 2" and "0 < gb"
    and "d = gq - gm" and "G\<^sup>2 > d\<^sup>2 / 16" and "\<Omega> = sqrt (G\<^sup>2 - d\<^sup>2 / 16)" and "0 \<le> t"
  shows "G\<^sup>2 / \<Omega>\<^sup>2 * exp (- gb * t) * (sin (\<Omega> * t))\<^sup>2
         \<le> 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- (gb / \<Omega>) * arctan (2 * \<Omega> / gb))"
proof -
  have om: "0 < \<Omega>" using assms(7,8) by simp
  have c1: "4 * \<Omega>\<^sup>2 + gb\<^sup>2 = 4 * G\<^sup>2 + gq * gm"
    using resonant_omega_identity[OF assms(4,6,7,8)] .
  have k: "0 < gb / \<Omega>" using om assms(5) by simp
  have "G\<^sup>2 / \<Omega>\<^sup>2 * exp (- gb * t) * (sin (\<Omega> * t))\<^sup>2
        = G\<^sup>2 / \<Omega>\<^sup>2 * damped_sine (gb / \<Omega>) (\<Omega> * t)"
    using pulse_rescale[OF om assms(5)] .
  also have "\<dots> \<le> G\<^sup>2 / \<Omega>\<^sup>2 * (4 / (4 + (gb / \<Omega>)\<^sup>2) * exp (- (gb / \<Omega>) * arctan (2 / (gb / \<Omega>))))"
    using damped_sine_le_peak[OF k, of "\<Omega> * t"] om assms(9) by (intro mult_left_mono) simp_all
  also have "\<dots> = 4 * G\<^sup>2 / (4 * \<Omega>\<^sup>2 + gb\<^sup>2) * exp (- (gb / \<Omega>) * arctan (2 * \<Omega> / gb))"
    by (rule pulse_peak_constant[OF om assms(5)])
  finally show ?thesis using c1 by simp
qed

theorem resonant_pulse_max_attained:
  fixes G gq gm gb d \<Omega> tstar :: real
  assumes "0 < G" and "0 \<le> gq" and "0 \<le> gm" and "gb = (gq + gm) / 2" and "0 < gb"
    and "d = gq - gm" and "G\<^sup>2 > d\<^sup>2 / 16" and "\<Omega> = sqrt (G\<^sup>2 - d\<^sup>2 / 16)"
    and "tstar = arctan (2 * \<Omega> / gb) / \<Omega>"
  shows "G\<^sup>2 / \<Omega>\<^sup>2 * exp (- gb * tstar) * (sin (\<Omega> * tstar))\<^sup>2
         = 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- (gb / \<Omega>) * arctan (2 * \<Omega> / gb))"
proof -
  have om: "0 < \<Omega>" using assms(7,8) by simp
  have c1: "4 * \<Omega>\<^sup>2 + gb\<^sup>2 = 4 * G\<^sup>2 + gq * gm"
    using resonant_omega_identity[OF assms(4,6,7,8)] .
  have k: "0 < gb / \<Omega>" using om assms(5) by simp
  have u: "\<Omega> * tstar = arctan (2 / (gb / \<Omega>))"
  proof -
    have "2 / (gb / \<Omega>) = 2 * \<Omega> / gb" using om assms(5) by (simp add: field_simps)
    then show ?thesis using om assms(9) by simp
  qed
  have "G\<^sup>2 / \<Omega>\<^sup>2 * exp (- gb * tstar) * (sin (\<Omega> * tstar))\<^sup>2
        = G\<^sup>2 / \<Omega>\<^sup>2 * damped_sine (gb / \<Omega>) (\<Omega> * tstar)"
    using pulse_rescale[OF om assms(5)] .
  also have "\<dots> = G\<^sup>2 / \<Omega>\<^sup>2 * (4 / (4 + (gb / \<Omega>)\<^sup>2) * exp (- (gb / \<Omega>) * arctan (2 / (gb / \<Omega>))))"
    using damped_sine_peak_facts(5)[OF k] u by simp
  also have "\<dots> = 4 * G\<^sup>2 / (4 * \<Omega>\<^sup>2 + gb\<^sup>2) * exp (- (gb / \<Omega>) * arctan (2 * \<Omega> / gb))"
    by (rule pulse_peak_constant[OF om assms(5)])
  finally show ?thesis using c1 by simp
qed

lemma max_population_symmetric:
  "max_population G gq gm = max_population G gm gq"
proof -
  have "(gq - gm)\<^sup>2 = (gm - gq)\<^sup>2" by (simp add: power2_eq_square algebra_simps)
  then show ?thesis unfolding max_population_def by (simp add: add.commute mult.commute)
qed

end
