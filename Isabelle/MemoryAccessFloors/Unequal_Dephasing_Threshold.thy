(*  Title:      Unequal_Dephasing_Threshold.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Resonant swap of one excitation with unequal pure dephasing (memory-floors note, Proposition 11,
    paragraph after "The exact threshold for equal rates").  Rates phi_q = q, phi_m = m, coupling G > 0,
    a = (q + m) / 2 (so Phi = 2 a), d = (q - m) / 2, delta = |d|.
    (A) the two criteria: sqrt(delta^2 - G^2) > sqrt(a^2 - 4 G^2) iff q m < 3 G^2, and
        min q m >= a - sqrt(a^2 - 4 G^2) iff q m >= 4 G^2;
    (B) closed forms w, u, v of the damped-oscillator and coherence equations;
    (C) the long-time comparison 4 u > w when Omega > kappa, and the opposite decay when Omega < kappa.
*)
theory Unequal_Dephasing_Threshold
  imports "HOL-Analysis.Analysis"
begin

section \<open>A. The two threshold criteria\<close>

theorem threshold_3G2:
  fixes q m G :: real
  assumes "0 < G" and "2 * G < (q + m) / 2" and "G < \<bar>q - m\<bar> / 2"
  shows "sqrt (((q + m) / 2)\<^sup>2 - 4 * G\<^sup>2) < sqrt ((\<bar>q - m\<bar> / 2)\<^sup>2 - G\<^sup>2) \<longleftrightarrow> q * m < 3 * G\<^sup>2"
proof -
  have a2: "4 * G\<^sup>2 < ((q + m) / 2)\<^sup>2"
  proof -
    have "(2 * G)\<^sup>2 < ((q + m) / 2)\<^sup>2" using assms(1,2) by (intro power_strict_mono) simp_all
    then show ?thesis by (simp add: power_mult_distrib)
  qed
  have key: "((q + m) / 2)\<^sup>2 - (\<bar>q - m\<bar> / 2)\<^sup>2 = q * m"
    by (simp add: power2_eq_square power_divide field_simps)
  have "sqrt (((q + m) / 2)\<^sup>2 - 4 * G\<^sup>2) < sqrt ((\<bar>q - m\<bar> / 2)\<^sup>2 - G\<^sup>2)
        \<longleftrightarrow> ((q + m) / 2)\<^sup>2 - 4 * G\<^sup>2 < (\<bar>q - m\<bar> / 2)\<^sup>2 - G\<^sup>2"
    using a2 by (intro real_sqrt_less_iff)
  also have "\<dots> \<longleftrightarrow> q * m < 3 * G\<^sup>2" using key by argo
  finally show ?thesis .
qed

theorem threshold_4G2:
  fixes q m G :: real
  assumes "0 < G" and "2 * G \<le> (q + m) / 2"
  shows "(q + m) / 2 - sqrt (((q + m) / 2)\<^sup>2 - 4 * G\<^sup>2) \<le> min q m \<longleftrightarrow> 4 * G\<^sup>2 \<le> q * m"
proof -
  define a where "a = (q + m) / 2"
  define dl where "dl = \<bar>q - m\<bar> / 2"
  have a2: "4 * G\<^sup>2 \<le> a\<^sup>2"
  proof -
    have "(2 * G)\<^sup>2 \<le> a\<^sup>2" using assms unfolding a_def by (intro power_mono) simp_all
    then show ?thesis by (simp add: power_mult_distrib)
  qed
  have mn: "min q m = a - dl"
  proof (cases "q \<le> m")
    case True
    then have "\<bar>q - m\<bar> = m - q" by (simp add: abs_of_nonpos)
    then show ?thesis using True unfolding a_def dl_def by (simp add: min_absorb1 field_simps)
  next
    case False
    then have "\<bar>q - m\<bar> = q - m" by (simp add: abs_of_nonneg)
    then show ?thesis using False unfolding a_def dl_def by (simp add: min_absorb2 field_simps)
  qed
  have dl0: "0 \<le> dl" unfolding dl_def by simp
  have key: "a\<^sup>2 - dl\<^sup>2 = q * m"
    unfolding a_def dl_def by (simp add: power2_eq_square power_divide field_simps)
  have "a - sqrt (a\<^sup>2 - 4 * G\<^sup>2) \<le> min q m \<longleftrightarrow> dl \<le> sqrt (a\<^sup>2 - 4 * G\<^sup>2)" unfolding mn by argo
  also have "\<dots> \<longleftrightarrow> dl\<^sup>2 \<le> a\<^sup>2 - 4 * G\<^sup>2"
  proof
    assume h: "dl \<le> sqrt (a\<^sup>2 - 4 * G\<^sup>2)"
    have "dl\<^sup>2 \<le> (sqrt (a\<^sup>2 - 4 * G\<^sup>2))\<^sup>2" using h dl0 by (intro power_mono) simp_all
    also have "\<dots> = a\<^sup>2 - 4 * G\<^sup>2" using a2 by (simp add: real_sqrt_pow2)
    finally show "dl\<^sup>2 \<le> a\<^sup>2 - 4 * G\<^sup>2" .
  next
    assume h: "dl\<^sup>2 \<le> a\<^sup>2 - 4 * G\<^sup>2"
    show "dl \<le> sqrt (a\<^sup>2 - 4 * G\<^sup>2)" by (rule real_le_rsqrt[OF h])
  qed
  also have "\<dots> \<longleftrightarrow> 4 * G\<^sup>2 \<le> q * m" using key by argo
  finally show ?thesis unfolding a_def .
qed

section \<open>B. Closed forms\<close>

definition kap :: "real \<Rightarrow> real \<Rightarrow> real" where
  "kap G a = sqrt (a\<^sup>2 - 4 * G\<^sup>2)"

definition wf :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "wf G a t = exp (- a * t) * (cosh (kap G a * t) + a / kap G a * sinh (kap G a * t))"

definition dwf :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "dwf G a t = - (4 * G\<^sup>2 / kap G a) * (exp (- a * t) * sinh (kap G a * t))"

definition uf :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "uf G a Om t = G / Om * (exp (- a * t) * sinh (Om * t))"

definition vf :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "vf a d Om t = exp (- a * t) * (cosh (Om * t) - d / Om * sinh (Om * t))"

lemma kap_facts:
  fixes G a :: real
  assumes "0 < G" and "2 * G < a"
  shows "0 < kap G a" and "(kap G a)\<^sup>2 = a\<^sup>2 - 4 * G\<^sup>2" and "0 < a"
proof -
  show "0 < a" using assms by simp
  have "(2 * G)\<^sup>2 < a\<^sup>2" using assms by (intro power_strict_mono) simp_all
  then have p: "0 < a\<^sup>2 - 4 * G\<^sup>2" by (simp add: power_mult_distrib)
  show "0 < kap G a" unfolding kap_def using p by simp
  show "(kap G a)\<^sup>2 = a\<^sup>2 - 4 * G\<^sup>2" unfolding kap_def using p by (simp add: real_sqrt_pow2)
qed

lemma wf_deriv:
  fixes G a t :: real
  assumes "0 < G" and "2 * G < a"
  shows "(wf G a has_real_derivative dwf G a t) (at t)"
proof -
  define k where "k = kap G a"
  have kp: "0 < k" unfolding k_def by (rule kap_facts(1)[OF assms])
  have k2: "k\<^sup>2 = a\<^sup>2 - 4 * G\<^sup>2" unfolding k_def by (rule kap_facts(2)[OF assms])
  have d: "((\<lambda>t. exp (- a * t) * (cosh (k * t) + a / k * sinh (k * t))) has_real_derivative
            exp (- a * t) * (- a * 1) * (cosh (k * t) + a / k * sinh (k * t))
            + exp (- a * t) * (sinh (k * t) * (k * 1) + a / k * (cosh (k * t) * (k * 1)))) (at t)"
    by (auto intro!: derivative_eq_intros)
  have eq: "exp (- a * t) * (- a * 1) * (cosh (k * t) + a / k * sinh (k * t))
            + exp (- a * t) * (sinh (k * t) * (k * 1) + a / k * (cosh (k * t) * (k * 1)))
            = - (4 * G\<^sup>2 / k) * (exp (- a * t) * sinh (k * t))"
  proof -
    have "exp (- a * t) * (- a * 1) * (cosh (k * t) + a / k * sinh (k * t))
            + exp (- a * t) * (sinh (k * t) * (k * 1) + a / k * (cosh (k * t) * (k * 1)))
          = exp (- a * t) * sinh (k * t) * (k - a\<^sup>2 / k)" using kp by (simp add: field_simps power2_eq_square)
    also have "\<dots> = exp (- a * t) * sinh (k * t) * ((k\<^sup>2 - a\<^sup>2) / k)" using kp by (simp add: field_simps power2_eq_square)
    also have "\<dots> = - (4 * G\<^sup>2 / k) * (exp (- a * t) * sinh (k * t))" unfolding k2 by (simp add: field_simps)
    finally show ?thesis .
  qed
  show ?thesis unfolding wf_def dwf_def k_def[symmetric] using d eq by simp
qed

lemma dwf_deriv:
  fixes G a t :: real
  assumes "0 < G" and "2 * G < a"
  shows "(dwf G a has_real_derivative (- 2 * a * dwf G a t - 4 * G\<^sup>2 * wf G a t)) (at t)"
proof -
  define k where "k = kap G a"
  have kp: "0 < k" unfolding k_def by (rule kap_facts(1)[OF assms])
  have k2: "k\<^sup>2 = a\<^sup>2 - 4 * G\<^sup>2" unfolding k_def by (rule kap_facts(2)[OF assms])
  have d: "((\<lambda>t. - (4 * G\<^sup>2 / k) * (exp (- a * t) * sinh (k * t))) has_real_derivative
            - (4 * G\<^sup>2 / k) * (exp (- a * t) * (- a * 1) * sinh (k * t) + exp (- a * t) * (cosh (k * t) * (k * 1)))) (at t)"
    using kp by (auto intro!: derivative_eq_intros)
  have eq: "- (4 * G\<^sup>2 / k) * (exp (- a * t) * (- a * 1) * sinh (k * t) + exp (- a * t) * (cosh (k * t) * (k * 1)))
            = - 2 * a * (- (4 * G\<^sup>2 / k) * (exp (- a * t) * sinh (k * t)))
              - 4 * G\<^sup>2 * (exp (- a * t) * (cosh (k * t) + a / k * sinh (k * t)))"
    using kp by (simp add: field_simps)
  show ?thesis unfolding dwf_def wf_def k_def[symmetric] using d eq by simp
qed

lemma wf_init:
  fixes G a :: real
  assumes "0 < G" and "2 * G < a"
  shows "wf G a 0 = 1" and "dwf G a 0 = 0"
  unfolding wf_def dwf_def by simp_all

theorem wf_ode:
  fixes G a :: real
  assumes "0 < G" and "2 * G < a"
  shows "\<forall>t. (wf G a has_real_derivative dwf G a t) (at t)
             \<and> (dwf G a has_real_derivative (- (2 * a) * dwf G a t - 4 * G\<^sup>2 * wf G a t)) (at t)"
    and "wf G a 0 = 1" and "dwf G a 0 = 0"
  using wf_deriv[OF assms] dwf_deriv[OF assms] wf_init[OF assms] by auto

lemma Om_facts:
  fixes G d Om :: real
  assumes "0 < G" and "G < \<bar>d\<bar>" and "Om = sqrt (d\<^sup>2 - G\<^sup>2)"
  shows "0 < Om" and "Om\<^sup>2 = d\<^sup>2 - G\<^sup>2"
proof -
  have "G\<^sup>2 < \<bar>d\<bar>\<^sup>2" using assms(1,2) by (intro power_strict_mono) simp_all
  then have p: "0 < d\<^sup>2 - G\<^sup>2" by simp
  show "0 < Om" using assms(3) p by simp
  show "Om\<^sup>2 = d\<^sup>2 - G\<^sup>2" using assms(3) p by (simp add: real_sqrt_pow2)
qed

lemma alg_v:
  fixes E C S a d G Om :: real
  assumes "Om \<noteq> 0" and "Om\<^sup>2 = d\<^sup>2 - G\<^sup>2"
  shows "E * (- a * 1) * (C - d / Om * S) + E * (S * (Om * 1) - d / Om * (C * (Om * 1)))
         = - (a + d) * (E * (C - d / Om * S)) - G * (G / Om * (E * S))"
proof -
  have "\<exists>x. S = Om * x" using assms(1) by (intro exI[where x = "S / Om"]) simp
  then obtain x where S: "S = Om * x" by blast
  have h1: "d / Om * (Om * x) = d * x" using assms(1) by simp
  have h2: "d / Om * (C * (Om * 1)) = d * C" using assms(1) by simp
  have h3: "G / Om * (E * (Om * x)) = G * (E * x)" using assms(1) by simp
  have "E * (- a * 1) * (C - d * x) + E * (Om * x * (Om * 1) - d * C)
        = - (a + d) * (E * (C - d * x)) - G * (G * (E * x)) + E * x * (Om\<^sup>2 - (d\<^sup>2 - G\<^sup>2))"
    by (simp add: algebra_simps power2_eq_square)
  then have "E * (- a * 1) * (C - d * x) + E * (Om * x * (Om * 1) - d * C)
        = - (a + d) * (E * (C - d * x)) - G * (G * (E * x))" using assms(2) by simp
  then show ?thesis unfolding S h1 h2 h3 .
qed

lemma alg_u:
  fixes E C S a d G Om :: real
  assumes "Om \<noteq> 0"
  shows "G / Om * (E * (- a * 1) * S + E * (C * (Om * 1)))
         = G * (E * (C - d / Om * S)) - (a - d) * (G / Om * (E * S))"
proof -
  have "\<exists>x. S = Om * x" using assms(1) by (intro exI[where x = "S / Om"]) simp
  then obtain x where S: "S = Om * x" by blast
  have h1: "d / Om * (Om * x) = d * x" using assms(1) by simp
  have h3: "G / Om * (E * (Om * x)) = G * (E * x)" using assms(1) by simp
  have h4: "G / Om * (E * (- a * 1) * (Om * x) + E * (C * (Om * 1))) = G * (E * (C - a * x))"
    using assms(1) by (simp add: field_simps)
  have "G * (E * (C - a * x)) = G * (E * (C - d * x)) - (a - d) * (G * (E * x))"
    by (simp add: algebra_simps)
  then show ?thesis unfolding S h1 h3 h4 .
qed

lemma coherence_ode_gen:
  fixes G a d Om :: real
  assumes "0 < Om" and "Om\<^sup>2 = d\<^sup>2 - G\<^sup>2"
  shows "(vf a d Om has_real_derivative (- (a + d) * vf a d Om t - G * uf G a Om t)) (at t)"
    and "(uf G a Om has_real_derivative (G * vf a d Om t - (a - d) * uf G a Om t)) (at t)"
proof -
  have on: "Om \<noteq> 0" using assms(1) by simp
  have dv: "((\<lambda>t. exp (- a * t) * (cosh (Om * t) - d / Om * sinh (Om * t))) has_real_derivative
          exp (- a * t) * (- a * 1) * (cosh (Om * t) - d / Om * sinh (Om * t))
          + exp (- a * t) * (sinh (Om * t) * (Om * 1) - d / Om * (cosh (Om * t) * (Om * 1)))) (at t)"
    by (auto intro!: derivative_eq_intros)
  have du: "((\<lambda>t. G / Om * (exp (- a * t) * sinh (Om * t))) has_real_derivative
          G / Om * (exp (- a * t) * (- a * 1) * sinh (Om * t) + exp (- a * t) * (cosh (Om * t) * (Om * 1)))) (at t)"
    using on by (auto intro!: derivative_eq_intros)
  show "(vf a d Om has_real_derivative (- (a + d) * vf a d Om t - G * uf G a Om t)) (at t)"
    unfolding vf_def uf_def using dv alg_v[OF on assms(2)] by simp
  show "(uf G a Om has_real_derivative (G * vf a d Om t - (a - d) * uf G a Om t)) (at t)"
    unfolding vf_def uf_def using du alg_u[OF on] by simp
qed

theorem coherence_ode:
  fixes G q m Om :: real
  assumes "0 < G" and "G < \<bar>q - m\<bar> / 2" and "Om = sqrt (((q - m) / 2)\<^sup>2 - G\<^sup>2)"
  shows "\<forall>t. (vf ((q + m) / 2) ((q - m) / 2) Om has_real_derivative
              (- q * vf ((q + m) / 2) ((q - m) / 2) Om t - G * uf G ((q + m) / 2) Om t)) (at t)"
    and "\<forall>t. (uf G ((q + m) / 2) Om has_real_derivative
              (G * vf ((q + m) / 2) ((q - m) / 2) Om t - m * uf G ((q + m) / 2) Om t)) (at t)"
    and "vf ((q + m) / 2) ((q - m) / 2) Om 0 = 1" and "uf G ((q + m) / 2) Om 0 = 0"
proof -
  have dd: "G < \<bar>(q - m) / 2\<bar>" using assms(2) by simp
  have op: "0 < Om" and o2: "Om\<^sup>2 = ((q - m) / 2)\<^sup>2 - G\<^sup>2"
    using Om_facts[OF assms(1) dd assms(3)] by simp_all
  have e1: "(q + m) / 2 + (q - m) / 2 = q" by argo
  have e2: "(q + m) / 2 - (q - m) / 2 = m" by argo
  show "\<forall>t. (vf ((q + m) / 2) ((q - m) / 2) Om has_real_derivative
              (- q * vf ((q + m) / 2) ((q - m) / 2) Om t - G * uf G ((q + m) / 2) Om t)) (at t)"
  proof
    fix t :: real
    show "(vf ((q + m) / 2) ((q - m) / 2) Om has_real_derivative
              (- q * vf ((q + m) / 2) ((q - m) / 2) Om t - G * uf G ((q + m) / 2) Om t)) (at t)"
      using coherence_ode_gen(1)[OF op o2, where a = "(q + m) / 2" and t = t] unfolding e1 .
  qed
  show "\<forall>t. (uf G ((q + m) / 2) Om has_real_derivative
              (G * vf ((q + m) / 2) ((q - m) / 2) Om t - m * uf G ((q + m) / 2) Om t)) (at t)"
  proof
    fix t :: real
    show "(uf G ((q + m) / 2) Om has_real_derivative
              (G * vf ((q + m) / 2) ((q - m) / 2) Om t - m * uf G ((q + m) / 2) Om t)) (at t)"
      using coherence_ode_gen(2)[OF op o2, where a = "(q + m) / 2" and t = t] unfolding e2 .
  qed
  show "vf ((q + m) / 2) ((q - m) / 2) Om 0 = 1" "uf G ((q + m) / 2) Om 0 = 0"
    unfolding vf_def uf_def by simp_all
qed

section \<open>C. Long-time behaviour\<close>

lemma cosh_le_exp:
  fixes x :: real
  assumes "0 \<le> x"
  shows "cosh x \<le> exp x"
proof -
  have "exp (- x) \<le> exp x" using assms by simp
  then show ?thesis unfolding cosh_def by (simp add: field_simps)
qed

lemma sinh_le_exp:
  fixes x :: real
  assumes "0 \<le> x"
  shows "sinh x \<le> exp x"
proof -
  have "0 < exp (- x)" by simp
  then show ?thesis unfolding sinh_def by (simp add: field_simps)
qed

lemma sinh_ge_exp_half:
  fixes x :: real
  assumes "0 \<le> x"
  shows "(exp x - 1) / 2 \<le> sinh x"
proof -
  have "exp (- x) \<le> 1" using assms by simp
  then show ?thesis unfolding sinh_def by (simp add: field_simps)
qed

lemma two_c_eq:
  fixes c e :: real
  shows "2 * c * (e - 1) = 4 * (c * ((e - 1) / 2))"
  by (simp add: algebra_simps)

theorem eventually_four_u_gt_w:
  fixes G a Om :: real
  assumes "0 < G" and "2 * G < a" and "kap G a < Om"
  shows "eventually (\<lambda>t. wf G a t < 4 * uf G a Om t) at_top"
proof -
  define k where "k = kap G a"
  have kp: "0 < k" unfolding k_def by (rule kap_facts(1)[OF assms(1,2)])
  have ap: "0 < a" by (rule kap_facts(3)[OF assms(1,2)])
  have kO: "k < Om" using assms(3) unfolding k_def .
  have Op: "0 < Om" using kp kO by simp
  define C where "C = (1 + a / k) * Om / (2 * G)"
  have Cp: "0 < C"
  proof -
    have "0 < 1 + a / k" using kp ap by (simp add: add_pos_pos)
    then show ?thesis unfolding C_def using Op assms(1) by (intro divide_pos_pos mult_pos_pos) simp_all
  qed
  define eps where "eps = Om - k"
  have ep: "0 < eps" unfolding eps_def using kO by simp
  define t0 where "t0 = max 1 (ln (C + 1) / eps)"
  have ev: "eventually (\<lambda>t. t0 \<le> t) at_top" by (rule eventually_ge_at_top)
  show ?thesis
  proof (rule eventually_mono[OF ev])
    fix t :: real
    assume th: "t0 \<le> t"
    have t1: "1 \<le> t" using th unfolding t0_def by simp
    have t0p: "0 < t" using t1 by simp
    have lt: "ln (C + 1) / eps \<le> t" using th unfolding t0_def by simp
    have "ln (C + 1) \<le> eps * t" using lt ep by (simp add: field_simps)
    then have "exp (ln (C + 1)) \<le> exp (eps * t)" by (rule exp_mono)
    then have E1: "C + 1 \<le> exp (eps * t)" using Cp by simp
    have kt: "0 < k * t" using kp t0p by simp
    have E2: "1 < exp (k * t)" using kt by simp
    have split: "exp (Om * t) = exp (k * t) * exp (eps * t)"
      unfolding eps_def by (simp add: exp_add[symmetric] algebra_simps)
    have "C * exp (k * t) + 1 < C * exp (k * t) + exp (k * t)" using E2 by simp
    also have "\<dots> = (C + 1) * exp (k * t)" by (simp add: algebra_simps)
    also have "\<dots> \<le> exp (eps * t) * exp (k * t)" using E1 E2 by (intro mult_right_mono) simp_all
    also have "\<dots> = exp (Om * t)" unfolding split by simp
    finally have E3: "C * exp (k * t) < exp (Om * t) - 1" by simp
    have Ot: "0 \<le> Om * t" using Op t0p by simp
    have kt0: "0 \<le> k * t" using kt by simp
    have ch: "cosh (k * t) \<le> exp (k * t)" by (rule cosh_le_exp[OF kt0])
    have sh: "sinh (k * t) \<le> exp (k * t)" by (rule sinh_le_exp[OF kt0])
    have R: "cosh (k * t) + a / k * sinh (k * t) \<le> (1 + a / k) * exp (k * t)"
    proof -
      have "a / k * sinh (k * t) \<le> a / k * exp (k * t)" using sh kp ap by (intro mult_left_mono) simp_all
      then show ?thesis using ch by (simp add: algebra_simps)
    qed
    have Lw: "(2 * G / Om) * (exp (Om * t) - 1) \<le> 4 * (G / Om * sinh (Om * t))"
    proof -
      have "(exp (Om * t) - 1) / 2 \<le> sinh (Om * t)" by (rule sinh_ge_exp_half[OF Ot])
      then have h: "G / Om * ((exp (Om * t) - 1) / 2) \<le> G / Om * sinh (Om * t)"
        using Op assms(1) by (intro mult_left_mono) simp_all
      have c: "2 * G / Om = 2 * (G / Om)" by simp
      have e: "2 * (G / Om) * (exp (Om * t) - 1) = 4 * (G / Om * ((exp (Om * t) - 1) / 2))"
        by (rule two_c_eq)
      have "4 * (G / Om * ((exp (Om * t) - 1) / 2)) \<le> 4 * (G / Om * sinh (Om * t))"
        using h by (rule mult_left_mono) simp
      then show ?thesis unfolding c e .
    qed
    have Cm: "(2 * G / Om) * (C * exp (k * t)) = (1 + a / k) * exp (k * t)"
      unfolding C_def using Op assms(1) by (simp add: field_simps)
    have "(1 + a / k) * exp (k * t) = (2 * G / Om) * (C * exp (k * t))" by (rule Cm[symmetric])
    also have "\<dots> < (2 * G / Om) * (exp (Om * t) - 1)"
      using E3 Op assms(1) by (intro mult_strict_left_mono) simp_all
    finally have Rl: "(1 + a / k) * exp (k * t) < (2 * G / Om) * (exp (Om * t) - 1)" .
    have W: "cosh (k * t) + a / k * sinh (k * t) < 4 * (G / Om * sinh (Om * t))"
      using R Rl Lw by linarith
    have "exp (- a * t) * (cosh (k * t) + a / k * sinh (k * t)) < exp (- a * t) * (4 * (G / Om * sinh (Om * t)))"
      using W by (intro mult_strict_left_mono) simp_all
    then show "wf G a t < 4 * uf G a Om t"
      unfolding wf_def uf_def k_def[symmetric] by (simp add: algebra_simps)
  qed
qed

lemma p_plus_2c_iff:
  fixes w u :: real
  shows "(1 - w) / 2 + 2 * u > 1 / 2 \<longleftrightarrow> w < 4 * u"
  by argo

theorem resonant_below_five_twelfths:
  fixes G q m :: real
  assumes "0 < G" and "2 * G < (q + m) / 2" and "G < \<bar>q - m\<bar> / 2" and "q * m < 3 * G\<^sup>2"
  shows "eventually (\<lambda>t. (1 - wf G ((q + m) / 2) t) / 2
                         + 2 * uf G ((q + m) / 2) (sqrt ((\<bar>q - m\<bar> / 2)\<^sup>2 - G\<^sup>2)) t > 1 / 2) at_top"
proof -
  have "kap G ((q + m) / 2) < sqrt ((\<bar>q - m\<bar> / 2)\<^sup>2 - G\<^sup>2)"
    unfolding kap_def using threshold_3G2[OF assms(1-3)] assms(4) by simp
  from eventually_four_u_gt_w[OF assms(1,2) this] show ?thesis
  proof (rule eventually_mono)
    fix t :: real
    assume "wf G ((q + m) / 2) t < 4 * uf G ((q + m) / 2) (sqrt ((\<bar>q - m\<bar> / 2)\<^sup>2 - G\<^sup>2)) t"
    then show "1 / 2 < (1 - wf G ((q + m) / 2) t) / 2
                 + 2 * uf G ((q + m) / 2) (sqrt ((\<bar>q - m\<bar> / 2)\<^sup>2 - G\<^sup>2)) t"
      by (rule iffD2[OF p_plus_2c_iff])
  qed
qed

lemma exp_neg_linear_tendsto:
  fixes c :: real
  assumes "0 < c"
  shows "((\<lambda>T. exp (- (c * T))) \<longlongrightarrow> 0) at_top"
proof -
  have "filterlim (\<lambda>T. - (c * T)) at_bot at_top"
  proof (subst filterlim_at_bot)
    show "\<forall>Z. eventually (\<lambda>T. - (c * T) \<le> Z) at_top"
    proof
      fix Z :: real
      have "eventually (\<lambda>T. - Z / c \<le> T) at_top" by (rule eventually_ge_at_top)
      then show "eventually (\<lambda>T. - (c * T) \<le> Z) at_top"
      proof (rule eventually_mono)
        fix T :: real
        assume "- Z / c \<le> T"
        then have "- Z \<le> T * c" using assms by (simp add: field_simps)
        then show "- (c * T) \<le> Z" by (simp add: algebra_simps)
      qed
    qed
  qed
  from filterlim_compose[OF exp_at_bot this] show ?thesis by (simp add: comp_def)
qed

theorem ratio_tends_to_zero:
  fixes G a Om :: real
  assumes "0 < G" and "2 * G < a" and "0 < Om" and "Om < kap G a"
  shows "((\<lambda>t. 4 * uf G a Om t / wf G a t) \<longlongrightarrow> 0) at_top"
proof -
  define k where "k = kap G a"
  have kp: "0 < k" unfolding k_def by (rule kap_facts(1)[OF assms(1,2)])
  have ap: "0 < a" by (rule kap_facts(3)[OF assms(1,2)])
  have kO: "Om < k" using assms(4) unfolding k_def .
  have lim: "((\<lambda>t. 4 * G / Om * exp (- ((k - Om) * t))) \<longlongrightarrow> 4 * G / Om * 0) at_top"
    by (intro tendsto_intros exp_neg_linear_tendsto) (use kO in simp)
  have ev: "eventually (\<lambda>t::real. 0 \<le> t) at_top" by (rule eventually_ge_at_top)
  have bound: "eventually (\<lambda>t. 0 \<le> 4 * uf G a Om t / wf G a t
                  \<and> 4 * uf G a Om t / wf G a t \<le> 4 * G / Om * exp (- ((k - Om) * t))) at_top"
  proof (rule eventually_mono[OF ev])
    fix t :: real
    assume t0: "0 \<le> t"
    have kt: "0 \<le> k * t" using kp t0 by simp
    have Ot: "0 \<le> Om * t" using assms(3) t0 by simp
    have e0: "0 < exp (- a * t)" by simp
    have sk: "0 \<le> sinh (k * t)" using kt by (simp add: sinh_real_nonneg_iff)
    have sO: "0 \<le> sinh (Om * t)" using Ot by (simp add: sinh_real_nonneg_iff)
    have ck: "exp (k * t) / 2 \<le> cosh (k * t)" unfolding cosh_def using kt by simp
    have wpos: "exp (- a * t) * (exp (k * t) / 2) \<le> wf G a t"
    proof -
      have "exp (k * t) / 2 \<le> cosh (k * t) + a / k * sinh (k * t)"
      proof -
        have "0 \<le> a / k * sinh (k * t)" using sk kp ap by (intro mult_nonneg_nonneg) simp_all
        then show ?thesis using ck by linarith
      qed
      then show ?thesis unfolding wf_def k_def[symmetric] using e0 by (intro mult_left_mono) simp_all
    qed
    have wp0: "0 < exp (- a * t) * (exp (k * t) / 2)" by simp
    have wp: "0 < wf G a t" using wpos wp0 by linarith
    have up: "0 \<le> uf G a Om t" unfolding uf_def using assms(1,3) e0 sO by (simp add: mult_nonneg_nonneg)
    have uup: "uf G a Om t \<le> G / Om * (exp (- a * t) * (exp (Om * t) / 2))"
    proof -
      have "sinh (Om * t) \<le> exp (Om * t) / 2" unfolding sinh_def by simp
      then show ?thesis unfolding uf_def using assms(1,3) e0 by (intro mult_left_mono mult_left_mono) simp_all
    qed
    have ex: "exp (- a * t) * (exp (Om * t) / 2) / (exp (- a * t) * (exp (k * t) / 2)) = exp (- ((k - Om) * t))"
    proof -
      have e1: "0 < exp (- a * t)" and e2: "0 < exp (k * t)" by simp_all
      have "exp (- a * t) * (exp (Om * t) / 2) / (exp (- a * t) * (exp (k * t) / 2)) = exp (Om * t) / exp (k * t)"
        using e1 e2 by (simp add: field_simps)
      also have "\<dots> = exp (Om * t - k * t)" by (simp add: exp_diff)
      also have "\<dots> = exp (- ((k - Om) * t))" by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have "4 * uf G a Om t / wf G a t \<le> 4 * (G / Om * (exp (- a * t) * (exp (Om * t) / 2))) / (exp (- a * t) * (exp (k * t) / 2))"
    proof (rule frac_le)
      have c0: "0 \<le> G / Om" using assms(1,3) by simp
      show "0 \<le> 4 * (G / Om * (exp (- a * t) * (exp (Om * t) / 2)))"
        by (intro mult_nonneg_nonneg) (use c0 in simp_all)
      show "4 * uf G a Om t \<le> 4 * (G / Om * (exp (- a * t) * (exp (Om * t) / 2)))"
        using uup by (rule mult_left_mono) simp
      show "0 < exp (- a * t) * (exp (k * t) / 2)" by (rule wp0)
      show "exp (- a * t) * (exp (k * t) / 2) \<le> wf G a t" by (rule wpos)
    qed
    also have "\<dots> = 4 * G / Om * (exp (- a * t) * (exp (Om * t) / 2) / (exp (- a * t) * (exp (k * t) / 2)))"
      by (simp add: mult.assoc)
    also have "\<dots> = 4 * G / Om * exp (- ((k - Om) * t))" unfolding ex ..
    finally have "4 * uf G a Om t / wf G a t \<le> 4 * G / Om * exp (- ((k - Om) * t))" .
    moreover have "0 \<le> 4 * uf G a Om t / wf G a t" using up wp by simp
    ultimately show "0 \<le> 4 * uf G a Om t / wf G a t
                  \<and> 4 * uf G a Om t / wf G a t \<le> 4 * G / Om * exp (- ((k - Om) * t))" by simp
  qed
  show ?thesis
  proof (rule real_tendsto_sandwich[where f = "\<lambda>t. 0" and h = "\<lambda>t. 4 * G / Om * exp (- ((k - Om) * t))"])
    show "\<forall>\<^sub>F t in at_top. (0::real) \<le> 4 * uf G a Om t / wf G a t"
      using bound by (rule eventually_mono) simp
    show "\<forall>\<^sub>F t in at_top. 4 * uf G a Om t / wf G a t \<le> 4 * G / Om * exp (- ((k - Om) * t))"
      using bound by (rule eventually_mono) simp
    show "((\<lambda>t. (0::real)) \<longlongrightarrow> 0) at_top" by simp
    show "((\<lambda>t. 4 * G / Om * exp (- ((k - Om) * t))) \<longlongrightarrow> 0) at_top" using lim by simp
  qed
qed

end
