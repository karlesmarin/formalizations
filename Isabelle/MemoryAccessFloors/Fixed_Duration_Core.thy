(*  Title:      Fixed_Duration_Core.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    The algebraic core of the proof of Theorem "fixed duration" (thm:fixed) of the memory-floor note A
    (memory-floors.tex, section "Fixed durations, and a proof without the maximum principle").

    What is formalised.  Notation of the proof: for an active functional f = tr(E R) with E having diagonal entries
    A, B and off-diagonal entry E_ab, and for a control value w (a complex number),
        H_w = h0 + 2 Im(cnj w * K),   h0 = -gq A a - gm B b - 2 Gamma Re(cnj E_ab * rho),
        K = E_ab (a - b) + rho (B - A).
    - (C1) max over |w| <= G of H_w is h0 + 2 G |K|, attained (H_max_bound, H_max_attained, H_max);
    - (C0) sign of h0: h0 <= -gamma_min f when the rates are >= gamma_min and Re(cnj E_ab rho) >= 0 (h0_bound);
    - (C2) cases (i) and (ii): K a real multiple of E_ab = i z e^{i theta} gives H_{g_theta} = h0 +- 2 G |K|
      (H_aligned_cases); with h0 < 0 and H_{g_theta} >= 0 the sign is plus and H_{g_theta} is the maximum
      (case_ii, case_i);
    - (C3) case (iii): the average of H_{G e^{i theta}} over [0, 2 pi] is h0, so for h0 < 0 not all are >= 0
      (H_average, case_iii);
    - (C4) case (iv): for f = b, H_w <= -gm b + 2 G |rho| (case_iv);
    - (C5) the limit eps -> 0 of the shifted systems keeps monotonicity, with the abstract bounds
      exp(-eps T) x <= y_eps <= x (epsilon_limit);
    - (C6) the conclusion p_b(T) = V_0(R(T)) <= V_T(R(0)) from the monotonicity of v(t) = V_{T-t}(R(t))
      (lyapunov_conclusion).

    What is NOT formalised (text only).  The Danskin theorem on the derivative of a maximum over a compact family,
    the Lipschitz property of v, the identification of H_w with the derivative of the active functional along the
    trajectory (a matrix equation for the generator of the master equation), the compactness/attainment of the
    supremum, and the evaluation of V_T(R(0)) as max p_res(s).  These enter the paper's proof; here only the real and
    complex algebra that decides the sign of each case is proved.
*)
theory Fixed_Duration_Core
  imports "HOL-Analysis.Analysis"
begin

section \<open>The function H and its maximum over the disc (C1)\<close>

definition Hfun :: "real \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> real" where
  "Hfun h0 K w = h0 + 2 * Im (cnj w * K)"

lemma Im_cnj_bound:
  assumes "norm w \<le> G"
  shows "Im (cnj w * K) \<le> G * norm K"
proof -
  have "Im (cnj w * K) \<le> norm (cnj w * K)" by (rule order_trans[OF abs_ge_self abs_Im_le_cmod])
  also have "\<dots> = norm w * norm K" by (simp add: norm_mult)
  also have "\<dots> \<le> G * norm K" using assms by (intro mult_right_mono) simp_all
  finally show ?thesis .
qed

theorem H_max_bound:
  assumes "norm w \<le> G"
  shows "Hfun h0 K w \<le> h0 + 2 * G * norm K"
  using Im_cnj_bound[OF assms, of K] by (simp add: Hfun_def)

definition wmax :: "real \<Rightarrow> complex \<Rightarrow> complex" where
  "wmax G K = - \<i> * of_real G * K / of_real (norm K)"

theorem H_max_attained:
  assumes "0 \<le> G"
  shows "norm (wmax G K) \<le> G" and "Hfun h0 K (wmax G K) = h0 + 2 * G * norm K"
proof -
  show "norm (wmax G K) \<le> G"
  proof (cases "K = 0")
    case True then show ?thesis using assms by (simp add: wmax_def)
  next
    case False
    then show ?thesis using assms by (simp add: wmax_def norm_divide norm_mult)
  qed
  show "Hfun h0 K (wmax G K) = h0 + 2 * G * norm K"
  proof (cases "K = 0")
    case True then show ?thesis by (simp add: wmax_def Hfun_def)
  next
    case False
    then have nK: "norm K \<noteq> 0" by simp
    have sq: "of_real (norm K ^ 2) = K * cnj K" by (rule complex_norm_square)
    have "cnj (wmax G K) * K = \<i> * of_real G * (K * cnj K) / of_real (norm K)"
      by (simp add: wmax_def complex_cnj_divide complex_cnj_mult algebra_simps)
    also have "\<dots> = \<i> * of_real (G * norm K)"
    proof -
      have nK': "(of_real (norm K) :: complex) \<noteq> 0" using nK by simp
      have sq': "K * cnj K = of_real (norm K) * of_real (norm K)"
        using sq by (simp add: power2_eq_square)
      show ?thesis
        by (simp add: sq' nK' of_real_mult field_simps)
    qed
    finally have "Im (cnj (wmax G K) * K) = G * norm K" by simp
    then show ?thesis by (simp add: Hfun_def)
  qed
qed

theorem H_max:
  assumes "0 \<le> G"
  shows "(\<forall>w. norm w \<le> G \<longrightarrow> Hfun h0 K w \<le> h0 + 2 * G * norm K)
         \<and> (\<exists>w. norm w \<le> G \<and> Hfun h0 K w = h0 + 2 * G * norm K)"
  using H_max_bound H_max_attained[OF assms] by blast

section \<open>The sign of h0 (C0)\<close>

definition h0f :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex \<Rightarrow> real" where
  "h0f gq gm Gam A B Eab a b rho = - gq * A * a - gm * B * b - 2 * Gam * Re (cnj Eab * rho)"

definition Kf :: "real \<Rightarrow> real \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex \<Rightarrow> complex" where
  "Kf A B Eab a b rho = Eab * of_real (a - b) + rho * of_real (B - A)"

definition ffun :: "real \<Rightarrow> real \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex \<Rightarrow> real" where
  "ffun A B Eab a b rho = A * a + B * b + 2 * Re (cnj Eab * rho)"

theorem h0_bound:
  assumes "gmin \<le> gq" "gmin \<le> gm" "gmin \<le> Gam" "0 \<le> A" "0 \<le> B" "0 \<le> a" "0 \<le> b"
    and "0 \<le> Re (cnj Eab * rho)"
  shows "h0f gq gm Gam A B Eab a b rho \<le> - gmin * ffun A B Eab a b rho"
proof -
  have "gmin * (A * a) \<le> gq * (A * a)" using assms by (intro mult_right_mono) simp_all
  moreover have "gmin * (B * b) \<le> gm * (B * b)" using assms by (intro mult_right_mono) simp_all
  moreover have "gmin * Re (cnj Eab * rho) \<le> Gam * Re (cnj Eab * rho)"
    using assms by (intro mult_right_mono) simp_all
  ultimately show ?thesis by (simp add: h0f_def ffun_def algebra_simps)
qed

corollary h0_negative:
  assumes "0 < gmin" "gmin \<le> gq" "gmin \<le> gm" "gmin \<le> Gam" "0 \<le> A" "0 \<le> B" "0 \<le> a" "0 \<le> b"
    and "0 \<le> Re (cnj Eab * rho)" and "0 < ffun A B Eab a b rho"
  shows "h0f gq gm Gam A B Eab a b rho < 0"
proof -
  have "h0f gq gm Gam A B Eab a b rho \<le> - gmin * ffun A B Eab a b rho"
    by (rule h0_bound) (use assms in simp_all)
  moreover have "0 < gmin * ffun A B Eab a b rho" using assms by simp
  ultimately show ?thesis by simp
qed

section \<open>Cases (i) and (ii): alignment (C2)\<close>

definition Eab_pulse :: "real \<Rightarrow> real \<Rightarrow> complex" where
  "Eab_pulse z th = \<i> * of_real z * cis th"

definition g_th :: "real \<Rightarrow> real \<Rightarrow> complex" where
  "g_th G th = of_real G * cis th"

lemma cnj_cis_cis: "cnj (cis th) * cis th = 1"
  by (simp add: cis_cnj cis_mult)

theorem H_aligned:
  "cnj (g_th G th) * (of_real c * Eab_pulse z th) = \<i> * of_real (G * c * z)"
proof -
  have "cnj (g_th G th) * (of_real c * Eab_pulse z th)
        = (cnj (cis th) * cis th) * (\<i> * of_real (G * c * z))"
    by (simp add: g_th_def Eab_pulse_def algebra_simps)
  then show ?thesis by (simp add: cnj_cis_cis)
qed

theorem H_aligned_cases:
  assumes "K = of_real c * Eab_pulse z th" and "0 \<le> G"
  shows "Hfun h0 K (g_th G th) = h0 + 2 * G * norm K
       \<or> Hfun h0 K (g_th G th) = h0 - 2 * G * norm K"
proof -
  have nK: "norm K = \<bar>c\<bar> * \<bar>z\<bar>"
    using assms(1) by (simp add: Eab_pulse_def norm_mult)
  have "Hfun h0 K (g_th G th) = h0 + 2 * (G * c * z)"
  proof -
    have "cnj (g_th G th) * K = \<i> * of_real (G * c * z)"
      using H_aligned[of G th c z] assms(1) by simp
    then show ?thesis by (simp add: Hfun_def)
  qed
  moreover have "G * c * z = G * norm K \<or> G * c * z = - (G * norm K)"
  proof -
    have "c * z = \<bar>c\<bar> * \<bar>z\<bar> \<or> c * z = - (\<bar>c\<bar> * \<bar>z\<bar>)"
      by (cases "0 \<le> c * z") (simp_all add: abs_mult [symmetric])
    then show ?thesis using nK by (auto simp: algebra_simps)
  qed
  ultimately show ?thesis by auto
qed

lemma case_ii_plus:
  assumes "K = of_real c * Eab_pulse z th" and "0 \<le> G" and "h0 < 0"
    and "0 \<le> Hfun h0 K (g_th G th)"
  shows "Hfun h0 K (g_th G th) = h0 + 2 * G * norm K"
proof -
  have GK: "0 \<le> G * norm K" using assms(2) by simp
  show ?thesis
    using H_aligned_cases[OF assms(1,2), of h0] assms(3,4) GK by (elim disjE) linarith+
qed

theorem case_ii:
  assumes "K = of_real c * Eab_pulse z th" and "0 \<le> G" and "h0 < 0"
    and "0 \<le> Hfun h0 K (g_th G th)" and "norm w \<le> G"
  shows "Hfun h0 K (g_th G th) = h0 + 2 * G * norm K"
    and "Hfun h0 K w \<le> Hfun h0 K (g_th G th)"
    and "Hfun h0 K w - Hfun h0 K (g_th G th) \<le> 0"
proof -
  have plus: "Hfun h0 K (g_th G th) = h0 + 2 * G * norm K"
    by (rule case_ii_plus[OF assms(1-4)])
  have "Hfun h0 K w \<le> h0 + 2 * G * norm K" by (rule H_max_bound[OF assms(5)])
  then show "Hfun h0 K (g_th G th) = h0 + 2 * G * norm K"
    and "Hfun h0 K w \<le> Hfun h0 K (g_th G th)"
    and "Hfun h0 K w - Hfun h0 K (g_th G th) \<le> 0"
    using plus by simp_all
qed

theorem case_i:
  assumes "K = of_real c * Eab_pulse z th" and "0 \<le> G" and "h0 < 0"
    and "Hfun h0 K (g_th G th) = 0" and "norm w \<le> G"
  shows "h0 + 2 * G * norm K = 0"
    and "Hfun h0 K w \<le> 0"
proof -
  have ge: "0 \<le> Hfun h0 K (g_th G th)" using assms(4) by simp
  have plus: "Hfun h0 K (g_th G th) = h0 + 2 * G * norm K"
    by (rule case_ii_plus[OF assms(1-3) ge])
  show "h0 + 2 * G * norm K = 0" using plus assms(4) by simp
  show "Hfun h0 K w \<le> 0" using case_ii(2)[OF assms(1-3) ge assms(5)] assms(4) by simp
qed

section \<open>Case (iii): the average over the phase (C3)\<close>

lemma Im_cnj_cis:
  "Im (cnj (of_real G * cis th) * K) = G * (Im K * cos th - Re K * sin th)"
  by (simp add: complex_cnj_mult cis_cnj cis.sel algebra_simps)

theorem H_average:
  "((\<lambda>th. Hfun h0 K (g_th G th)) has_integral 2 * pi * h0) {0..2 * pi}"
proof -
  let ?F = "\<lambda>th. h0 * th + 2 * G * (Im K * sin th + Re K * cos th)"
  have d: "\<And>x. (?F has_vector_derivative Hfun h0 K (g_th G x)) (at x within {0..2 * pi})"
  proof -
    fix x :: real
    have "(?F has_real_derivative (h0 + 2 * G * (Im K * cos x - Re K * sin x))) (at x)"
      by (rule derivative_eq_intros refl | simp)+
    then have "(?F has_vector_derivative (h0 + 2 * G * (Im K * cos x - Re K * sin x))) (at x)"
      by (simp add: has_real_derivative_iff_has_vector_derivative)
    moreover have "Hfun h0 K (g_th G x) = h0 + 2 * G * (Im K * cos x - Re K * sin x)"
      by (simp add: Hfun_def g_th_def Im_cnj_cis algebra_simps)
    ultimately show "(?F has_vector_derivative Hfun h0 K (g_th G x)) (at x within {0..2 * pi})"
      by (simp add: has_vector_derivative_at_within)
  qed
  have "((\<lambda>th. Hfun h0 K (g_th G th)) has_integral ?F (2 * pi) - ?F 0) {0..2 * pi}"
    by (rule fundamental_theorem_of_calculus) (use d in auto)
  moreover have "?F (2 * pi) - ?F 0 = 2 * pi * h0" by simp
  ultimately show ?thesis by (simp add: mult.commute)
qed

theorem case_iii:
  assumes "h0 < 0"
  shows "\<exists>th\<in>{0..2 * pi}. Hfun h0 K (g_th G th) < 0"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "\<forall>th\<in>{0..2 * pi}. 0 \<le> Hfun h0 K (g_th G th)" by (simp add: not_less)
  then have "0 \<le> 2 * pi * h0" using has_integral_nonneg[OF H_average] by blast
  moreover have "2 * pi * h0 < 0" using assms by (simp add: mult_pos_neg)
  ultimately show False by simp
qed

section \<open>Case (iv): the projector on b (C4)\<close>

theorem case_iv:
  assumes "norm w \<le> G"
  shows "Hfun (h0f gq gm Gam 0 1 0 a b rho) (Kf 0 1 0 a b rho) w \<le> - gm * b + 2 * G * norm rho"
proof -
  have "h0f gq gm Gam 0 1 0 a b rho = - gm * b" by (simp add: h0f_def)
  moreover have "Kf 0 1 0 a b rho = rho" by (simp add: Kf_def)
  ultimately show ?thesis using H_max_bound[OF assms, of "- gm * b" rho] by simp
qed

corollary case_iv_nonpos:
  assumes "norm w \<le> G" and "- gm * b + 2 * G * norm rho \<le> 0"
  shows "Hfun (h0f gq gm Gam 0 1 0 a b rho) (Kf 0 1 0 a b rho) w \<le> 0"
  using case_iv[OF assms(1), of gq gm Gam a b rho] assms(2) by linarith

section \<open>The shift epsilon (C5)\<close>

theorem epsilon_limit:
  fixes v :: "real \<Rightarrow> real" and y :: "real \<Rightarrow> real \<Rightarrow> real"
  assumes lohi: "\<And>e t. 0 < e \<Longrightarrow> t \<in> {0..T} \<Longrightarrow> exp (- e * T) * v t \<le> y e t \<and> y e t \<le> v t"
    and mono: "\<And>e s t. 0 < e \<Longrightarrow> s \<in> {0..T} \<Longrightarrow> t \<in> {0..T} \<Longrightarrow> s \<le> t \<Longrightarrow> y e t \<le> y e s"
    and s: "s \<in> {0..T}" and t: "t \<in> {0..T}" and st: "s \<le> t"
  shows "v t \<le> v s"
proof -
  have ev: "eventually (\<lambda>e. exp (- e * T) * v t \<le> v s) (at_right (0::real))"
    using eventually_at_right_less[of "0::real"]
  proof eventually_elim
    case (elim e)
    have "exp (- e * T) * v t \<le> y e t" using lohi[OF elim t] by simp
    also have "\<dots> \<le> y e s" using mono[OF elim s t st] .
    also have "\<dots> \<le> v s" using lohi[OF elim s] by simp
    finally show ?case .
  qed
  have "((\<lambda>e. exp (- e * T) * v t) \<longlongrightarrow> exp (- 0 * T) * v t) (at_right (0::real))"
    by (intro tendsto_intros)
  then have "((\<lambda>e. exp (- e * T) * v t) \<longlongrightarrow> v t) (at_right (0::real))" by simp
  from tendsto_upperbound[OF this ev] show ?thesis by simp
qed

section \<open>The conclusion (C6)\<close>

theorem lyapunov_conclusion:
  fixes V :: "real \<Rightarrow> 'a \<Rightarrow> real" and R :: "real \<Rightarrow> 'a" and pb M :: real
  assumes mono: "\<And>s t. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> t \<le> T \<Longrightarrow> V (T - t) (R t) \<le> V (T - s) (R s)"
    and "0 \<le> T" and fin: "pb = V 0 (R T)" and start: "V T (R 0) = M"
  shows "pb \<le> M"
proof -
  have "V (T - T) (R T) \<le> V (T - 0) (R 0)" using mono[of 0 T] assms(2) by simp
  then show ?thesis using fin start by simp
qed

end
