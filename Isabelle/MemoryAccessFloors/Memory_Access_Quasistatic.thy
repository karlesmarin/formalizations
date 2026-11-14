(*  Title:      Memory_Access_Quasistatic.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    From "Exact limits for writing a quantum memory" (C. Marín, draft, November 2026): the one-variable inequalities behind the
    quasi-static bound of the square pulse, and the strong-dephasing envelope (phi >= 4G).
*)

theory Memory_Access_Quasistatic
  imports Memory_Access_Extras
begin

section \<open>0. Elementary real-analysis facts\<close>

lemma cos_ge_one_minus_sq:
  fixes x :: real
  shows "1 - x\<^sup>2 / 2 \<le> cos x"
proof -
  have e: "cos x = 1 - 2 * (sin (x / 2))\<^sup>2"
    using cos_double_sin[of "x / 2"] by simp
  have a: "\<bar>sin (x / 2)\<bar> \<le> \<bar>x / 2\<bar>" by (rule abs_sin_x_le_abs_x)
  have h1: "\<bar>sin (x / 2)\<bar>\<^sup>2 \<le> \<bar>x / 2\<bar>\<^sup>2" by (rule power_mono[OF a abs_ge_zero])
  have h2: "(sin (x / 2))\<^sup>2 \<le> (x / 2)\<^sup>2" using h1 unfolding power2_abs .
  have h3: "(x / 2)\<^sup>2 = x\<^sup>2 / 4" by (simp add: power_divide)
  show ?thesis unfolding e using h2 h3 by argo
qed

lemma pi_sq_lt_12: "pi\<^sup>2 < (12 :: real)"
proof -
  have h: "pi \<le> (3.2 :: real)"
    by (rule order_trans[OF pi_approx(2)]) simp
  have "0 \<le> pi" by (rule pi_ge_zero)
  then have "pi * pi \<le> (3.2 :: real) * 3.2" by (intro mult_mono h) simp_all
  then show ?thesis unfolding power2_eq_square by argo
qed

section \<open>A. The one-variable inequality of Proposition 11(a)\<close>

definition qsA :: "real \<Rightarrow> real" where
  "qsA q = sin (pi / 2 * sqrt (1 + q)) / sqrt (1 + q)"

lemma qs_s_facts:
  fixes q :: real
  assumes "0 \<le> q"
  shows "1 \<le> sqrt (1 + q)" and "(sqrt (1 + q))\<^sup>2 = 1 + q"
proof -
  show "1 \<le> sqrt (1 + q)" using assms by simp
  show "(sqrt (1 + q))\<^sup>2 = 1 + q" using assms by (simp add: real_sqrt_pow2)
qed

lemma qsA_sin_aux:
  fixes s :: real
  assumes "1 \<le> s"
  shows "s * (3 - s\<^sup>2) / 2 \<le> sin (pi / 2 * s)"
proof -
  define x where "x = s - 1"
  have x0: "0 \<le> x" using assms unfolding x_def by simp
  have s1x: "s = 1 + x" unfolding x_def by simp
  have sx: "pi / 2 * s = pi / 2 + pi / 2 * x" using s1x by (simp add: algebra_simps)
  have "sin (pi / 2 * s) = cos (pi / 2 * x)" unfolding sx by (simp add: sin_add)
  moreover have "1 - (pi / 2 * x)\<^sup>2 / 2 \<le> cos (pi / 2 * x)" by (rule cos_ge_one_minus_sq)
  ultimately have c: "1 - (pi / 2 * x)\<^sup>2 / 2 \<le> sin (pi / 2 * s)" by simp
  have e1: "(pi / 2 * x)\<^sup>2 / 2 = pi\<^sup>2 * x\<^sup>2 / 8" by (simp add: power_mult_distrib power_divide)
  have e2: "s * (3 - s\<^sup>2) / 2 = 1 - 3 * x\<^sup>2 / 2 - x ^ 3 / 2"
    unfolding x_def by (simp add: field_simps algebra_simps power2_eq_square power3_eq_cube)
  have k: "0 \<le> x\<^sup>2 * (12 + 4 * x - pi\<^sup>2)"
    by (rule mult_nonneg_nonneg) (use pi_sq_lt_12 x0 in \<open>simp_all\<close>)
  have "1 - 3 * x\<^sup>2 / 2 - x ^ 3 / 2 \<le> 1 - pi\<^sup>2 * x\<^sup>2 / 8"
    using k by (simp add: power3_eq_cube power2_eq_square algebra_simps)
  then show ?thesis using c e1 e2 by argo
qed

lemma qsA_le_one:
  fixes q :: real
  assumes "0 \<le> q"
  shows "qsA q \<le> 1"
proof -
  have s1: "1 \<le> sqrt (1 + q)" by (rule qs_s_facts(1)[OF assms])
  have sp: "0 \<le> sqrt (1 + q)" using s1 by simp
  have "sin (pi / 2 * sqrt (1 + q)) \<le> sqrt (1 + q)" using sin_le_one[of "pi / 2 * sqrt (1 + q)"] s1 by argo
  then have "sin (pi / 2 * sqrt (1 + q)) / sqrt (1 + q) \<le> sqrt (1 + q) / sqrt (1 + q)"
    by (rule divide_right_mono[OF _ sp])
  moreover have "sqrt (1 + q) / sqrt (1 + q) = 1" using s1 by simp
  ultimately show ?thesis unfolding qsA_def by simp
qed

lemma qsA_ge:
  fixes q :: real
  assumes "0 \<le> q"
  shows "1 - q / 2 \<le> qsA q"
proof -
  have s1: "1 \<le> sqrt (1 + q)" by (rule qs_s_facts(1)[OF assms])
  have s2: "(sqrt (1 + q))\<^sup>2 = 1 + q" by (rule qs_s_facts(2)[OF assms])
  have sp: "0 < sqrt (1 + q)" using s1 by simp
  have key: "sqrt (1 + q) * (3 - (sqrt (1 + q))\<^sup>2) / 2 \<le> sin (pi / 2 * sqrt (1 + q))"
    by (rule qsA_sin_aux[OF s1])
  have "(1 - q / 2) * sqrt (1 + q) \<le> sin (pi / 2 * sqrt (1 + q))"
  proof -
    have h: "1 - q / 2 = (3 - (sqrt (1 + q))\<^sup>2) / 2" using s2 by argo
    have "(1 - q / 2) * sqrt (1 + q) = sqrt (1 + q) * (3 - (sqrt (1 + q))\<^sup>2) / 2"
      by (subst h) (simp add: algebra_simps)
    then show ?thesis using key by argo
  qed
  then have "(1 - q / 2) * sqrt (1 + q) / sqrt (1 + q) \<le> sin (pi / 2 * sqrt (1 + q)) / sqrt (1 + q)"
    by (rule divide_right_mono) (use sp in simp)
  moreover have "(1 - q / 2) * sqrt (1 + q) / sqrt (1 + q) = 1 - q / 2" using sp by simp
  ultimately show ?thesis unfolding qsA_def by simp
qed

lemma qsA_pop_coh:
  fixes q :: real
  assumes "0 \<le> q"
  shows "3 - (qsA q)\<^sup>2 - 2 * qsA q \<le> 2 * q"
proof -
  define t where "t = 1 - qsA q"
  have t0: "0 \<le> t" unfolding t_def using qsA_le_one[OF assms] by simp
  have t1: "t \<le> q / 2" unfolding t_def using qsA_ge[OF assms] by simp
  have "3 - (qsA q)\<^sup>2 - 2 * qsA q = 4 * t - t\<^sup>2" unfolding t_def by (simp add: algebra_simps power2_eq_square)
  also have "\<dots> \<le> 4 * t" using zero_le_power2[of t] by simp
  also have "\<dots> \<le> 2 * q" using t1 by simp
  finally show ?thesis .
qed

theorem qs_pointwise:
  fixes q x :: real
  assumes "0 \<le> q"
  shows "3 - (qsA q)\<^sup>2 - 2 * qsA q * cos x \<le> 2 * q + x\<^sup>2"
proof -
  define A where "A = qsA q"
  have A1: "A \<le> 1" unfolding A_def by (rule qsA_le_one[OF assms])
  have pc: "3 - A\<^sup>2 - 2 * A \<le> 2 * q" unfolding A_def by (rule qsA_pop_coh[OF assms])
  have c1: "cos x \<le> 1" by (rule cos_le_one)
  have c2: "1 - x\<^sup>2 / 2 \<le> cos x" by (rule cos_ge_one_minus_sq)
  have "2 * A * (1 - cos x) \<le> x\<^sup>2"
  proof (cases "A \<le> 0")
    case True
    have "0 \<le> (- A) * (1 - cos x)" using True c1 by (intro mult_nonneg_nonneg) simp_all
    moreover have "0 \<le> x\<^sup>2" by simp
    ultimately show ?thesis by argo
  next
    case False
    then have A0: "0 < A" by simp
    have "2 * A * (1 - cos x) \<le> 2 * A * (x\<^sup>2 / 2)"
      using c2 A0 by (intro mult_left_mono) simp_all
    also have "\<dots> = A * x\<^sup>2" by simp
    also have "\<dots> \<le> 1 * x\<^sup>2" by (rule mult_right_mono[OF A1 zero_le_power2])
    finally show ?thesis by simp
  qed
  then have "3 - A\<^sup>2 - 2 * A * cos x = (3 - A\<^sup>2 - 2 * A) + 2 * A * (1 - cos x)" by (simp add: algebra_simps)
  also have "\<dots> \<le> 2 * q + x\<^sup>2" using pc \<open>2 * A * (1 - cos x) \<le> x\<^sup>2\<close> by argo
  finally show ?thesis unfolding A_def .
qed

section \<open>B. Strong dephasing (Proposition 10)\<close>

definition strong_z :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "strong_z G phi T = exp (- phi * T) *
     (cosh (sqrt (phi\<^sup>2 - 4 * G\<^sup>2) * T) + phi / sqrt (phi\<^sup>2 - 4 * G\<^sup>2) * sinh (sqrt (phi\<^sup>2 - 4 * G\<^sup>2) * T))"

lemma kappa_facts:
  fixes G phi :: real
  assumes "0 < G" and "4 * G \<le> phi"
  shows "0 < phi\<^sup>2 - 4 * G\<^sup>2" and "0 < sqrt (phi\<^sup>2 - 4 * G\<^sup>2)"
    and "(sqrt (phi\<^sup>2 - 4 * G\<^sup>2))\<^sup>2 = phi\<^sup>2 - 4 * G\<^sup>2" and "0 < phi"
proof -
  show "0 < phi" using assms by simp
  have "(4 * G)\<^sup>2 \<le> phi\<^sup>2" using assms by (intro power_mono) simp_all
  then have "16 * G\<^sup>2 \<le> phi\<^sup>2" by (simp add: power_mult_distrib)
  moreover have "0 < G\<^sup>2" using assms(1) by simp
  ultimately show p: "0 < phi\<^sup>2 - 4 * G\<^sup>2" by argo
  show "0 < sqrt (phi\<^sup>2 - 4 * G\<^sup>2)" using p by simp
  show "(sqrt (phi\<^sup>2 - 4 * G\<^sup>2))\<^sup>2 = phi\<^sup>2 - 4 * G\<^sup>2" using p by (simp add: real_sqrt_pow2)
qed

lemma sinh_ge_self:
  fixes y :: real
  assumes "0 \<le> y"
  shows "y \<le> sinh y"
proof -
  define f where "f = (\<lambda>t::real. sinh t - t)"
  have "f 0 \<le> f y"
  proof (rule DERIV_nonneg_imp_nondecreasing[OF assms])
    fix t :: real
    assume "0 \<le> t" "t \<le> y"
    have "(f has_real_derivative cosh t - 1) (at t)"
      unfolding f_def by (auto intro!: derivative_eq_intros)
    moreover have "0 \<le> cosh t - 1" using cosh_real_ge_1[of t] by simp
    ultimately show "\<exists>d. DERIV f t :> d \<and> 0 \<le> d" by blast
  qed
  then show ?thesis unfolding f_def by simp
qed

theorem strong_z_ge:
  fixes G phi T :: real
  assumes "0 < G" and "4 * G \<le> phi" and "0 \<le> T"
  shows "exp (- phi * T) * (1 + phi * T) \<le> strong_z G phi T"
proof -
  define k where "k = sqrt (phi\<^sup>2 - 4 * G\<^sup>2)"
  have kp: "0 < k" unfolding k_def by (rule kappa_facts(2)[OF assms(1,2)])
  have pp: "0 < phi" by (rule kappa_facts(4)[OF assms(1,2)])
  have ch: "1 \<le> cosh (k * T)" by (rule cosh_real_ge_1)
  have sh: "k * T \<le> sinh (k * T)" by (rule sinh_ge_self) (use kp assms(3) in simp)
  have "phi / k * (k * T) \<le> phi / k * sinh (k * T)"
    using sh pp kp by (intro mult_left_mono) simp_all
  moreover have "phi / k * (k * T) = phi * T" using kp by simp
  ultimately have "1 + phi * T \<le> cosh (k * T) + phi / k * sinh (k * T)" using ch by argo
  then show ?thesis unfolding strong_z_def k_def[symmetric] by (intro mult_left_mono) simp_all
qed

theorem strong_z_deriv:
  fixes G phi T :: real
  assumes "0 < G" and "4 * G \<le> phi"
  shows "((\<lambda>T. strong_z G phi T) has_real_derivative
          (- 4 * G\<^sup>2 * exp (- phi * T) * sinh (sqrt (phi\<^sup>2 - 4 * G\<^sup>2) * T) / sqrt (phi\<^sup>2 - 4 * G\<^sup>2))) (at T)"
proof -
  define k where "k = sqrt (phi\<^sup>2 - 4 * G\<^sup>2)"
  have kp: "0 < k" unfolding k_def by (rule kappa_facts(2)[OF assms])
  have k2: "k\<^sup>2 = phi\<^sup>2 - 4 * G\<^sup>2" unfolding k_def by (rule kappa_facts(3)[OF assms])
  have d: "((\<lambda>T. exp (- phi * T) * (cosh (k * T) + phi / k * sinh (k * T))) has_real_derivative
            exp (- phi * T) * (- phi * 1) * (cosh (k * T) + phi / k * sinh (k * T))
            + exp (- phi * T) * (sinh (k * T) * (k * 1) + phi / k * (cosh (k * T) * (k * 1)))) (at T)"
    by (auto intro!: derivative_eq_intros)
  have eq: "exp (- phi * T) * (- phi * 1) * (cosh (k * T) + phi / k * sinh (k * T))
            + exp (- phi * T) * (sinh (k * T) * (k * 1) + phi / k * (cosh (k * T) * (k * 1)))
            = - 4 * G\<^sup>2 * exp (- phi * T) * sinh (k * T) / k"
  proof -
    have "exp (- phi * T) * (- phi * 1) * (cosh (k * T) + phi / k * sinh (k * T))
            + exp (- phi * T) * (sinh (k * T) * (k * 1) + phi / k * (cosh (k * T) * (k * 1)))
          = exp (- phi * T) * sinh (k * T) * (k - phi\<^sup>2 / k)" using kp by (simp add: field_simps power2_eq_square)
    also have "\<dots> = exp (- phi * T) * sinh (k * T) * ((k\<^sup>2 - phi\<^sup>2) / k)" using kp by (simp add: field_simps power2_eq_square)
    also have "\<dots> = - 4 * G\<^sup>2 * exp (- phi * T) * sinh (k * T) / k" unfolding k2 by (simp add: field_simps)
    finally show ?thesis .
  qed
  show ?thesis unfolding strong_z_def k_def[symmetric] using d eq by simp
qed

theorem strong_z_antimono:
  fixes G phi T1 T2 :: real
  assumes "0 < G" and "4 * G \<le> phi" and "0 \<le> T1" and "T1 \<le> T2"
  shows "strong_z G phi T2 \<le> strong_z G phi T1"
proof (rule DERIV_nonpos_imp_nonincreasing[OF assms(4)])
  fix t :: real
  assume t: "T1 \<le> t" "t \<le> T2"
  have kp: "0 < sqrt (phi\<^sup>2 - 4 * G\<^sup>2)" by (rule kappa_facts(2)[OF assms(1,2)])
  have t0: "0 \<le> t" using t assms(3) by simp
  have "0 \<le> sinh (sqrt (phi\<^sup>2 - 4 * G\<^sup>2) * t)" using kp t0 by (simp add: sinh_real_nonneg_iff)
  then have "- 4 * G\<^sup>2 * exp (- phi * t) * sinh (sqrt (phi\<^sup>2 - 4 * G\<^sup>2) * t) / sqrt (phi\<^sup>2 - 4 * G\<^sup>2) \<le> 0"
    using kp assms(1) by (simp add: mult_nonneg_nonneg divide_nonpos_pos mult_nonneg_nonpos)
  then show "\<exists>d. DERIV (strong_z G phi) t :> d \<and> d \<le> 0"
    using strong_z_deriv[OF assms(1,2), of t] by blast
qed

theorem strong_gap:
  fixes G phi T s :: real
  assumes "0 < G" and "4 * G \<le> phi" and "0 < T" and "0 \<le> s" and "s \<le> T"
  shows "(1 - strong_z G phi T) / 2 + 2 * (exp (- phi * T) * \<bar>sin (G * s)\<bar>) < 1 / 2"
proof -
  have ge: "exp (- phi * T) * (1 + phi * T) \<le> strong_z G phi T"
    by (rule strong_z_ge[OF assms(1,2)]) (use assms(3) in simp)
  have e0: "0 < exp (- phi * T)" by simp
  have sn: "\<bar>sin (G * s)\<bar> \<le> G * T"
  proof -
    have "\<bar>sin (G * s)\<bar> \<le> \<bar>G * s\<bar>" by (rule abs_sin_x_le_abs_x)
    moreover have "\<bar>G * s\<bar> = G * s" using assms(1,4) by simp
    moreover have "G * s \<le> G * T" using assms(1,5) by (intro mult_left_mono) simp_all
    ultimately show ?thesis by argo
  qed
  have "4 * (exp (- phi * T) * \<bar>sin (G * s)\<bar>) \<le> 4 * (exp (- phi * T) * (G * T))"
    using sn e0 by (intro mult_left_mono mult_left_mono) simp_all
  also have "\<dots> \<le> exp (- phi * T) * (phi * T)"
  proof -
    have "4 * G * T \<le> phi * T" using assms(2,3) by (intro mult_right_mono) simp_all
    then have "exp (- phi * T) * (4 * G * T) \<le> exp (- phi * T) * (phi * T)"
      by (rule mult_left_mono) simp
    then show ?thesis by argo
  qed
  also have "\<dots> < exp (- phi * T) * (1 + phi * T)" using e0 by simp
  also have "\<dots> \<le> strong_z G phi T" by (rule ge)
  finally have fin: "4 * (exp (- phi * T) * \<bar>sin (G * s)\<bar>) < strong_z G phi T" .
  define E where "E = exp (- phi * T)"
  define S where "S = \<bar>sin (G * s)\<bar>"
  define Z where "Z = strong_z G phi T"
  have fin': "4 * (E * S) < Z" using fin unfolding E_def S_def Z_def .
  show ?thesis unfolding E_def[symmetric] S_def[symmetric] Z_def[symmetric] using fin' by argo
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

theorem strong_limit:
  fixes G phi :: real
  assumes "0 < G" and "4 * G \<le> phi"
  shows "((\<lambda>T. (1 - strong_z G phi T) / 2) \<longlongrightarrow> 1 / 2) at_top"
proof -
  define k where "k = sqrt (phi\<^sup>2 - 4 * G\<^sup>2)"
  have kp: "0 < k" unfolding k_def by (rule kappa_facts(2)[OF assms])
  have k2: "k\<^sup>2 = phi\<^sup>2 - 4 * G\<^sup>2" unfolding k_def by (rule kappa_facts(3)[OF assms])
  have pp: "0 < phi" by (rule kappa_facts(4)[OF assms])
  have kphi: "k < phi"
  proof (rule power2_less_imp_less)
    show "k\<^sup>2 < phi\<^sup>2" using k2 assms(1) by simp
    show "0 \<le> phi" using pp by simp
  qed
  define a where "a = (1 + phi / k) / 2"
  define b where "b = (1 - phi / k) / 2"
  have id: "\<And>T. strong_z G phi T = a * exp (- ((phi - k) * T)) + b * exp (- ((phi + k) * T))"
  proof -
    fix T :: real
    have e1: "exp (- phi * T) * exp (k * T) = exp (- ((phi - k) * T))"
      by (simp add: exp_add[symmetric] algebra_simps)
    have e2: "exp (- phi * T) * exp (- (k * T)) = exp (- ((phi + k) * T))"
      by (simp add: exp_add[symmetric] algebra_simps)
    have "strong_z G phi T
          = a * (exp (- phi * T) * exp (k * T)) + b * (exp (- phi * T) * exp (- (k * T)))"
      unfolding strong_z_def k_def[symmetric] a_def b_def
      using kp by (simp add: cosh_def sinh_def real_scaleR_def field_simps)
    then show "strong_z G phi T = a * exp (- ((phi - k) * T)) + b * exp (- ((phi + k) * T))"
      unfolding e1 e2 .
  qed
  have t1: "((\<lambda>T. exp (- ((phi - k) * T))) \<longlongrightarrow> 0) at_top"
    by (rule exp_neg_linear_tendsto) (use kphi in simp)
  have t2: "((\<lambda>T. exp (- ((phi + k) * T))) \<longlongrightarrow> 0) at_top"
    by (rule exp_neg_linear_tendsto) (use kp pp in simp)
  have "((\<lambda>T. a * exp (- ((phi - k) * T)) + b * exp (- ((phi + k) * T))) \<longlongrightarrow> a * 0 + b * 0) at_top"
    by (intro tendsto_intros t1 t2)
  then have z0: "((\<lambda>T. strong_z G phi T) \<longlongrightarrow> 0) at_top" unfolding id by simp
  have "((\<lambda>T. (1 - strong_z G phi T) / 2) \<longlongrightarrow> (1 - 0) / 2) at_top"
    by (intro tendsto_intros z0) simp
  then show ?thesis by simp
qed

end
