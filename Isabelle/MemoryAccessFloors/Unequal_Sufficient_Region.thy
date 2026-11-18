(*  Title:      Unequal_Sufficient_Region.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    The elementary inequalities behind Corollary cor:unequal of paper A (memory floors): a sufficient region
    below |phi_q - phi_m| = 2 sqrt(5) G.  Units G = 1; delta > 1, P = phi_q phi_m, Omega = sqrt (delta^2 - 1),
    a = sqrt (delta^2 + P), kappa = sqrt (delta^2 + P - 4).  Only these inequalities are formalised; the storage
    function and the cones of Proposition prop:unequal are a written argument.
*)

theory Unequal_Sufficient_Region
  imports "HOL-Analysis.Analysis"
begin

section \<open>The three conditions of P_suf\<close>

theorem psuf_kappa:
  fixes L P delta Omega kappa :: real
  assumes d1: "1 < delta" and Om: "Omega = sqrt (delta^2 - 1)" and ka: "kappa = sqrt (delta^2 + P - 4)"
    and L0: "0 < L" and h: "3 + 2 * Omega * L + L^2 \<le> P"
  shows "L \<le> kappa - Omega"
proof -
  have dd: "1 < delta^2" using less_1_mult[OF d1 d1] by (simp add: power2_eq_square)
  have o2: "Omega^2 = delta^2 - 1" unfolding Om by (rule real_sqrt_pow2) (use dd in linarith)
  have o0: "0 \<le> Omega" unfolding Om by (rule real_sqrt_ge_zero) (use dd in linarith)
  have "(Omega + L)^2 \<le> delta^2 + P - 4"
    using o2 h L0 o0 by (simp add: power2_eq_square algebra_simps)
  then have "Omega + L \<le> kappa" using ka by (simp add: real_le_rsqrt)
  then show ?thesis by linarith
qed

theorem psuf_a:
  fixes L P delta Omega a :: real
  assumes d1: "1 < delta" and Om: "Omega = sqrt (delta^2 - 1)" and a_def: "a = sqrt (delta^2 + P)"
    and L0: "0 < L" and h: "(delta^2 / Omega + L)^2 - delta^2 \<le> P"
  shows "L \<le> a - delta^2 / Omega"
proof -
  have "(delta^2 / Omega + L)^2 \<le> delta^2 + P" using h by linarith
  then have "delta^2 / Omega + L \<le> a" using a_def by (simp add: real_le_rsqrt)
  then show ?thesis by linarith
qed

theorem psuf_initial:
  fixes P delta a :: real
  assumes d1: "1 < delta" and d4: "delta < 4" and a_def: "a = sqrt (delta^2 + P)" and h: "16 - 8 * delta \<le> P"
  shows "4 \<le> a + delta"
proof -
  have "(4 - delta)^2 \<le> delta^2 + P" using h by (simp add: power2_eq_square algebra_simps)
  then have "4 - delta \<le> a" using a_def by (simp add: real_le_rsqrt)
  then show ?thesis by linarith
qed

section \<open>The exponential step\<close>

theorem exp_step:
  fixes Omega s tau L m :: real
  assumes O0: "0 < Omega" and O2: "Omega < 2" and s0: "0 < s" and Ldef: "L = ln (2 / Omega) / s"
    and Lm: "L \<le> m" and st: "s \<le> tau"
  shows "(2 / Omega) * exp (- m * tau) \<le> 1"
proof -
  have r1: "1 < 2 / Omega" using O0 O2 by (simp add: less_divide_eq)
  have l0: "0 \<le> ln (2 / Omega)" using r1 by simp
  have L0: "0 \<le> L" using Ldef l0 s0 by simp
  have t0: "0 < tau" using s0 st by linarith
  have "L * s \<le> m * tau" using Lm st L0 s0 t0 by (intro mult_mono) auto
  moreover have "L * s = ln (2 / Omega)" using Ldef s0 by simp
  ultimately have "ln (2 / Omega) \<le> m * tau" by simp
  then have "exp (- m * tau) \<le> exp (- ln (2 / Omega))" by simp
  also have "\<dots> = Omega / 2"
  proof -
    have "0 < 2 / Omega" by (rule less_trans[OF zero_less_one r1])
    then show ?thesis using O0 by (simp add: exp_minus exp_ln inverse_eq_divide)
  qed
  finally have "exp (- m * tau) \<le> Omega / 2" .
  then have "(2 / Omega) * exp (- m * tau) \<le> (2 / Omega) * (Omega / 2)"
    using O0 by (intro mult_left_mono) auto
  also have "\<dots> = 1" using O0 by simp
  finally show ?thesis .
qed

section \<open>Monotonicity of sinh x / x and cosh\<close>

theorem sinh_ratio_mono:
  fixes u v :: real
  assumes "0 < u" "u \<le> v"
  shows "sinh u / u \<le> sinh v / v"
proof -
  have v0: "0 < v" using assms by linarith
  have ser: "(\<lambda>n. if even n then 0 else x^n / fact n) sums sinh x" for x :: real
  proof -
    have "(\<lambda>n. if even n then 0 else x^n /\<^sub>R fact n) = (\<lambda>n. if even n then 0 else x^n / fact n)"
      by (rule ext) (simp add: real_scaleR_def divide_inverse mult.commute)
    then show ?thesis using sinh_converges[of x] by simp
  qed
  have su: "(\<lambda>n. (if even n then 0 else u^n / fact n) / u) sums (sinh u / u)"
    by (rule sums_divide[OF ser])
  have sv: "(\<lambda>n. (if even n then 0 else v^n / fact n) / v) sums (sinh v / v)"
    by (rule sums_divide[OF ser])
  have tm: "(if even n then 0 else u^n / fact n) / u \<le> (if even n then 0 else v^n / fact n) / v" for n
  proof (cases "even n")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain m where n: "n = Suc m" by (cases n) auto
    have "u^m \<le> v^m" using assms by (intro power_mono) auto
    then have ineq: "u^m / fact (Suc m) \<le> v^m / fact (Suc m)" by (simp add: divide_right_mono)
    have gen: "x^(Suc m) / f / x = x^m / f" if "0 < x" for x f :: real
      using that by (cases "f = 0") (simp_all add: power_Suc field_simps)
    have e1: "u^n / fact n / u = u^m / fact (Suc m)" using n gen[OF assms(1), of "fact (Suc m)"] by simp
    have e2: "v^n / fact n / v = v^m / fact (Suc m)" using n gen[OF v0, of "fact (Suc m)"] by simp
    have l: "(if even n then 0 else u^n / fact n) / u = u^n / fact n / u" using False by simp
    have r: "(if even n then 0 else v^n / fact n) / v = v^n / fact n / v" using False by simp
    show ?thesis by (subst l, subst r) (use e1 e2 ineq in linarith)
  qed
  show ?thesis by (rule sums_le[OF tm su sv])
qed

theorem cosh_mono:
  fixes u v :: real
  assumes "0 < u" "u \<le> v"
  shows "cosh u \<le> cosh v"
  using assms by (simp add: cosh_real_nonneg_le_iff)

section \<open>The resonant ratio\<close>

theorem resonant_ratio:
  fixes Omega kappa a tau :: real
  assumes Ok: "0 < Omega" "Omega \<le> kappa" and a0: "0 < a" and t0: "0 < tau"
  shows "4 * (sinh (Omega * tau) / Omega) / (cosh (kappa * tau) + (a / kappa) * sinh (kappa * tau))
           \<le> 4 / (a + Omega * cosh (Omega * tau) / sinh (Omega * tau))"
proof -
  define S C N where "S = sinh (Omega * tau)" and "C = cosh (Omega * tau)" and "N = S / Omega"
  have k0: "0 < kappa" using Ok by linarith
  have ot: "0 < Omega * tau" using Ok(1) t0 by simp
  have S0: "0 < S" unfolding S_def using ot by simp
  have C0: "0 < C" unfolding C_def by simp
  have N0: "0 < N" unfolding N_def using S0 Ok(1) by simp
  have h1: "C \<le> cosh (kappa * tau)" unfolding C_def
    using cosh_mono[OF ot] Ok(2) t0 by (simp add: mult_right_mono)
  have h2: "N \<le> sinh (kappa * tau) / kappa"
  proof -
    have "sinh (Omega * tau) / (Omega * tau) \<le> sinh (kappa * tau) / (kappa * tau)"
      by (rule sinh_ratio_mono[OF ot]) (use Ok(2) t0 in \<open>simp add: mult_right_mono\<close>)
    then show ?thesis using Ok(1) k0 t0 a0 unfolding N_def S_def
      by (simp add: field_simps)
  qed
  have h2': "a * N \<le> (a / kappa) * sinh (kappa * tau)" using mult_left_mono[OF h2 less_imp_le[OF a0]] by (simp add: field_simps)
  have D: "C + a * N \<le> cosh (kappa * tau) + (a / kappa) * sinh (kappa * tau)" using h1 h2' by linarith
  have Dpos: "0 < C + a * N" by (rule add_pos_pos[OF C0 mult_pos_pos[OF a0 N0]])
  have "4 * N / (cosh (kappa * tau) + (a / kappa) * sinh (kappa * tau)) \<le> 4 * N / (C + a * N)"
    using D Dpos N0 by (intro divide_left_mono) auto
  also have "\<dots> = 4 / (a + Omega * C / S)"
    using Ok(1) S0 N0 unfolding N_def by (simp add: field_simps)
  finally show ?thesis unfolding N_def S_def C_def .
qed

section \<open>The cotangent step\<close>

theorem coth_step:
  fixes Omega delta tau s :: real
  assumes O0: "0 < Omega" and d0: "0 < delta" and t0: "0 < tau" and ts: "tau \<le> s"
    and th: "tanh (Omega * s) = Omega / delta"
  shows "delta \<le> Omega * cosh (Omega * tau) / sinh (Omega * tau)"
proof -
  have ot: "0 < Omega * tau" using O0 t0 by simp
  have le: "tanh (Omega * tau) \<le> tanh (Omega * s)"
    using ts O0 by (simp add: tanh_real_le_iff mult_left_mono)
  have T0: "0 < tanh (Omega * tau)" using ot by (simp add: tanh_real_pos_iff)
  have "delta * tanh (Omega * tau) \<le> Omega" using le th d0 by (simp add: field_simps)
  moreover have "tanh (Omega * tau) = sinh (Omega * tau) / cosh (Omega * tau)" by (simp add: tanh_def)
  ultimately show ?thesis using T0 ot by (simp add: field_simps)
qed

section \<open>The initial interval\<close>

theorem initial_interval:
  fixes P delta Omega a kappa tau s :: real
  assumes d1: "1 < delta" and d4: "delta < 4"
    and Om: "Omega = sqrt (delta^2 - 1)" and a_def: "a = sqrt (delta^2 + P)"
    and ka: "kappa = sqrt (delta^2 + P - 4)"
    and P3: "3 \<le> P" and P16: "16 - 8 * delta \<le> P"
    and t0: "0 < tau" and ts: "tau \<le> s" and th: "tanh (Omega * s) = Omega / delta"
  shows "4 * (sinh (Omega * tau) / Omega) / (cosh (kappa * tau) + (a / kappa) * sinh (kappa * tau)) \<le> 1"
proof -
  have dd: "1 < delta^2" using less_1_mult[OF d1 d1] by (simp add: power2_eq_square)
  have O0: "0 < Omega" unfolding Om by (rule real_sqrt_gt_0_iff[THEN iffD2]) (use dd in linarith)
  have Ok: "Omega \<le> kappa" unfolding Om ka by (rule real_sqrt_le_mono) (use P3 in linarith)
  have a0: "0 < a" unfolding a_def by (rule real_sqrt_gt_0_iff[THEN iffD2]) (use dd P3 in linarith)
  have r1: "4 * (sinh (Omega * tau) / Omega) / (cosh (kappa * tau) + (a / kappa) * sinh (kappa * tau))
              \<le> 4 / (a + Omega * cosh (Omega * tau) / sinh (Omega * tau))"
    by (rule resonant_ratio[OF O0 Ok a0 t0])
  have g: "delta \<le> Omega * cosh (Omega * tau) / sinh (Omega * tau)"
    by (rule coth_step[OF O0 _ t0 ts th]) (use d1 in linarith)
  have c: "4 \<le> a + delta" by (rule psuf_initial[OF d1 d4 a_def P16])
  have pos: "0 < a + Omega * cosh (Omega * tau) / sinh (Omega * tau)" using c g by linarith
  have "4 / (a + Omega * cosh (Omega * tau) / sinh (Omega * tau)) \<le> 1"
    using pos c g by (simp add: divide_le_eq_1_pos)
  with r1 show ?thesis by linarith
qed

end
