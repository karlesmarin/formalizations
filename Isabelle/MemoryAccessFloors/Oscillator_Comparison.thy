(*  Title:      Oscillator_Comparison.thy
    Author:     Carles Marin
    Copyright:  Carles Marin
    License:    BSD-3-Clause

    Memory-floors note, Proposition "strong" (unequal rates).  Over-damped oscillator
    z'' + 2 phi z' + 4 G^2 z = 0, z(0) = 1, z'(0) = 0, in the closed form zz G phi T, for 2 G < phi.
    (A) it solves the equation; (B) comparison in the damping: m <= phi implies zz m <= zz phi, and
    exp(-m T) (1 + m T) <= zz m; (C) the integral form of the coherence bound; (D) the algebraic
    conclusion p + 2 c <= 1/2 - (1/2) exp(-m T) (1 + m T - 4 G T) < 1/2 for m >= 4 G.
*)
theory Oscillator_Comparison
  imports "HOL-Analysis.Analysis"
begin

section \<open>A. The closed form and its equation\<close>

definition kap :: "real \<Rightarrow> real \<Rightarrow> real" where
  "kap G phi = sqrt (phi\<^sup>2 - 4 * G\<^sup>2)"

definition zz :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "zz G phi T = exp (- phi * T) * (cosh (kap G phi * T) + phi / kap G phi * sinh (kap G phi * T))"

lemma kap_facts:
  fixes G phi :: real
  assumes "0 < G" and "2 * G < phi"
  shows "0 < phi\<^sup>2 - 4 * G\<^sup>2" and "0 < kap G phi" and "(kap G phi)\<^sup>2 = phi\<^sup>2 - 4 * G\<^sup>2" and "0 < phi"
proof -
  show "0 < phi" using assms by simp
  have "(2 * G)\<^sup>2 < phi\<^sup>2" using assms by (intro power_strict_mono) simp_all
  then show p: "0 < phi\<^sup>2 - 4 * G\<^sup>2" by (simp add: power_mult_distrib)
  show "0 < kap G phi" unfolding kap_def using p by simp
  show "(kap G phi)\<^sup>2 = phi\<^sup>2 - 4 * G\<^sup>2" unfolding kap_def using p by (simp add: real_sqrt_pow2)
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

lemma sinh_le_x_cosh:
  fixes y :: real
  assumes "0 \<le> y"
  shows "sinh y \<le> y * cosh y"
proof -
  define f where "f = (\<lambda>t::real. t * cosh t - sinh t)"
  have "f 0 \<le> f y"
  proof (rule DERIV_nonneg_imp_nondecreasing[OF assms])
    fix t :: real
    assume "0 \<le> t" "t \<le> y"
    have "(f has_real_derivative t * sinh t) (at t)"
      unfolding f_def by (auto intro!: derivative_eq_intros)
    moreover have "0 \<le> t * sinh t" using \<open>0 \<le> t\<close> by (simp add: sinh_real_nonneg_iff)
    ultimately show "\<exists>d. DERIV f t :> d \<and> 0 \<le> d" by blast
  qed
  then show ?thesis unfolding f_def by simp
qed

theorem zz_zero:
  fixes G phi :: real
  shows "zz G phi 0 = 1"
  unfolding zz_def by simp

theorem zz_deriv:
  fixes G phi T :: real
  assumes "0 < G" and "2 * G < phi"
  shows "((zz G phi) has_real_derivative
          (- 4 * G\<^sup>2 * exp (- phi * T) * sinh (kap G phi * T) / kap G phi)) (at T)"
proof -
  define k where "k = kap G phi"
  have kp: "0 < k" unfolding k_def by (rule kap_facts(2)[OF assms])
  have k2: "k\<^sup>2 = phi\<^sup>2 - 4 * G\<^sup>2" unfolding k_def by (rule kap_facts(3)[OF assms])
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
  show ?thesis unfolding zz_def k_def[symmetric] using d eq by simp
qed

text \<open>The velocity z' = -4 G^2 exp(-phi T) sinh(kappa T) / kappa vanishes at 0, and its derivative
  gives the equation z'' + 2 phi z' + 4 G^2 z = 0.\<close>

definition zz1 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "zz1 G phi T = - 4 * G\<^sup>2 * exp (- phi * T) * sinh (kap G phi * T) / kap G phi"

theorem zz1_zero: "zz1 G phi 0 = 0"
  unfolding zz1_def by simp

theorem zz1_deriv:
  fixes G phi T :: real
  assumes "0 < G" and "2 * G < phi"
  shows "((zz1 G phi) has_real_derivative
          (- 4 * G\<^sup>2 * exp (- phi * T) * (cosh (kap G phi * T) - phi / kap G phi * sinh (kap G phi * T)))) (at T)"
proof -
  define k where "k = kap G phi"
  have kp: "0 < k" unfolding k_def by (rule kap_facts(2)[OF assms])
  have d: "((\<lambda>T. - 4 * G\<^sup>2 * exp (- phi * T) * sinh (k * T) / k) has_real_derivative
            (- 4 * G\<^sup>2 * exp (- phi * T) * (cosh (k * T) - phi / k * sinh (k * T)))) (at T)"
    using kp
    apply (auto intro!: derivative_eq_intros)
    apply (simp_all add: field_simps algebra_simps)
    done
  show ?thesis unfolding zz1_def k_def[symmetric] using d by simp
qed

theorem zz_ode:
  fixes G phi T :: real
  assumes "0 < G" and "2 * G < phi"
  shows "- 4 * G\<^sup>2 * exp (- phi * T) * (cosh (kap G phi * T) - phi / kap G phi * sinh (kap G phi * T))
         + 2 * phi * zz1 G phi T + 4 * G\<^sup>2 * zz G phi T = 0"
proof -
  have kp: "0 < kap G phi" by (rule kap_facts(2)[OF assms])
  show ?thesis unfolding zz_def zz1_def using kp by (simp add: field_simps)
qed

section \<open>B. Comparison in the damping rate\<close>

theorem zz_lower:
  fixes G phi T :: real
  assumes "0 < G" and "2 * G < phi" and "0 \<le> T"
  shows "exp (- phi * T) * (1 + phi * T) \<le> zz G phi T"
proof -
  define k where "k = kap G phi"
  have kp: "0 < k" unfolding k_def by (rule kap_facts(2)[OF assms(1,2)])
  have pp: "0 < phi" by (rule kap_facts(4)[OF assms(1,2)])
  have ch: "1 \<le> cosh (k * T)" by (rule cosh_real_ge_1)
  have sh: "k * T \<le> sinh (k * T)" by (rule sinh_ge_self) (use kp assms(3) in simp)
  have "phi / k * (k * T) \<le> phi / k * sinh (k * T)"
    using sh pp kp by (intro mult_left_mono) simp_all
  moreover have "phi / k * (k * T) = phi * T" using kp by simp
  ultimately have "1 + phi * T \<le> cosh (k * T) + phi / k * sinh (k * T)" using ch by argo
  then show ?thesis unfolding zz_def k_def[symmetric] by (intro mult_left_mono) simp_all
qed

lemma kap_deriv:
  fixes G phi :: real
  assumes "0 < G" and "2 * G < phi"
  shows "((kap G) has_real_derivative phi / kap G phi) (at phi)"
proof -
  have kp: "0 < kap G phi" by (rule kap_facts(2)[OF assms])
  have pos: "0 < phi\<^sup>2 - 4 * G\<^sup>2" by (rule kap_facts(1)[OF assms])
  have d2: "((\<lambda>p::real. p\<^sup>2 - 4 * G\<^sup>2) has_real_derivative 2 * phi) (at phi)"
    by (auto intro!: derivative_eq_intros)
  have "((\<lambda>p::real. sqrt (p\<^sup>2 - 4 * G\<^sup>2)) has_real_derivative inverse (sqrt (phi\<^sup>2 - 4 * G\<^sup>2)) / 2 * (2 * phi)) (at phi)"
    using DERIV_chain2[where f = sqrt and g = "\<lambda>p::real. p\<^sup>2 - 4 * G\<^sup>2", OF DERIV_real_sqrt[OF pos] d2] by simp
  moreover have "inverse (sqrt (phi\<^sup>2 - 4 * G\<^sup>2)) / 2 * (2 * phi) = phi / kap G phi"
    unfolding kap_def by (simp add: field_simps)
  ultimately have d: "((\<lambda>p::real. sqrt (p\<^sup>2 - 4 * G\<^sup>2)) has_real_derivative phi / kap G phi) (at phi)" by simp
  have fe: "kap G = (\<lambda>p::real. sqrt (p\<^sup>2 - 4 * G\<^sup>2))" by (rule ext) (simp add: kap_def)
  show ?thesis by (subst fe) (rule d)
qed

text \<open>The derivative of zz in phi is exp(-phi T) (4 G^2 / kappa^3) (kappa T cosh(kappa T) - sinh(kappa T)),
  which is nonnegative.\<close>

lemma zz_deriv_phi:
  fixes G phi T :: real
  assumes "0 < G" and "2 * G < phi" and "0 \<le> T"
  shows "\<exists>d. DERIV (\<lambda>p. zz G p T) phi :> d \<and> 0 \<le> d"
proof -
  define k where "k = kap G phi"
  have kp: "0 < k" unfolding k_def by (rule kap_facts(2)[OF assms(1,2)])
  have k2: "k\<^sup>2 = phi\<^sup>2 - 4 * G\<^sup>2" unfolding k_def by (rule kap_facts(3)[OF assms(1,2)])
  have kd: "(kap G has_real_derivative phi / kap G phi) (at phi)" by (rule kap_deriv[OF assms(1,2)])
  define x where "x = k * T"
  define D where "D = exp (- phi * T) * (4 * G\<^sup>2 / k ^ 3) * (x * cosh x - sinh x)"
  define D1 where "D1 = exp (- phi * T) * (T * cosh (kap G phi * T) * (phi\<^sup>2 / (kap G phi)\<^sup>2 - 1)
      + sinh (kap G phi * T) * ((kap G phi - phi\<^sup>2 / kap G phi) / (kap G phi)\<^sup>2))"
  have kp0: "0 < kap G phi" by (rule kap_facts(2)[OF assms(1,2)])
  have raw: "((\<lambda>p. zz G p T) has_real_derivative D1) (at phi)"
    unfolding zz_def D1_def
    using kp0 kd
    apply (auto intro!: derivative_eq_intros kd)
    apply (simp_all add: field_simps power2_eq_square)
    done
  have eq: "D1 = D"
  proof -
    have e1: "phi\<^sup>2 = k\<^sup>2 + 4 * G\<^sup>2" using k2 by simp
    have "D1 = exp (- phi * T) * (T * cosh x * (phi\<^sup>2 / k\<^sup>2 - 1) + sinh x * ((k - phi\<^sup>2 / k) / k\<^sup>2))"
      unfolding D1_def x_def k_def[symmetric] by simp
    also have "\<dots> = exp (- phi * T) * (T * cosh x * (4 * G\<^sup>2 / k\<^sup>2) - sinh x * (4 * G\<^sup>2 / k ^ 3))"
    proof -
      have a1: "phi\<^sup>2 / k\<^sup>2 - 1 = 4 * G\<^sup>2 / k\<^sup>2" using kp e1 by (simp add: field_simps)
      have a2: "(k - phi\<^sup>2 / k) / k\<^sup>2 = - (4 * G\<^sup>2 / k ^ 3)" using kp e1 by (simp add: field_simps power2_eq_square power3_eq_cube)
      show ?thesis unfolding a1 a2 by (simp add: field_simps)
    qed
    also have "\<dots> = D"
      unfolding D_def x_def using kp by (simp add: field_simps power2_eq_square power3_eq_cube)
    finally show ?thesis .
  qed
  have x0: "0 \<le> x" unfolding x_def using kp assms(3) by simp
  have "sinh x \<le> x * cosh x" by (rule sinh_le_x_cosh[OF x0])
  then have "0 \<le> x * cosh x - sinh x" by simp
  then have "0 \<le> D" unfolding D_def using kp assms(1) by (intro mult_nonneg_nonneg) simp_all
  then show ?thesis using raw eq by auto
qed

theorem zz_mono_phi:
  fixes G phi1 phi2 T :: real
  assumes "0 < G" and "2 * G < phi1" and "phi1 \<le> phi2" and "0 \<le> T"
  shows "zz G phi1 T \<le> zz G phi2 T"
proof (rule DERIV_nonneg_imp_nondecreasing[OF assms(3), of "\<lambda>p. zz G p T"])
  fix p :: real
  assume "phi1 \<le> p" "p \<le> phi2"
  then show "\<exists>d. DERIV (\<lambda>p. zz G p T) p :> d \<and> 0 \<le> d"
    using zz_deriv_phi[of G p T] assms by simp
qed

theorem strong_comparison:
  fixes G m phibar T :: real
  assumes "0 < G" and "2 * G < m" and "m \<le> phibar" and "0 \<le> T"
  shows "exp (- m * T) * (1 + m * T) \<le> zz G m T" and "zz G m T \<le> zz G phibar T"
  using zz_lower[OF assms(1,2,4)] zz_mono_phi[OF assms(1,2,3,4)] by simp_all

section \<open>C. The coherence bound in integral form\<close>

theorem coherence_integral_bound:
  fixes G m T c :: real and v :: "real \<Rightarrow> real"
  assumes "0 \<le> G" and "0 \<le> T" and "continuous_on {0..T} v"
    and "\<forall>s\<in>{0..T}. \<bar>v s\<bar> \<le> exp (- m * s)"
    and "c \<le> integral {0..T} (\<lambda>s. G * exp (- m * (T - s)) * \<bar>v s\<bar>)"
  shows "c \<le> G * T * exp (- m * T)"
proof -
  have ci: "continuous_on {0..T} (\<lambda>s. G * exp (- m * (T - s)) * \<bar>v s\<bar>)"
    using assms(3) by (intro continuous_intros)
  have i1: "(\<lambda>s. G * exp (- m * (T - s)) * \<bar>v s\<bar>) integrable_on {0..T}"
    by (rule integrable_continuous_real[OF ci])
  have i2: "(\<lambda>s::real. G * exp (- m * T)) integrable_on {0..T}"
    by (rule integrable_continuous_real[OF continuous_on_const])
  have pt: "\<forall>s\<in>{0..T}. G * exp (- m * (T - s)) * \<bar>v s\<bar> \<le> G * exp (- m * T)"
  proof
    fix s assume s: "s \<in> {0..T}"
    have "G * exp (- m * (T - s)) * \<bar>v s\<bar> \<le> G * exp (- m * (T - s)) * exp (- m * s)"
      using assms(4) s assms(1) by (intro mult_left_mono) simp_all
    also have "\<dots> = G * exp (- m * T)"
      by (simp add: exp_add[symmetric] mult.assoc) (simp add: algebra_simps)
    finally show "G * exp (- m * (T - s)) * \<bar>v s\<bar> \<le> G * exp (- m * T)" .
  qed
  have "integral {0..T} (\<lambda>s. G * exp (- m * (T - s)) * \<bar>v s\<bar>) \<le> integral {0..T} (\<lambda>s::real. G * exp (- m * T))"
    by (rule integral_le[OF i1 i2]) (use pt in blast)
  also have "\<dots> = T * (G * exp (- m * T))" using assms(2) by simp
  finally show ?thesis using assms(5) by (simp add: mult.commute mult.left_commute)
qed

section \<open>D. The algebraic conclusion\<close>

theorem strong_conclusion:
  fixes G m T p c Z :: real
  assumes "0 < G" and "4 * G \<le> m" and "0 \<le> T"
    and "p \<le> (1 - Z) / 2" and "exp (- m * T) * (1 + m * T) \<le> Z"
    and "c \<le> G * T * exp (- m * T)"
  shows "p + 2 * c \<le> 1 / 2 - exp (- m * T) * (1 + m * T - 4 * G * T) / 2"
    and "p + 2 * c < 1 / 2"
proof -
  show "p + 2 * c \<le> 1 / 2 - exp (- m * T) * (1 + m * T - 4 * G * T) / 2"
  proof -
    define E1 where "E1 = exp (- m * T) * (1 + m * T)"
    define E2 where "E2 = G * T * exp (- m * T)"
    have e1: "exp (- m * T) * (1 + m * T - 4 * G * T) / 2 = E1 / 2 - 2 * E2"
      unfolding E1_def E2_def by algebra
    have "c \<le> E2" using assms(6) unfolding E2_def by simp
    moreover have "E1 \<le> Z" using assms(5) unfolding E1_def by simp
    ultimately show ?thesis using assms(4) unfolding e1 by argo
  qed
  have "4 * G * T \<le> m * T" using assms(2,3) by (intro mult_right_mono) simp_all
  then have "0 < 1 + m * T - 4 * G * T" by simp
  then have "0 < exp (- m * T) * (1 + m * T - 4 * G * T) / 2" by simp
  then show "p + 2 * c < 1 / 2" using \<open>p + 2 * c \<le> 1 / 2 - exp (- m * T) * (1 + m * T - 4 * G * T) / 2\<close> by linarith
qed

text \<open>The whole chain: rates with 4 G <= m <= phibar; the resonant population is
  (1 - zz phibar) / 2; the coherence is at most G T exp(-m T); so p + 2 c < 1/2.\<close>

theorem strong_unequal_chain:
  fixes G m phibar T p c :: real
  assumes "0 < G" and "4 * G \<le> m" and "m \<le> phibar" and "0 \<le> T"
    and "p \<le> (1 - zz G phibar T) / 2" and "c \<le> G * T * exp (- m * T)"
  shows "p + 2 * c < 1 / 2"
proof -
  have g2: "2 * G < m" using assms(1,2) by simp
  have lo: "exp (- m * T) * (1 + m * T) \<le> zz G m T"
    and mono: "zz G m T \<le> zz G phibar T" using strong_comparison[OF assms(1) g2 assms(3,4)] by simp_all
  have "exp (- m * T) * (1 + m * T) \<le> zz G phibar T" using lo mono by linarith
  then show ?thesis using strong_conclusion(2)[OF assms(1,2,4) assms(5) _ assms(6)] by blast
qed

end
