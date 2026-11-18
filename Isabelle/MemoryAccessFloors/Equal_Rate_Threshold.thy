(*  Title:      Equal_Rate_Threshold.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    From "Memory floors" (C. Marín, paper A, November 2026), Proposition 11, paragraph "The exact threshold
    for equal rates", and Proposition "gap" ("How far apart are the two sides?").

    Units G = 1, phi > 2 the common rate, kappa = sqrt (phi^2 - 4),
      h (phi, T) = cosh (kappa T) + (phi / kappa) sinh (kappa T),   f = h - 4 sin T.
    A. h is nondecreasing in phi (for phi > 2) and in T (for T >= 0).
    B. High side: f > 0 for every T >= 0 as soon as phi >= 2.0942.
    C. Low side: f (phi, 0.8268) < 0 for every 2 < phi <= 2.0941.
    Together they enclose the threshold phi* = 2.0941221538... (computed elsewhere, by certified intervals) in
    [2.0941, 2.0942].
    D. The algebra of the gap: the minimum of (G^2/6) ((t - a)^2 + (t - b)^2) and the pure-dephasing pulse.
*)
theory Equal_Rate_Threshold
  imports "HOL-Decision_Procs.Approximation"
begin

section \<open>0. Elementary facts\<close>

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

lemma sinh_le_mul_cosh:
  fixes x :: real
  assumes "0 \<le> x"
  shows "sinh x \<le> x * cosh x"
proof -
  define g where "g = (\<lambda>t::real. t * cosh t - sinh t)"
  have "g 0 \<le> g x"
  proof (rule DERIV_nonneg_imp_nondecreasing[OF assms])
    fix t :: real
    assume t: "0 \<le> t" "t \<le> x"
    have "(g has_real_derivative t * sinh t) (at t)"
      unfolding g_def by (auto intro!: derivative_eq_intros)
    moreover have "0 \<le> t * sinh t"
      using sinh_ge_self[OF t(1)] t(1) by (intro mult_nonneg_nonneg) linarith+
    ultimately show "\<exists>d. DERIV g t :> d \<and> 0 \<le> d" by blast
  qed
  then show ?thesis unfolding g_def by simp
qed

lemma cosh_exp: "cosh (x::real) = (exp x + exp (- x)) / 2"
  by (simp add: cosh_def)

lemma sinh_exp: "sinh (x::real) = (exp x - exp (- x)) / 2"
  by (simp add: sinh_def)

section \<open>A. The function h and its monotonicity (Proposition 11, equal rates)\<close>

definition kap :: "real \<Rightarrow> real" where
  "kap phi = sqrt (phi\<^sup>2 - 4)"

definition hh :: "real \<Rightarrow> real \<Rightarrow> real" where
  "hh phi T = cosh (kap phi * T) + phi / kap phi * sinh (kap phi * T)"

definition ff :: "real \<Rightarrow> real \<Rightarrow> real" where
  "ff phi T = hh phi T - 4 * sin T"

lemma kap_facts:
  fixes phi :: real
  assumes "2 < phi"
  shows "0 < kap phi" and "(kap phi)\<^sup>2 = phi\<^sup>2 - 4" and "phi\<^sup>2 = (kap phi)\<^sup>2 + 4"
proof -
  have "(2::real)\<^sup>2 < phi\<^sup>2" by (rule power_strict_mono) (use assms in simp_all)
  then have p: "0 < phi\<^sup>2 - 4" by simp
  show "0 < kap phi" unfolding kap_def using p by simp
  show k2: "(kap phi)\<^sup>2 = phi\<^sup>2 - 4" unfolding kap_def using p by (simp add: real_sqrt_pow2)
  show "phi\<^sup>2 = (kap phi)\<^sup>2 + 4" using k2 by simp
qed

text \<open>The T-derivative of h is kappa sinh (kappa T) + phi cosh (kappa T).\<close>

lemma hh_deriv_T:
  fixes phi T :: real
  assumes "2 < phi"
  shows "((hh phi) has_real_derivative kap phi * sinh (kap phi * T) + phi * cosh (kap phi * T)) (at T)"
proof -
  have kp: "0 < kap phi" by (rule kap_facts(1)[OF assms])
  have d0: "((\<lambda>t. cosh (kap phi * t) + phi / kap phi * sinh (kap phi * t)) has_real_derivative
        sinh (kap phi * T) * kap phi + phi / kap phi * (cosh (kap phi * T) * kap phi)) (at T)"
    by (auto intro!: derivative_eq_intros)
  have eq: "sinh (kap phi * T) * kap phi + phi / kap phi * (cosh (kap phi * T) * kap phi)
      = kap phi * sinh (kap phi * T) + phi * cosh (kap phi * T)"
    using kp by (simp add: field_simps)
  have d: "((\<lambda>t. cosh (kap phi * t) + phi / kap phi * sinh (kap phi * t)) has_real_derivative
        kap phi * sinh (kap phi * T) + phi * cosh (kap phi * T)) (at T)" by (rule DERIV_cong[OF d0 eq])
  have fe: "hh phi = (\<lambda>t. cosh (kap phi * t) + phi / kap phi * sinh (kap phi * t))"
    by (rule ext) (simp add: hh_def)
  show ?thesis by (subst fe) (rule d)
qed

theorem hh_mono_T:
  fixes phi T T' :: real
  assumes "2 < phi" and "0 \<le> T" and "T \<le> T'"
  shows "hh phi T \<le> hh phi T'"
proof (rule DERIV_nonneg_imp_nondecreasing[OF assms(3)])
  fix t :: real
  assume t: "T \<le> t" "t \<le> T'"
  have kp: "0 < kap phi" by (rule kap_facts(1)[OF assms(1)])
  have t0: "0 \<le> t" using t(1) assms(2) by linarith
  have s: "0 \<le> sinh (kap phi * t)" using sinh_ge_self[of "kap phi * t"] kp t0 by simp
  have c: "0 \<le> cosh (kap phi * t)" using cosh_real_ge_1[of "kap phi * t"] by simp
  have "0 \<le> kap phi * sinh (kap phi * t) + phi * cosh (kap phi * t)"
    using kp assms(1) s c by (intro add_nonneg_nonneg mult_nonneg_nonneg) simp_all
  then show "\<exists>d. DERIV (hh phi) t :> d \<and> 0 \<le> d"
    using hh_deriv_T[OF assms(1), of t] by blast
qed

text \<open>The phi-derivative of h is, with x = kappa T,
  (phi T sinh x) / kappa + (phi^2 x cosh x - 4 sinh x) / kappa^3, which is nonnegative.\<close>

lemma kap_deriv:
  fixes phi :: real
  assumes "2 < phi"
  shows "(kap has_real_derivative phi / kap phi) (at phi)"
proof -
  have kp: "0 < kap phi" by (rule kap_facts(1)[OF assms])
  have pos: "0 < phi\<^sup>2 - 4" using kap_facts(2)[OF assms] zero_less_power[OF kp, of 2] by simp
  have d2: "((\<lambda>p::real. p\<^sup>2 - 4) has_real_derivative 2 * phi) (at phi)"
    by (auto intro!: derivative_eq_intros)
  have "((\<lambda>p::real. sqrt (p\<^sup>2 - 4)) has_real_derivative inverse (sqrt (phi\<^sup>2 - 4)) / 2 * (2 * phi)) (at phi)"
    using DERIV_chain2[where f = sqrt and g = "\<lambda>p::real. p\<^sup>2 - 4", OF DERIV_real_sqrt[OF pos] d2] by simp
  moreover have "inverse (sqrt (phi\<^sup>2 - 4)) / 2 * (2 * phi) = phi / kap phi"
    unfolding kap_def by (simp add: field_simps)
  ultimately have d: "((\<lambda>p::real. sqrt (p\<^sup>2 - 4)) has_real_derivative phi / kap phi) (at phi)" by simp
  have fe: "kap = (\<lambda>p::real. sqrt (p\<^sup>2 - 4))" by (rule ext) (simp add: kap_def)
  show ?thesis by (subst fe) (rule d)
qed

lemma deriv_gen:
  fixes f :: "real \<Rightarrow> real" and f1 phi T :: real
  assumes kd: "(f has_real_derivative f1) (at phi)" and kp: "f phi \<noteq> 0"
  shows "((\<lambda>p. cosh (f p * T) + p / f p * sinh (f p * T)) has_real_derivative
      sinh (f phi * T) * (f1 * T) + ((1 * f phi - phi * f1) / (f phi)\<^sup>2 * sinh (f phi * T)
        + phi / f phi * (cosh (f phi * T) * (f1 * T)))) (at phi)"
  by (auto intro!: derivative_eq_intros kd simp: kp field_simps) (algebra)?

lemma hh_deriv_phi:
  fixes phi T :: real
  assumes "2 < phi" and "0 \<le> T"
  shows "\<exists>d. DERIV (\<lambda>p. hh p T) phi :> d \<and> 0 \<le> d"
proof -
  define k where "k = kap phi"
  have kp: "0 < k" unfolding k_def by (rule kap_facts(1)[OF assms(1)])
  have e: "phi\<^sup>2 = k\<^sup>2 + 4" unfolding k_def by (rule kap_facts(3)[OF assms(1)])
  define x where "x = k * T"
  define D where "D = phi * T * sinh x / k + (phi\<^sup>2 * x * cosh x - 4 * sinh x) / k ^ 3"
  have kd: "(kap has_real_derivative phi / k) (at phi)"
    unfolding k_def by (rule kap_deriv[OF assms(1)])
  have hf: "(\<lambda>p. hh p T) = (\<lambda>p. cosh (kap p * T) + p / kap p * sinh (kap p * T))"
    by (rule ext) (simp add: hh_def)
  have raw: "((\<lambda>p. hh p T) has_real_derivative
      sinh x * (phi / k * T) + ((1 * k - phi * (phi / k)) / k\<^sup>2 * sinh x
        + phi / k * (cosh x * (phi / k * T)))) (at phi)"
  proof -
    have kne: "kap phi \<noteq> 0" using kp unfolding k_def by simp
    have kd': "(kap has_real_derivative phi / kap phi) (at phi)" by (rule kap_deriv[OF assms(1)])
    show ?thesis unfolding hf x_def k_def by (rule deriv_gen[OF kd' kne])
  qed
  have eq: "sinh x * (phi / k * T) + ((1 * k - phi * (phi / k)) / k\<^sup>2 * sinh x
        + phi / k * (cosh x * (phi / k * T))) = D"
    unfolding D_def using kp e by (simp add: field_simps x_def) (algebra)
  have x0: "0 \<le> x" unfolding x_def using kp assms(2) by simp
  have sh: "0 \<le> sinh x" using sinh_ge_self[OF x0] x0 by linarith
  have ch: "1 \<le> cosh x" using cosh_real_ge_1[of x] by simp
  have p4: "4 \<le> phi\<^sup>2" using e by simp
  have "4 * sinh x \<le> 4 * (x * cosh x)" using sinh_le_mul_cosh[OF x0] by simp
  also have "\<dots> \<le> phi\<^sup>2 * (x * cosh x)"
    by (rule mult_right_mono[OF p4]) (use x0 ch in simp)
  finally have n2: "0 \<le> phi\<^sup>2 * x * cosh x - 4 * sinh x" by (simp add: mult.assoc)
  have pp: "0 < phi" using assms(1) by simp
  have n1: "0 \<le> phi * T * sinh x" using pp assms(2) sh by (intro mult_nonneg_nonneg) simp_all
  have "0 \<le> D"
    unfolding D_def using kp n1 n2 by (intro add_nonneg_nonneg divide_nonneg_pos) simp_all
  then show ?thesis using raw eq by auto
qed

theorem hh_mono_phi:
  fixes phi1 phi2 T :: real
  assumes "2 < phi1" and "phi1 \<le> phi2" and "0 \<le> T"
  shows "hh phi1 T \<le> hh phi2 T"
proof (rule DERIV_nonneg_imp_nondecreasing[OF assms(2), of "\<lambda>p. hh p T"])
  fix p :: real
  assume "phi1 \<le> p" "p \<le> phi2"
  then show "\<exists>d. DERIV (\<lambda>p. hh p T) p :> d \<and> 0 \<le> d"
    using hh_deriv_phi[of p T] assms by simp
qed

corollary ff_mono_phi:
  assumes "2 < phi1" and "phi1 \<le> phi2" and "0 \<le> T"
  shows "ff phi1 T \<le> ff phi2 T"
  unfolding ff_def using hh_mono_phi[OF assms] by simp

section \<open>B. High side: f > 0 from phi = 2.0942 on\<close>

text \<open>The same f written with exp only, which is what the interval method of HOL-Decision_Procs reads.\<close>

definition fexp :: "real \<Rightarrow> real \<Rightarrow> real" where
  "fexp phi T = (exp (sqrt (phi\<^sup>2 - 4) * T) + exp (- (sqrt (phi\<^sup>2 - 4) * T))) / 2
     + phi / sqrt (phi\<^sup>2 - 4) * ((exp (sqrt (phi\<^sup>2 - 4) * T) - exp (- (sqrt (phi\<^sup>2 - 4) * T))) / 2)
     - 4 * sin T"

lemma ff_eq_fexp: "ff phi T = fexp phi T"
  unfolding ff_def hh_def fexp_def kap_def by (simp add: cosh_exp sinh_exp)

definition phi_hi :: real where "phi_hi = 20942 / 10 ^ 4"
definition phi_lo :: real where "phi_lo = 20941 / 10 ^ 4"

lemma phi_hi_gt: "2 < phi_hi" unfolding phi_hi_def by simp

lemma fexp_hi_a1: "T \<in> {0 .. 0.4::real} \<Longrightarrow> 0 < fexp (20942 / 10 ^ 4) T"
  unfolding fexp_def by (approximation 40 splitting: T = 3 taylor: T = 3)

lemma fexp_hi_a2: "T \<in> {0.4 .. 0.7::real} \<Longrightarrow> 0 < fexp (20942 / 10 ^ 4) T"
  unfolding fexp_def by (approximation 40 splitting: T = 3 taylor: T = 3)

lemma fexp_hi_a3: "T \<in> {0.7 .. 0.8::real} \<Longrightarrow> 0 < fexp (20942 / 10 ^ 4) T"
  unfolding fexp_def by (approximation 40 splitting: T = 4 taylor: T = 3)

lemma fexp_hi_b: "T \<in> {0.8 .. 0.86::real} \<Longrightarrow> 0 < fexp (20942 / 10 ^ 4) T"
  unfolding fexp_def by (approximation 40 splitting: T = 4 taylor: T = 3)

lemma fexp_hi_c: "T \<in> {0.86 .. 1.5708::real} \<Longrightarrow> 0 < fexp (20942 / 10 ^ 4) T"
  unfolding fexp_def by (approximation 40 splitting: T = 4 taylor: T = 3)

lemma hh_hi_at_end: "4 < fexp (20942 / 10 ^ 4) 1.5708 + 4 * sin (1.5708::real)"
  unfolding fexp_def by (approximation 60)

theorem ff_pos_hi:
  fixes phi T :: real
  assumes "phi_hi \<le> phi" and "0 \<le> T"
  shows "0 < ff phi T"
proof -
  have p2: "2 < phi_hi" by (rule phi_hi_gt)
  have mono: "ff phi_hi T \<le> ff phi T" by (rule ff_mono_phi[OF p2 assms(1) assms(2)])
  have base: "0 < ff phi_hi T"
  proof (cases "T \<le> 1.5708")
    case True
    then consider "T \<le> 0.4" | "0.4 < T" "T \<le> 0.7" | "0.7 < T" "T \<le> 0.8"
      | "0.8 < T" "T \<le> 0.86" | "0.86 < T" by linarith
    then show ?thesis unfolding ff_eq_fexp phi_hi_def
    proof cases
      case 1
      then show "0 < fexp (20942 / 10 ^ 4) T" by (intro fexp_hi_a1) (use assms(2) in simp)
    next
      case 2
      then show "0 < fexp (20942 / 10 ^ 4) T" by (intro fexp_hi_a2) simp
    next
      case 3
      then show "0 < fexp (20942 / 10 ^ 4) T" by (intro fexp_hi_a3) simp
    next
      case 4
      then show "0 < fexp (20942 / 10 ^ 4) T" by (intro fexp_hi_b) simp
    next
      case 5
      then show "0 < fexp (20942 / 10 ^ 4) T" using True by (intro fexp_hi_c) simp
    qed
  next
    case False
    then have T1: "1.5708 \<le> T" by simp
    have e1: "hh phi_hi 1.5708 = fexp (20942 / 10 ^ 4) 1.5708 + 4 * sin 1.5708"
      using ff_eq_fexp[where phi = phi_hi and T = "1.5708"] unfolding ff_def phi_hi_def by simp
    have e2: "4 < hh phi_hi 1.5708" unfolding e1 by (rule hh_hi_at_end)
    have m: "hh phi_hi 1.5708 \<le> hh phi_hi T" by (rule hh_mono_T[OF p2 _ T1]) simp
    have s1: "sin T \<le> 1" by (rule sin_le_one)
    show ?thesis unfolding ff_def using e2 m s1 by linarith
  qed
  show ?thesis using base mono by simp
qed

section \<open>C. Low side: f < 0 somewhere for every 2 < phi <= 2.0941\<close>

lemma fexp_lo: "fexp (20941 / 10 ^ 4) 0.8268 < 0"
  unfolding fexp_def by (approximation 40)

theorem ff_neg_lo:
  fixes phi :: real
  assumes "2 < phi" and "phi \<le> phi_lo"
  shows "ff phi 0.8268 < 0"
proof -
  have "ff phi_lo 0.8268 < 0" unfolding ff_eq_fexp phi_lo_def by (rule fexp_lo)
  moreover have "ff phi 0.8268 \<le> ff phi_lo 0.8268" by (rule ff_mono_phi[OF assms]) simp
  ultimately show ?thesis by simp
qed

corollary threshold_enclosure:
  fixes phi :: real
  shows "2 < phi \<Longrightarrow> phi \<le> phi_lo \<Longrightarrow> \<exists>T. 0 \<le> T \<and> ff phi T < 0"
    and "phi_hi \<le> phi \<Longrightarrow> \<forall>T. 0 \<le> T \<longrightarrow> 0 < ff phi T"
  using ff_neg_lo ff_pos_hi by (auto intro!: exI[of _ "0.8268"])

section \<open>D. The algebra of the gap (Proposition "gap")\<close>

text \<open>(a) The minimum over t of (G^2/6) ((t - a)^2 + (t - b)^2) is G^2 (a - b)^2 / 12, attained at (a + b) / 2.\<close>

lemma gap_lower_bound:
  fixes G a b t :: real
  shows "G\<^sup>2 * (a - b)\<^sup>2 / 12 \<le> (G\<^sup>2 / 6) * ((t - a)\<^sup>2 + (t - b)\<^sup>2)"
proof -
  have id: "(t - a)\<^sup>2 + (t - b)\<^sup>2 = 2 * (t - (a + b) / 2)\<^sup>2 + (a - b)\<^sup>2 / 2" by (simp add: power2_eq_square field_simps)
  have h: "0 \<le> (G\<^sup>2 / 6) * (2 * (t - (a + b) / 2)\<^sup>2)" by (simp add: zero_le_mult_iff)
  have "(G\<^sup>2 / 6) * (2 * (t - (a + b) / 2)\<^sup>2 + (a - b)\<^sup>2 / 2)
      = (G\<^sup>2 / 6) * (2 * (t - (a + b) / 2)\<^sup>2) + G\<^sup>2 * (a - b)\<^sup>2 / 12" by (simp add: field_simps)
  with h show ?thesis unfolding id by linarith
qed

lemma gap_at_midpoint:
  fixes G a b :: real
  shows "(G\<^sup>2 / 6) * (((a + b) / 2 - a)\<^sup>2 + ((a + b) / 2 - b)\<^sup>2) = G\<^sup>2 * (a - b)\<^sup>2 / 12"
  by (simp add: power2_eq_square field_simps)

text \<open>(b) With a - b = Phi / (2 G^2) the minimum is Phi^2 / (48 G^2).\<close>

lemma gap_min_value:
  fixes G a b Phi :: real
  assumes "G \<noteq> 0" and "a - b = Phi / (2 * G\<^sup>2)"
  shows "G\<^sup>2 * (a - b)\<^sup>2 / 12 = Phi\<^sup>2 / (48 * G\<^sup>2)"
  using assms(1) by (simp add: assms(2) power_divide power_mult_distrib field_simps power2_eq_square)

text \<open>(c) Pure dephasing: w (t) = exp (-Phi t / 2) (cos (omega t) + (Phi / (2 omega)) sin (omega t)),
  omega^2 = 4 G^2 - Phi^2 / 4, solves w'' + Phi w' + 4 G^2 w = 0, w (0) = 1, w' (0) = 0.\<close>

definition wph :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "wph Phi om t = exp (- Phi * t / 2) * (cos (om * t) + Phi / (2 * om) * sin (om * t))"

definition wph1 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "wph1 Phi om t = - (exp (- Phi * t / 2) * (om + Phi\<^sup>2 / (4 * om)) * sin (om * t))"

lemma wph_deriv:
  fixes Phi om t :: real
  assumes "0 < om"
  shows "((wph Phi om) has_real_derivative wph1 Phi om t) (at t)"
proof -
  have "((wph Phi om) has_real_derivative
      (exp (- Phi * t / 2) * (- Phi / 2)) * (cos (om * t) + Phi / (2 * om) * sin (om * t))
      + exp (- Phi * t / 2) * (- (sin (om * t) * om) + Phi / (2 * om) * (cos (om * t) * om))) (at t)"
    unfolding wph_def[abs_def] by (auto intro!: derivative_eq_intros)
  moreover have "(exp (- Phi * t / 2) * (- Phi / 2)) * (cos (om * t) + Phi / (2 * om) * sin (om * t))
      + exp (- Phi * t / 2) * (- (sin (om * t) * om) + Phi / (2 * om) * (cos (om * t) * om))
      = wph1 Phi om t"
    unfolding wph1_def using assms by (simp add: field_simps power2_eq_square)
  ultimately show ?thesis by simp
qed

lemma wph1_deriv:
  fixes G Phi om t :: real
  assumes "0 < om" and "om\<^sup>2 = 4 * G\<^sup>2 - Phi\<^sup>2 / 4"
  shows "((wph1 Phi om) has_real_derivative - Phi * wph1 Phi om t - 4 * G\<^sup>2 * wph Phi om t) (at t)"
proof -
  have g: "4 * G\<^sup>2 = om\<^sup>2 + Phi\<^sup>2 / 4" using assms(2) by simp
  have "((wph1 Phi om) has_real_derivative
      - ((exp (- Phi * t / 2) * (- Phi / 2)) * (om + Phi\<^sup>2 / (4 * om)) * sin (om * t)
         + exp (- Phi * t / 2) * (om + Phi\<^sup>2 / (4 * om)) * (cos (om * t) * om))) (at t)"
    unfolding wph1_def[abs_def] by (auto intro!: derivative_eq_intros)
  moreover have "- ((exp (- Phi * t / 2) * (- Phi / 2)) * (om + Phi\<^sup>2 / (4 * om)) * sin (om * t)
         + exp (- Phi * t / 2) * (om + Phi\<^sup>2 / (4 * om)) * (cos (om * t) * om))
      = - Phi * wph1 Phi om t - 4 * G\<^sup>2 * wph Phi om t"
    unfolding wph1_def wph_def g using assms(1) by (simp add: field_simps power2_eq_square)
  ultimately show ?thesis by simp
qed

lemma wph_initial:
  fixes Phi om :: real
  shows "wph Phi om 0 = 1" and "wph1 Phi om 0 = 0"
  unfolding wph_def wph1_def by simp_all

theorem wph1_stationary:
  fixes Phi om :: real
  assumes "0 < om"
  shows "wph1 Phi om (pi / om) = 0"
  unfolding wph1_def using assms by simp

theorem wph1_negative:
  fixes Phi om t :: real
  assumes "0 < om" and "0 < t" and "t < pi / om"
  shows "wph1 Phi om t < 0"
proof -
  have "0 < om * t" using assms(1,2) by simp
  moreover have "om * t < pi" using assms(1,3) by (simp add: less_divide_eq mult.commute)
  ultimately have s: "0 < sin (om * t)" by (rule sin_gt_zero)
  have b: "0 < om + Phi\<^sup>2 / (4 * om)"
    using assms(1) by (intro add_pos_nonneg divide_nonneg_pos) simp_all
  have "0 < exp (- Phi * t / 2) * (om + Phi\<^sup>2 / (4 * om)) * sin (om * t)" using s b by simp
  then show ?thesis unfolding wph1_def by simp
qed

end
