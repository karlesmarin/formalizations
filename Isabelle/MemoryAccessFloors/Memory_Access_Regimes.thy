(*  Title:      Memory_Access_Regimes.thy
    Author:     Carles Marín
    Copyright:  Carles Marín
    License:    BSD-3-Clause

    encaje: segunda teoria de la sesion 186 (regimenes sobreamortiguado, critico y subamortiguado del Teorema 1 de
    "Exact limits for writing a quantum memory"); reutiliza damped_sine de Memory_Access_Floors; no es herramienta.
*)

theory Memory_Access_Regimes
  imports Memory_Access_Floors
begin

text \<open>Notation throughout: @{text "G > 0"}, @{text "gq \<ge> 0"}, @{text "gm \<ge> 0"},
  @{text "gb = (gq + gm) / 2"}, @{text "d = gq - gm"} (the paper's @{text "\<delta>"}).\<close>

section \<open>A. Logarithmic-derivative identity of the new proof\<close>

lemma log_derivative_alg:
  fixes G gq gm s c w L :: real
  assumes "s \<noteq> 0" and "w \<noteq> 0" and "s * s + c * c = 1"
    and "w = G + ((gq - gm) / 2) * s * c" and "L = (gq * (c * c) + gm * (s * s)) / 2"
  shows "2 * c / s - 2 * L / w = (2 * G * c / s - gm) / w"
proof -
  have n: "2 * c * w - s * (2 * L) = 2 * G * c - gm * s"
  proof -
    have "2 * c * w - s * (2 * L) - (2 * G * c - gm * s) = gm * s * (1 - (s * s + c * c))"
      by (simp add: assms(4,5) algebra_simps; argo)
    also have "\<dots> = 0" using assms(3) by simp
    finally show ?thesis by simp
  qed
  have a: "2 * c / s - 2 * L / w = (2 * c * w - s * (2 * L)) / (s * w)"
    using assms(1,2) by (simp add: field_simps)
  have b: "(2 * G * c / s - gm) / w = (2 * G * c - gm * s) / (s * w)"
    using assms(1,2) by (simp add: field_simps)
  show ?thesis using a b n by simp
qed

lemma log_derivative_identity:
  fixes G gq gm \<theta> w L :: real
  assumes "0 < \<theta>" and "\<theta> < pi / 2"
    and "w = G + ((gq - gm) / 4) * sin (2 * \<theta>)"
    and "L = (gq * (cos \<theta>)\<^sup>2 + gm * (sin \<theta>)\<^sup>2) / 2"
    and "w \<noteq> 0"
  shows "2 * cos \<theta> / sin \<theta> - 2 * L / w = (2 * G * cos \<theta> / sin \<theta> - gm) / w"
proof -
  have s: "0 < sin \<theta>" using assms(1,2) by (intro sin_gt_zero) auto
  have e: "sin \<theta> * sin \<theta> + cos \<theta> * cos \<theta> = 1"
    using sin_cos_squared_add[of \<theta>] by (simp add: power2_eq_square)
  have w2: "w = G + ((gq - gm) / 2) * sin \<theta> * cos \<theta>"
    using assms(3) by (simp add: sin_double)
  have L2: "L = (gq * (cos \<theta> * cos \<theta>) + gm * (sin \<theta> * sin \<theta>)) / 2"
    using assms(4) by (simp add: power2_eq_square)
  show ?thesis by (rule log_derivative_alg[OF _ assms(5) e w2 L2]) (use s in simp)
qed

section \<open>B. Over-damped resonant pulse\<close>

subsection \<open>The parameters\<close>

lemma overdamped_parameters:
  fixes G gq gm gb d \<kappa> :: real
  assumes "0 < G" and "0 \<le> gq" and "0 \<le> gm" and "gb = (gq + gm) / 2" and "d = gq - gm"
    and "G < \<bar>d\<bar> / 4" and "\<kappa> = sqrt (d\<^sup>2 / 16 - G\<^sup>2)"
  shows "0 < \<kappa>" and "\<kappa>\<^sup>2 = d\<^sup>2 / 16 - G\<^sup>2" and "gb\<^sup>2 - 4 * \<kappa>\<^sup>2 = 4 * G\<^sup>2 + gq * gm"
    and "0 < 4 * G\<^sup>2 + gq * gm" and "0 < gb" and "2 * \<kappa> < gb"
proof -
  have "G\<^sup>2 < (\<bar>d\<bar> / 4)\<^sup>2" using assms(1,6) by (intro power_strict_mono) auto
  then have lt: "G\<^sup>2 < d\<^sup>2 / 16" by (simp add: power_divide power2_abs)
  then show kpos: "0 < \<kappa>" using assms(7) by simp
  show k2: "\<kappa>\<^sup>2 = d\<^sup>2 / 16 - G\<^sup>2" using assms(7) lt by (simp add: real_sqrt_pow2)
  show idn: "gb\<^sup>2 - 4 * \<kappa>\<^sup>2 = 4 * G\<^sup>2 + gq * gm"
  proof -
    have "gb\<^sup>2 - 4 * \<kappa>\<^sup>2 = gb\<^sup>2 - 4 * (d\<^sup>2 / 16 - G\<^sup>2)" by (simp only: k2)
    also have "\<dots> = 4 * G\<^sup>2 + gq * gm"
      by (simp add: assms(4,5) power2_eq_square algebra_simps; argo)
    finally show ?thesis .
  qed
  have gm0: "0 \<le> gq * gm" using assms(2,3) by simp
  have g2: "0 < G\<^sup>2" using assms(1) by simp
  show pos: "0 < 4 * G\<^sup>2 + gq * gm" using gm0 g2 by argo
  have "0 \<le> gb" using assms(2,3,4) by simp
  moreover have "gb \<noteq> 0"
  proof
    assume "gb = 0"
    then have "4 * \<kappa>\<^sup>2 = - (4 * G\<^sup>2 + gq * gm)" using idn by simp
    moreover have "0 < \<kappa>\<^sup>2" using kpos by simp
    ultimately show False using pos by argo
  qed
  ultimately show gbpos: "0 < gb" by simp
  have m4: "(2 * \<kappa>)\<^sup>2 = 4 * \<kappa>\<^sup>2" by (simp add: power_mult_distrib)
  have "(2 * \<kappa>)\<^sup>2 < gb\<^sup>2" using idn pos m4 by linarith
  then have h: "(2 * \<kappa>)\<^sup>2 < gb\<^sup>2" .
  have gb0: "0 \<le> gb" using gbpos by simp
  show "2 * \<kappa> < gb" by (rule power2_less_imp_less[OF h gb0])
qed

lemma tanh_artanh_real:
  fixes x :: real
  assumes "\<bar>x\<bar> < 1"
  shows "tanh (artanh x) = x"
proof -
  have p: "0 < 1 + x" "0 < 1 - x" using assms by (auto simp: abs_less_iff)
  define y where "y = artanh x"
  have e: "exp (y + y) = (1 + x) / (1 - x)" unfolding y_def artanh_def using p by (simp add: field_simps)
  have q: "exp y * exp y = (1 + x) / (1 - x)"
  proof -
    have "exp y * exp y = exp (y + y)" by (rule exp_add[symmetric])
    then show ?thesis using e by simp
  qed
  have qpos: "0 < exp y" by simp
  have hq: "(1 - x) * (exp y * exp y) = 1 + x" using q p(2) by (simp add: field_simps)
  have key: "exp y * exp y - 1 = x * (exp y * exp y + 1)" using hq by argo
  have sh: "sinh y = x * cosh y"
    using qpos key by (simp add: sinh_def cosh_def exp_minus field_simps; argo)
  have "cosh y \<noteq> 0" by (rule cosh_real_nonzero)
  then have "tanh y = x" using sh by (simp add: tanh_def)
  then show ?thesis unfolding y_def .
qed

subsection \<open>The normalised damped hyperbolic sine\<close>

definition damped_sinh :: "real \<Rightarrow> real \<Rightarrow> real" where
  "damped_sinh k u = exp (- k * u) * (sinh u)\<^sup>2"

lemma damped_sinh_deriv:
  "DERIV (damped_sinh k) x :> exp (- k * x) * sinh x * (2 * cosh x - k * sinh x)"
proof -
  have "((\<lambda>x. exp (- k * x) * (sinh x)\<^sup>2) has_real_derivative
        (exp (- k * x) * (- k)) * (sinh x)\<^sup>2 + exp (- k * x) * (2 * sinh x * cosh x)) (at x)"
    by (auto intro!: derivative_eq_intros)
  then show ?thesis
    unfolding damped_sinh_def[abs_def] by (simp add: algebra_simps power2_eq_square)
qed

lemma damped_sinh_peak_facts:
  fixes k :: real
  assumes "2 < k"
  defines "u0 \<equiv> artanh (2 / k)"
  shows "0 < u0" and "k * sinh u0 = 2 * cosh u0"
    and "damped_sinh k u0 = 4 / (k\<^sup>2 - 4) * exp (- k * artanh (2 / k))"
proof -
  have kpos: "0 < k" using assms(1) by simp
  have lt1: "\<bar>2 / k\<bar> < 1" using assms(1) kpos by (simp add: divide_less_eq)
  have cpos: "0 < cosh u0" by (rule cosh_real_pos)
  have "tanh u0 = 2 / k" unfolding u0_def using lt1 by (rule tanh_artanh_real)
  then have "sinh u0 / cosh u0 = 2 / k" by (simp add: tanh_def)
  then show ks: "k * sinh u0 = 2 * cosh u0" using cpos kpos by (simp add: field_simps)
  have "0 < k * sinh u0" using ks cpos by simp
  then have "0 < sinh u0" using kpos by (rule zero_less_mult_pos)
  then show "0 < u0" by (simp add: sinh_real_pos_iff)
  have e1: "k\<^sup>2 * (sinh u0)\<^sup>2 = 4 * (cosh u0)\<^sup>2"
  proof -
    have "(k * sinh u0)\<^sup>2 = (2 * cosh u0)\<^sup>2" using ks by simp
    then show ?thesis by (simp add: power_mult_distrib)
  qed
  have e2: "(cosh u0)\<^sup>2 = (sinh u0)\<^sup>2 + 1" by (rule cosh_square_eq)
  have P: "(sinh u0)\<^sup>2 * (k\<^sup>2 - 4) = 4" using e1 e2 by (simp add: algebra_simps; argo)
  have kk: "0 < k\<^sup>2 - 4"
  proof -
    have "2\<^sup>2 < k\<^sup>2" using assms(1) by (intro power_strict_mono) simp_all
    then show ?thesis by simp
  qed
  have s2: "(sinh u0)\<^sup>2 = 4 / (k\<^sup>2 - 4)" using kk P by (simp add: eq_divide_eq)
  show "damped_sinh k u0 = 4 / (k\<^sup>2 - 4) * exp (- k * artanh (2 / k))"
    unfolding damped_sinh_def using s2 u0_def by simp
qed

lemma damped_sinh_le_peak:
  fixes k u :: real
  assumes "2 < k" and "0 \<le> u"
  shows "damped_sinh k u \<le> 4 / (k\<^sup>2 - 4) * exp (- k * artanh (2 / k))"
proof -
  define u0 where "u0 = artanh (2 / k)"
  have u0pos: "0 < u0" and ks: "k * sinh u0 = 2 * cosh u0"
    using damped_sinh_peak_facts[OF assms(1)] unfolding u0_def by simp_all
  have cpos: "0 < cosh u0" by (rule cosh_real_pos)
  have kpos: "0 < k" using assms(1) by simp
  have rel: "k * sinh (x - u0) = cosh u0 * (k * sinh x - 2 * cosh x)" for x
  proof -
    have "k * sinh (x - u0) = k * sinh x * cosh u0 - cosh x * (k * sinh u0)"
      by (simp add: sinh_diff algebra_simps)
    also have "\<dots> = k * sinh x * cosh u0 - cosh x * (2 * cosh u0)" using ks by simp
    also have "\<dots> = cosh u0 * (k * sinh x - 2 * cosh x)" by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have E: "2 * cosh x - k * sinh x = - (k * sinh (x - u0) / cosh u0)" for x
  proof -
    have "k * sinh (x - u0) / cosh u0 = k * sinh x - 2 * cosh x"
      using cpos by (subst rel) simp
    then show ?thesis by simp
  qed
  show ?thesis
  proof (cases "u \<le> u0")
    case True
    have "damped_sinh k u \<le> damped_sinh k u0"
    proof (rule DERIV_nonneg_imp_nondecreasing[OF True])
      fix x assume x: "u \<le> x" "x \<le> u0"
      have "sinh (x - u0) \<le> 0" using x by (simp add: sinh_real_nonpos_iff)
      then have "k * sinh (x - u0) \<le> 0" using kpos by (intro mult_nonneg_nonpos) simp_all
      then have "k * sinh (x - u0) / cosh u0 \<le> 0" using cpos by (simp add: divide_nonpos_pos)
      then have "0 \<le> 2 * cosh x - k * sinh x" using E[of x] by simp
      moreover have "0 \<le> sinh x" using x assms(2) by (simp add: sinh_real_nonneg_iff)
      ultimately have "0 \<le> exp (- k * x) * sinh x * (2 * cosh x - k * sinh x)" by simp
      then show "\<exists>y. DERIV (damped_sinh k) x :> y \<and> 0 \<le> y"
        using damped_sinh_deriv by blast
    qed
    then show ?thesis using damped_sinh_peak_facts(3)[OF assms(1)] unfolding u0_def by simp
  next
    case False
    then have le: "u0 \<le> u" by simp
    have "damped_sinh k u \<le> damped_sinh k u0"
    proof (rule DERIV_nonpos_imp_nonincreasing[OF le])
      fix x assume x: "u0 \<le> x" "x \<le> u"
      have "0 \<le> sinh (x - u0)" using x by (simp add: sinh_real_nonneg_iff)
      then have "0 \<le> k * sinh (x - u0)" using kpos by simp
      then have "0 \<le> k * sinh (x - u0) / cosh u0" using cpos by (simp add: divide_nonneg_pos)
      then have "2 * cosh x - k * sinh x \<le> 0" using E[of x] by simp
      moreover have "0 \<le> sinh x" using x u0pos by (simp add: sinh_real_nonneg_iff)
      ultimately have "exp (- k * x) * sinh x * (2 * cosh x - k * sinh x) \<le> 0"
        by (simp add: mult_nonneg_nonpos)
      then show "\<exists>y. DERIV (damped_sinh k) x :> y \<and> y \<le> 0"
        using damped_sinh_deriv by blast
    qed
    then show ?thesis using damped_sinh_peak_facts(3)[OF assms(1)] unfolding u0_def by simp
  qed
qed

subsection \<open>The over-damped pulse, its maximum and where it is attained\<close>

definition pulse_over :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "pulse_over G gb \<kappa> t = G\<^sup>2 * exp (- gb * t) * (sinh (\<kappa> * t) / \<kappa>)\<^sup>2"

lemma pulse_over_rescale:
  fixes G gb \<kappa> t :: real
  assumes "0 < \<kappa>"
  shows "pulse_over G gb \<kappa> t = G\<^sup>2 / \<kappa>\<^sup>2 * damped_sinh (gb / \<kappa>) (\<kappa> * t)"
proof -
  have "- (gb / \<kappa>) * (\<kappa> * t) = - gb * t" using assms by (simp add: field_simps)
  then show ?thesis
    unfolding pulse_over_def damped_sinh_def using assms by (simp add: power_divide field_simps)
qed

lemma pulse_over_peak_constant:
  fixes G gb \<kappa> D :: real
  assumes "0 < \<kappa>" and "gb\<^sup>2 - 4 * \<kappa>\<^sup>2 = D" and "0 < D"
  shows "G\<^sup>2 / \<kappa>\<^sup>2 * (4 / ((gb / \<kappa>)\<^sup>2 - 4)) = 4 * G\<^sup>2 / D"
proof -
  have "(gb / \<kappa>)\<^sup>2 - 4 = D / \<kappa>\<^sup>2" using assms by (simp add: power_divide field_simps)
  then show ?thesis using assms by (simp add: field_simps)
qed

theorem over_pulse_max_bound:
  fixes G gq gm gb d \<kappa> t :: real
  assumes "0 < G" and "0 \<le> gq" and "0 \<le> gm" and "gb = (gq + gm) / 2" and "d = gq - gm"
    and "G < \<bar>d\<bar> / 4" and "\<kappa> = sqrt (d\<^sup>2 / 16 - G\<^sup>2)" and "0 \<le> t"
  shows "pulse_over G gb \<kappa> t
         \<le> 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- gb * (artanh (2 * \<kappa> / gb) / \<kappa>))"
proof -
  have P: "0 < \<kappa>" "gb\<^sup>2 - 4 * \<kappa>\<^sup>2 = 4 * G\<^sup>2 + gq * gm" "0 < 4 * G\<^sup>2 + gq * gm" "0 < gb" "2 * \<kappa> < gb"
    using overdamped_parameters[OF assms(1-7)] by simp_all
  have k2: "2 < gb / \<kappa>" using P(1,5) by (simp add: less_divide_eq)
  have ex: "gb * (artanh (2 * \<kappa> / gb) / \<kappa>) = (gb / \<kappa>) * artanh (2 / (gb / \<kappa>))"
    using P(1,4) by (simp add: field_simps)
  have "pulse_over G gb \<kappa> t = G\<^sup>2 / \<kappa>\<^sup>2 * damped_sinh (gb / \<kappa>) (\<kappa> * t)"
    by (rule pulse_over_rescale[OF P(1)])
  also have "\<dots> \<le> G\<^sup>2 / \<kappa>\<^sup>2 * (4 / ((gb / \<kappa>)\<^sup>2 - 4) * exp (- (gb / \<kappa>) * artanh (2 / (gb / \<kappa>))))"
    using damped_sinh_le_peak[OF k2, of "\<kappa> * t"] P(1) assms(8) by (intro mult_left_mono) simp_all
  also have "\<dots> = 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- (gb / \<kappa>) * artanh (2 / (gb / \<kappa>)))"
    using pulse_over_peak_constant[OF P(1,2,3)] by (simp only: mult.assoc[symmetric])
  also have "exp (- (gb / \<kappa>) * artanh (2 / (gb / \<kappa>))) = exp (- gb * (artanh (2 * \<kappa> / gb) / \<kappa>))"
    using ex by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem over_pulse_max_attained:
  fixes G gq gm gb d \<kappa> tstar :: real
  assumes "0 < G" and "0 \<le> gq" and "0 \<le> gm" and "gb = (gq + gm) / 2" and "d = gq - gm"
    and "G < \<bar>d\<bar> / 4" and "\<kappa> = sqrt (d\<^sup>2 / 16 - G\<^sup>2)"
    and "tstar = artanh (2 * \<kappa> / gb) / \<kappa>"
  shows "pulse_over G gb \<kappa> tstar = 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- gb * tstar)"
proof -
  have P: "0 < \<kappa>" "gb\<^sup>2 - 4 * \<kappa>\<^sup>2 = 4 * G\<^sup>2 + gq * gm" "0 < 4 * G\<^sup>2 + gq * gm" "0 < gb" "2 * \<kappa> < gb"
    using overdamped_parameters[OF assms(1-7)] by simp_all
  have k2: "2 < gb / \<kappa>" using P(1,5) by (simp add: less_divide_eq)
  have u: "\<kappa> * tstar = artanh (2 / (gb / \<kappa>))"
    using P(1,4) assms(8) by (simp add: field_simps)
  have ex: "gb * tstar = (gb / \<kappa>) * artanh (2 / (gb / \<kappa>))"
    using u P(1) by (simp add: field_simps)
  have "pulse_over G gb \<kappa> tstar = G\<^sup>2 / \<kappa>\<^sup>2 * damped_sinh (gb / \<kappa>) (\<kappa> * tstar)"
    by (rule pulse_over_rescale[OF P(1)])
  also have "\<dots> = G\<^sup>2 / \<kappa>\<^sup>2 * (4 / ((gb / \<kappa>)\<^sup>2 - 4) * exp (- (gb / \<kappa>) * artanh (2 / (gb / \<kappa>))))"
    using damped_sinh_peak_facts(3)[OF k2] u by simp
  also have "\<dots> = 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- (gb / \<kappa>) * artanh (2 / (gb / \<kappa>)))"
    using pulse_over_peak_constant[OF P(1,2,3)] by (simp only: mult.assoc[symmetric])
  also have "exp (- (gb / \<kappa>) * artanh (2 / (gb / \<kappa>))) = exp (- gb * tstar)"
    using ex by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem over_pulse_global_max:
  fixes G gq gm gb d \<kappa> tstar t :: real
  assumes "0 < G" and "0 \<le> gq" and "0 \<le> gm" and "gb = (gq + gm) / 2" and "d = gq - gm"
    and "G < \<bar>d\<bar> / 4" and "\<kappa> = sqrt (d\<^sup>2 / 16 - G\<^sup>2)"
    and "tstar = artanh (2 * \<kappa> / gb) / \<kappa>" and "0 \<le> t"
  shows "pulse_over G gb \<kappa> t \<le> pulse_over G gb \<kappa> tstar"
proof -
  have "pulse_over G gb \<kappa> t
        \<le> 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- gb * (artanh (2 * \<kappa> / gb) / \<kappa>))"
    by (rule over_pulse_max_bound[OF assms(1-7) assms(9)])
  also have "\<dots> = 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- gb * tstar)"
    using assms(8) by simp
  also have "\<dots> = pulse_over G gb \<kappa> tstar"
    by (rule over_pulse_max_attained[OF assms(1-8), symmetric])
  finally show ?thesis .
qed

subsection \<open>The critical case G = |d|/4\<close>

lemma z_exp_le:
  fixes z :: real
  assumes "0 \<le> z"
  shows "z * exp (- z) \<le> exp (- 1)"
proof -
  have h: "z \<le> exp (z - 1)" using exp_ge_add_one_self[of "z - 1"] by simp
  have e: "exp (- 1) = exp (z - 1) * exp (- z)"
    by (simp add: exp_add[symmetric])
  have "z * exp (- z) \<le> exp (z - 1) * exp (- z)" using h by (intro mult_right_mono) simp_all
  then show ?thesis using e by simp
qed

lemma critical_pulse_max_bound:
  fixes G gb t :: real
  assumes "0 < gb" and "0 \<le> t"
  shows "G\<^sup>2 * t\<^sup>2 * exp (- gb * t) \<le> 4 * G\<^sup>2 / gb\<^sup>2 * exp (- 2)"
proof -
  define z where "z = gb * t / 2"
  have z0: "0 \<le> z" unfolding z_def using assms by simp
  have t2: "t\<^sup>2 = 4 * z\<^sup>2 / gb\<^sup>2" unfolding z_def using assms(1) by (simp add: field_simps power2_eq_square)
  have ee: "exp (- gb * t) = exp (- z) * exp (- z)"
    by (simp add: exp_add[symmetric] z_def; argo)
  have "(z * exp (- z))\<^sup>2 \<le> (exp (- 1))\<^sup>2"
    using z_exp_le[OF z0] z0 by (intro power_mono) simp_all
  then have h: "(z * exp (- z))\<^sup>2 \<le> exp (- 2)"
    by (simp add: exp_add[symmetric] power2_eq_square; argo)
  have "G\<^sup>2 * t\<^sup>2 * exp (- gb * t) = 4 * G\<^sup>2 / gb\<^sup>2 * (z * exp (- z))\<^sup>2"
    using assms(1) t2 ee by (simp add: field_simps power2_eq_square)
  also have "\<dots> \<le> 4 * G\<^sup>2 / gb\<^sup>2 * exp (- 2)"
    using h by (intro mult_left_mono) simp_all
  finally show ?thesis .
qed

lemma critical_pulse_max_attained:
  fixes G gb :: real
  assumes "0 < gb"
  shows "G\<^sup>2 * (2 / gb)\<^sup>2 * exp (- gb * (2 / gb)) = 4 * G\<^sup>2 / gb\<^sup>2 * exp (- 2)"
proof -
  have "gb * (2 / gb) = 2" using assms by simp
  then show ?thesis by (simp add: power_divide field_simps)
qed

theorem critical_pulse_max:
  fixes G gq gm gb d t :: real
  assumes "0 < G" and "0 \<le> gq" and "0 \<le> gm" and "gb = (gq + gm) / 2" and "d = gq - gm"
    and "G = \<bar>d\<bar> / 4"
  shows "0 < gb"
    and "4 * G\<^sup>2 / gb\<^sup>2 = 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm)"
    and "0 \<le> t \<Longrightarrow> G\<^sup>2 * t\<^sup>2 * exp (- gb * t) \<le> G\<^sup>2 * (2 / gb)\<^sup>2 * exp (- gb * (2 / gb))"
    and "G\<^sup>2 * (2 / gb)\<^sup>2 * exp (- gb * (2 / gb)) = 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- 2)"
proof -
  have G2: "G\<^sup>2 = d\<^sup>2 / 16"
  proof -
    have "G\<^sup>2 = (\<bar>d\<bar> / 4)\<^sup>2" using assms(6) by simp
    then show ?thesis by (simp add: power_divide power2_abs)
  qed
  have idn: "gb\<^sup>2 = 4 * G\<^sup>2 + gq * gm"
  proof -
    have "gb\<^sup>2 = (gq + gm)\<^sup>2 / 4" by (simp add: assms(4) power_divide)
    also have "\<dots> = 4 * (d\<^sup>2 / 16) + gq * gm"
      by (simp add: assms(5) power2_eq_square algebra_simps; argo)
    also have "\<dots> = 4 * G\<^sup>2 + gq * gm" by (simp only: G2)
    finally show ?thesis .
  qed
  have g2: "0 < G\<^sup>2" using assms(1) by simp
  have gm0: "0 \<le> gq * gm" using assms(2,3) by simp
  have "0 < gb\<^sup>2" using idn g2 gm0 by argo
  moreover have "0 \<le> gb" using assms(2,3,4) by simp
  ultimately show gbpos: "0 < gb" by simp
  show eq: "4 * G\<^sup>2 / gb\<^sup>2 = 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm)" using idn by simp
  show "0 \<le> t \<Longrightarrow> G\<^sup>2 * t\<^sup>2 * exp (- gb * t) \<le> G\<^sup>2 * (2 / gb)\<^sup>2 * exp (- gb * (2 / gb))"
    using critical_pulse_max_bound[OF gbpos, of t G] critical_pulse_max_attained[OF gbpos, of G] by simp
  show "G\<^sup>2 * (2 / gb)\<^sup>2 * exp (- gb * (2 / gb)) = 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- 2)"
    using critical_pulse_max_attained[OF gbpos, of G] eq by simp
qed

subsection \<open>The resonant equations are satisfied (over-damped case)\<close>

text \<open>Real form of the resonant pulse with @{text "b = -i \<beta>"}: the amplitudes @{text a} (state 1) and
  @{text \<beta>} (state 2) solve @{text "a' = -(gq/2) a - G \<beta>"} and @{text "\<beta>' = -(gm/2) \<beta> + G a"}, with
  @{text "a(0) = 1"}, @{text "\<beta>(0) = 0"}.  The signs are exactly those of the task.\<close>

definition a_over :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "a_over gb d \<kappa> t = exp (- gb * t / 2) * (cosh (\<kappa> * t) - d / (4 * \<kappa>) * sinh (\<kappa> * t))"

definition beta_over :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "beta_over G gb \<kappa> t = G * exp (- gb * t / 2) * sinh (\<kappa> * t) / \<kappa>"

text \<open>Pure algebra of the two resonant equations, with @{text "r = 1/\<kappa>"} so that no division is left
  for the simplifier.\<close>

lemma ode_alg_a:
  fixes E c s \<kappa> gb d gq gm G :: real
  assumes "\<kappa> \<noteq> 0" and "\<kappa>\<^sup>2 = d\<^sup>2 / 16 - G\<^sup>2" and "gb = (gq + gm) / 2" and "d = gq - gm"
  shows "(E * (- gb / 2)) * (c - d / (4 * \<kappa>) * s) + E * (s * \<kappa> - d / (4 * \<kappa>) * (c * \<kappa>))
         = - (gq / 2) * (E * (c - d / (4 * \<kappa>) * s)) - G * (G * E * s / \<kappa>)"
proof -
  define r where "r = 1 / \<kappa>"
  have hr: "\<kappa> * r = 1" using assms(1) by (simp add: r_def)
  have e1: "d / (4 * \<kappa>) = d * r / 4" by (simp add: r_def field_simps)
  have e2: "G * E * s / \<kappa> = G * E * s * r" by (simp add: r_def)
  have hG: "G * G = d * d / 16 - \<kappa> * \<kappa>"
  proof -
    have "\<kappa> * \<kappa> = d * d / 16 - G * G" using assms(2) by (simp add: power2_eq_square)
    then show ?thesis by linarith
  qed
  have f1: "d * r / 4 * (c * \<kappa>) = d * c / 4"
  proof -
    have "d * r / 4 * (c * \<kappa>) = d * c / 4 * (\<kappa> * r)" by (simp add: algebra_simps)
    also have "\<dots> = d * c / 4" using hr by simp
    finally show ?thesis .
  qed
  have f2: "G * (G * E * s * r) = E * s * (d * d * r / 16 - \<kappa>)"
  proof -
    have "G * (G * E * s * r) = (G * G) * r * (E * s)" by (simp add: algebra_simps)
    also have "\<dots> = (d * d / 16 - \<kappa> * \<kappa>) * r * (E * s)" using hG by simp
    also have "\<dots> = E * s * (d * d * r / 16 - \<kappa> * (\<kappa> * r))" by (simp add: algebra_simps)
    also have "\<dots> = E * s * (d * d * r / 16 - \<kappa>)" using hr by simp
    finally show ?thesis .
  qed
  have key: "(E * (- gb / 2)) * (c - d * r / 4 * s) + E * (s * \<kappa> - d * r / 4 * (c * \<kappa>))
             = - (gq / 2) * (E * (c - d * r / 4 * s)) - G * (G * E * s * r)"
    by (subst f1, subst f2) (simp only: assms(3,4); algebra)
  show ?thesis using key by (simp only: e1 e2)
qed

lemma ode_alg_b:
  fixes E c s \<kappa> gb d gq gm G :: real
  assumes "\<kappa> \<noteq> 0" and "gb = (gq + gm) / 2" and "d = gq - gm"
  shows "((G * (E * (- gb / 2))) * s + (G * E) * (c * \<kappa>)) / \<kappa>
         = - (gm / 2) * (G * E * s / \<kappa>) + G * (E * (c - d / (4 * \<kappa>) * s))"
proof -
  define r where "r = 1 / \<kappa>"
  have hr: "\<kappa> * r = 1" using assms(1) by (simp add: r_def)
  have e1: "d / (4 * \<kappa>) = d * r / 4" by (simp add: r_def field_simps)
  have e3: "a / \<kappa> = a * r" for a :: real by (simp add: r_def)
  have g1: "(G * E) * (c * \<kappa>) * r = G * E * c"
  proof -
    have "(G * E) * (c * \<kappa>) * r = G * E * c * (\<kappa> * r)" by (simp add: algebra_simps)
    also have "\<dots> = G * E * c" using hr by simp
    finally show ?thesis .
  qed
  have split: "((G * (E * (- gb / 2))) * s + (G * E) * (c * \<kappa>)) * r
               = (G * (E * (- gb / 2))) * s * r + (G * E) * (c * \<kappa>) * r"
    by (simp add: algebra_simps)
  have key: "((G * (E * (- gb / 2))) * s + (G * E) * (c * \<kappa>)) * r
             = - (gm / 2) * (G * E * s * r) + G * (E * (c - d * r / 4 * s))"
    by (subst split, subst g1) (simp only: assms(2,3); algebra)
  show ?thesis using key by (simp only: e1 e3)
qed

theorem over_ode_a:
  fixes G gq gm gb d \<kappa> t :: real
  assumes "gb = (gq + gm) / 2" and "d = gq - gm" and "0 < \<kappa>" and "\<kappa>\<^sup>2 = d\<^sup>2 / 16 - G\<^sup>2"
  shows "((\<lambda>t. a_over gb d \<kappa> t) has_real_derivative
          (- (gq / 2) * a_over gb d \<kappa> t - G * beta_over G gb \<kappa> t)) (at t)"
proof -
  have h: "((\<lambda>t. a_over gb d \<kappa> t) has_real_derivative
        (exp (- gb * t / 2) * (- gb / 2)) * (cosh (\<kappa> * t) - d / (4 * \<kappa>) * sinh (\<kappa> * t))
        + exp (- gb * t / 2) * (sinh (\<kappa> * t) * \<kappa> - d / (4 * \<kappa>) * (cosh (\<kappa> * t) * \<kappa>))) (at t)"
    unfolding a_over_def by (auto intro!: derivative_eq_intros)
  have "(exp (- gb * t / 2) * (- gb / 2)) * (cosh (\<kappa> * t) - d / (4 * \<kappa>) * sinh (\<kappa> * t))
        + exp (- gb * t / 2) * (sinh (\<kappa> * t) * \<kappa> - d / (4 * \<kappa>) * (cosh (\<kappa> * t) * \<kappa>))
        = - (gq / 2) * a_over gb d \<kappa> t - G * beta_over G gb \<kappa> t"
    unfolding a_over_def beta_over_def by (rule ode_alg_a) (use assms in simp_all)
  with h show ?thesis by simp
qed

theorem over_ode_beta:
  fixes G gq gm gb d \<kappa> t :: real
  assumes "gb = (gq + gm) / 2" and "d = gq - gm" and "0 < \<kappa>"
  shows "((\<lambda>t. beta_over G gb \<kappa> t) has_real_derivative
          (- (gm / 2) * beta_over G gb \<kappa> t + G * a_over gb d \<kappa> t)) (at t)"
proof -
  have h: "((\<lambda>t. beta_over G gb \<kappa> t) has_real_derivative
        ((G * (exp (- gb * t / 2) * (- gb / 2))) * sinh (\<kappa> * t) + (G * exp (- gb * t / 2)) * (cosh (\<kappa> * t) * \<kappa>)) / \<kappa>) (at t)"
    unfolding beta_over_def using assms(3) by (auto intro!: derivative_eq_intros)
  have "((G * (exp (- gb * t / 2) * (- gb / 2))) * sinh (\<kappa> * t) + (G * exp (- gb * t / 2)) * (cosh (\<kappa> * t) * \<kappa>)) / \<kappa>
        = - (gm / 2) * beta_over G gb \<kappa> t + G * a_over gb d \<kappa> t"
    unfolding a_over_def beta_over_def by (rule ode_alg_b) (use assms in simp_all)
  with h show ?thesis by simp
qed

section \<open>C. Stopping rule: a(t*) / \<beta>(t*) = gm / (2 G)\<close>

definition a_osc :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "a_osc gb d \<Omega> t = exp (- gb * t / 2) * (cos (\<Omega> * t) - d / (4 * \<Omega>) * sin (\<Omega> * t))"

definition beta_osc :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "beta_osc G gb \<Omega> t = G * exp (- gb * t / 2) * sin (\<Omega> * t) / \<Omega>"

definition a_crit :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "a_crit gb d t = exp (- gb * t / 2) * (1 - d / 4 * t)"

definition beta_crit :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "beta_crit G gb t = G * t * exp (- gb * t / 2)"

text \<open>The common algebra: if @{text "c = gb s / (2 w)"} then @{text "E (c - d s / (4 w)) = gm/(2G) * (G E s / w)"}.\<close>

lemma stop_alg:
  fixes E c s w gb d gq gm G :: real
  assumes "w \<noteq> 0" and "G \<noteq> 0" and "c = gb * s / (2 * w)"
    and "gb = (gq + gm) / 2" and "d = gq - gm"
  shows "E * (c - d / (4 * w) * s) = gm / (2 * G) * (G * E * s / w)"
  using assms(1,2) by (simp add: assms(3,4,5) field_split_simps; argo)

theorem stopping_rule_under:
  fixes G gq gm gb d \<Omega> tstar :: real
  assumes "0 < G" and "0 \<le> gq" and "0 \<le> gm" and "gb = (gq + gm) / 2" and "0 < gb"
    and "d = gq - gm" and "G\<^sup>2 > d\<^sup>2 / 16" and "\<Omega> = sqrt (G\<^sup>2 - d\<^sup>2 / 16)"
    and "tstar = arctan (2 * \<Omega> / gb) / \<Omega>"
  shows "0 < beta_osc G gb \<Omega> tstar"
    and "a_osc gb d \<Omega> tstar = gm / (2 * G) * beta_osc G gb \<Omega> tstar"
    and "a_osc gb d \<Omega> tstar / beta_osc G gb \<Omega> tstar = gm / (2 * G)"
proof -
  have om: "0 < \<Omega>" using assms(7,8) by simp
  have u: "\<Omega> * tstar = arctan (2 * \<Omega> / gb)" using om assms(9) by simp
  have apos: "0 < 2 * \<Omega> / gb" using om assms(5) by simp
  have u0: "0 \<le> \<Omega> * tstar" and u1: "\<Omega> * tstar < pi / 2"
    using u apos arctan_ubound by (auto intro: arctan_monotone' simp: arctan_zero_zero)
  have u0': "0 < \<Omega> * tstar"
    using u apos by (metis arctan_less_iff arctan_zero_zero)
  have spos: "0 < sin (\<Omega> * tstar)" using u0' u1 by (intro sin_gt_zero) auto
  have cpos: "0 < cos (\<Omega> * tstar)" using u0 u1 by (intro cos_gt_zero_pi) auto
  have "tan (\<Omega> * tstar) = 2 * \<Omega> / gb" using u by (simp add: tan_arctan)
  then have "sin (\<Omega> * tstar) / cos (\<Omega> * tstar) = 2 * \<Omega> / gb" by (simp add: tan_def)
  then have hc: "cos (\<Omega> * tstar) = gb * sin (\<Omega> * tstar) / (2 * \<Omega>)"
    using cpos om assms(5) by (simp add: field_simps)
  have bpos: "0 < beta_osc G gb \<Omega> tstar"
    unfolding beta_osc_def using assms(1) spos om by simp
  show "0 < beta_osc G gb \<Omega> tstar" by (rule bpos)
  show eq: "a_osc gb d \<Omega> tstar = gm / (2 * G) * beta_osc G gb \<Omega> tstar"
    unfolding a_osc_def beta_osc_def
    using stop_alg[OF _ _ hc assms(4,6), where G = G and E = "exp (- gb * tstar / 2)"] om assms(1) by simp
  show "a_osc gb d \<Omega> tstar / beta_osc G gb \<Omega> tstar = gm / (2 * G)"
    using eq bpos by simp
qed

theorem stopping_rule_over:
  fixes G gq gm gb d \<kappa> tstar :: real
  assumes "0 < G" and "0 \<le> gq" and "0 \<le> gm" and "gb = (gq + gm) / 2" and "d = gq - gm"
    and "G < \<bar>d\<bar> / 4" and "\<kappa> = sqrt (d\<^sup>2 / 16 - G\<^sup>2)" and "tstar = artanh (2 * \<kappa> / gb) / \<kappa>"
  shows "0 < beta_over G gb \<kappa> tstar"
    and "a_over gb d \<kappa> tstar = gm / (2 * G) * beta_over G gb \<kappa> tstar"
    and "a_over gb d \<kappa> tstar / beta_over G gb \<kappa> tstar = gm / (2 * G)"
proof -
  have P: "0 < \<kappa>" "0 < gb" "2 * \<kappa> < gb"
    using overdamped_parameters[OF assms(1-7)] by simp_all
  have u: "\<kappa> * tstar = artanh (2 * \<kappa> / gb)" using P(1) assms(8) by simp
  have lt1: "\<bar>2 * \<kappa> / gb\<bar> < 1" using P by (simp add: divide_less_eq)
  have apos: "0 < 2 * \<kappa> / gb" using P by simp
  have cpos: "0 < cosh (\<kappa> * tstar)" by (rule cosh_real_pos)
  have "tanh (\<kappa> * tstar) = 2 * \<kappa> / gb" unfolding u using lt1 by (rule tanh_artanh_real)
  then have "sinh (\<kappa> * tstar) / cosh (\<kappa> * tstar) = 2 * \<kappa> / gb" by (simp add: tanh_def)
  then have hc: "cosh (\<kappa> * tstar) = gb * sinh (\<kappa> * tstar) / (2 * \<kappa>)"
    using cpos P(1,2) by (simp add: field_simps)
  have "0 < sinh (\<kappa> * tstar)"
  proof -
    have eqs: "sinh (\<kappa> * tstar) = (2 * \<kappa> / gb) * cosh (\<kappa> * tstar)"
      using \<open>sinh (\<kappa> * tstar) / cosh (\<kappa> * tstar) = 2 * \<kappa> / gb\<close> cpos by (simp add: field_simps)
    show ?thesis by (subst eqs, rule mult_pos_pos[OF apos cpos])
  qed
  then have bpos: "0 < beta_over G gb \<kappa> tstar"
    unfolding beta_over_def using assms(1) P(1) by simp
  show "0 < beta_over G gb \<kappa> tstar" by (rule bpos)
  show eq: "a_over gb d \<kappa> tstar = gm / (2 * G) * beta_over G gb \<kappa> tstar"
    unfolding a_over_def beta_over_def
    using stop_alg[OF _ _ hc assms(4,5), where G = G and E = "exp (- gb * tstar / 2)"] P(1) assms(1) by simp
  show "a_over gb d \<kappa> tstar / beta_over G gb \<kappa> tstar = gm / (2 * G)"
    using eq bpos by simp
qed

theorem stopping_rule_critical:
  fixes G gq gm gb d tstar :: real
  assumes "0 < G" and "gb = (gq + gm) / 2" and "0 < gb" and "d = gq - gm" and "tstar = 2 / gb"
  shows "0 < beta_crit G gb tstar"
    and "a_crit gb d tstar = gm / (2 * G) * beta_crit G gb tstar"
    and "a_crit gb d tstar / beta_crit G gb tstar = gm / (2 * G)"
proof -
  have bpos: "0 < beta_crit G gb tstar"
    unfolding beta_crit_def using assms(1,3,5) by simp
  show "0 < beta_crit G gb tstar" by (rule bpos)
  have e: "d = 2 * gb - 2 * gm" using assms(2,4) by simp
  have gbt: "gb * tstar = 2" using assms(3,5) by simp
  have h1: "1 - d / 4 * tstar = gm / 2 * tstar"
  proof -
    have "d * tstar = 2 * (gb * tstar) - 2 * gm * tstar" by (simp add: e algebra_simps)
    then show ?thesis using gbt by linarith
  qed
  show eq: "a_crit gb d tstar = gm / (2 * G) * beta_crit G gb tstar"
    unfolding a_crit_def beta_crit_def
    by (subst h1) (use assms(1) in \<open>simp add: field_simps\<close>)
  show "a_crit gb d tstar / beta_crit G gb tstar = gm / (2 * G)"
    using eq bpos by simp
qed

section \<open>D. The folk bound in the over-damped case\<close>

lemma sinh_ge_self:
  fixes y :: real
  assumes "0 \<le> y"
  shows "y \<le> sinh y"
proof -
  have "(\<lambda>x. sinh x - x) y \<ge> (\<lambda>x. sinh x - x) 0"
  proof (rule DERIV_nonneg_imp_nondecreasing[OF assms])
    fix x assume x: "0 \<le> x" "x \<le> y"
    have "DERIV (\<lambda>x. sinh x - x) x :> cosh x - 1" by (auto intro!: derivative_eq_intros)
    moreover have "0 \<le> cosh x - 1" using cosh_real_ge_1[of x] by simp
    ultimately show "\<exists>z. DERIV (\<lambda>x. sinh x - x) x :> z \<and> 0 \<le> z" by blast
  qed
  then show ?thesis by simp
qed

theorem folk_bound_over:
  fixes G gq gm gb d \<kappa> t0 :: real
  assumes "0 < G" and "0 \<le> gq" and "0 \<le> gm" and "gb = (gq + gm) / 2" and "d = gq - gm"
    and "G < \<bar>d\<bar> / 4" and "\<kappa> = sqrt (d\<^sup>2 / 16 - G\<^sup>2)" and "t0 = pi / (2 * G)"
  shows "exp (- pi * (gq + gm) / (4 * G)) \<le> pulse_over G gb \<kappa> t0"
proof -
  have kpos: "0 < \<kappa>" using overdamped_parameters(1)[OF assms(1-7)] .
  have t0pos: "0 \<le> t0" using assms(1,8) by simp
  have s: "\<kappa> * t0 \<le> sinh (\<kappa> * t0)" using sinh_ge_self[of "\<kappa> * t0"] kpos t0pos by simp
  have "t0 \<le> sinh (\<kappa> * t0) / \<kappa>" using s kpos by (simp add: le_divide_eq mult.commute)
  then have sq: "t0\<^sup>2 \<le> (sinh (\<kappa> * t0) / \<kappa>)\<^sup>2" using t0pos by (intro power_mono)
  have g: "G\<^sup>2 * t0\<^sup>2 = pi\<^sup>2 / 4"
  proof -
    have "t0\<^sup>2 = pi\<^sup>2 / (4 * G\<^sup>2)" using assms(8) by (simp add: power_divide power_mult_distrib)
    then show ?thesis using assms(1) by (simp add: field_simps)
  qed
  have p: "1 \<le> pi\<^sup>2 / 4"
  proof -
    have "3\<^sup>2 < pi\<^sup>2" using pi_gt3 by (intro power_strict_mono) simp_all
    then show ?thesis by simp
  qed
  have ex: "- gb * t0 = - pi * (gq + gm) / (4 * G)" using assms(1) by (simp add: assms(4,8) field_simps)
  have "exp (- pi * (gq + gm) / (4 * G)) = 1 * exp (- gb * t0)" using ex by simp
  also have "\<dots> \<le> (G\<^sup>2 * t0\<^sup>2) * exp (- gb * t0)" using g p by (intro mult_right_mono) simp_all
  also have "\<dots> \<le> (G\<^sup>2 * (sinh (\<kappa> * t0) / \<kappa>)\<^sup>2) * exp (- gb * t0)"
    using sq by (intro mult_right_mono mult_left_mono) simp_all
  also have "\<dots> = pulse_over G gb \<kappa> t0" unfolding pulse_over_def by (simp add: mult.commute mult.left_commute)
  finally show ?thesis .
qed

end
