(*  Title:      Memory_Access_Dephasing.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Equal relaxation rates with dephasing, from "Exact limits for writing a quantum memory" (C. Marín, draft, November 2026):
    the coherence vector cannot grow, and the resonant pulse is optimal at every fixed duration up to its
    half-transfer time. Reduced real model: X' = -2 w y, y' = -Phi y + 2 w X, |w| <= G, X(0) = 1, y(0) = 0.
*)

theory Memory_Access_Dephasing
  imports Memory_Access_All_Pulses
begin

section \<open>A. The resonant solution in closed form\<close>

definition dp_Om :: "real \<Rightarrow> real \<Rightarrow> real" where
  "dp_Om G \<Phi> = sqrt (4 * G\<^sup>2 - \<Phi>\<^sup>2 / 4)"

definition dp_Xr :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "dp_Xr G \<Phi> t = exp (- \<Phi> * t / 2) * (cos (dp_Om G \<Phi> * t) + \<Phi> / (2 * dp_Om G \<Phi>) * sin (dp_Om G \<Phi> * t))"

definition dp_yr :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "dp_yr G \<Phi> t = 2 * G / dp_Om G \<Phi> * (exp (- \<Phi> * t / 2) * sin (dp_Om G \<Phi> * t))"

text \<open>The first zero of the resonant @{text "X"}: @{text "\<Omega> t = \<pi>/2 + arctan (\<Phi> / (2 \<Omega>))"}, i.e.
  @{text "\<pi> - arctan (2 \<Omega> / \<Phi>)"} for @{text "\<Phi> > 0"} and @{text "\<pi>/2"} for @{text "\<Phi> = 0"}.\<close>

definition dp_thalf :: "real \<Rightarrow> real \<Rightarrow> real" where
  "dp_thalf G \<Phi> = (pi / 2 + arctan (\<Phi> / (2 * dp_Om G \<Phi>))) / dp_Om G \<Phi>"

lemma dp_Om_pos:
  assumes "0 < G" and "0 \<le> \<Phi>" and "\<Phi> < 4 * G"
  shows "0 < dp_Om G \<Phi>" and "(dp_Om G \<Phi>)\<^sup>2 = 4 * G\<^sup>2 - \<Phi>\<^sup>2 / 4"
proof -
  have "\<Phi>\<^sup>2 < (4 * G)\<^sup>2" by (rule power_strict_mono) (use assms in simp_all)
  then have h: "\<Phi>\<^sup>2 / 4 < 4 * G\<^sup>2" by (simp add: power_mult_distrib)
  then show "0 < dp_Om G \<Phi>" unfolding dp_Om_def by simp
  show "(dp_Om G \<Phi>)\<^sup>2 = 4 * G\<^sup>2 - \<Phi>\<^sup>2 / 4" unfolding dp_Om_def using h by (simp add: real_sqrt_pow2)
qed

text \<open>A damped oscillation and its derivative, with abstract constants.\<close>

lemma damped_osc_deriv:
  fixes a om k t :: real
  shows "((\<lambda>s. exp (a * s) * (cos (om * s) + k * sin (om * s))) has_real_derivative
          exp (a * t) * ((a + k * om) * cos (om * t) + (a * k - om) * sin (om * t))) (at t)"
proof -
  have "((\<lambda>s. exp (a * s) * (cos (om * s) + k * sin (om * s))) has_real_derivative
        exp (a * t) * a * (cos (om * t) + k * sin (om * t))
        + exp (a * t) * (- sin (om * t) * om + k * (cos (om * t) * om))) (at t)"
    by (auto intro!: derivative_eq_intros)
  then show ?thesis by (rule DERIV_cong) (simp add: algebra_simps)
qed

lemma damped_sin_deriv:
  fixes a om t :: real
  shows "((\<lambda>s. exp (a * s) * sin (om * s)) has_real_derivative
          exp (a * t) * (a * sin (om * t) + om * cos (om * t))) (at t)"
proof -
  have "((\<lambda>s. exp (a * s) * sin (om * s)) has_real_derivative
        exp (a * t) * a * sin (om * t) + exp (a * t) * (cos (om * t) * om)) (at t)"
    by (auto intro!: derivative_eq_intros)
  then show ?thesis by (rule DERIV_cong) (simp add: algebra_simps)
qed

lemma dp_Xr_deriv:
  assumes "0 < G" and "0 \<le> \<Phi>" and "\<Phi> < 4 * G"
  shows "(dp_Xr G \<Phi> has_real_derivative - 2 * G * dp_yr G \<Phi> t) (at t)"
proof -
  define om where "om = dp_Om G \<Phi>"
  have om0: "0 < om" and om2: "om\<^sup>2 = 4 * G\<^sup>2 - \<Phi>\<^sup>2 / 4"
    unfolding om_def using dp_Om_pos[OF assms] by simp_all
  have h: "((\<lambda>s. exp ((- \<Phi> / 2) * s) * (cos (om * s) + (\<Phi> / (2 * om)) * sin (om * s))) has_real_derivative
          exp ((- \<Phi> / 2) * t) * (((- \<Phi> / 2) + (\<Phi> / (2 * om)) * om) * cos (om * t)
            + ((- \<Phi> / 2) * (\<Phi> / (2 * om)) - om) * sin (om * t))) (at t)"
    by (rule damped_osc_deriv)
  have c1: "(- \<Phi> / 2) + (\<Phi> / (2 * om)) * om = 0" using om0 by (simp add: field_simps)
  have c2: "(- \<Phi> / 2) * (\<Phi> / (2 * om)) - om = - (4 * G\<^sup>2) / om"
  proof -
    have "(- \<Phi> / 2) * (\<Phi> / (2 * om)) - om = - (\<Phi>\<^sup>2 / 4 + om\<^sup>2) / om"
      using om0 by (simp add: field_simps power2_eq_square)
    also have "\<Phi>\<^sup>2 / 4 + om\<^sup>2 = 4 * G\<^sup>2" using om2 by simp
    finally show ?thesis .
  qed
  have e1: "(\<lambda>s. exp ((- \<Phi> / 2) * s) * (cos (om * s) + (\<Phi> / (2 * om)) * sin (om * s))) = dp_Xr G \<Phi>"
    unfolding dp_Xr_def om_def by (rule ext) (simp add: mult.commute)
  have "(dp_Xr G \<Phi> has_real_derivative exp ((- \<Phi> / 2) * t) * (- (4 * G\<^sup>2) / om * sin (om * t))) (at t)"
    using h unfolding e1 c1 c2 by simp
  then show ?thesis unfolding dp_yr_def om_def[symmetric] by (rule DERIV_cong) (simp add: field_simps power2_eq_square)
qed

lemma dp_yr_deriv:
  assumes "0 < G" and "0 \<le> \<Phi>" and "\<Phi> < 4 * G"
  shows "(dp_yr G \<Phi> has_real_derivative - \<Phi> * dp_yr G \<Phi> t + 2 * G * dp_Xr G \<Phi> t) (at t)"
proof -
  define om where "om = dp_Om G \<Phi>"
  have om0: "0 < om" using dp_Om_pos[OF assms] unfolding om_def by simp
  have h: "((\<lambda>s. 2 * G / om * (exp ((- \<Phi> / 2) * s) * sin (om * s))) has_real_derivative
          2 * G / om * (exp ((- \<Phi> / 2) * t) * ((- \<Phi> / 2) * sin (om * t) + om * cos (om * t)))) (at t)"
    by (rule DERIV_cmult[OF damped_sin_deriv])
  have e1: "(\<lambda>s. 2 * G / om * (exp ((- \<Phi> / 2) * s) * sin (om * s))) = dp_yr G \<Phi>"
    unfolding dp_yr_def om_def by (rule ext) (simp add: mult.commute)
  show ?thesis using h unfolding e1 by (rule DERIV_cong)
    (use om0 in \<open>simp add: dp_yr_def dp_Xr_def om_def[symmetric] field_simps\<close>)
qed

lemma dp_Xr_0: "dp_Xr G \<Phi> 0 = 1" unfolding dp_Xr_def by simp
lemma dp_yr_0: "dp_yr G \<Phi> 0 = 0" unfolding dp_yr_def by simp

section \<open>B. Monotonicity tools\<close>

lemma mono_nonneg:
  fixes g :: "real \<Rightarrow> real" and a b :: real
  assumes "a \<le> b" and "continuous_on {a..b} g"
    and "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> \<exists>D. (g has_real_derivative D) (at x) \<and> 0 \<le> D"
  shows "g a \<le> g b"
proof (cases "a = b")
  case True then show ?thesis by simp
next
  case False
  then have ab: "a < b" using assms(1) by simp
  have step: "\<forall>x\<in>{a<..<b}. \<exists>D. (g has_real_derivative D) (at x) \<and> 0 \<le> D" using assms(3) by simp
  obtain D where D: "\<And>x. x \<in> {a<..<b} \<Longrightarrow> (g has_real_derivative D x) (at x) \<and> 0 \<le> D x"
    using step by (metis bchoice)
  have hd: "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> (g has_derivative (\<lambda>h. D x * h)) (at x)"
  proof -
    fix x assume x: "a < x" "x < b"
    then have "x \<in> {a<..<b}" by simp
    from has_field_derivative_imp_has_derivative[OF conjunct1[OF D[OF this]]]
    show "(g has_derivative (\<lambda>h. D x * h)) (at x)" .
  qed
  obtain \<xi> where xi: "a < \<xi>" "\<xi> < b" "g b - g a = D \<xi> * (b - a)"
    using mvt[OF ab assms(2) hd] by blast
  have "0 \<le> D \<xi>" using D xi(1,2) by simp
  then have "0 \<le> g b - g a" using xi(3) ab by simp
  then show ?thesis by simp
qed

lemma mono_nonpos:
  fixes g :: "real \<Rightarrow> real" and a b :: real
  assumes "a \<le> b" and "continuous_on {a..b} g"
    and "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> \<exists>D. (g has_real_derivative D) (at x) \<and> D \<le> 0"
  shows "g b \<le> g a"
proof -
  have "(\<lambda>x. - g x) a \<le> (\<lambda>x. - g x) b"
  proof (rule mono_nonneg[OF assms(1)])
    show "continuous_on {a..b} (\<lambda>x. - g x)" by (rule continuous_on_minus[OF assms(2)])
    fix x assume x: "a < x" "x < b"
    obtain D where "(g has_real_derivative D) (at x)" "D \<le> 0" using assms(3)[OF x] by blast
    then show "\<exists>D. ((\<lambda>x. - g x) has_real_derivative D) (at x) \<and> 0 \<le> D"
      by (intro exI[of _ "- D"] conjI DERIV_minus) simp_all
  qed
  then show ?thesis by simp
qed

text \<open>Barrier lemma: a function that starts non-negative cannot become negative if wherever it is negative
  its derivative is non-negative.\<close>

lemma barrier:
  fixes f :: "real \<Rightarrow> real" and a :: real
  assumes "0 \<le> a" and "continuous_on {0..a} f" and "0 \<le> f 0"
    and "\<And>s. 0 < s \<Longrightarrow> s < a \<Longrightarrow> \<exists>D. (f has_real_derivative D) (at s) \<and> (f s < 0 \<longrightarrow> 0 \<le> D)"
  shows "0 \<le> f a"
proof (rule ccontr)
  assume neg: "\<not> 0 \<le> f a"
  define S where "S = {s \<in> {0..a}. (\<lambda>_. 0) s \<le> f s}"
  have Scl: "closed S" unfolding S_def
    by (rule continuous_on_closed_Collect_le[OF continuous_on_const assms(2) closed_atLeastAtMost])
  have Sne: "S \<noteq> {}" using assms(1,3) unfolding S_def by auto
  have Sb: "bdd_above S" unfolding S_def by (intro bdd_aboveI[of _ a]) auto
  define s1 where "s1 = Sup S"
  have s1S: "s1 \<in> S" unfolding s1_def by (rule closed_contains_Sup[OF Sne Sb Scl])
  then have s1a: "0 \<le> s1" "s1 \<le> a" and fs1: "0 \<le> f s1" unfolding S_def by simp_all
  have s1lt: "s1 < a"
  proof (rule ccontr)
    assume "\<not> s1 < a"
    then have "s1 = a" using s1a(2) by simp
    then show False using fs1 neg by simp
  qed
  have after: "\<And>s. s1 < s \<Longrightarrow> s \<le> a \<Longrightarrow> f s < 0"
  proof (rule ccontr)
    fix s assume s: "s1 < s" "s \<le> a" and "\<not> f s < 0"
    then have "s \<in> S" unfolding S_def using s1a(1) by auto
    then have "s \<le> s1" unfolding s1_def by (rule cSup_upper[OF _ Sb])
    then show False using s(1) by simp
  qed
  have "f s1 \<le> f a"
  proof (rule mono_nonneg[OF s1a(2)])
    show "continuous_on {s1..a} f" by (rule continuous_on_subset[OF assms(2)]) (use s1a(1) in auto)
    fix x assume x: "s1 < x" "x < a"
    obtain D where D: "(f has_real_derivative D) (at x)" "f x < 0 \<longrightarrow> 0 \<le> D"
      using assms(4)[of x] x s1a(1) by auto
    have "f x < 0" using after[OF x(1)] x(2) by simp
    then show "\<exists>D. (f has_real_derivative D) (at x) \<and> 0 \<le> D" using D by blast
  qed
  then show False using fs1 neg by simp
qed

section \<open>B2. Oblique polar coordinates: derivatives\<close>

text \<open>For real functions @{text "q1, q2"} the oblique polar coordinates are
  @{text "ln (q1^2+q2^2) / 2"} and @{text "2 arctan (q2 / (sqrt (q1^2+q2^2) + q1))"} (the argument, in the plane
  cut along the non-positive real axis).\<close>

lemma Lg_deriv:
  fixes q1 q2 :: "real \<Rightarrow> real" and a b t :: real
  assumes "(q1 has_real_derivative a) (at t)" and "(q2 has_real_derivative b) (at t)"
    and "0 < (q1 t)\<^sup>2 + (q2 t)\<^sup>2"
  shows "((\<lambda>s. (1 / 2) * ln ((q1 s)\<^sup>2 + (q2 s)\<^sup>2)) has_real_derivative
          (q1 t * a + q2 t * b) / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2)) (at t)"
proof -
  have ds: "((\<lambda>s. (q1 s)\<^sup>2 + (q2 s)\<^sup>2) has_real_derivative (2 * q1 t * a) + (2 * q2 t * b)) (at t)"
    by (rule DERIV_cong[OF DERIV_add[OF DERIV_power[OF assms(1)] DERIV_power[OF assms(2)]]]) simp
  have dl: "((\<lambda>s. ln ((q1 s)\<^sup>2 + (q2 s)\<^sup>2)) has_real_derivative
             (1 / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2)) * ((2 * q1 t * a) + (2 * q2 t * b))) (at t)"
    by (rule DERIV_chain'[OF ds DERIV_ln_divide[OF assms(3)]])
  have ne: "(q1 t)\<^sup>2 + (q2 t)\<^sup>2 \<noteq> 0" by (rule assms(3)[THEN less_imp_neq, THEN not_sym])
  have alg: "\<And>S p q a b :: real. S \<noteq> 0 \<Longrightarrow> (1 / 2) * ((1 / S) * ((2 * p * a) + (2 * q * b))) = (p * a + q * b) / S"
    by (simp add: field_simps)
  have "((\<lambda>s. (1 / 2) * ln ((q1 s)\<^sup>2 + (q2 s)\<^sup>2)) has_real_derivative
        (1 / 2) * ((1 / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2)) * ((2 * q1 t * a) + (2 * q2 t * b)))) (at t)"
    by (rule DERIV_cmult[OF dl])
  then show ?thesis by (rule DERIV_cong[OF _ alg[OF ne]])
qed

lemma Th_deriv:
  fixes q1 q2 :: "real \<Rightarrow> real" and a b t :: real
  assumes d1: "(q1 has_real_derivative a) (at t)" and d2: "(q2 has_real_derivative b) (at t)"
    and slit: "0 < sqrt ((q1 t)\<^sup>2 + (q2 t)\<^sup>2) + q1 t"
  shows "((\<lambda>s. 2 * arctan (q2 s / (sqrt ((q1 s)\<^sup>2 + (q2 s)\<^sup>2) + q1 s))) has_real_derivative
          (q1 t * b - q2 t * a) / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2)) (at t)"
proof -
  define r where "r = sqrt ((q1 t)\<^sup>2 + (q2 t)\<^sup>2)"
  define D where "D = r + q1 t"
  have Dpos: "0 < D" unfolding D_def r_def using slit by simp
  have S0: "0 < (q1 t)\<^sup>2 + (q2 t)\<^sup>2"
  proof (rule ccontr)
    assume nz: "\<not> 0 < (q1 t)\<^sup>2 + (q2 t)\<^sup>2"
    have h0: "0 \<le> (q1 t)\<^sup>2 + (q2 t)\<^sup>2" by simp
    have z: "(q1 t)\<^sup>2 + (q2 t)\<^sup>2 = 0" using nz h0 by linarith
    then have "q1 t = 0" by (simp add: sum_squares_eq_zero_iff)
    moreover have "r = 0" unfolding r_def using z by simp
    ultimately show False using Dpos unfolding D_def by simp
  qed
  have rpos: "0 < r" unfolding r_def using S0 by simp
  have hr: "r\<^sup>2 = (q1 t)\<^sup>2 + (q2 t)\<^sup>2" unfolding r_def using S0 by (simp add: real_sqrt_pow2)
  have ds: "((\<lambda>s. (q1 s)\<^sup>2 + (q2 s)\<^sup>2) has_real_derivative (2 * q1 t * a) + (2 * q2 t * b)) (at t)"
    by (rule DERIV_cong[OF DERIV_add[OF DERIV_power[OF d1] DERIV_power[OF d2]]]) simp
  have dr: "((\<lambda>s. sqrt ((q1 s)\<^sup>2 + (q2 s)\<^sup>2)) has_real_derivative
             inverse r / 2 * ((2 * q1 t * a) + (2 * q2 t * b))) (at t)"
    unfolding r_def by (rule DERIV_chain'[OF ds DERIV_real_sqrt[OF S0]])
  have dD: "((\<lambda>s. sqrt ((q1 s)\<^sup>2 + (q2 s)\<^sup>2) + q1 s) has_real_derivative
             inverse r / 2 * ((2 * q1 t * a) + (2 * q2 t * b)) + a) (at t)"
    by (rule DERIV_add[OF dr d1])
  have Dne: "sqrt ((q1 t)\<^sup>2 + (q2 t)\<^sup>2) + q1 t \<noteq> 0" using slit by simp
  have dq: "((\<lambda>s. q2 s / (sqrt ((q1 s)\<^sup>2 + (q2 s)\<^sup>2) + q1 s)) has_real_derivative
             (b * D - (inverse r / 2 * ((2 * q1 t * a) + (2 * q2 t * b)) + a) * q2 t) / D\<^sup>2) (at t)"
    unfolding D_def r_def
    by (rule DERIV_cong[OF DERIV_quotient[OF d2 dD[unfolded r_def] Dne]]) (simp add: power2_eq_square)
  have dat: "((\<lambda>s. arctan (q2 s / (sqrt ((q1 s)\<^sup>2 + (q2 s)\<^sup>2) + q1 s))) has_real_derivative
              inverse (1 + (q2 t / D)\<^sup>2) * ((b * D - (inverse r / 2 * ((2 * q1 t * a) + (2 * q2 t * b)) + a) * q2 t) / D\<^sup>2)) (at t)"
  proof -
    have "((\<lambda>s. arctan (q2 s / (sqrt ((q1 s)\<^sup>2 + (q2 s)\<^sup>2) + q1 s))) has_real_derivative
          inverse (1 + (q2 t / (sqrt ((q1 t)\<^sup>2 + (q2 t)\<^sup>2) + q1 t))\<^sup>2) * ((b * D - (inverse r / 2 * ((2 * q1 t * a) + (2 * q2 t * b)) + a) * q2 t) / D\<^sup>2)) (at t)"
      by (rule DERIV_chain'[OF dq DERIV_arctan])
    then show ?thesis by (simp add: D_def r_def)
  qed
  have tot: "((\<lambda>s. 2 * arctan (q2 s / (sqrt ((q1 s)\<^sup>2 + (q2 s)\<^sup>2) + q1 s))) has_real_derivative
              2 * (inverse (1 + (q2 t / D)\<^sup>2) * ((b * D - (inverse r / 2 * ((2 * q1 t * a) + (2 * q2 t * b)) + a) * q2 t) / D\<^sup>2))) (at t)"
    by (rule DERIV_cmult[OF dat])
  have e1: "1 + (q2 t / D)\<^sup>2 = 2 * r / D"
  proof -
    have "D\<^sup>2 + (q2 t)\<^sup>2 = 2 * r * D" unfolding D_def using hr by (simp add: power2_eq_square algebra_simps)
    then show ?thesis using Dpos by (simp add: field_simps power2_eq_square)
  qed
  have e3: "(b * D - (inverse r / 2 * ((2 * q1 t * a) + (2 * q2 t * b)) + a) * q2 t) = D * (q1 t * b - q2 t * a) / r"
  proof -
    have key: "r * D - (q2 t)\<^sup>2 - q1 t * D = 0"
    proof -
      have "r * D - (q2 t)\<^sup>2 - q1 t * D = r\<^sup>2 - (q1 t)\<^sup>2 - (q2 t)\<^sup>2" unfolding D_def by (simp add: algebra_simps power2_eq_square)
      then show ?thesis using hr by simp
    qed
    have "(b * D - (inverse r / 2 * ((2 * q1 t * a) + (2 * q2 t * b)) + a) * q2 t) - D * (q1 t * b - q2 t * a) / r
          = b * (r * D - (q2 t)\<^sup>2 - q1 t * D) / r"
      unfolding D_def using rpos by (simp add: field_simps power2_eq_square)
    then show ?thesis using key by simp
  qed
  show ?thesis
  proof (rule DERIV_cong[OF tot])
    have "2 * (inverse (1 + (q2 t / D)\<^sup>2) * ((b * D - (inverse r / 2 * ((2 * q1 t * a) + (2 * q2 t * b)) + a) * q2 t) / D\<^sup>2))
          = 2 * (inverse (2 * r / D) * ((D * (q1 t * b - q2 t * a) / r) / D\<^sup>2))" unfolding e1 e3 by simp
    also have "\<dots> = (q1 t * b - q2 t * a) / r\<^sup>2" using rpos Dpos by (simp add: field_simps power2_eq_square)
    also have "\<dots> = (q1 t * b - q2 t * a) / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2)" unfolding hr by simp
    finally show "2 * (inverse (1 + (q2 t / D)\<^sup>2) * ((b * D - (inverse r / 2 * ((2 * q1 t * a) + (2 * q2 t * b)) + a) * q2 t) / D\<^sup>2))
                  = (q1 t * b - q2 t * a) / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2)" .
  qed
qed

lemma slit_iff:
  fixes q1 q2 :: real
  shows "0 < sqrt (q1\<^sup>2 + q2\<^sup>2) + q1 \<longleftrightarrow> (q2 \<noteq> 0 \<or> 0 < q1)"
proof
  assume h: "0 < sqrt (q1\<^sup>2 + q2\<^sup>2) + q1"
  show "q2 \<noteq> 0 \<or> 0 < q1"
  proof (rule ccontr)
    assume "\<not> (q2 \<noteq> 0 \<or> 0 < q1)"
    then have "q2 = 0" "q1 \<le> 0" by simp_all
    then have "sqrt (q1\<^sup>2 + q2\<^sup>2) = - q1" by (simp add: real_sqrt_abs)
    then show False using h by simp
  qed
next
  assume h: "q2 \<noteq> 0 \<or> 0 < q1"
  show "0 < sqrt (q1\<^sup>2 + q2\<^sup>2) + q1"
  proof (cases "0 < q1")
    case True then show ?thesis by (simp add: add_pos_nonneg)
  next
    case False
    then have q2: "q2 \<noteq> 0" using h by simp
    have "\<bar>q1\<bar> < sqrt (q1\<^sup>2 + q2\<^sup>2)"
    proof -
      have "q1\<^sup>2 < q1\<^sup>2 + q2\<^sup>2" using q2 by simp
      then have "sqrt (q1\<^sup>2) < sqrt (q1\<^sup>2 + q2\<^sup>2)" by (rule real_sqrt_less_mono)
      then show ?thesis by (simp add: real_sqrt_abs)
    qed
    then show ?thesis using abs_ge_minus_self[of q1] by linarith
  qed
qed

section \<open>B3. The algebraic identities of the Lyapunov function\<close>

lemma dp_numV:
  fixes G \<Phi> Om X y w :: real
  assumes "0 < Om" and "Om\<^sup>2 = 4 * G\<^sup>2 - \<Phi>\<^sup>2 / 4"
  shows "((2 * G * X - \<Phi> / 2 * y) * (2 * G * (- 2 * w * y) - \<Phi> / 2 * (- \<Phi> * y + 2 * w * X))
          + (Om * y) * (Om * (- \<Phi> * y + 2 * w * X)))
         + \<Phi> / (2 * Om) * ((2 * G * X - \<Phi> / 2 * y) * (Om * (- \<Phi> * y + 2 * w * X))
          - (Om * y) * (2 * G * (- 2 * w * y) - \<Phi> / 2 * (- \<Phi> * y + 2 * w * X)))
         = 4 * (w - G) * G * \<Phi> * y\<^sup>2"
proof -
  have z: "Om\<^sup>2 - (4 * G\<^sup>2 - \<Phi>\<^sup>2 / 4) = 0" using assms(2) by simp
  have "(((2 * G * X - \<Phi> / 2 * y) * (2 * G * (- 2 * w * y) - \<Phi> / 2 * (- \<Phi> * y + 2 * w * X))
          + (Om * y) * (Om * (- \<Phi> * y + 2 * w * X)))
         + \<Phi> / (2 * Om) * ((2 * G * X - \<Phi> / 2 * y) * (Om * (- \<Phi> * y + 2 * w * X))
          - (Om * y) * (2 * G * (- 2 * w * y) - \<Phi> / 2 * (- \<Phi> * y + 2 * w * X))))
         - 4 * (w - G) * G * \<Phi> * y\<^sup>2 = - y * (\<Phi> * y - 2 * X * w) * (Om\<^sup>2 - (4 * G\<^sup>2 - \<Phi>\<^sup>2 / 4))"
    using assms(1) by (simp add: field_simps power2_eq_square)
  then show ?thesis using z by simp
qed

lemma dp_numT:
  fixes G \<Phi> Om X y w :: real
  assumes "Om\<^sup>2 = 4 * G\<^sup>2 - \<Phi>\<^sup>2 / 4"
  shows "(2 * G * X - \<Phi> / 2 * y) * (Om * (- \<Phi> * y + 2 * w * X))
          - (Om * y) * (2 * G * (- 2 * w * y) - \<Phi> / 2 * (- \<Phi> * y + 2 * w * X))
          - Om * ((2 * G * X - \<Phi> / 2 * y)\<^sup>2 + (Om * y)\<^sup>2)
         = 4 * G * Om * (w - G) * (X\<^sup>2 + y\<^sup>2)"
proof -
  have z: "Om\<^sup>2 - (4 * G\<^sup>2 - \<Phi>\<^sup>2 / 4) = 0" using assms by simp
  have "((2 * G * X - \<Phi> / 2 * y) * (Om * (- \<Phi> * y + 2 * w * X))
          - (Om * y) * (2 * G * (- 2 * w * y) - \<Phi> / 2 * (- \<Phi> * y + 2 * w * X))
          - Om * ((2 * G * X - \<Phi> / 2 * y)\<^sup>2 + (Om * y)\<^sup>2))
         - 4 * G * Om * (w - G) * (X\<^sup>2 + y\<^sup>2) = - Om * y\<^sup>2 * (Om\<^sup>2 - (4 * G\<^sup>2 - \<Phi>\<^sup>2 / 4))"
    by (simp add: field_simps power2_eq_square)
  then show ?thesis using z by simp
qed

section \<open>B4. Trigonometric facts\<close>

lemma polar_gen:
  fixes q1 q2 :: real
  assumes slit: "0 < sqrt (q1\<^sup>2 + q2\<^sup>2) + q1"
  shows "sqrt (q1\<^sup>2 + q2\<^sup>2) * cos (2 * arctan (q2 / (sqrt (q1\<^sup>2 + q2\<^sup>2) + q1))) = q1"
    and "sqrt (q1\<^sup>2 + q2\<^sup>2) * sin (2 * arctan (q2 / (sqrt (q1\<^sup>2 + q2\<^sup>2) + q1))) = q2"
proof -
  define r where "r = sqrt (q1\<^sup>2 + q2\<^sup>2)"
  define D where "D = r + q1"
  define u where "u = q2 / D"
  have Dpos: "0 < D" unfolding D_def r_def using slit by simp
  have S0: "0 < q1\<^sup>2 + q2\<^sup>2"
  proof (rule ccontr)
    assume nz: "\<not> 0 < q1\<^sup>2 + q2\<^sup>2"
    have h0: "0 \<le> q1\<^sup>2 + q2\<^sup>2" by simp
    have z: "q1\<^sup>2 + q2\<^sup>2 = 0" using nz h0 by linarith
    then have "q1 = 0" by (simp add: sum_squares_eq_zero_iff)
    moreover have "r = 0" unfolding r_def using z by simp
    ultimately show False using Dpos unfolding D_def by simp
  qed
  have rpos: "0 < r" unfolding r_def using S0 by simp
  have hr: "r\<^sup>2 = q1\<^sup>2 + q2\<^sup>2" unfolding r_def using S0 by (simp add: real_sqrt_pow2)
  have e1: "1 + u\<^sup>2 = 2 * r / D"
  proof -
    have "D\<^sup>2 + q2\<^sup>2 = 2 * r * D" unfolding D_def using hr by (simp add: power2_eq_square algebra_simps)
    then show ?thesis unfolding u_def using Dpos by (simp add: field_simps power2_eq_square)
  qed
  have e2: "1 - u\<^sup>2 = 2 * q1 / D"
  proof -
    have h: "D\<^sup>2 - q2\<^sup>2 = 2 * q1 * D" unfolding D_def using hr by (simp add: power2_eq_square algebra_simps)
    have Dne: "D \<noteq> 0" using Dpos by simp
    have "1 - u\<^sup>2 = (D\<^sup>2 - q2\<^sup>2) / D\<^sup>2" unfolding u_def using Dne by (simp add: field_simps power_divide)
    also have "\<dots> = 2 * q1 * D / D\<^sup>2" unfolding h by simp
    also have "\<dots> = 2 * q1 / D" using Dne by (simp add: field_simps power2_eq_square)
    finally show ?thesis .
  qed
  have sq: "0 < 1 + u\<^sup>2" by (rule add_pos_nonneg) simp_all
  have c2: "(cos (arctan u))\<^sup>2 = 1 / (1 + u\<^sup>2)" by (simp add: cos_arctan power_divide real_sqrt_pow2)
  have s2: "(sin (arctan u))\<^sup>2 = u\<^sup>2 / (1 + u\<^sup>2)" by (simp add: sin_arctan power_divide real_sqrt_pow2)
  have sc: "sin (arctan u) * cos (arctan u) = u / (1 + u\<^sup>2)"
  proof -
    have "sqrt (1 + u\<^sup>2) * sqrt (1 + u\<^sup>2) = 1 + u\<^sup>2"
      using real_sqrt_pow2[of "1 + u\<^sup>2"] by (simp add: power2_eq_square)
    then show ?thesis by (simp add: sin_arctan cos_arctan field_simps)
  qed
  have cs: "cos (2 * arctan u) = (1 - u\<^sup>2) / (1 + u\<^sup>2)"
  proof -
    have "cos (2 * arctan u) = (cos (arctan u))\<^sup>2 - (sin (arctan u))\<^sup>2" by (rule cos_double)
    also have "\<dots> = 1 / (1 + u\<^sup>2) - u\<^sup>2 / (1 + u\<^sup>2)" using c2 s2 by simp
    also have "\<dots> = (1 - u\<^sup>2) / (1 + u\<^sup>2)" by (simp add: diff_divide_distrib)
    finally show ?thesis .
  qed
  have sn: "sin (2 * arctan u) = 2 * u / (1 + u\<^sup>2)"
  proof -
    have "sin (2 * arctan u) = 2 * sin (arctan u) * cos (arctan u)" by (rule sin_double)
    also have "\<dots> = 2 * (sin (arctan u) * cos (arctan u))" by (simp only: mult.assoc)
    also have "\<dots> = 2 * (u / (1 + u\<^sup>2))" unfolding sc by simp
    finally show ?thesis by simp
  qed
  have rD: "r / D \<noteq> 0" using rpos Dpos by simp
  show "sqrt (q1\<^sup>2 + q2\<^sup>2) * cos (2 * arctan (q2 / (sqrt (q1\<^sup>2 + q2\<^sup>2) + q1))) = q1"
    unfolding r_def[symmetric] D_def[symmetric] u_def[symmetric] cs e1 e2 using rpos Dpos by (simp add: field_simps)
  show "sqrt (q1\<^sup>2 + q2\<^sup>2) * sin (2 * arctan (q2 / (sqrt (q1\<^sup>2 + q2\<^sup>2) + q1))) = q2"
  proof -
    have "r * sin (2 * arctan u) = r * (2 * u / (2 * r / D))" unfolding sn e1 by simp
    also have "\<dots> = q2" unfolding u_def using rpos Dpos by (simp add: field_simps)
    finally show ?thesis unfolding r_def[symmetric] D_def[symmetric] u_def[symmetric] .
  qed
qed

lemma f_pos_gen:
  fixes c \<theta> :: real
  assumes "0 \<le> \<theta>" and "\<theta> < pi / 2 + arctan c"
  shows "0 < cos \<theta> + c * sin \<theta>"
proof -
  define \<phi> where "\<phi> = arctan c"
  have c1: "0 < 1 + c\<^sup>2" by (rule add_pos_nonneg) simp_all
  have cphi: "0 < cos \<phi>" unfolding \<phi>_def using c1 by (simp add: cos_arctan)
  have sphi: "sin \<phi> = c * cos \<phi>" unfolding \<phi>_def by (simp add: sin_arctan cos_arctan)
  have phi_lt: "\<phi> < pi / 2" unfolding \<phi>_def by (rule arctan_ubound)
  have "cos (\<theta> - \<phi>) = cos \<phi> * (cos \<theta> + c * sin \<theta>)"
    by (simp add: cos_diff sphi algebra_simps)
  moreover have "0 < cos (\<theta> - \<phi>)"
  proof (rule cos_gt_zero_pi)
    show "- (pi / 2) < \<theta> - \<phi>" using assms(1) phi_lt by linarith
    show "\<theta> - \<phi> < pi / 2" using assms(2) unfolding \<phi>_def by linarith
  qed
  ultimately have "0 < cos \<phi> * (cos \<theta> + c * sin \<theta>)" by simp
  then show ?thesis using cphi by (simp add: zero_less_mult_iff)
qed

lemma f_zero_gen:
  fixes c :: real
  shows "cos (pi / 2 + arctan c) + c * sin (pi / 2 + arctan c) = 0"
proof -
  have "cos (pi / 2 + arctan c) + c * sin (pi / 2 + arctan c) = - sin (arctan c) + c * cos (arctan c)"
    unfolding cos_add sin_add by simp
  also have "\<dots> = 0" by (simp add: sin_arctan cos_arctan)
  finally show ?thesis .
qed

section \<open>C. The reduced model\<close>

locale dephasing =
  fixes G \<Phi> T :: real and X y w :: "real \<Rightarrow> real"
  assumes G: "0 < G" and Ph0: "0 \<le> \<Phi>" and Ph4: "\<Phi> < 4 * G" and T: "0 \<le> T"
    and dX: "\<And>t. t \<in> {0..T} \<Longrightarrow> (X has_real_derivative - 2 * w t * y t) (at t within {0..T})"
    and dy: "\<And>t. t \<in> {0..T} \<Longrightarrow> (y has_real_derivative - \<Phi> * y t + 2 * w t * X t) (at t within {0..T})"
    and wb: "\<And>t. t \<in> {0..T} \<Longrightarrow> \<bar>w t\<bar> \<le> G"
    and X0: "X 0 = 1" and y0: "y 0 = 0"
begin

abbreviation Om :: real where "Om \<equiv> dp_Om G \<Phi>"

lemma Om_pos: "0 < Om" by (rule dp_Om_pos(1)[OF G Ph0 Ph4])
lemma Om_sq: "Om\<^sup>2 = 4 * G\<^sup>2 - \<Phi>\<^sup>2 / 4" by (rule dp_Om_pos(2)[OF G Ph0 Ph4])

lemma contX: "continuous_on {0..T} X"
  by (subst continuous_on_eq_continuous_within) (auto intro: DERIV_continuous dX)

lemma conty: "continuous_on {0..T} y"
  by (subst continuous_on_eq_continuous_within) (auto intro: DERIV_continuous dy)

lemma dX_int:
  assumes "0 < t" and "t < T"
  shows "(X has_real_derivative - 2 * w t * y t) (at t)"
proof -
  have "t \<in> interior {0..T}" using assms by simp
  then show ?thesis using dX[of t] assms at_within_interior[of t "{0..T}"] by simp
qed

lemma dy_int:
  assumes "0 < t" and "t < T"
  shows "(y has_real_derivative - \<Phi> * y t + 2 * w t * X t) (at t)"
proof -
  have "t \<in> interior {0..T}" using assms by simp
  then show ?thesis using dy[of t] assms at_within_interior[of t "{0..T}"] by simp
qed

lemma wb_int: "\<bar>w t\<bar> \<le> G" if "0 < t" "t < T" for t using wb[of t] that by simp

subsection \<open>P1: the state stays in the unit disc\<close>

definition rho2 :: "real \<Rightarrow> real" where "rho2 t = (X t)\<^sup>2 + (y t)\<^sup>2"

lemma contr2: "continuous_on {0..T} rho2"
  unfolding rho2_def by (intro continuous_intros contX conty)

lemma rho2_deriv:
  assumes "0 < t" and "t < T"
  shows "(rho2 has_real_derivative - 2 * \<Phi> * (y t)\<^sup>2) (at t)"
proof -
  have "(rho2 has_real_derivative (2 * X t * (- 2 * w t * y t)) + (2 * y t * (- \<Phi> * y t + 2 * w t * X t))) (at t)"
    unfolding rho2_def by (rule DERIV_cong[OF DERIV_add[OF DERIV_power[OF dX_int[OF assms]] DERIV_power[OF dy_int[OF assms]]]]) simp
  then show ?thesis by (rule DERIV_cong) (simp add: algebra_simps power2_eq_square)
qed

theorem P1:
  assumes "t \<in> {0..T}"
  shows "(X t)\<^sup>2 + (y t)\<^sup>2 \<le> 1"
proof -
  have tT: "t \<le> T" using assms by simp
  have t0: "0 \<le> t" using assms by simp
  have "rho2 t \<le> rho2 0"
  proof (rule mono_nonpos[OF t0])
    show "continuous_on {0..t} rho2" by (rule continuous_on_subset[OF contr2]) (use tT in auto)
    fix x assume x: "0 < x" "x < t"
    have "(y x)\<^sup>2 \<ge> 0" by simp
    then show "\<exists>D. (rho2 has_real_derivative D) (at x) \<and> D \<le> 0"
      using rho2_deriv[of x] x tT Ph0 by (intro exI[of _ "- 2 * \<Phi> * (y x)\<^sup>2"] conjI) (auto intro: mult_nonneg_nonneg)
  qed
  then show ?thesis unfolding rho2_def using X0 y0 by simp
qed

lemma rho2_pos:
  assumes "t \<in> {0..T}"
  shows "0 < rho2 t"
proof -
  have tT: "t \<le> T" using assms by simp
  have t0: "0 \<le> t" using assms by simp
  define g where "g = (\<lambda>s. rho2 s * exp (2 * \<Phi> * s))"
  have "g 0 \<le> g t"
  proof (rule mono_nonneg[OF t0])
    have "continuous_on {0..T} g" unfolding g_def by (intro continuous_intros contr2)
    then show "continuous_on {0..t} g" by (rule continuous_on_subset) (use tT in auto)
    fix x assume x: "0 < x" "x < t"
    have xT: "x < T" using x tT by simp
    have e: "((\<lambda>s. exp (2 * \<Phi> * s)) has_real_derivative exp (2 * \<Phi> * x) * (2 * \<Phi>)) (at x)"
      by (auto intro!: derivative_eq_intros)
    have "(g has_real_derivative (- 2 * \<Phi> * (y x)\<^sup>2) * exp (2 * \<Phi> * x) + rho2 x * (exp (2 * \<Phi> * x) * (2 * \<Phi>))) (at x)"
      unfolding g_def by (rule DERIV_cong[OF DERIV_mult[OF rho2_deriv[OF x(1) xT] e]]) simp
    moreover have "0 \<le> (- 2 * \<Phi> * (y x)\<^sup>2) * exp (2 * \<Phi> * x) + rho2 x * (exp (2 * \<Phi> * x) * (2 * \<Phi>))"
    proof -
      have "(- 2 * \<Phi> * (y x)\<^sup>2) * exp (2 * \<Phi> * x) + rho2 x * (exp (2 * \<Phi> * x) * (2 * \<Phi>))
            = 2 * \<Phi> * exp (2 * \<Phi> * x) * (X x)\<^sup>2" unfolding rho2_def by (simp add: algebra_simps)
      also have "0 \<le> \<dots>" using Ph0 by (intro mult_nonneg_nonneg) simp_all
      finally show ?thesis .
    qed
    ultimately show "\<exists>D. (g has_real_derivative D) (at x) \<and> 0 \<le> D" by blast
  qed
  then have "1 \<le> rho2 t * exp (2 * \<Phi> * t)" unfolding g_def rho2_def using X0 y0 by simp
  then show ?thesis
  proof -
    assume h: "1 \<le> rho2 t * exp (2 * \<Phi> * t)"
    show ?thesis
    proof (rule ccontr)
      assume "\<not> 0 < rho2 t"
      then have "rho2 t \<le> 0" by simp
      then have "rho2 t * exp (2 * \<Phi> * t) \<le> 0" by (simp add: mult_nonpos_nonneg)
      then show False using h by simp
    qed
  qed
qed

subsection \<open>The oblique coordinates and the Lyapunov function\<close>

text \<open>@{text "q1 = 2 G X - (\<Phi>/2) y"}, @{text "q2 = \<Omega> y"}: for the resonant pulse @{text "z = q1 + i q2"}
  obeys @{text "z' = (-\<Phi>/2 + i \<Omega>) z"}.  @{text Thf} is the argument of @{text z} (plane cut along the
  non-positive real axis) and @{text "Vf = ln |z| + (\<Phi>/(2\<Omega>)) arg z"}.\<close>

definition q1 :: "real \<Rightarrow> real" where "q1 s = 2 * G * X s - \<Phi> / 2 * y s"
definition q2 :: "real \<Rightarrow> real" where "q2 s = Om * y s"
definition Zq :: "real \<Rightarrow> real" where "Zq s = (q1 s)\<^sup>2 + (q2 s)\<^sup>2"
definition Thf :: "real \<Rightarrow> real" where "Thf s = 2 * arctan (q2 s / (sqrt (Zq s) + q1 s))"
definition Vf :: "real \<Rightarrow> real" where "Vf s = (1 / 2) * ln (Zq s) + \<Phi> / (2 * Om) * Thf s"

lemma Zq_pos:
  assumes "s \<in> {0..T}"
  shows "0 < Zq s"
proof (rule ccontr)
  assume "\<not> 0 < Zq s"
  have h0: "0 \<le> Zq s" unfolding Zq_def by simp
  then have z: "Zq s = 0" using \<open>\<not> 0 < Zq s\<close> by linarith
  then have a: "q1 s = 0" and b: "q2 s = 0" unfolding Zq_def by (simp_all add: sum_squares_eq_zero_iff)
  have ys: "y s = 0" using b Om_pos unfolding q2_def by simp
  have "2 * G * X s = 0" using a ys unfolding q1_def by simp
  then have "X s = 0" using G by simp
  then show False using rho2_pos[OF assms] ys unfolding rho2_def by simp
qed

lemma q1_deriv:
  assumes "0 < t" and "t < T"
  shows "(q1 has_real_derivative 2 * G * (- 2 * w t * y t) - \<Phi> / 2 * (- \<Phi> * y t + 2 * w t * X t)) (at t)"
proof -
  have "((\<lambda>s. 2 * G * X s - \<Phi> / 2 * y s) has_real_derivative
        2 * G * (- 2 * w t * y t) - \<Phi> / 2 * (- \<Phi> * y t + 2 * w t * X t)) (at t)"
    by (rule DERIV_diff[OF DERIV_cmult[OF dX_int[OF assms]] DERIV_cmult[OF dy_int[OF assms]]])
  moreover have "q1 = (\<lambda>s. 2 * G * X s - \<Phi> / 2 * y s)" by (rule ext) (simp add: q1_def)
  ultimately show ?thesis by simp
qed

lemma q2_deriv:
  assumes "0 < t" and "t < T"
  shows "(q2 has_real_derivative Om * (- \<Phi> * y t + 2 * w t * X t)) (at t)"
proof -
  have "((\<lambda>s. Om * y s) has_real_derivative Om * (- \<Phi> * y t + 2 * w t * X t)) (at t)"
    by (rule DERIV_cmult[OF dy_int[OF assms]])
  moreover have "q2 = (\<lambda>s. Om * y s)" by (rule ext) (simp add: q2_def)
  ultimately show ?thesis by simp
qed

lemma contq1: "continuous_on {0..T} q1"
  unfolding q1_def by (intro continuous_intros contX conty)

lemma contq2: "continuous_on {0..T} q2"
  unfolding q2_def by (intro continuous_intros conty)

lemma Vf_deriv_nonpos:
  assumes "0 < t" and "t < T" and slit: "0 < sqrt (Zq t) + q1 t"
  shows "\<exists>D. (Vf has_real_derivative D) (at t) \<and> D \<le> 0"
proof -
  define a where "a = 2 * G * (- 2 * w t * y t) - \<Phi> / 2 * (- \<Phi> * y t + 2 * w t * X t)"
  define b where "b = Om * (- \<Phi> * y t + 2 * w t * X t)"
  have Zp: "0 < (q1 t)\<^sup>2 + (q2 t)\<^sup>2" using Zq_pos[of t] assms(1,2) unfolding Zq_def by simp
  have dl: "((\<lambda>s. (1 / 2) * ln ((q1 s)\<^sup>2 + (q2 s)\<^sup>2)) has_real_derivative
             (q1 t * a + q2 t * b) / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2)) (at t)"
    by (rule Lg_deriv[OF q1_deriv[OF assms(1,2)] q2_deriv[OF assms(1,2)] Zp, folded a_def b_def])
  have dth: "((\<lambda>s. 2 * arctan (q2 s / (sqrt ((q1 s)\<^sup>2 + (q2 s)\<^sup>2) + q1 s))) has_real_derivative
              (q1 t * b - q2 t * a) / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2)) (at t)"
    by (rule Th_deriv[OF q1_deriv[OF assms(1,2)] q2_deriv[OF assms(1,2)], folded a_def b_def])
       (use slit in \<open>simp add: Zq_def\<close>)
  have e1: "(\<lambda>s. (1 / 2) * ln ((q1 s)\<^sup>2 + (q2 s)\<^sup>2)) = (\<lambda>s. (1 / 2) * ln (Zq s))" by (simp add: Zq_def)
  have e2: "(\<lambda>s. 2 * arctan (q2 s / (sqrt ((q1 s)\<^sup>2 + (q2 s)\<^sup>2) + q1 s))) = Thf" by (rule ext) (simp add: Thf_def Zq_def)
  have tot: "(Vf has_real_derivative (q1 t * a + q2 t * b) / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2)
              + \<Phi> / (2 * Om) * ((q1 t * b - q2 t * a) / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2))) (at t)"
  proof -
    have "((\<lambda>s. (1 / 2) * ln (Zq s) + \<Phi> / (2 * Om) * Thf s) has_real_derivative
          (q1 t * a + q2 t * b) / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2)
          + \<Phi> / (2 * Om) * ((q1 t * b - q2 t * a) / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2))) (at t)"
      by (rule DERIV_add[OF dl[unfolded e1] DERIV_cmult[OF dth[unfolded e2]]])
    moreover have "Vf = (\<lambda>s. (1 / 2) * ln (Zq s) + \<Phi> / (2 * Om) * Thf s)" by (rule ext) (simp add: Vf_def)
    ultimately show ?thesis by simp
  qed
  have num: "(q1 t * a + q2 t * b) / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2) + \<Phi> / (2 * Om) * ((q1 t * b - q2 t * a) / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2))
             = 4 * (w t - G) * G * \<Phi> * (y t)\<^sup>2 / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2)"
  proof -
    have "(q1 t * a + q2 t * b) + \<Phi> / (2 * Om) * (q1 t * b - q2 t * a) = 4 * (w t - G) * G * \<Phi> * (y t)\<^sup>2"
      unfolding q1_def q2_def a_def b_def by (rule dp_numV[OF Om_pos Om_sq])
    have gen: "\<And>P Q S c :: real. (P / S) + c * (Q / S) = (P + c * Q) / S" by (simp add: add_divide_distrib)
    show ?thesis unfolding gen by (simp only: \<open>(q1 t * a + q2 t * b) + \<Phi> / (2 * Om) * (q1 t * b - q2 t * a) = 4 * (w t - G) * G * \<Phi> * (y t)\<^sup>2\<close>)
  qed
  have wle: "w t - G \<le> 0" using wb[of t] assms(1,2) by simp
  have "4 * (w t - G) * G * \<Phi> * (y t)\<^sup>2 / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2) \<le> 0"
  proof (rule divide_nonpos_nonneg)
    have "(w t - G) * (4 * G * \<Phi> * (y t)\<^sup>2) \<le> 0" using wle G Ph0 by (intro mult_nonpos_nonneg) simp_all
    then show "4 * (w t - G) * G * \<Phi> * (y t)\<^sup>2 \<le> 0" by (simp add: algebra_simps)
    show "0 \<le> (q1 t)\<^sup>2 + (q2 t)\<^sup>2" by simp
  qed
  then show ?thesis using tot num by auto
qed

lemma Thm_deriv_nonpos:
  assumes "0 < t" and "t < T" and slit: "0 < sqrt (Zq t) + q1 t"
  shows "\<exists>D. ((\<lambda>s. Thf s - Om * s) has_real_derivative D) (at t) \<and> D \<le> 0"
proof -
  define a where "a = 2 * G * (- 2 * w t * y t) - \<Phi> / 2 * (- \<Phi> * y t + 2 * w t * X t)"
  define b where "b = Om * (- \<Phi> * y t + 2 * w t * X t)"
  have Zp: "0 < (q1 t)\<^sup>2 + (q2 t)\<^sup>2" using Zq_pos[of t] assms(1,2) unfolding Zq_def by simp
  have dth: "((\<lambda>s. 2 * arctan (q2 s / (sqrt ((q1 s)\<^sup>2 + (q2 s)\<^sup>2) + q1 s))) has_real_derivative
              (q1 t * b - q2 t * a) / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2)) (at t)"
    by (rule Th_deriv[OF q1_deriv[OF assms(1,2)] q2_deriv[OF assms(1,2)], folded a_def b_def])
       (use slit in \<open>simp add: Zq_def\<close>)
  have e2: "(\<lambda>s. 2 * arctan (q2 s / (sqrt ((q1 s)\<^sup>2 + (q2 s)\<^sup>2) + q1 s))) = Thf" by (rule ext) (simp add: Thf_def Zq_def)
  have "((\<lambda>s. Thf s - Om * s) has_real_derivative (q1 t * b - q2 t * a) / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2) - Om * 1) (at t)"
    by (rule DERIV_diff[OF dth[unfolded e2] DERIV_cmult[OF DERIV_ident]])
  moreover have "(q1 t * b - q2 t * a) / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2) - Om * 1
                 = 4 * G * Om * (w t - G) * ((X t)\<^sup>2 + (y t)\<^sup>2) / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2)"
  proof -
    have "q1 t * b - q2 t * a - Om * ((q1 t)\<^sup>2 + (q2 t)\<^sup>2) = 4 * G * Om * (w t - G) * ((X t)\<^sup>2 + (y t)\<^sup>2)"
      unfolding q1_def q2_def a_def b_def by (rule dp_numT[OF Om_sq])
    have gen: "\<And>Q S om :: real. S \<noteq> 0 \<Longrightarrow> Q / S - om * 1 = (Q - om * S) / S" by (simp add: field_simps)
    have ne: "(q1 t)\<^sup>2 + (q2 t)\<^sup>2 \<noteq> 0" by (rule Zp[THEN less_imp_neq, THEN not_sym])
    show ?thesis by (rule trans[OF gen[OF ne]]) (simp only: \<open>q1 t * b - q2 t * a - Om * ((q1 t)\<^sup>2 + (q2 t)\<^sup>2) = 4 * G * Om * (w t - G) * ((X t)\<^sup>2 + (y t)\<^sup>2)\<close>)
  qed
  moreover have "4 * G * Om * (w t - G) * ((X t)\<^sup>2 + (y t)\<^sup>2) / ((q1 t)\<^sup>2 + (q2 t)\<^sup>2) \<le> 0"
  proof (rule divide_nonpos_nonneg)
    have wle: "w t - G \<le> 0" using wb[of t] assms(1,2) by simp
    have "(w t - G) * (4 * G * Om * ((X t)\<^sup>2 + (y t)\<^sup>2)) \<le> 0"
      using wle G Om_pos by (intro mult_nonpos_nonneg) simp_all
    then show "4 * G * Om * (w t - G) * ((X t)\<^sup>2 + (y t)\<^sup>2) \<le> 0" by (simp add: algebra_simps)
    show "0 \<le> (q1 t)\<^sup>2 + (q2 t)\<^sup>2" by simp
  qed
  ultimately show ?thesis by auto
qed

lemma Vf_0: "Vf 0 = ln (2 * G)" and Thf_0: "Thf 0 = 0"
proof -
  have q10: "q1 0 = 2 * G" unfolding q1_def using X0 y0 by simp
  have q20: "q2 0 = 0" unfolding q2_def using y0 by simp
  have Z0: "Zq 0 = (2 * G)\<^sup>2" unfolding Zq_def using q10 q20 by simp
  show "Thf 0 = 0" unfolding Thf_def using q20 by simp
  have "ln ((2 * G)\<^sup>2) = 2 * ln (2 * G)"
  proof -
    have p: "0 < 2 * G" using G by simp
    have "ln ((2 * G)\<^sup>2) = ln ((2 * G) * (2 * G))" by (simp only: power2_eq_square)
    also have "\<dots> = ln (2 * G) + ln (2 * G)"
    proof -
      have Gne: "G \<noteq> 0" using G by simp
      show ?thesis by (rule trans[OF ln_mult[of "2 * G" "2 * G"]]) (simp add: Gne)
    qed
    finally show ?thesis by simp
  qed
  then have "(1 / 2) * ln ((2 * G)\<^sup>2) = ln (2 * G)" by simp
  then show "Vf 0 = ln (2 * G)" unfolding Vf_def Z0 using \<open>Thf 0 = 0\<close> by simp
qed

lemma contVf:
  assumes "t \<le> T" and slit: "\<And>s. s \<in> {0..t} \<Longrightarrow> 0 < sqrt (Zq s) + q1 s"
  shows "continuous_on {0..t} Vf" and "continuous_on {0..t} Thf"
proof -
  have sub: "{0..t} \<subseteq> {0..T}" using assms(1) by auto
  have cq1: "continuous_on {0..t} q1" by (rule continuous_on_subset[OF contq1 sub])
  have cq2: "continuous_on {0..t} q2" by (rule continuous_on_subset[OF contq2 sub])
  have cZ: "continuous_on {0..t} Zq" unfolding Zq_def by (intro continuous_intros cq1 cq2)
  have cD: "continuous_on {0..t} (\<lambda>s. sqrt (Zq s) + q1 s)" by (intro continuous_intros cZ cq1)
  have cq: "continuous_on {0..t} (\<lambda>s. q2 s / (sqrt (Zq s) + q1 s))"
  proof (rule continuous_on_divide[OF cq2 cD])
    show "\<forall>s\<in>{0..t}. sqrt (Zq s) + q1 s \<noteq> 0" using slit by force
  qed
  have cth: "continuous_on {0..t} Thf" unfolding Thf_def
    by (rule continuous_on_mult[OF continuous_on_const continuous_on_arctan[OF cq]])
  show "continuous_on {0..t} Thf" by (rule cth)
  have cln: "continuous_on {0..t} (\<lambda>s. ln (Zq s))"
  proof (rule continuous_on_ln[OF cZ])
    show "\<forall>s\<in>{0..t}. Zq s \<noteq> 0" using Zq_pos sub by force
  qed
  show "continuous_on {0..t} Vf" unfolding Vf_def
    by (rule continuous_on_add[OF continuous_on_mult[OF continuous_on_const cln]
                                  continuous_on_mult[OF continuous_on_const cth]])
qed

theorem lyapunov:
  assumes t: "t \<in> {0..T}" and slit: "\<And>s. s \<in> {0..t} \<Longrightarrow> 0 < sqrt (Zq s) + q1 s"
  shows "Vf t \<le> ln (2 * G)" and "Thf t \<le> Om * t"
proof -
  have tT: "t \<le> T" and t0: "0 \<le> t" using t by simp_all
  have inner: "\<And>x. 0 < x \<Longrightarrow> x < t \<Longrightarrow> 0 < x \<and> x < T \<and> 0 < sqrt (Zq x) + q1 x"
    using tT slit by force
  have "Vf t \<le> Vf 0"
  proof (rule mono_nonpos[OF t0 contVf(1)[OF tT slit]])
    fix x assume x: "0 < x" "x < t"
    show "\<exists>D. (Vf has_real_derivative D) (at x) \<and> D \<le> 0"
      by (rule Vf_deriv_nonpos) (use inner[OF x] in auto)
  qed
  then show "Vf t \<le> ln (2 * G)" using Vf_0 by simp
  have "(\<lambda>s. Thf s - Om * s) t \<le> (\<lambda>s. Thf s - Om * s) 0"
  proof (rule mono_nonpos[OF t0])
    show "continuous_on {0..t} (\<lambda>s. Thf s - Om * s)" by (intro continuous_intros contVf(2)[OF tT slit])
    fix x assume x: "0 < x" "x < t"
    show "\<exists>D. ((\<lambda>s. Thf s - Om * s) has_real_derivative D) (at x) \<and> D \<le> 0"
      by (rule Thm_deriv_nonpos) (use inner[OF x] in auto)
  qed
  then show "Thf t \<le> Om * t" using Thf_0 by simp
qed

subsection \<open>P3: fixed duration\<close>

abbreviation Xr :: "real \<Rightarrow> real" where "Xr \<equiv> dp_Xr G \<Phi>"
abbreviation yr :: "real \<Rightarrow> real" where "yr \<equiv> dp_yr G \<Phi>"
abbreviation t_half :: real where "t_half \<equiv> dp_thalf G \<Phi>"

lemma Om_t_half: "Om * t_half = pi / 2 + arctan (\<Phi> / (2 * Om))"
proof -
  have "Om \<noteq> 0" using Om_pos by simp
  then show ?thesis unfolding dp_thalf_def by simp
qed

lemma t_half_pos: "0 < t_half"
proof -
  have "0 < pi / 2 + arctan (\<Phi> / (2 * Om))" using arctan_lbound[of "\<Phi> / (2 * Om)"] by simp
  then show ?thesis unfolding dp_thalf_def using Om_pos by simp
qed

lemma Xr_pos:
  assumes "0 \<le> s" and "s < t_half"
  shows "0 < Xr s"
proof -
  have "Om * s < Om * t_half" by (rule mult_strict_left_mono[OF assms(2) Om_pos])
  then have lt: "Om * s < pi / 2 + arctan (\<Phi> / (2 * Om))" using Om_t_half by simp
  have "0 < cos (Om * s) + \<Phi> / (2 * Om) * sin (Om * s)"
    by (rule f_pos_gen) (use Om_pos assms(1) lt in simp_all)
  then show ?thesis unfolding dp_Xr_def by simp
qed

lemma yr_pos:
  assumes "0 < s" and "s \<le> t_half"
  shows "0 < yr s"
proof -
  have "Om * s \<le> Om * t_half" by (rule mult_left_mono[OF assms(2) less_imp_le[OF Om_pos]])
  then have le: "Om * s \<le> pi / 2 + arctan (\<Phi> / (2 * Om))" using Om_t_half by simp
  have ub: "arctan (\<Phi> / (2 * Om)) < pi / 2" by (rule arctan_ubound)
  have "0 < sin (Om * s)" by (rule sin_gt_zero) (use Om_pos assms(1) le ub in simp_all)
  then show ?thesis unfolding dp_yr_def using G Om_pos by simp
qed

lemma Xr_half: "Xr t_half = 0"
proof -
  have "cos (Om * t_half) + \<Phi> / (2 * Om) * sin (Om * t_half) = 0"
    unfolding Om_t_half by (rule f_zero_gen)
  then show ?thesis unfolding dp_Xr_def by simp
qed

lemma contXr: "continuous_on {0..T} Xr"
proof (subst continuous_on_eq_continuous_within, intro ballI)
  fix x assume "x \<in> {0..T}"
  show "continuous (at x within {0..T}) Xr"
    by (rule continuous_at_imp_continuous_within[OF DERIV_continuous[OF dp_Xr_deriv[OF G Ph0 Ph4]]])
qed

lemma contyr: "continuous_on {0..T} yr"
proof (subst continuous_on_eq_continuous_within, intro ballI)
  fix x assume "x \<in> {0..T}"
  show "continuous (at x within {0..T}) yr"
    by (rule continuous_at_imp_continuous_within[OF DERIV_continuous[OF dp_yr_deriv[OF G Ph0 Ph4]]])
qed

text \<open>The two cross products with the resonant solution: @{text "X yr - y Xr"} and @{text "X yr + y Xr"}.
  Wherever one is negative its derivative is non-negative, so none of them can become negative.\<close>

lemma xi_nonneg:
  assumes a0: "0 \<le> a" and aT: "a \<le> T" and ah: "a < t_half"
    and Xp: "\<And>s. 0 < s \<Longrightarrow> s < a \<Longrightarrow> 0 < X s"
  shows "0 \<le> X a * yr a - y a * Xr a" and "0 \<le> X a * yr a + y a * Xr a"
proof -
  have sub: "{0..a} \<subseteq> {0..T}" using aT by auto
  have cX: "continuous_on {0..a} X" by (rule continuous_on_subset[OF contX sub])
  have cy: "continuous_on {0..a} y" by (rule continuous_on_subset[OF conty sub])
  have cXr: "continuous_on {0..a} Xr" by (rule continuous_on_subset[OF contXr sub])
  have cyr: "continuous_on {0..a} yr" by (rule continuous_on_subset[OF contyr sub])
  have inner: "\<And>s. 0 < s \<Longrightarrow> s < a \<Longrightarrow> 0 < yr s \<and> 0 < Xr s \<and> w s \<le> G \<and> - G \<le> w s \<and> s < T"
  proof -
    fix s assume s: "0 < s" "s < a"
    have sT: "s < T" using s aT by simp
    have "0 < yr s" by (rule yr_pos) (use s ah in simp_all)
    moreover have "0 < Xr s" by (rule Xr_pos) (use s ah in simp_all)
    moreover have "\<bar>w s\<bar> \<le> G" by (rule wb_int[OF s(1) sT])
    ultimately show "0 < yr s \<and> 0 < Xr s \<and> w s \<le> G \<and> - G \<le> w s \<and> s < T" using sT by (simp add: abs_le_iff)
  qed
  show "0 \<le> X a * yr a - y a * Xr a"
  proof (rule barrier[OF a0])
    show "continuous_on {0..a} (\<lambda>s. X s * yr s - y s * Xr s)"
      by (rule continuous_on_diff[OF continuous_on_mult[OF cX cyr] continuous_on_mult[OF cy cXr]])
    show "0 \<le> X 0 * yr 0 - y 0 * Xr 0" using X0 y0 by (simp add: dp_yr_0 dp_Xr_0)
    fix s assume s: "0 < s" "s < a"
    obtain yrs Xrs wle wge sT where facts: "0 < yr s" "0 < Xr s" "w s \<le> G" "- G \<le> w s" "s < T"
      using inner[OF s] by blast
    define D where "D = ((- 2 * w s * y s) * yr s + X s * (- \<Phi> * yr s + 2 * G * Xr s))
                       - ((- \<Phi> * y s + 2 * w s * X s) * Xr s + y s * (- 2 * G * yr s))"
    have dd: "((\<lambda>s. X s * yr s - y s * Xr s) has_real_derivative D) (at s)"
      unfolding D_def
      by (rule DERIV_cong[OF DERIV_diff[OF DERIV_mult[OF dX_int[OF s(1) facts(5)] dp_yr_deriv[OF G Ph0 Ph4]]
                              DERIV_mult[OF dy_int[OF s(1) facts(5)] dp_Xr_deriv[OF G Ph0 Ph4]]]]) simp
    have Dform: "D = \<Phi> * (y s * Xr s - X s * yr s) + 2 * (G - w s) * (Xr s * X s + yr s * y s)"
      unfolding D_def by (simp add: algebra_simps)
    have key: "X s * yr s - y s * Xr s < 0 \<longrightarrow> 0 \<le> D"
    proof
      assume neg: "X s * yr s - y s * Xr s < 0"
      have Xs: "0 < X s" using Xp[OF s] .
      have h: "0 < y s * Xr s" using neg mult_pos_pos[OF Xs facts(1)] by linarith
      have ypos: "0 < y s"
      proof (rule ccontr)
        assume "\<not> 0 < y s"
        then have "y s \<le> 0" by simp
        then have "y s * Xr s \<le> 0" using facts(2) by (simp add: mult_nonpos_nonneg)
        then show False using h by simp
      qed
      have e1: "0 \<le> \<Phi> * (y s * Xr s - X s * yr s)" using Ph0 neg by (intro mult_nonneg_nonneg) simp_all
      have e2: "0 \<le> 2 * (G - w s) * (Xr s * X s + yr s * y s)"
        using facts(3) Xs ypos facts(1,2) by (intro mult_nonneg_nonneg) (simp_all add: mult_pos_pos add_pos_pos less_imp_le)
      show "0 \<le> D" unfolding Dform using e1 e2 by simp
    qed
    show "\<exists>D. ((\<lambda>s. X s * yr s - y s * Xr s) has_real_derivative D) (at s) \<and>
              (X s * yr s - y s * Xr s < 0 \<longrightarrow> 0 \<le> D)" using dd key by auto
  qed
  show "0 \<le> X a * yr a + y a * Xr a"
  proof (rule barrier[OF a0])
    show "continuous_on {0..a} (\<lambda>s. X s * yr s + y s * Xr s)"
      by (rule continuous_on_add[OF continuous_on_mult[OF cX cyr] continuous_on_mult[OF cy cXr]])
    show "0 \<le> X 0 * yr 0 + y 0 * Xr 0" using X0 y0 by (simp add: dp_yr_0 dp_Xr_0)
    fix s assume s: "0 < s" "s < a"
    obtain yrs Xrs wle wge sT where facts: "0 < yr s" "0 < Xr s" "w s \<le> G" "- G \<le> w s" "s < T"
      using inner[OF s] by blast
    define D where "D = ((- 2 * w s * y s) * yr s + X s * (- \<Phi> * yr s + 2 * G * Xr s))
                       + ((- \<Phi> * y s + 2 * w s * X s) * Xr s + y s * (- 2 * G * yr s))"
    have dd: "((\<lambda>s. X s * yr s + y s * Xr s) has_real_derivative D) (at s)"
      unfolding D_def
      by (rule DERIV_cong[OF DERIV_add[OF DERIV_mult[OF dX_int[OF s(1) facts(5)] dp_yr_deriv[OF G Ph0 Ph4]]
                              DERIV_mult[OF dy_int[OF s(1) facts(5)] dp_Xr_deriv[OF G Ph0 Ph4]]]]) simp
    have Dform: "D = \<Phi> * (- (X s * yr s + y s * Xr s)) + 2 * (G + w s) * (Xr s * X s - yr s * y s)"
      unfolding D_def by (simp add: algebra_simps)
    have key: "X s * yr s + y s * Xr s < 0 \<longrightarrow> 0 \<le> D"
    proof
      assume neg: "X s * yr s + y s * Xr s < 0"
      have Xs: "0 < X s" using Xp[OF s] .
      have h: "y s * Xr s < 0" using neg mult_pos_pos[OF Xs facts(1)] by linarith
      have yneg: "y s < 0"
      proof (rule ccontr)
        assume "\<not> y s < 0"
        then have "0 \<le> y s" by simp
        then have "0 \<le> y s * Xr s" using facts(2) by (simp add: mult_nonneg_nonneg)
        then show False using h by simp
      qed
      have e1: "0 \<le> \<Phi> * (- (X s * yr s + y s * Xr s))" using Ph0 neg by (intro mult_nonneg_nonneg) simp_all
      have e2: "0 \<le> 2 * (G + w s) * (Xr s * X s - yr s * y s)"
      proof -
        have "0 < Xr s * X s" by (rule mult_pos_pos[OF facts(2) Xs])
        moreover have "0 < - (yr s * y s)" using facts(1) yneg by (simp add: mult_pos_neg)
        ultimately have p1: "0 \<le> Xr s * X s - yr s * y s" by simp
        have p2: "0 \<le> 2 * (G + w s)" using facts(4) by simp
        show ?thesis by (rule mult_nonneg_nonneg[OF p2 p1])
      qed
      show "0 \<le> D" unfolding Dform using e1 e2 by simp
    qed
    show "\<exists>D. ((\<lambda>s. X s * yr s + y s * Xr s) has_real_derivative D) (at s) \<and>
              (X s * yr s + y s * Xr s < 0 \<longrightarrow> 0 \<le> D)" using dd key by auto
  qed
qed

lemma nonneg_from_prod:
  fixes a b :: real
  assumes "0 < b" and "0 \<le> a * b"
  shows "0 \<le> a"
proof (rule ccontr)
  assume "\<not> 0 \<le> a"
  then have "a < 0" by simp
  then have "a * b < 0" using assms(1) by (rule mult_neg_pos)
  then show False using assms(2) by simp
qed

lemma X_pos:
  assumes s0: "s \<in> {0..T}" and sh: "s < t_half"
  shows "0 < X s"
proof (rule ccontr)
  assume nX: "\<not> 0 < X s"
  define Z where "Z = {r \<in> {0..s}. X r \<le> (\<lambda>_. 0) r}"
  have sub: "{0..s} \<subseteq> {0..T}" using s0 by auto
  have Zcl: "closed Z" unfolding Z_def
    by (rule continuous_on_closed_Collect_le[OF continuous_on_subset[OF contX sub] continuous_on_const closed_atLeastAtMost])
  have Zne: "Z \<noteq> {}" using s0 nX unfolding Z_def by auto
  have Zb: "bdd_below Z" unfolding Z_def by (intro bdd_belowI[of _ 0]) auto
  define tz where "tz = Inf Z"
  have tzZ: "tz \<in> Z" unfolding tz_def by (rule closed_contains_Inf[OF Zne Zb Zcl])
  then have tz0: "0 \<le> tz" and tz1: "tz \<le> s" and Xtz: "X tz \<le> 0" unfolding Z_def by simp_all
  have tzpos: "0 < tz"
  proof (rule ccontr)
    assume "\<not> 0 < tz"
    then have "tz = 0" using tz0 by simp
    then show False using Xtz X0 by simp
  qed
  have Xp: "\<And>r. 0 < r \<Longrightarrow> r < tz \<Longrightarrow> 0 < X r"
  proof (rule ccontr)
    fix r assume r: "0 < r" "r < tz" and "\<not> 0 < X r"
    then have "r \<in> Z" unfolding Z_def using tz1 by auto
    then have "tz \<le> r" unfolding tz_def by (rule cInf_lower[OF _ Zb])
    then show False using r(2) by simp
  qed
  have aT: "tz \<le> T" using tz1 s0 by simp
  have ah: "tz < t_half" using tz1 sh by simp
  note xi = xi_nonneg[OF tz0 aT ah Xp]
  have yrt: "0 < yr tz" by (rule yr_pos[OF tzpos less_imp_le[OF ah]])
  have Xrt: "0 < Xr tz" by (rule Xr_pos[OF tz0 ah])
  have "0 \<le> X tz * yr tz" using xi by linarith
  then have X0': "0 \<le> X tz" by (rule nonneg_from_prod[OF yrt])
  then have Xz: "X tz = 0" using Xtz by simp
  have "0 \<le> y tz * Xr tz" and "0 \<le> - (y tz * Xr tz)" using xi Xz by simp_all
  then have "y tz * Xr tz = 0" by simp
  then have "y tz = 0" using Xrt by simp
  then show False using rho2_pos[of tz] tz0 tz1 s0 Xz unfolding rho2_def by simp
qed

lemma cone_K:
  assumes s: "s \<in> {0..T}" and sh: "s < t_half"
  shows "\<bar>y s\<bar> * Xr s \<le> X s * yr s"
proof -
  have s0: "0 \<le> s" using s by simp
  have Xp: "\<And>r. 0 < r \<Longrightarrow> r < s \<Longrightarrow> 0 < X r"
  proof -
    fix r :: real assume r: "0 < r" "r < s"
    show "0 < X r" by (rule X_pos) (use r s sh in auto)
  qed
  note xi = xi_nonneg[OF s0 _ sh Xp]
  have x1: "0 \<le> X s * yr s - y s * Xr s" and x2: "0 \<le> X s * yr s + y s * Xr s"
    using xi s by auto
  have "\<bar>y s * Xr s\<bar> \<le> X s * yr s" using x1 x2 by (simp add: abs_le_iff)
  moreover have "\<bar>y s * Xr s\<bar> = \<bar>y s\<bar> * Xr s" using Xr_pos[OF s0 sh] by (simp add: abs_mult)
  ultimately show ?thesis by simp
qed

lemma X_ge_Xr_lt:
  assumes t: "t \<in> {0..T}" and th: "t < t_half"
  shows "Xr t \<le> X t"
proof -
  have t0: "0 \<le> t" and tT: "t \<le> T" using t by simp_all
  have sub: "{0..t} \<subseteq> {0..T}" using tT by auto
  have Xrpos: "\<And>s. s \<in> {0..t} \<Longrightarrow> 0 < Xr s" using Xr_pos th by auto
  have cg: "continuous_on {0..t} (\<lambda>s. X s / Xr s)"
    by (rule continuous_on_divide[OF continuous_on_subset[OF contX sub] continuous_on_subset[OF contXr sub]])
       (use Xrpos in force)
  have "(\<lambda>s. X s / Xr s) 0 \<le> (\<lambda>s. X s / Xr s) t"
  proof (rule mono_nonneg[OF t0 cg])
    fix s assume s: "0 < s" "s < t"
    have sT: "s < T" using s tT by simp
    have sI: "s \<in> {0..T}" using s tT by simp
    have sh: "s < t_half" using s th by simp
    have Xrs: "0 < Xr s" using Xrpos[of s] s by simp
    have yrs: "0 < yr s" by (rule yr_pos) (use s sh in simp_all)
    have K: "\<bar>y s\<bar> * Xr s \<le> X s * yr s" by (rule cone_K[OF sI sh])
    have wbs: "\<bar>w s\<bar> \<le> G" by (rule wb_int[OF s(1) sT])
    have dq: "((\<lambda>s. X s / Xr s) has_real_derivative
               ((- 2 * w s * y s) * Xr s - (- 2 * G * yr s) * X s) / (Xr s)\<^sup>2) (at s)"
      by (rule DERIV_cong[OF DERIV_quotient[OF dX_int[OF s(1) sT] dp_Xr_deriv[OF G Ph0 Ph4] less_imp_neq[OF Xrs, THEN not_sym]]])
         (simp add: power2_eq_square)
    have h1: "w s * y s * Xr s \<le> \<bar>w s\<bar> * (\<bar>y s\<bar> * Xr s)"
    proof -
      have "w s * y s * Xr s \<le> \<bar>w s * y s * Xr s\<bar>" by (rule abs_ge_self)
      also have "\<dots> = \<bar>w s\<bar> * (\<bar>y s\<bar> * Xr s)" by (simp add: abs_mult abs_of_pos[OF Xrs] mult.assoc)
      finally show ?thesis .
    qed
    have h2: "\<bar>w s\<bar> * (\<bar>y s\<bar> * Xr s) \<le> G * (\<bar>y s\<bar> * Xr s)"
      by (rule mult_right_mono[OF wbs mult_nonneg_nonneg[OF abs_ge_zero less_imp_le[OF Xrs]]])
    have h3: "G * (\<bar>y s\<bar> * Xr s) \<le> G * (X s * yr s)" by (rule mult_left_mono[OF K less_imp_le[OF G]])
    have num: "0 \<le> (- 2 * w s * y s) * Xr s - (- 2 * G * yr s) * X s"
    proof -
      have eq: "(- 2 * w s * y s) * Xr s - (- 2 * G * yr s) * X s = 2 * (G * (X s * yr s) - w s * y s * Xr s)"
        by (simp add: algebra_simps)
      have chain: "w s * y s * Xr s \<le> G * (X s * yr s)" by (rule order_trans[OF h1 order_trans[OF h2 h3]])
      have nn: "0 \<le> G * (X s * yr s) - w s * y s * Xr s" by (rule diff_ge_0_iff_ge[THEN iffD2, OF chain])
      show ?thesis unfolding eq using nn by simp
    qed
    show "\<exists>D. ((\<lambda>s. X s / Xr s) has_real_derivative D) (at s) \<and> 0 \<le> D"
      using dq num by (intro exI[of _ "((- 2 * w s * y s) * Xr s - (- 2 * G * yr s) * X s) / (Xr s)\<^sup>2"] conjI)
        (simp_all add: divide_nonneg_nonneg)
  qed
  then have "1 \<le> X t / Xr t" using X0 dp_Xr_0 by simp
  moreover have Xrt: "0 < Xr t" by (rule Xr_pos[OF t0 th])
  ultimately show ?thesis by (simp add: le_divide_eq_1_pos[OF Xrt])
qed

theorem P3:
  assumes t: "t \<in> {0..T}" and th: "t \<le> t_half"
  shows "dp_Xr G \<Phi> t \<le> X t"
proof (cases "t < t_half")
  case True show ?thesis by (rule X_ge_Xr_lt[OF t True])
next
  case False
  then have teq: "t = t_half" using th by simp
  have Xh: "dp_Xr G \<Phi> t = 0" unfolding teq by (rule Xr_half)
  have "0 \<le> X t"
  proof -
    define C where "C = {s \<in> {0..T}. (\<lambda>_. 0) s \<le> X s}"
    have Ccl: "closed C" unfolding C_def
      by (rule continuous_on_closed_Collect_le[OF continuous_on_const contX closed_atLeastAtMost])
    have sub: "{0..<t_half} \<subseteq> C"
    proof
      fix s assume s: "s \<in> {0..<t_half}"
      have "0 < X s" by (rule X_pos) (use s t teq in auto)
      then show "s \<in> C" unfolding C_def using s t teq by auto
    qed
    have "t \<in> closure {0..<t_half}" using t_half_pos teq by (simp add: closure_atLeastLessThan)
    then show ?thesis using closure_minimal[OF sub Ccl] unfolding C_def teq by auto
  qed
  then show ?thesis using Xh by simp
qed

corollary P3_population:
  assumes t: "t \<in> {0..T}" and th: "t \<le> t_half"
  shows "exp (- \<gamma> * t) * (1 - X t) / 2 \<le> exp (- \<gamma> * t) * (1 - dp_Xr G \<Phi> t) / 2"
proof -
  have "dp_Xr G \<Phi> t \<le> X t" by (rule P3[OF t th])
  then have "1 - X t \<le> 1 - dp_Xr G \<Phi> t" by simp
  then show ?thesis by (intro divide_right_mono mult_left_mono) simp_all
qed

subsection \<open>P2: the bound for every duration\<close>

lemma slit_phys:
  assumes "y s \<noteq> 0 \<or> 0 < X s"
  shows "0 < sqrt (Zq s) + q1 s"
proof -
  have "q2 s \<noteq> 0 \<or> 0 < q1 s"
  proof (cases "y s = 0")
    case True
    then have "0 < X s" using assms by simp
    then have "0 < q1 s" unfolding q1_def using True G by simp
    then show ?thesis by simp
  next
    case False
    then have "q2 s \<noteq> 0" unfolding q2_def using Om_pos by simp
    then show ?thesis by simp
  qed
  then show ?thesis unfolding Zq_def by (rule iffD2[OF slit_iff])
qed

lemma P2_core:
  assumes t: "t \<in> {0..T}" and sl: "\<And>s. s \<in> {0..t} \<Longrightarrow> y s \<noteq> 0 \<or> 0 < X s" and yt: "0 \<le> y t"
  shows "0 \<le> X t \<or> (\<exists>s. 0 \<le> s \<and> s \<le> t \<and> Xr s \<le> X t \<and> Xr s \<le> 0)"
proof -
  have tt: "t \<in> {0..t}" using t by simp
  have slZ: "\<And>s. s \<in> {0..t} \<Longrightarrow> 0 < sqrt (Zq s) + q1 s" using sl slit_phys by blast
  note ly = lyapunov[OF t slZ]
  define r where "r = sqrt (Zq t)"
  define th where "th = Thf t"
  define c where "c = \<Phi> / (2 * Om)"
  have Zt: "0 < Zq t" by (rule Zq_pos[OF t])
  have rpos: "0 < r" unfolding r_def using Zt by simp
  have polar: "r * cos th = q1 t" "r * sin th = q2 t"
    using polar_gen[of "q1 t" "q2 t"] slZ[OF tt] unfolding r_def th_def Thf_def Zq_def by simp_all
  have lnr: "ln r = (1 / 2) * ln (Zq t)" unfolding r_def by (simp only: ln_sqrt[OF less_imp_le[OF Zt]])
  have Vt: "ln r + c * th \<le> ln (2 * G)" using ly(1) unfolding Vf_def lnr th_def c_def by simp
  have rle: "r \<le> 2 * G * exp (- (c * th))"
  proof -
    have "r = exp (ln r)" using rpos by simp
    also have "\<dots> \<le> exp (ln (2 * G) - c * th)" using Vt by simp
    also have "\<dots> = 2 * G * exp (- (c * th))" using G by (simp add: exp_diff exp_minus field_simps)
    finally show ?thesis .
  qed
  have th0: "0 \<le> th"
  proof -
    have q2n: "0 \<le> q2 t" unfolding q2_def using Om_pos yt by simp
    have "0 \<le> q2 t / (sqrt (Zq t) + q1 t)" using q2n slZ[OF tt] by (simp add: divide_nonneg_pos)
    then have "arctan 0 \<le> arctan (q2 t / (sqrt (Zq t) + q1 t))" by (rule arctan_monotone')
    then show ?thesis unfolding th_def Thf_def by simp
  qed
  have thle: "th \<le> Om * t" using ly(2) unfolding th_def .
  have key: "2 * G * X t = r * (cos th + c * sin th)"
  proof -
    have "r * (cos th + c * sin th) = q1 t + c * q2 t" using polar by (simp add: algebra_simps)
    also have "\<dots> = 2 * G * X t" unfolding q1_def q2_def c_def using Om_pos by (simp add: field_simps)
    finally show ?thesis by simp
  qed
  show ?thesis
  proof (cases "cos th + c * sin th < 0")
    case True
    define s where "s = th / Om"
    have s0: "0 \<le> s" unfolding s_def using th0 Om_pos by simp
    have st: "s \<le> t" unfolding s_def using thle Om_pos by (simp add: divide_le_eq mult.commute)
    have Oms: "Om * s = th" unfolding s_def using Om_pos by simp
    have ex: "exp (- \<Phi> * s / 2) = exp (- (c * th))"
      unfolding s_def c_def using Om_pos by (simp add: field_simps)
    have Xrs: "Xr s = exp (- (c * th)) * (cos th + c * sin th)"
      unfolding dp_Xr_def Oms ex c_def by simp
    have ineq: "exp (- (c * th)) * (cos th + c * sin th) \<le> X t"
    proof -
      have "(2 * G * exp (- (c * th))) * (cos th + c * sin th) \<le> r * (cos th + c * sin th)"
        by (rule mult_right_mono_neg[OF rle]) (use True in simp)
      then have "2 * G * (exp (- (c * th)) * (cos th + c * sin th)) \<le> 2 * G * X t" using key by (simp add: algebra_simps)
      then show ?thesis using G by simp
    qed
    have "exp (- (c * th)) * (cos th + c * sin th) \<le> 0"
      using True by (intro mult_nonneg_nonpos) simp_all
    then show ?thesis using s0 st Xrs ineq by auto
  next
    case False
    then have "0 \<le> cos th + c * sin th" by simp
    then have "0 \<le> 2 * G * X t" unfolding key using rpos by (intro mult_nonneg_nonneg) simp_all
    then have "0 \<le> X t" using G by (simp add: zero_le_mult_iff)
    then show ?thesis by simp
  qed
qed

lemma P2_gen:
  assumes t: "t \<in> {0..T}" and sl: "\<And>s. s \<in> {0..t} \<Longrightarrow> y s \<noteq> 0 \<or> 0 < X s"
  shows "0 \<le> X t \<or> (\<exists>s. 0 \<le> s \<and> s \<le> t \<and> Xr s \<le> X t \<and> Xr s \<le> 0)"
proof (cases "0 \<le> y t")
  case True show ?thesis by (rule P2_core[OF t sl True])
next
  case False
  interpret mir: dephasing G \<Phi> T X "\<lambda>s. - y s" "\<lambda>s. - w s"
  proof (unfold_locales)
    show "0 < G" by (rule G)
    show "0 \<le> \<Phi>" by (rule Ph0)
    show "\<Phi> < 4 * G" by (rule Ph4)
    show "0 \<le> T" by (rule T)
    fix s assume s: "s \<in> {0..T}"
    have e1: "- 2 * (- w s) * (- y s) = - 2 * w s * y s" by simp
    show "(X has_real_derivative - 2 * (- w s) * (- y s)) (at s within {0..T})" unfolding e1 by (rule dX[OF s])
    have e2: "- (- \<Phi> * y s + 2 * w s * X s) = - \<Phi> * (- y s) + 2 * (- w s) * X s" by simp
    show "((\<lambda>s. - y s) has_real_derivative - \<Phi> * (- y s) + 2 * (- w s) * X s) (at s within {0..T})"
      unfolding e2[symmetric] by (rule DERIV_minus[OF dy[OF s]])
    show "\<bar>- w s\<bar> \<le> G" using wb[OF s] by simp
  next
    show "X 0 = 1" by (rule X0)
    show "- y 0 = 0" using y0 by simp
  qed
  have "0 \<le> - y t" using False by simp
  from mir.P2_core[OF t _ this] sl show ?thesis by auto
qed

theorem P2:
  fixes \<gamma> :: real
  assumes g: "0 \<le> \<gamma>" and t: "t \<in> {0..T}"
    and cond: "t \<le> t_half \<or> (\<forall>s\<in>{0..t}. y s \<noteq> 0 \<or> 0 < X s)"
  shows "\<exists>s. 0 \<le> s \<and> exp (- \<gamma> * t) * (1 - X t) / 2 \<le> exp (- \<gamma> * s) * (1 - dp_Xr G \<Phi> s) / 2"
proof (cases "t \<le> t_half")
  case True
  then show ?thesis using P3_population[OF t True, of \<gamma>] t by (intro exI[of _ t]) simp
next
  case False
  then have sl: "\<And>s. s \<in> {0..t} \<Longrightarrow> y s \<noteq> 0 \<or> 0 < X s" using cond by auto
  have th: "t_half \<le> t" using False by simp
  from P2_gen[OF t sl] show ?thesis
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

section \<open>D. The proposition, free of the locale\<close>

lemma dp_thalf_eq:
  assumes "0 < G" and "0 \<le> \<Phi>" and "\<Phi> < 4 * G"
  shows "dp_Om G \<Phi> * dp_thalf G \<Phi> = pi / 2 + arctan (\<Phi> / (2 * dp_Om G \<Phi>))"
    and "0 < \<Phi> \<Longrightarrow> dp_Om G \<Phi> * dp_thalf G \<Phi> = pi - arctan (2 * dp_Om G \<Phi> / \<Phi>)"
    and "\<Phi> = 0 \<Longrightarrow> dp_thalf G \<Phi> = pi / (2 * dp_Om G \<Phi>)"
proof -
  have om0: "0 < dp_Om G \<Phi>" by (rule dp_Om_pos(1)[OF assms])
  then show e: "dp_Om G \<Phi> * dp_thalf G \<Phi> = pi / 2 + arctan (\<Phi> / (2 * dp_Om G \<Phi>))"
    unfolding dp_thalf_def by simp
  show "0 < \<Phi> \<Longrightarrow> dp_Om G \<Phi> * dp_thalf G \<Phi> = pi - arctan (2 * dp_Om G \<Phi> / \<Phi>)"
  proof -
    assume ph: "0 < \<Phi>"
    have q: "0 < \<Phi> / (2 * dp_Om G \<Phi>)" using ph om0 by simp
    have "arctan (inverse (\<Phi> / (2 * dp_Om G \<Phi>))) = pi / 2 - arctan (\<Phi> / (2 * dp_Om G \<Phi>))"
      by (rule arctan_inverse[OF q])
    moreover have "inverse (\<Phi> / (2 * dp_Om G \<Phi>)) = 2 * dp_Om G \<Phi> / \<Phi>" by (simp add: inverse_divide)
    ultimately show "dp_Om G \<Phi> * dp_thalf G \<Phi> = pi - arctan (2 * dp_Om G \<Phi> / \<Phi>)" using e by simp
  qed
  show "\<Phi> = 0 \<Longrightarrow> dp_thalf G \<Phi> = pi / (2 * dp_Om G \<Phi>)" unfolding dp_thalf_def by simp
qed

theorem memory_dephasing_equal_rates:
  fixes G \<Phi> \<gamma> T t :: real and X y w :: "real \<Rightarrow> real"
  assumes G: "0 < G" and Ph0: "0 \<le> \<Phi>" and Ph4: "\<Phi> < 4 * G" and g: "0 \<le> \<gamma>" and T: "0 \<le> T"
    and dX: "\<And>t. t \<in> {0..T} \<Longrightarrow> (X has_real_derivative - 2 * w t * y t) (at t within {0..T})"
    and dy: "\<And>t. t \<in> {0..T} \<Longrightarrow> (y has_real_derivative - \<Phi> * y t + 2 * w t * X t) (at t within {0..T})"
    and wb: "\<And>t. t \<in> {0..T} \<Longrightarrow> \<bar>w t\<bar> \<le> G"
    and X0: "X 0 = 1" and y0: "y 0 = 0" and t: "t \<in> {0..T}"
  shows "(X t)\<^sup>2 + (y t)\<^sup>2 \<le> 1"
    and "t \<le> dp_thalf G \<Phi> \<Longrightarrow>
         exp (- \<gamma> * t) * (1 - X t) / 2 \<le> exp (- \<gamma> * t) * (1 - dp_Xr G \<Phi> t) / 2"
    and "t \<le> dp_thalf G \<Phi> \<or> (\<forall>s\<in>{0..t}. y s \<noteq> 0 \<or> 0 < X s) \<Longrightarrow>
         \<exists>s. 0 \<le> s \<and> exp (- \<gamma> * t) * (1 - X t) / 2 \<le> exp (- \<gamma> * s) * (1 - dp_Xr G \<Phi> s) / 2"
proof -
  interpret dephasing G \<Phi> T X y w
    by unfold_locales (use assms in \<open>blast+\<close>)
  show "(X t)\<^sup>2 + (y t)\<^sup>2 \<le> 1" by (rule P1[OF t])
  show "t \<le> dp_thalf G \<Phi> \<Longrightarrow>
         exp (- \<gamma> * t) * (1 - X t) / 2 \<le> exp (- \<gamma> * t) * (1 - dp_Xr G \<Phi> t) / 2"
    by (rule P3_population[OF t])
  show "t \<le> dp_thalf G \<Phi> \<or> (\<forall>s\<in>{0..t}. y s \<noteq> 0 \<or> 0 < X s) \<Longrightarrow>
         \<exists>s. 0 \<le> s \<and> exp (- \<gamma> * t) * (1 - X t) / 2 \<le> exp (- \<gamma> * s) * (1 - dp_Xr G \<Phi> s) / 2"
    by (rule P2[OF g t])
qed

end
