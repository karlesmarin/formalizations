(*  Title:      Memory_Access_All_Pulses.thy
    Author:     Carles Marín
    Copyright:  Carles Marín
    License:    BSD-3-Clause

    Theorem 1 of the memory-floors note (bound over ALL pulses), relaxation only.
*)
theory Memory_Access_All_Pulses
  imports Memory_Access_Floors
begin

section \<open>A. Skew-polar Lyapunov function\<close>

text \<open>With @{text "a = sqrt A"}, @{text "b = sqrt B"}, the linear map
  @{text "y1 = G a + (d/4) b"}, @{text "y2 = \<Omega> b"} turns the matrix of the resonant pulse into a rotation.
  The Lyapunov function is @{text "ln |y| + (gb / (2 \<Omega>)) arg y"}, with @{text "arg y = pi/2 - arctan (y1/y2)"}
  (formula @{text lyap}); for every admissible control it does not increase, and the bound on @{text B}
  follows from the damped-sine lemma of the base theory.\<close>

definition lyap :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "lyap G gq gm \<Omega> a b =
     (1 / 2) * ln ((G * a + (gq - gm) / 4 * b)\<^sup>2 + (\<Omega> * b)\<^sup>2)
     + (gq + gm) / (4 * \<Omega>) * (pi / 2 - arctan ((G * a + (gq - gm) / 4 * b) / (\<Omega> * b)))"

definition peak :: "real \<Rightarrow> real" where
  "peak k = 4 / (4 + k\<^sup>2) * exp (- k * arctan (2 / k))"

lemma lyap_alg:
  fixes S c y1 y2 D1 D2 :: real
  assumes "S \<noteq> 0"
  shows "(1 / 2) * ((1 / S) * ((2 * y1 * D1) + (2 * y2 * D2))) + c * (0 - (D1 * y2 - y1 * D2) / S)
         = ((y1 - c * y2) * D1 + (y2 + c * y1) * D2) / S"
  using assms by (simp add: field_simps)

lemma lyap_has_derivative:
  fixes G gq gm \<Omega> :: real and a b :: "real \<Rightarrow> real" and a' b' t :: real
  assumes "0 < \<Omega>" and "0 < b t"
    and "(a has_real_derivative a') (at t)" and "(b has_real_derivative b') (at t)"
  shows "((\<lambda>s. lyap G gq gm \<Omega> (a s) (b s)) has_real_derivative
     (((G * a t + (gq - gm) / 4 * b t) - (gq + gm) / (4 * \<Omega>) * (\<Omega> * b t)) * (G * a' + (gq - gm) / 4 * b')
      + ((\<Omega> * b t) + (gq + gm) / (4 * \<Omega>) * (G * a t + (gq - gm) / 4 * b t)) * (\<Omega> * b'))
     / ((G * a t + (gq - gm) / 4 * b t)\<^sup>2 + (\<Omega> * b t)\<^sup>2)) (at t)"
proof -
  define y1 where "y1 = (\<lambda>s. G * a s + (gq - gm) / 4 * b s)"
  define y2 where "y2 = (\<lambda>s. \<Omega> * b s)"
  have y2pos: "0 < y2 t" unfolding y2_def using assms(1,2) by simp
  have n0: "y2 t \<noteq> 0" using y2pos by simp
  have pos: "0 < (y1 t)\<^sup>2 + (y2 t)\<^sup>2" using y2pos by (simp add: add_nonneg_pos)
  have d1: "(y1 has_real_derivative G * a' + (gq - gm) / 4 * b') (at t)"
    unfolding y1_def by (intro DERIV_add DERIV_cmult assms(3,4))
  have d2: "(y2 has_real_derivative \<Omega> * b') (at t)"
    unfolding y2_def by (intro DERIV_cmult assms(4))
  have dq: "((\<lambda>s. y1 s / y2 s) has_real_derivative
             ((G * a' + (gq - gm) / 4 * b') * y2 t - y1 t * (\<Omega> * b')) / (y2 t)\<^sup>2) (at t)"
    by (rule DERIV_cong[OF DERIV_quotient[OF d1 d2 n0]]) (simp add: power2_eq_square mult.commute)
  have dat: "((\<lambda>s. arctan (y1 s / y2 s)) has_real_derivative
              inverse (1 + (y1 t / y2 t)\<^sup>2) * (((G * a' + (gq - gm) / 4 * b') * y2 t - y1 t * (\<Omega> * b')) / (y2 t)\<^sup>2)) (at t)"
    by (rule DERIV_chain'[OF dq DERIV_arctan])
  have ds: "((\<lambda>s. (y1 s)\<^sup>2 + (y2 s)\<^sup>2) has_real_derivative
              (2 * y1 t * (G * a' + (gq - gm) / 4 * b')) + (2 * y2 t * (\<Omega> * b'))) (at t)"
    by (rule DERIV_cong[OF DERIV_add[OF DERIV_power[OF d1] DERIV_power[OF d2]]]) simp
  have dl: "((\<lambda>s. ln ((y1 s)\<^sup>2 + (y2 s)\<^sup>2)) has_real_derivative
              (1 / ((y1 t)\<^sup>2 + (y2 t)\<^sup>2)) * ((2 * y1 t * (G * a' + (gq - gm) / 4 * b')) + (2 * y2 t * (\<Omega> * b')))) (at t)"
    by (rule DERIV_chain'[OF ds DERIV_ln_divide[OF pos]])
  have tot: "((\<lambda>s. (1 / 2) * ln ((y1 s)\<^sup>2 + (y2 s)\<^sup>2) + (gq + gm) / (4 * \<Omega>) * (pi / 2 - arctan (y1 s / y2 s))) has_real_derivative
     ((1 / 2) * ((1 / ((y1 t)\<^sup>2 + (y2 t)\<^sup>2)) * ((2 * y1 t * (G * a' + (gq - gm) / 4 * b')) + (2 * y2 t * (\<Omega> * b'))))
      + (gq + gm) / (4 * \<Omega>) * (0 - inverse (1 + (y1 t / y2 t)\<^sup>2) * (((G * a' + (gq - gm) / 4 * b') * y2 t - y1 t * (\<Omega> * b')) / (y2 t)\<^sup>2)))) (at t)"
    by (rule DERIV_add[OF DERIV_cmult[OF dl] DERIV_cmult[OF DERIV_diff[OF DERIV_const dat]]])
  have h1: "inverse (1 + (y1 t / y2 t)\<^sup>2) * (X / (y2 t)\<^sup>2) = X / ((y1 t)\<^sup>2 + (y2 t)\<^sup>2)" for X :: real
    using n0 pos by (simp add: field_simps power2_eq_square)
  have eq: "(1 / 2) * ((1 / ((y1 t)\<^sup>2 + (y2 t)\<^sup>2)) * ((2 * y1 t * (G * a' + (gq - gm) / 4 * b')) + (2 * y2 t * (\<Omega> * b'))))
      + (gq + gm) / (4 * \<Omega>) * (0 - inverse (1 + (y1 t / y2 t)\<^sup>2) * (((G * a' + (gq - gm) / 4 * b') * y2 t - y1 t * (\<Omega> * b')) / (y2 t)\<^sup>2))
      = ((y1 t - (gq + gm) / (4 * \<Omega>) * y2 t) * (G * a' + (gq - gm) / 4 * b')
         + (y2 t + (gq + gm) / (4 * \<Omega>) * y1 t) * (\<Omega> * b')) / ((y1 t)\<^sup>2 + (y2 t)\<^sup>2)"
    unfolding h1 by (rule lyap_alg[OF pos[THEN less_imp_neq, symmetric]])
  have funeq: "(\<lambda>s. lyap G gq gm \<Omega> (a s) (b s)) = (\<lambda>s. (1 / 2) * ln ((y1 s)\<^sup>2 + (y2 s)\<^sup>2) + (gq + gm) / (4 * \<Omega>) * (pi / 2 - arctan (y1 s / y2 s)))"
    unfolding lyap_def y1_def y2_def by simp
  show ?thesis using tot eq unfolding funeq y1_def y2_def by simp
qed

lemma lyap_num_identity:
  fixes G gq gm \<Omega> a b u :: real
  assumes "0 < a" and "0 < b" and "0 < \<Omega>" and "\<Omega>\<^sup>2 = G\<^sup>2 - (gq - gm)\<^sup>2 / 16"
  shows "((G * a + (gq - gm) / 4 * b) - (gq + gm) / (4 * \<Omega>) * (\<Omega> * b))
           * (G * ((- gq * a\<^sup>2 - 2 * u) / (2 * a)) + (gq - gm) / 4 * ((- gm * b\<^sup>2 + 2 * u) / (2 * b)))
         + ((\<Omega> * b) + (gq + gm) / (4 * \<Omega>) * (G * a + (gq - gm) / 4 * b)) * (\<Omega> * ((- gm * b\<^sup>2 + 2 * u) / (2 * b)))
         = G * (gq * a\<^sup>2 + gm * b\<^sup>2) / (2 * a * b) * (u - G * a * b)"
proof -
  have z: "16 * G\<^sup>2 - 16 * \<Omega>\<^sup>2 - (gq - gm)\<^sup>2 = 0" using assms(4) by simp
  have key: "(((G * a + (gq - gm) / 4 * b) - (gq + gm) / (4 * \<Omega>) * (\<Omega> * b))
           * (G * ((- gq * a\<^sup>2 - 2 * u) / (2 * a)) + (gq - gm) / 4 * ((- gm * b\<^sup>2 + 2 * u) / (2 * b)))
         + ((\<Omega> * b) + (gq + gm) / (4 * \<Omega>) * (G * a + (gq - gm) / 4 * b)) * (\<Omega> * ((- gm * b\<^sup>2 + 2 * u) / (2 * b))))
         - G * (gq * a\<^sup>2 + gm * b\<^sup>2) / (2 * a * b) * (u - G * a * b)
         = (b\<^sup>2 * gm - 2 * u) * (16 * G\<^sup>2 - 16 * \<Omega>\<^sup>2 - (gq - gm)\<^sup>2) / 32"
    using assms(1,2,3) by (simp add: field_simps power2_eq_square)
  then show ?thesis using z by simp
qed

lemma lyap_num_nonpos:
  fixes G gq gm \<Omega> a b u :: real
  assumes "0 < a" and "0 < b" and "0 < \<Omega>" and "\<Omega>\<^sup>2 = G\<^sup>2 - (gq - gm)\<^sup>2 / 16"
    and "0 < G" and "0 \<le> gq" and "0 \<le> gm" and "u \<le> G * a * b"
  shows "((G * a + (gq - gm) / 4 * b) - (gq + gm) / (4 * \<Omega>) * (\<Omega> * b))
           * (G * ((- gq * a\<^sup>2 - 2 * u) / (2 * a)) + (gq - gm) / 4 * ((- gm * b\<^sup>2 + 2 * u) / (2 * b)))
         + ((\<Omega> * b) + (gq + gm) / (4 * \<Omega>) * (G * a + (gq - gm) / 4 * b)) * (\<Omega> * ((- gm * b\<^sup>2 + 2 * u) / (2 * b))) \<le> 0"
proof -
  have "0 \<le> G * (gq * a\<^sup>2 + gm * b\<^sup>2) / (2 * a * b)"
    using assms by (intro divide_nonneg_pos mult_nonneg_nonneg add_nonneg_nonneg) simp_all
  moreover have "u - G * a * b \<le> 0" using assms(8) by simp
  ultimately show ?thesis
    using lyap_num_identity[OF assms(1,2,3,4), of u] mult_nonneg_nonpos by metis
qed

lemma arctan_le_id:
  fixes x :: real
  assumes "0 \<le> x"
  shows "arctan x \<le> x"
proof -
  have "(\<lambda>y. y - arctan y) 0 \<le> (\<lambda>y. y - arctan y) x"
  proof (rule DERIV_nonneg_imp_nondecreasing[OF assms])
    fix y :: real assume "0 \<le> y" "y \<le> x"
    have "DERIV (\<lambda>y. y - arctan y) y :> 1 - inverse (1 + y\<^sup>2)"
      by (rule DERIV_diff[OF DERIV_ident DERIV_arctan])
    moreover have "0 \<le> 1 - inverse (1 + y\<^sup>2)"
    proof -
      have "inverse (1 + y\<^sup>2) \<le> 1" by (simp add: inverse_le_1_iff)
      then show ?thesis by simp
    qed
    ultimately show "\<exists>D. DERIV (\<lambda>y. y - arctan y) y :> D \<and> 0 \<le> D" by blast
  qed
  then show ?thesis by simp
qed

section \<open>B. From the Lyapunov bound to the damped sine\<close>

lemma lyap_bound:
  fixes G gq gm \<Omega> a b c :: real
  assumes "0 < \<Omega>" and "0 < b" and "0 < gq + gm" and "lyap G gq gm \<Omega> a b \<le> c"
  shows "\<Omega>\<^sup>2 * b\<^sup>2 \<le> exp (2 * c) * peak ((gq + gm) / 2 / \<Omega>)"
proof -
  define y1 where "y1 = G * a + (gq - gm) / 4 * b"
  define y2 where "y2 = \<Omega> * b"
  define k where "k = (gq + gm) / 2 / \<Omega>"
  define \<phi> where "\<phi> = pi / 2 - arctan (y1 / y2)"
  have y2pos: "0 < y2" unfolding y2_def using assms(1,2) by simp
  have kpos: "0 < k" unfolding k_def using assms(1,3) by simp
  have S: "0 < y1\<^sup>2 + y2\<^sup>2" using y2pos by (simp add: add_nonneg_pos)
  have phi0: "0 \<le> \<phi>" unfolding \<phi>_def using arctan_ubound[of "y1 / y2"] by simp
  have hk: "(gq + gm) / (4 * \<Omega>) = k / 2" unfolding k_def using assms(1) by (simp add: field_simps)
  have lyp: "lyap G gq gm \<Omega> a b = (1 / 2) * ln (y1\<^sup>2 + y2\<^sup>2) + (k / 2) * \<phi>"
    unfolding lyap_def y1_def y2_def \<phi>_def hk by simp
  have l: "ln (y1\<^sup>2 + y2\<^sup>2) \<le> 2 * c - k * \<phi>" using assms(4) lyp by linarith
  have e1: "y1\<^sup>2 + y2\<^sup>2 \<le> exp (2 * c) * exp (- k * \<phi>)"
  proof -
    have "y1\<^sup>2 + y2\<^sup>2 = exp (ln (y1\<^sup>2 + y2\<^sup>2))" using S by simp
    also have "\<dots> \<le> exp (2 * c - k * \<phi>)" using l by simp
    also have "\<dots> = exp (2 * c) * exp (- k * \<phi>)" by (simp add: exp_add[symmetric] algebra_simps)
    finally show ?thesis .
  qed
  have sin2: "(sin \<phi>)\<^sup>2 = y2\<^sup>2 / (y1\<^sup>2 + y2\<^sup>2)"
  proof -
    have "sin \<phi> = cos (arctan (y1 / y2))" unfolding \<phi>_def by (simp add: sin_diff)
    then have "(sin \<phi>)\<^sup>2 = (1 / sqrt (1 + (y1 / y2)\<^sup>2))\<^sup>2" by (simp add: cos_arctan)
    also have "\<dots> = 1 / (1 + (y1 / y2)\<^sup>2)"
      by (simp add: power_divide real_sqrt_pow2 add_nonneg_nonneg)
    also have "\<dots> = y2\<^sup>2 / (y1\<^sup>2 + y2\<^sup>2)" using y2pos by (simp add: field_simps power2_eq_square)
    finally show ?thesis .
  qed
  have y2sq: "y2\<^sup>2 = (y1\<^sup>2 + y2\<^sup>2) * (sin \<phi>)\<^sup>2" using sin2 S by simp
  have "(sin \<phi>)\<^sup>2 \<ge> 0" by simp
  then have "y2\<^sup>2 \<le> exp (2 * c) * exp (- k * \<phi>) * (sin \<phi>)\<^sup>2"
    using y2sq e1 by (metis mult_right_mono)
  also have "\<dots> = exp (2 * c) * damped_sine k \<phi>" unfolding damped_sine_def by simp
  also have "\<dots> \<le> exp (2 * c) * peak k"
    using damped_sine_le_peak[OF kpos phi0] unfolding peak_def by (intro mult_left_mono) simp_all
  finally have "y2\<^sup>2 \<le> exp (2 * c) * peak k" .
  moreover have "y2\<^sup>2 = \<Omega>\<^sup>2 * b\<^sup>2" unfolding y2_def by (simp add: power_mult_distrib)
  ultimately show ?thesis unfolding k_def by simp
qed

lemma peak_const:
  fixes G gq gm \<Omega> :: real
  assumes "\<Omega> = sqrt (G\<^sup>2 - (gq - gm)\<^sup>2 / 16)" and "(gq - gm)\<^sup>2 / 16 < G\<^sup>2" and "0 < gq + gm"
  shows "G\<^sup>2 / \<Omega>\<^sup>2 * peak ((gq + gm) / 2 / \<Omega>)
         = 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- (((gq + gm) / 2) / \<Omega>) * arctan (2 * \<Omega> / ((gq + gm) / 2)))"
proof -
  have om: "0 < \<Omega>" using assms(1,2) by simp
  have gbp: "0 < (gq + gm) / 2" using assms(3) by simp
  have c1: "4 * \<Omega>\<^sup>2 + ((gq + gm) / 2)\<^sup>2 = 4 * G\<^sup>2 + gq * gm"
    using resonant_omega_identity[OF refl refl assms(2) assms(1)] .
  show ?thesis unfolding peak_def
    using pulse_peak_constant[OF om gbp, of G] c1 by simp
qed

lemma lyap0_bound:
  fixes G gq gm \<Omega> \<eta> :: real
  assumes "0 < \<Omega>" and "0 \<le> gq" and "0 \<le> gm" and "0 < \<eta>"
    and "0 < G * sqrt (1 + \<eta>\<^sup>2) + (gq - gm) / 4 * \<eta>"
  shows "exp (2 * lyap G gq gm \<Omega> (sqrt (1 + \<eta>\<^sup>2)) \<eta>)
         \<le> ((G * sqrt (1 + \<eta>\<^sup>2) + (gq - gm) / 4 * \<eta>)\<^sup>2 + (\<Omega> * \<eta>)\<^sup>2)
           * exp ((gq + gm) / (2 * \<Omega>) * ((\<Omega> * \<eta>) / (G * sqrt (1 + \<eta>\<^sup>2) + (gq - gm) / 4 * \<eta>)))"
proof -
  define y1 where "y1 = G * sqrt (1 + \<eta>\<^sup>2) + (gq - gm) / 4 * \<eta>"
  define y2 where "y2 = \<Omega> * \<eta>"
  have y1pos: "0 < y1" unfolding y1_def using assms(5) .
  have y2pos: "0 < y2" unfolding y2_def using assms(1,4) by simp
  have S: "0 < y1\<^sup>2 + y2\<^sup>2" using y2pos by (simp add: add_nonneg_pos)
  have kk: "0 \<le> (gq + gm) / (2 * \<Omega>)" using assms(1,2,3) by simp
  have phi: "pi / 2 - arctan (y1 / y2) = arctan (y2 / y1)"
  proof -
    have q: "0 < y1 / y2" using y1pos y2pos by simp
    have h: "arctan (inverse (y1 / y2)) = pi / 2 - arctan (y1 / y2)" by (rule arctan_inverse[OF q])
    have "inverse (y1 / y2) = y2 / y1" by (simp add: inverse_divide)
    then show ?thesis using h by simp
  qed
  have phile: "arctan (y2 / y1) \<le> y2 / y1" by (rule arctan_le_id) (use y1pos y2pos in simp)
  have lyp: "lyap G gq gm \<Omega> (sqrt (1 + \<eta>\<^sup>2)) \<eta>
       = (1 / 2) * ln (y1\<^sup>2 + y2\<^sup>2) + (gq + gm) / (4 * \<Omega>) * arctan (y2 / y1)"
    unfolding lyap_def y1_def y2_def phi[unfolded y1_def y2_def] by simp
  have "exp (2 * lyap G gq gm \<Omega> (sqrt (1 + \<eta>\<^sup>2)) \<eta>)
        = (y1\<^sup>2 + y2\<^sup>2) * exp ((gq + gm) / (2 * \<Omega>) * arctan (y2 / y1))"
  proof -
    have "2 * lyap G gq gm \<Omega> (sqrt (1 + \<eta>\<^sup>2)) \<eta>
          = ln (y1\<^sup>2 + y2\<^sup>2) + (gq + gm) / (2 * \<Omega>) * arctan (y2 / y1)"
      unfolding lyp using assms(1) by (simp add: field_simps)
    then show ?thesis using S by (simp add: exp_add)
  qed
  also have "\<dots> \<le> (y1\<^sup>2 + y2\<^sup>2) * exp ((gq + gm) / (2 * \<Omega>) * (y2 / y1))"
  proof (rule mult_left_mono)
    have "(gq + gm) / (2 * \<Omega>) * arctan (y2 / y1) \<le> (gq + gm) / (2 * \<Omega>) * (y2 / y1)"
      by (rule mult_left_mono[OF phile kk])
    then show "exp ((gq + gm) / (2 * \<Omega>) * arctan (y2 / y1)) \<le> exp ((gq + gm) / (2 * \<Omega>) * (y2 / y1))"
      by simp
    show "0 \<le> y1\<^sup>2 + y2\<^sup>2" using S by simp
  qed
  finally show ?thesis unfolding y1_def y2_def .
qed

section \<open>C. The theorem\<close>

locale pulse =
  fixes G gq gm T :: real and A B u :: "real \<Rightarrow> real"
  assumes G: "0 < G" and gq: "0 \<le> gq" and gm: "0 \<le> gm"
    and Gd: "\<bar>gq - gm\<bar> / 4 < G" and T: "0 \<le> T"
    and dA: "\<And>t. t \<in> {0..T} \<Longrightarrow> (A has_real_derivative (- gq * A t - 2 * u t)) (at t within {0..T})"
    and dB: "\<And>t. t \<in> {0..T} \<Longrightarrow> (B has_real_derivative (- gm * B t + 2 * u t)) (at t within {0..T})"
    and A_nn: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> A t"
    and B_nn: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> B t"
    and uineq: "\<And>t. t \<in> {0..T} \<Longrightarrow> (u t)\<^sup>2 \<le> G\<^sup>2 * A t * B t"
    and A_0: "A 0 = 1" and B_0: "B 0 = 0"
begin

definition Om :: real where "Om = sqrt (G\<^sup>2 - (gq - gm)\<^sup>2 / 16)"

lemma Gd2: "(gq - gm)\<^sup>2 / 16 < G\<^sup>2"
proof -
  have "(\<bar>gq - gm\<bar> / 4)\<^sup>2 < G\<^sup>2" by (rule power_strict_mono) (use Gd in simp_all)
  then show ?thesis by (simp add: power_divide)
qed

lemma Om_pos: "0 < Om" unfolding Om_def using Gd2 by simp

lemma Om_sq: "Om\<^sup>2 = G\<^sup>2 - (gq - gm)\<^sup>2 / 16"
  unfolding Om_def using Gd2 by (simp add: real_sqrt_pow2)

lemma contA: "continuous_on {0..T} A"
  by (subst continuous_on_eq_continuous_within) (auto intro: DERIV_continuous dA)

lemma contB: "continuous_on {0..T} B"
  by (subst continuous_on_eq_continuous_within) (auto intro: DERIV_continuous dB)

lemma dA_int:
  assumes "0 < t" and "t < T"
  shows "(A has_real_derivative (- gq * A t - 2 * u t)) (at t)"
proof -
  have "t \<in> interior {0..T}" using assms by simp
  then show ?thesis using dA[of t] assms at_within_interior[of t "{0..T}"] by simp
qed

lemma dB_int:
  assumes "0 < t" and "t < T"
  shows "(B has_real_derivative (- gm * B t + 2 * u t)) (at t)"
proof -
  have "t \<in> interior {0..T}" using assms by simp
  then show ?thesis using dB[of t] assms at_within_interior[of t "{0..T}"] by simp
qed

subsection \<open>The regularised amplitudes\<close>

text \<open>@{text "pa d t = A t + d e^{-gq t}"} and @{text "pb d t = B t + d e^{-gm t}"} are positive on @{text "[0,T]"}
  and satisfy the same equations as @{text A}, @{text B} with the SAME @{text u} and no error term, since
  @{text "(d e^{-gq t})' = -gq (d e^{-gq t})"}.\<close>

definition pa :: "real \<Rightarrow> real \<Rightarrow> real" where "pa d t = A t + d * exp (- gq * t)"
definition pb :: "real \<Rightarrow> real \<Rightarrow> real" where "pb d t = B t + d * exp (- gm * t)"

lemma pa_eq: "pa d = (\<lambda>s. A s + d * exp (- gq * s))" by (rule ext) (simp add: pa_def)
lemma pb_eq: "pb d = (\<lambda>s. B s + d * exp (- gm * s))" by (rule ext) (simp add: pb_def)

lemma pa_pos: assumes "0 < d" and "t \<in> {0..T}" shows "0 < pa d t"
  unfolding pa_def using assms A_nn[of t] by (simp add: add_nonneg_pos)

lemma pb_pos: assumes "0 < d" and "t \<in> {0..T}" shows "0 < pb d t"
  unfolding pb_def using assms B_nn[of t] by (simp add: add_nonneg_pos)

lemma pa_deriv:
  assumes "0 < t" and "t < T"
  shows "(pa d has_real_derivative (- gq * pa d t - 2 * u t)) (at t)"
proof -
  have e: "((\<lambda>s. d * exp (- gq * s)) has_real_derivative d * (exp (- gq * t) * (- gq))) (at t)"
    by (auto intro!: derivative_eq_intros)
  have "((\<lambda>s. A s + d * exp (- gq * s)) has_real_derivative
        (- gq * A t - 2 * u t) + d * (exp (- gq * t) * (- gq))) (at t)"
    by (rule DERIV_add[OF dA_int[OF assms] e])
  then show ?thesis unfolding pa_eq pa_def by (rule DERIV_cong) (simp add: algebra_simps)
qed

lemma pb_deriv:
  assumes "0 < t" and "t < T"
  shows "(pb d has_real_derivative (- gm * pb d t + 2 * u t)) (at t)"
proof -
  have e: "((\<lambda>s. d * exp (- gm * s)) has_real_derivative d * (exp (- gm * t) * (- gm))) (at t)"
    by (auto intro!: derivative_eq_intros)
  have "((\<lambda>s. B s + d * exp (- gm * s)) has_real_derivative
        (- gm * B t + 2 * u t) + d * (exp (- gm * t) * (- gm))) (at t)"
    by (rule DERIV_add[OF dB_int[OF assms] e])
  then show ?thesis unfolding pb_eq pb_def by (rule DERIV_cong) (simp add: algebra_simps)
qed

lemma sqrt_pa_deriv:
  assumes "0 < d" and "0 < t" and "t < T"
  shows "((\<lambda>s. sqrt (pa d s)) has_real_derivative
          (- gq * (sqrt (pa d t))\<^sup>2 - 2 * u t) / (2 * sqrt (pa d t))) (at t)"
proof -
  have p: "0 < pa d t" using pa_pos[OF assms(1)] assms(2,3) by simp
  have "((\<lambda>s. sqrt (pa d s)) has_real_derivative inverse (sqrt (pa d t)) / 2 * (- gq * pa d t - 2 * u t)) (at t)"
    by (rule DERIV_chain'[OF pa_deriv[OF assms(2,3)] DERIV_real_sqrt[OF p]])
  then show ?thesis
    by (rule DERIV_cong) (use p in \<open>simp add: real_sqrt_pow2 field_simps\<close>)
qed

lemma sqrt_pb_deriv:
  assumes "0 < d" and "0 < t" and "t < T"
  shows "((\<lambda>s. sqrt (pb d s)) has_real_derivative
          (- gm * (sqrt (pb d t))\<^sup>2 + 2 * u t) / (2 * sqrt (pb d t))) (at t)"
proof -
  have p: "0 < pb d t" using pb_pos[OF assms(1)] assms(2,3) by simp
  have "((\<lambda>s. sqrt (pb d s)) has_real_derivative inverse (sqrt (pb d t)) / 2 * (- gm * pb d t + 2 * u t)) (at t)"
    by (rule DERIV_chain'[OF pb_deriv[OF assms(2,3)] DERIV_real_sqrt[OF p]])
  then show ?thesis
    by (rule DERIV_cong) (use p in \<open>simp add: real_sqrt_pow2 field_simps\<close>)
qed

lemma u_le:
  assumes "0 < d" and "s \<in> {0..T}"
  shows "u s \<le> G * sqrt (pa d s) * sqrt (pb d s)"
proof -
  have h1: "A s \<le> pa d s" unfolding pa_def using assms(1) by simp
  have h2: "B s \<le> pb d s" unfolding pb_def using assms(1) by simp
  have "A s * B s \<le> pa d s * pb d s"
    using h1 h2 A_nn[OF assms(2)] B_nn[OF assms(2)] pa_pos[OF assms] pb_pos[OF assms]
    by (intro mult_mono) simp_all
  then have "G\<^sup>2 * A s * B s \<le> G\<^sup>2 * (pa d s * pb d s)"
    by (simp add: mult.assoc mult_left_mono)
  moreover have "(G * sqrt (pa d s) * sqrt (pb d s))\<^sup>2 = G\<^sup>2 * (pa d s * pb d s)"
    using pa_pos[OF assms] pb_pos[OF assms]
    by (simp add: power_mult_distrib real_sqrt_pow2 mult.assoc)
  ultimately have "(u s)\<^sup>2 \<le> (G * sqrt (pa d s) * sqrt (pb d s))\<^sup>2"
    using uineq[OF assms(2)] by linarith
  moreover have "0 \<le> G * sqrt (pa d s) * sqrt (pb d s)"
  proof -
    have a0: "0 < sqrt (pa d s)" using pa_pos[OF assms] by simp
    have b0: "0 < sqrt (pb d s)" using pb_pos[OF assms] by simp
    have "0 < G * sqrt (pa d s) * sqrt (pb d s)" using G a0 b0 by (simp add: mult_pos_pos)
    then show ?thesis by (rule less_imp_le)
  qed
  ultimately show ?thesis by (rule power2_le_imp_le)
qed

lemma reg_mono:
  assumes "0 < d" and "t \<in> {0..T}"
  shows "lyap G gq gm Om (sqrt (pa d t)) (sqrt (pb d t)) \<le> lyap G gq gm Om (sqrt (pa d 0)) (sqrt (pb d 0))"
proof (cases "t = 0")
  case True then show ?thesis by simp
next
  case False
  then have t0: "0 < t" using assms(2) by simp
  have tT: "t \<le> T" using assms(2) by simp
  define g where "g = (\<lambda>s. lyap G gq gm Om (sqrt (pa d s)) (sqrt (pb d s)))"
  have step: "\<forall>s\<in>{0<..<t}. \<exists>D. (g has_real_derivative D) (at s) \<and> D \<le> 0"
  proof
    fix s assume s: "s \<in> {0<..<t}"
    then have s0: "0 < s" and sT: "s < T" and sI: "s \<in> {0..T}" using tT by auto
    have a0: "0 < sqrt (pa d s)" using pa_pos[OF assms(1) sI] by simp
    have b0: "0 < sqrt (pb d s)" using pb_pos[OF assms(1) sI] by simp
    note h = lyap_has_derivative[OF Om_pos b0 sqrt_pa_deriv[OF assms(1) s0 sT] sqrt_pb_deriv[OF assms(1) s0 sT],
                                  of G gq gm]
    have nonpos: "((G * sqrt (pa d s) + (gq - gm) / 4 * sqrt (pb d s)) - (gq + gm) / (4 * Om) * (Om * sqrt (pb d s)))
           * (G * ((- gq * (sqrt (pa d s))\<^sup>2 - 2 * u s) / (2 * sqrt (pa d s)))
              + (gq - gm) / 4 * ((- gm * (sqrt (pb d s))\<^sup>2 + 2 * u s) / (2 * sqrt (pb d s))))
         + ((Om * sqrt (pb d s)) + (gq + gm) / (4 * Om) * (G * sqrt (pa d s) + (gq - gm) / 4 * sqrt (pb d s)))
           * (Om * ((- gm * (sqrt (pb d s))\<^sup>2 + 2 * u s) / (2 * sqrt (pb d s)))) \<le> 0"
      by (rule lyap_num_nonpos[OF a0 b0 Om_pos Om_sq G gq gm u_le[OF assms(1) sI]])
    have den: "0 \<le> (G * sqrt (pa d s) + (gq - gm) / 4 * sqrt (pb d s))\<^sup>2 + (Om * sqrt (pb d s))\<^sup>2" by simp
    show "\<exists>D. (g has_real_derivative D) (at s) \<and> D \<le> 0"
      unfolding g_def using h divide_nonpos_nonneg[OF nonpos den] by blast
  qed
  then obtain D where D: "\<And>s. s \<in> {0<..<t} \<Longrightarrow> (g has_real_derivative D s) (at s) \<and> D s \<le> 0"
    by (metis bchoice)
  have cpa: "continuous_on {0..T} (pa d)" unfolding pa_eq by (intro continuous_intros contA)
  have cpb: "continuous_on {0..T} (pb d)" unfolding pb_eq by (intro continuous_intros contB)
  have cg: "continuous_on {0..t} g"
  proof -
    have csa: "continuous_on {0..T} (\<lambda>s. sqrt (pa d s))" by (intro continuous_intros cpa)
    have csb: "continuous_on {0..T} (\<lambda>s. sqrt (pb d s))" by (intro continuous_intros cpb)
    have c1: "continuous_on {0..T} (\<lambda>s. G * sqrt (pa d s) + (gq - gm) / 4 * sqrt (pb d s))"
      by (intro continuous_intros csa csb)
    have c2: "continuous_on {0..T} (\<lambda>s. Om * sqrt (pb d s))" by (intro continuous_intros csb)
    have c2ne: "\<And>s. s \<in> {0..T} \<Longrightarrow> Om * sqrt (pb d s) \<noteq> 0"
    proof -
      fix s assume s: "s \<in> {0..T}"
      have "0 < pb d s" by (rule pb_pos[OF assms(1) s])
      then show "Om * sqrt (pb d s) \<noteq> 0" using Om_pos by simp
    qed
    have c2pos: "\<And>s. s \<in> {0..T} \<Longrightarrow> 0 < (G * sqrt (pa d s) + (gq - gm) / 4 * sqrt (pb d s))\<^sup>2 + (Om * sqrt (pb d s))\<^sup>2"
      using c2ne by (simp add: add_nonneg_pos)
    have cln: "continuous_on {0..T} (\<lambda>s. ln ((G * sqrt (pa d s) + (gq - gm) / 4 * sqrt (pb d s))\<^sup>2 + (Om * sqrt (pb d s))\<^sup>2))"
    proof -
      have cS: "continuous_on {0..T} (\<lambda>s. (G * sqrt (pa d s) + (gq - gm) / 4 * sqrt (pb d s))\<^sup>2 + (Om * sqrt (pb d s))\<^sup>2)"
        by (intro continuous_on_add continuous_on_power c1 c2)
      show ?thesis by (rule continuous_on_ln[OF cS]) (intro ballI; rule c2pos[THEN less_imp_neq, THEN not_sym]; assumption)
    qed
    have cat: "continuous_on {0..T} (\<lambda>s. arctan ((G * sqrt (pa d s) + (gq - gm) / 4 * sqrt (pb d s)) / (Om * sqrt (pb d s))))"
    proof -
      have c2ne': "\<forall>s\<in>{0..T}. Om * sqrt (pb d s) \<noteq> 0" using c2ne by blast
      have cq: "continuous_on {0..T} (\<lambda>s. (G * sqrt (pa d s) + (gq - gm) / 4 * sqrt (pb d s)) / (Om * sqrt (pb d s)))"
        by (rule continuous_on_divide[OF c1 c2 c2ne'])
      show ?thesis by (rule continuous_on_arctan[OF cq])
    qed
    have "continuous_on {0..T} g"
      unfolding g_def lyap_def
      by (intro continuous_on_add continuous_on_mult continuous_on_const continuous_on_diff cln cat)
    then show ?thesis by (rule continuous_on_subset) (use tT in auto)
  qed
  have hd: "\<And>x. 0 < x \<Longrightarrow> x < t \<Longrightarrow> (g has_derivative (\<lambda>h. D x * h)) (at x)"
  proof -
    fix x assume x: "0 < x" "x < t"
    then have "x \<in> {0<..<t}" by simp
    from has_field_derivative_imp_has_derivative[OF conjunct1[OF D[OF this]]]
    show "(g has_derivative (\<lambda>h. D x * h)) (at x)" .
  qed
  obtain \<xi> where xi: "0 < \<xi>" "\<xi> < t" "g t - g 0 = D \<xi> * (t - 0)"
    using mvt[OF t0 cg hd] by blast
  have "D \<xi> \<le> 0" using D xi(1,2) by simp
  then have "g t - g 0 \<le> 0" using xi(3) t0 by (simp add: mult_nonpos_nonneg)
  then show ?thesis unfolding g_def by simp
qed

subsection \<open>The bound for each regularisation, then the limit\<close>

lemma bound_reg:
  assumes "0 < \<eta>" and "\<eta> < 1" and "0 < gq + gm" and "t \<in> {0..T}"
  shows "Om\<^sup>2 * B t \<le> ((G * sqrt (1 + \<eta>\<^sup>2) + (gq - gm) / 4 * \<eta>)\<^sup>2 + (Om * \<eta>)\<^sup>2)
           * exp ((gq + gm) / (2 * Om) * ((Om * \<eta>) / (G * sqrt (1 + \<eta>\<^sup>2) + (gq - gm) / 4 * \<eta>)))
           * peak ((gq + gm) / 2 / Om)"
proof -
  define d where "d = \<eta>\<^sup>2"
  have dpos: "0 < d" unfolding d_def using assms(1) by simp
  have y1pos: "0 < G * sqrt (1 + \<eta>\<^sup>2) + (gq - gm) / 4 * \<eta>"
  proof -
    have s1: "1 \<le> sqrt (1 + \<eta>\<^sup>2)" by (rule real_le_rsqrt) simp
    have h1: "G \<le> G * sqrt (1 + \<eta>\<^sup>2)" using mult_left_mono[OF s1 less_imp_le[OF G]] by simp
    have hh: "- (\<bar>gq - gm\<bar> / 4) \<le> (gq - gm) / 4" using abs_ge_minus_self[of "gq - gm"] by argo
    have h2: "- (\<bar>gq - gm\<bar> / 4) * \<eta> \<le> (gq - gm) / 4 * \<eta>"
      by (rule mult_right_mono[OF hh less_imp_le[OF assms(1)]])
    have h3: "\<bar>gq - gm\<bar> / 4 * \<eta> \<le> \<bar>gq - gm\<bar> / 4 * 1"
      by (rule mult_left_mono) (use assms(2) in auto)
    show ?thesis using h1 h2 h3 Gd by linarith
  qed
  have a0: "sqrt (pa d 0) = sqrt (1 + \<eta>\<^sup>2)" by (simp add: pa_def A_0 d_def)
  have b0: "sqrt (pb d 0) = \<eta>"
  proof -
    have "pb d 0 = \<eta>\<^sup>2" by (simp add: pb_def B_0 d_def)
    then show ?thesis using assms(1) by simp
  qed
  have bpos: "0 < sqrt (pb d t)" using pb_pos[OF dpos assms(4)] by simp
  have lb: "Om\<^sup>2 * (sqrt (pb d t))\<^sup>2
            \<le> exp (2 * lyap G gq gm Om (sqrt (pa d 0)) (sqrt (pb d 0))) * peak ((gq + gm) / 2 / Om)"
    by (rule lyap_bound[OF Om_pos bpos assms(3) reg_mono[OF dpos assms(4)]])
  have l0: "exp (2 * lyap G gq gm Om (sqrt (1 + \<eta>\<^sup>2)) \<eta>)
         \<le> ((G * sqrt (1 + \<eta>\<^sup>2) + (gq - gm) / 4 * \<eta>)\<^sup>2 + (Om * \<eta>)\<^sup>2)
           * exp ((gq + gm) / (2 * Om) * ((Om * \<eta>) / (G * sqrt (1 + \<eta>\<^sup>2) + (gq - gm) / 4 * \<eta>)))"
    by (rule lyap0_bound[OF Om_pos gq gm assms(1) y1pos])
  have pk: "0 \<le> peak ((gq + gm) / 2 / Om)" unfolding peak_def by simp
  have "B t \<le> pb d t" unfolding pb_def using dpos by simp
  then have "Om\<^sup>2 * B t \<le> Om\<^sup>2 * pb d t" by (intro mult_left_mono) simp_all
  also have "\<dots> = Om\<^sup>2 * (sqrt (pb d t))\<^sup>2"
    using pb_pos[OF dpos assms(4)] by (simp add: real_sqrt_pow2)
  also have "\<dots> \<le> exp (2 * lyap G gq gm Om (sqrt (1 + \<eta>\<^sup>2)) \<eta>) * peak ((gq + gm) / 2 / Om)"
    using lb unfolding a0 b0 .
  also have "\<dots> \<le> (((G * sqrt (1 + \<eta>\<^sup>2) + (gq - gm) / 4 * \<eta>)\<^sup>2 + (Om * \<eta>)\<^sup>2)
           * exp ((gq + gm) / (2 * Om) * ((Om * \<eta>) / (G * sqrt (1 + \<eta>\<^sup>2) + (gq - gm) / 4 * \<eta>)))) * peak ((gq + gm) / 2 / Om)"
    by (rule mult_right_mono[OF l0 pk])
  finally show ?thesis .
qed

theorem bound_pos:
  assumes "0 < gq + gm" and "t \<in> {0..T}"
  shows "B t \<le> 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm)
                * exp (- (((gq + gm) / 2) / Om) * arctan (2 * Om / ((gq + gm) / 2)))"
proof -
  define y1 where "y1 = (\<lambda>\<eta>::real. G * sqrt (1 + \<eta>\<^sup>2) + (gq - gm) / 4 * \<eta>)"
  define cf where "cf = (\<lambda>\<eta>::real. ((y1 \<eta>)\<^sup>2 + (Om * \<eta>)\<^sup>2) * exp ((gq + gm) / (2 * Om) * ((Om * \<eta>) / y1 \<eta>)))"
  define k where "k = (gq + gm) / 2 / Om"
  have y10: "y1 0 = G" unfolding y1_def by simp
  have cont: "isCont cf 0"
    unfolding cf_def y1_def using G by (intro continuous_intros) simp_all
  have val: "cf 0 = G\<^sup>2" unfolding cf_def using y10 by simp
  have lim0: "(cf \<longlongrightarrow> G\<^sup>2) (at_right 0)"
  proof -
    have "(cf \<longlongrightarrow> cf 0) (at 0)" using cont by (simp add: isCont_def)
    then show ?thesis using val by (simp add: Lim_at_imp_Lim_at_within)
  qed
  have lim: "((\<lambda>\<eta>. cf \<eta> * peak k / Om\<^sup>2) \<longlongrightarrow> G\<^sup>2 * peak k / Om\<^sup>2) (at_right 0)"
    by (intro tendsto_intros lim0) (use Om_pos in simp)
  have ev: "\<forall>\<^sub>F \<eta> in at_right 0. B t \<le> cf \<eta> * peak k / Om\<^sup>2"
  proof (subst eventually_at_right_field)
    show "\<exists>b>0. \<forall>y>0. y < b \<longrightarrow> B t \<le> cf y * peak k / Om\<^sup>2"
    proof (intro exI[of _ 1] conjI allI impI)
      show "(0::real) < 1" by simp
      fix y :: real assume y: "0 < y" "y < 1"
      have "Om\<^sup>2 * B t \<le> cf y * peak k"
        using bound_reg[OF y assms] unfolding cf_def y1_def k_def by (simp add: mult.assoc)
      then show "B t \<le> cf y * peak k / Om\<^sup>2" using Om_pos by (simp add: pos_le_divide_eq mult.commute)
    qed
  qed
  have "B t \<le> G\<^sup>2 * peak k / Om\<^sup>2" by (rule tendsto_lowerbound[OF lim ev]) simp
  also have "\<dots> = G\<^sup>2 / Om\<^sup>2 * peak k" by simp
  also have "\<dots> = 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- (((gq + gm) / 2) / Om) * arctan (2 * Om / ((gq + gm) / 2)))"
    unfolding k_def using peak_const[OF Om_def Gd2 assms(1)] .
  finally show ?thesis .
qed

theorem bound_zero:
  assumes "gq + gm = 0" and "t \<in> {0..T}"
  shows "B t \<le> 1"
proof -
  have q0: "gq = 0" and m0: "gm = 0" using gq gm assms(1) by linarith+
  show ?thesis
  proof (cases "t = 0")
    case True then show ?thesis using B_0 by simp
  next
    case False
    then have t0: "0 < t" using assms(2) by simp
    have tT: "t \<le> T" using assms(2) by simp
    define g where "g = (\<lambda>s. A s + B s)"
    have cg: "continuous_on {0..t} g"
      unfolding g_def by (rule continuous_on_subset[OF continuous_on_add[OF contA contB]]) (use tT in auto)
    have hd: "\<And>x. 0 < x \<Longrightarrow> x < t \<Longrightarrow> (g has_derivative (\<lambda>h. 0 * h)) (at x)"
    proof -
      fix x assume x: "0 < x" "x < t"
      have "(g has_real_derivative (- gq * A x - 2 * u x) + (- gm * B x + 2 * u x)) (at x)"
        unfolding g_def by (rule DERIV_add[OF dA_int dB_int]) (use x tT in auto)
      then have "(g has_real_derivative 0) (at x)" using q0 m0 by simp
      from has_field_derivative_imp_has_derivative[OF this] show "(g has_derivative (\<lambda>h. 0 * h)) (at x)" .
    qed
    obtain \<xi> where "g t - g 0 = 0 * (t - 0)" using mvt[OF t0 cg hd] by blast
    then have "A t + B t = 1" unfolding g_def using A_0 B_0 by simp
    then show ?thesis using A_nn[OF assms(2)] by linarith
  qed
qed

theorem bound_all:
  assumes "t \<in> {0..T}"
  shows "B t \<le> max_population G gq gm"
proof (cases "gq + gm = 0")
  case True
  then have "gq = 0" "gm = 0" using gq gm by linarith+
  then have "max_population G gq gm = 1" using G unfolding max_population_def by simp
  then show ?thesis using bound_zero[OF True assms] by simp
next
  case False
  then have pos: "0 < gq + gm" using gq gm by linarith
  show ?thesis unfolding max_population_def using bound_pos[OF pos assms] unfolding Om_def by simp
qed

end

section \<open>D. Theorem 1, free of the locale\<close>

theorem memory_access_all_pulses:
  fixes G gq gm T :: real and A B u :: "real \<Rightarrow> real"
  assumes G: "0 < G" and gq: "0 \<le> gq" and gm: "0 \<le> gm" and Gd: "\<bar>gq - gm\<bar> / 4 < G" and T: "0 \<le> T"
    and dA: "\<And>t. t \<in> {0..T} \<Longrightarrow> (A has_real_derivative (- gq * A t - 2 * u t)) (at t within {0..T})"
    and dB: "\<And>t. t \<in> {0..T} \<Longrightarrow> (B has_real_derivative (- gm * B t + 2 * u t)) (at t within {0..T})"
    and A_nn: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> A t" and B_nn: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> B t"
    and uineq: "\<And>t. t \<in> {0..T} \<Longrightarrow> (u t)\<^sup>2 \<le> G\<^sup>2 * A t * B t"
    and A0: "A 0 = 1" and B0: "B 0 = 0" and t: "t \<in> {0..T}"
  shows "B t \<le> max_population G gq gm"
    and "0 < gq + gm \<Longrightarrow> B t \<le> 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm)
           * exp (- (((gq + gm) / 2) / sqrt (G\<^sup>2 - (gq - gm)\<^sup>2 / 16)) * arctan (2 * sqrt (G\<^sup>2 - (gq - gm)\<^sup>2 / 16) / ((gq + gm) / 2)))"
    and "gq + gm = 0 \<Longrightarrow> B t \<le> 1"
proof -
  interpret pulse G gq gm T A B u
    by unfold_locales (use assms in \<open>blast+\<close>)
  show "B t \<le> max_population G gq gm" by (rule bound_all[OF t])
  show "0 < gq + gm \<Longrightarrow> B t \<le> 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm)
           * exp (- (((gq + gm) / 2) / sqrt (G\<^sup>2 - (gq - gm)\<^sup>2 / 16)) * arctan (2 * sqrt (G\<^sup>2 - (gq - gm)\<^sup>2 / 16) / ((gq + gm) / 2)))"
    using bound_pos[OF _ t] unfolding Om_def by simp
  show "gq + gm = 0 \<Longrightarrow> B t \<le> 1" by (rule bound_zero[OF _ t])
qed

section \<open>E. The resonant solution in closed form, and sharpness\<close>

text \<open>Not needed for the proof above (the comparison is made in skew-polar coordinates, which avoids the
  inverse of the resonant time), but it shows that the bound is attained inside the same class of
  admissible triples.\<close>

definition res_Om :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "res_Om G gq gm = sqrt (G\<^sup>2 - (gq - gm)\<^sup>2 / 16)"

definition res_c :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "res_c G gq gm t = cos (res_Om G gq gm * t) - (gq - gm) / (4 * res_Om G gq gm) * sin (res_Om G gq gm * t)"

definition res_A :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "res_A G gq gm t = exp (- ((gq + gm) / 2) * t) * (res_c G gq gm t)\<^sup>2"

definition res_B :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "res_B G gq gm t = G\<^sup>2 / (res_Om G gq gm)\<^sup>2 * exp (- ((gq + gm) / 2) * t) * (sin (res_Om G gq gm * t))\<^sup>2"

definition res_u :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "res_u G gq gm t = G\<^sup>2 / res_Om G gq gm * exp (- ((gq + gm) / 2) * t) * res_c G gq gm t * sin (res_Om G gq gm * t)"

lemma res_A_deriv:
  fixes G gq gm t :: real
  assumes "0 < G" and "(gq - gm)\<^sup>2 / 16 < G\<^sup>2"
  shows "(res_A G gq gm has_real_derivative (- gq * res_A G gq gm t - 2 * res_u G gq gm t)) (at t)"
proof -
  define \<Omega> where "\<Omega> = res_Om G gq gm"
  have om: "0 < \<Omega>" unfolding \<Omega>_def res_Om_def using assms(2) by simp
  have om_ne: "\<Omega> \<noteq> 0" using om by simp
  have osq: "\<Omega>\<^sup>2 = G\<^sup>2 - (gq - gm)\<^sup>2 / 16" unfolding \<Omega>_def res_Om_def using assms(2) by (simp add: real_sqrt_pow2)
  define E where "E = exp (- ((gq + gm) / 2) * t)"
  define cs where "cs = cos (\<Omega> * t)"
  define sn where "sn = sin (\<Omega> * t)"
  define cr where "cr = cs - (gq - gm) / (4 * \<Omega>) * sn"
  have raw: "((\<lambda>s. exp (- ((gq + gm) / 2) * s) * (cos (\<Omega> * s) - (gq - gm) / (4 * \<Omega>) * sin (\<Omega> * s))\<^sup>2) has_real_derivative
      E * (- ((gq + gm) / 2) * cr\<^sup>2 + 2 * cr * (- \<Omega> * sn - (gq - gm) / (4 * \<Omega>) * \<Omega> * cs))) (at t)"
    unfolding E_def cr_def cs_def sn_def using om_ne
    by (auto intro!: derivative_eq_intros simp: field_simps power2_eq_square)
  have key: "E * (- ((gq + gm) / 2) * cr\<^sup>2 + 2 * cr * (- \<Omega> * sn - (gq - gm) / (4 * \<Omega>) * \<Omega> * cs))
             - (- gq * (E * cr\<^sup>2) - 2 * (G\<^sup>2 / \<Omega> * E * cr * sn))
             = (G\<^sup>2 - (gq - gm)\<^sup>2 / 16 - \<Omega>\<^sup>2) * (- E * sn * (- 4 * \<Omega> * cs + (gq - gm) * sn) / 2) / \<Omega>\<^sup>2"
    unfolding cr_def using om_ne by (simp add: field_simps power2_eq_square)
  have z: "G\<^sup>2 - (gq - gm)\<^sup>2 / 16 - \<Omega>\<^sup>2 = 0" using osq by simp
  have "E * (- ((gq + gm) / 2) * cr\<^sup>2 + 2 * cr * (- \<Omega> * sn - (gq - gm) / (4 * \<Omega>) * \<Omega> * cs))
        = - gq * (E * cr\<^sup>2) - 2 * (G\<^sup>2 / \<Omega> * E * cr * sn)" using key z by simp
  then show ?thesis
    using raw unfolding res_A_def res_c_def res_u_def \<Omega>_def[symmetric] E_def cr_def cs_def sn_def
    by (simp add: mult.assoc)
qed

lemma res_B_deriv:
  fixes G gq gm t :: real
  assumes "0 < G" and "(gq - gm)\<^sup>2 / 16 < G\<^sup>2"
  shows "(res_B G gq gm has_real_derivative (- gm * res_B G gq gm t + 2 * res_u G gq gm t)) (at t)"
proof -
  define \<Omega> where "\<Omega> = res_Om G gq gm"
  have om: "0 < \<Omega>" unfolding \<Omega>_def res_Om_def using assms(2) by simp
  have om_ne: "\<Omega> \<noteq> 0" using om by simp
  define E where "E = exp (- ((gq + gm) / 2) * t)"
  define cs where "cs = cos (\<Omega> * t)"
  define sn where "sn = sin (\<Omega> * t)"
  define cr where "cr = cs - (gq - gm) / (4 * \<Omega>) * sn"
  have raw: "((\<lambda>s. G\<^sup>2 / \<Omega>\<^sup>2 * exp (- ((gq + gm) / 2) * s) * (sin (\<Omega> * s))\<^sup>2) has_real_derivative
      G\<^sup>2 / \<Omega>\<^sup>2 * (E * (- ((gq + gm) / 2) * sn\<^sup>2 + 2 * sn * (\<Omega> * cs)))) (at t)"
    unfolding E_def cs_def sn_def using om_ne
    by (auto intro!: derivative_eq_intros simp: field_simps power2_eq_square)
  have key: "G\<^sup>2 / \<Omega>\<^sup>2 * (E * (- ((gq + gm) / 2) * sn\<^sup>2 + 2 * sn * (\<Omega> * cs)))
             = - gm * (G\<^sup>2 / \<Omega>\<^sup>2 * E * sn\<^sup>2) + 2 * (G\<^sup>2 / \<Omega> * E * cr * sn)"
    unfolding cr_def using om_ne by (simp add: field_simps power2_eq_square)
  show ?thesis
    using raw key unfolding res_B_def res_c_def res_u_def \<Omega>_def[symmetric] E_def cr_def cs_def sn_def
    by (simp add: mult.assoc)
qed

lemma res_admissible:
  fixes G gq gm :: real
  assumes "0 < G" and "(gq - gm)\<^sup>2 / 16 < G\<^sup>2"
  shows "(res_u G gq gm t)\<^sup>2 = G\<^sup>2 * res_A G gq gm t * res_B G gq gm t"
    and "res_A G gq gm 0 = 1" and "res_B G gq gm 0 = 0"
    and "0 \<le> res_A G gq gm t" and "0 \<le> res_B G gq gm t"
proof -
  have om: "0 < res_Om G gq gm" unfolding res_Om_def using assms(2) by simp
  show "(res_u G gq gm t)\<^sup>2 = G\<^sup>2 * res_A G gq gm t * res_B G gq gm t"
    unfolding res_u_def res_A_def res_B_def using om by (simp add: field_simps power2_eq_square)
  show "res_A G gq gm 0 = 1" unfolding res_A_def res_c_def by simp
  show "res_B G gq gm 0 = 0" unfolding res_B_def by simp
  show "0 \<le> res_A G gq gm t" unfolding res_A_def by simp
  show "0 \<le> res_B G gq gm t" unfolding res_B_def by simp
qed

theorem bound_sharp:
  fixes G gq gm :: real
  assumes "0 < G" and "0 \<le> gq" and "0 \<le> gm" and "\<bar>gq - gm\<bar> / 4 < G" and "0 < gq + gm"
  shows "\<exists>T. 0 \<le> T \<and> pulse G gq gm T (res_A G gq gm) (res_B G gq gm) (res_u G gq gm)
              \<and> res_B G gq gm T = max_population G gq gm"
proof -
  have Gd2: "(gq - gm)\<^sup>2 / 16 < G\<^sup>2"
  proof -
    have "(\<bar>gq - gm\<bar> / 4)\<^sup>2 < G\<^sup>2" by (rule power_strict_mono) (use assms(4) in simp_all)
    then show ?thesis by (simp add: power_divide)
  qed
  define \<Omega> where "\<Omega> = sqrt (G\<^sup>2 - (gq - gm)\<^sup>2 / 16)"
  have om: "0 < \<Omega>" unfolding \<Omega>_def using Gd2 by simp
  have gbp: "0 < (gq + gm) / 2" using assms(5) by simp
  define T where "T = arctan (2 * \<Omega> / ((gq + gm) / 2)) / \<Omega>"
  have T0: "0 \<le> T" unfolding T_def using om gbp by (intro divide_nonneg_pos) simp_all
  have adm: "pulse G gq gm T (res_A G gq gm) (res_B G gq gm) (res_u G gq gm)"
  proof (unfold_locales)
    show "0 < G" by fact show "0 \<le> gq" by fact show "0 \<le> gm" by fact show "\<bar>gq - gm\<bar> / 4 < G" by fact
    show "0 \<le> T" by (rule T0)
    show "\<And>t. t \<in> {0..T} \<Longrightarrow> (res_A G gq gm has_real_derivative (- gq * res_A G gq gm t - 2 * res_u G gq gm t)) (at t within {0..T})"
      using res_A_deriv[OF assms(1) Gd2] by (auto intro: has_field_derivative_at_within)
    show "\<And>t. t \<in> {0..T} \<Longrightarrow> (res_B G gq gm has_real_derivative (- gm * res_B G gq gm t + 2 * res_u G gq gm t)) (at t within {0..T})"
      using res_B_deriv[OF assms(1) Gd2] by (auto intro: has_field_derivative_at_within)
    show "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> res_A G gq gm t" using res_admissible(4)[OF assms(1) Gd2] by simp
    show "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> res_B G gq gm t" using res_admissible(5)[OF assms(1) Gd2] by simp
    show "\<And>t. t \<in> {0..T} \<Longrightarrow> (res_u G gq gm t)\<^sup>2 \<le> G\<^sup>2 * res_A G gq gm t * res_B G gq gm t"
      using res_admissible(1)[OF assms(1) Gd2] by simp
    show "res_A G gq gm 0 = 1" using res_admissible(2)[OF assms(1) Gd2] .
    show "res_B G gq gm 0 = 0" using res_admissible(3)[OF assms(1) Gd2] .
  qed
  have "res_B G gq gm T = G\<^sup>2 / \<Omega>\<^sup>2 * exp (- ((gq + gm) / 2) * T) * (sin (\<Omega> * T))\<^sup>2"
    unfolding res_B_def res_Om_def \<Omega>_def by simp
  also have "\<dots> = 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- (((gq + gm) / 2) / \<Omega>) * arctan (2 * \<Omega> / ((gq + gm) / 2)))"
    by (rule resonant_pulse_max_attained[OF assms(1,2,3) refl gbp refl Gd2 \<Omega>_def T_def])
  also have "\<dots> = max_population G gq gm" unfolding max_population_def \<Omega>_def by simp
  finally show ?thesis using T0 adm by blast
qed

end
