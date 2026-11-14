(*  Title:      Memory_Access_Over.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License: BSD

    Theorem 1 of "Exact limits for writing a quantum memory" (C. Marín, draft, November 2026),
    relaxation only: no control pulse transfers more population than the resonant one, in the
    critical regime |gq - gm| = 4G and in the over-damped regime |gq - gm| > 4G (the under-damped
    regime is Memory_Access_All_Pulses).
*)

theory Memory_Access_Over
  imports Memory_Access_Regimes
begin

section \<open>A. Auxiliary real lemmas\<close>

lemma mono_open:
  fixes g :: "real \<Rightarrow> real" and t :: real
  assumes "0 < t" and "continuous_on {0..t} g"
    and "\<forall>s\<in>{0<..<t}. \<exists>D. (g has_real_derivative D) (at s) \<and> 0 \<le> D"
  shows "g 0 \<le> g t"
proof -
  obtain D where D: "\<And>s. s \<in> {0<..<t} \<Longrightarrow> (g has_real_derivative D s) (at s) \<and> 0 \<le> D s"
    using assms(3) by (metis bchoice)
  have hd: "(g has_derivative (\<lambda>h. D x * h)) (at x)" if x: "0 < x" "x < t" for x
  proof -
    have "x \<in> {0<..<t}" using x by simp
    then show ?thesis by (rule has_field_derivative_imp_has_derivative[OF conjunct1[OF D]])
  qed
  obtain \<xi> where xi: "0 < \<xi>" "\<xi> < t" "g t - g 0 = D \<xi> * (t - 0)"
    using mvt[OF assms(1,2) hd] by blast
  have "0 \<le> D \<xi>" using D xi(1,2) by simp
  then have "0 \<le> g t - g 0" using xi(3) assms(1) by simp
  then show ?thesis by simp
qed

lemma ev_right:
  fixes P :: "real \<Rightarrow> bool" and e :: real
  assumes "0 < e" and "\<forall>x. 0 < x \<and> x < e \<longrightarrow> P x"
  shows "\<forall>\<^sub>F x in at_right (0::real). P x"
  unfolding eventually_at_right_field using assms by (intro exI[of _ e]) auto

lemma cont_right:
  fixes f :: "real \<Rightarrow> real"
  assumes "isCont f 0"
  shows "(f \<longlongrightarrow> f 0) (at_right 0)"
proof -
  have "(f \<longlongrightarrow> f 0) (at 0)" using assms by (simp add: isCont_def)
  then show ?thesis by (rule Lim_at_imp_Lim_at_within)
qed

lemma isCont_ln_pos:
  fixes f :: "real \<Rightarrow> real" and x :: real
  assumes "isCont f x" and "0 < f x"
  shows "isCont (\<lambda>s. ln (f s)) x"
proof -
  have "isCont ln (f x)" using DERIV_isCont[OF DERIV_ln_divide[OF assms(2)]] .
  then show ?thesis by (rule isCont_o2[OF assms(1)])
qed

lemma cont_on_ln:
  fixes f :: "real \<Rightarrow> real" and S :: "real set"
  assumes "continuous_on S f" and "\<forall>x\<in>S. 0 < f x"
  shows "continuous_on S (\<lambda>x. ln (f x))"
proof -
  have "continuous_on {0<..} (ln :: real \<Rightarrow> real)"
    by (rule continuous_at_imp_continuous_on) (auto intro: DERIV_isCont[OF DERIV_ln_divide])
  then show ?thesis using assms by (intro continuous_on_compose2[OF _ assms(1)]) auto
qed

lemma persist_alg:
  fixes a b u G gq gm c m :: real
  assumes "0 < a" and "0 < b" and "m - gq / 2 = - c" and "c * (m - gm / 2) = G\<^sup>2"
  shows "G * ((- gq * a\<^sup>2 - 2 * u) / (2 * a)) + c * ((- gm * b\<^sup>2 + 2 * u) / (2 * b)) + m * (G * a + c * b)
         = (G * b - c * a) * (G * a * b - u) / (a * b)"
proof -
  have key: "G * ((- gq * a\<^sup>2 - 2 * u) / (2 * a)) + c * ((- gm * b\<^sup>2 + 2 * u) / (2 * b)) + m * (G * a + c * b)
         - (G * b - c * a) * (G * a * b - u) / (a * b)
         = G * a * (m - gq / 2 + c) + b * (c * (m - gm / 2) - G\<^sup>2)"
    using assms(1,2) by (simp add: field_simps power2_eq_square)
  have "m - gq / 2 + c = 0" using assms(3) by simp
  moreover have "c * (m - gm / 2) - G\<^sup>2 = 0" using assms(4) by simp
  ultimately show ?thesis using key by simp
qed

lemma hyp_deriv_nonneg:
  fixes a b u G gq gm k cp cq m1 m2 p q :: real
  assumes "0 < a" and "0 < b" and "0 < G" and "0 \<le> gq" and "0 \<le> gm" and "0 < k" and "0 < p" and "0 < q"
    and "u \<le> G * a * b" and "k\<^sup>2 = (gq - gm)\<^sup>2 / 16 - G\<^sup>2"
    and "cp = (gq - gm) / 4 + k" and "cq = (gq - gm) / 4 - k"
    and "m1 = (gq + gm) / 4 - k" and "m2 = (gq + gm) / 4 + k"
    and "p = G * a + cp * b" and "q = G * a + cq * b"
  shows "0 \<le> m1 * (G * ((- gq * a\<^sup>2 - 2 * u) / (2 * a)) + cq * ((- gm * b\<^sup>2 + 2 * u) / (2 * b))) / q
             - m2 * (G * ((- gq * a\<^sup>2 - 2 * u) / (2 * a)) + cp * ((- gm * b\<^sup>2 + 2 * u) / (2 * b))) / p"
proof -
  have ne: "a \<noteq> 0" "b \<noteq> 0" "p \<noteq> 0" "q \<noteq> 0" using assms(1,2,7,8) by simp_all
  have key: "m1 * (G * (- gq * a\<^sup>2 - 2 * u) * b + cq * (- gm * b\<^sup>2 + 2 * u) * a) * p
        - m2 * (G * (- gq * a\<^sup>2 - 2 * u) * b + cp * (- gm * b\<^sup>2 + 2 * u) * a) * q
        - 2 * (G * a * b - u) * G * k * (gq * a\<^sup>2 + gm * b\<^sup>2)
        = 2 * a * b * k * (- gm * b\<^sup>2 + 2 * u) * (k\<^sup>2 - (gq - gm)\<^sup>2 / 16 + G\<^sup>2)"
    by (simp add: assms(11-16) field_simps power2_eq_square)
  have z: "k\<^sup>2 - (gq - gm)\<^sup>2 / 16 + G\<^sup>2 = 0" using assms(10) by simp
  have num: "m1 * (G * (- gq * a\<^sup>2 - 2 * u) * b + cq * (- gm * b\<^sup>2 + 2 * u) * a) * p
        - m2 * (G * (- gq * a\<^sup>2 - 2 * u) * b + cp * (- gm * b\<^sup>2 + 2 * u) * a) * q
        = 2 * (G * a * b - u) * G * k * (gq * a\<^sup>2 + gm * b\<^sup>2)"
    using key z by simp
  have e: "m1 * (G * ((- gq * a\<^sup>2 - 2 * u) / (2 * a)) + cq * ((- gm * b\<^sup>2 + 2 * u) / (2 * b))) / q
             - m2 * (G * ((- gq * a\<^sup>2 - 2 * u) / (2 * a)) + cp * ((- gm * b\<^sup>2 + 2 * u) / (2 * b))) / p
        = (m1 * (G * (- gq * a\<^sup>2 - 2 * u) * b + cq * (- gm * b\<^sup>2 + 2 * u) * a) * p
        - m2 * (G * (- gq * a\<^sup>2 - 2 * u) * b + cp * (- gm * b\<^sup>2 + 2 * u) * a) * q) / (2 * a * b * p * q)"
    using ne by (simp add: field_simps)
  have w0: "0 \<le> G * a * b - u" using assms(9) by simp
  have "0 \<le> 2 * (G * a * b - u) * G * k * (gq * a\<^sup>2 + gm * b\<^sup>2)"
    using w0 assms(3,4,5,6) by (intro mult_nonneg_nonneg add_nonneg_nonneg) simp_all
  moreover have "0 < 2 * a * b * p * q" using assms(1,2,7,8) by simp
  ultimately show ?thesis unfolding e num by (rule divide_nonneg_pos)
qed

lemma dJ:
  fixes a b :: "real \<Rightarrow> real" and a' b' G cp cq m1 m2 t :: real
  assumes "0 < G * a t + cq * b t" and "0 < G * a t + cp * b t"
    and "(a has_real_derivative a') (at t)" and "(b has_real_derivative b') (at t)"
  shows "((\<lambda>s. m1 * ln (G * a s + cq * b s) - m2 * ln (G * a s + cp * b s)) has_real_derivative
      (m1 * (G * a' + cq * b') / (G * a t + cq * b t) - m2 * (G * a' + cp * b') / (G * a t + cp * b t))) (at t)"
proof -
  have dq: "((\<lambda>s. G * a s + cq * b s) has_real_derivative G * a' + cq * b') (at t)"
    by (intro DERIV_add DERIV_cmult assms(3,4))
  have dp: "((\<lambda>s. G * a s + cp * b s) has_real_derivative G * a' + cp * b') (at t)"
    by (intro DERIV_add DERIV_cmult assms(3,4))
  have l1: "((\<lambda>s. ln (G * a s + cq * b s)) has_real_derivative
      (1 / (G * a t + cq * b t)) * (G * a' + cq * b')) (at t)"
    by (rule DERIV_chain'[OF dq DERIV_ln_divide[OF assms(1)]])
  have l2: "((\<lambda>s. ln (G * a s + cp * b s)) has_real_derivative
      (1 / (G * a t + cp * b t)) * (G * a' + cp * b')) (at t)"
    by (rule DERIV_chain'[OF dp DERIV_ln_divide[OF assms(2)]])
  have "((\<lambda>s. m1 * ln (G * a s + cq * b s) - m2 * ln (G * a s + cp * b s)) has_real_derivative
      m1 * ((1 / (G * a t + cq * b t)) * (G * a' + cq * b')) - m2 * ((1 / (G * a t + cp * b t)) * (G * a' + cp * b'))) (at t)"
    by (rule DERIV_diff[OF DERIV_cmult[OF l1] DERIV_cmult[OF l2]])
  then show ?thesis by (rule DERIV_cong) simp
qed

lemma crit_alg:
  fixes a b u G gq gm y :: real
  assumes "0 < a" and "0 < b" and "0 < y" and "G\<^sup>2 = (gq - gm)\<^sup>2 / 16" and "y = G * a + (gq - gm) / 4 * b"
  shows "(G * ((- gq * a\<^sup>2 - 2 * u) / (2 * a)) + (gq - gm) / 4 * ((- gm * b\<^sup>2 + 2 * u) / (2 * b))) / y
      + (gq + gm) / 4 * (((- gm * b\<^sup>2 + 2 * u) / (2 * b) * y
           - b * (G * ((- gq * a\<^sup>2 - 2 * u) / (2 * a)) + (gq - gm) / 4 * ((- gm * b\<^sup>2 + 2 * u) / (2 * b)))) / y\<^sup>2)
      = - ((G * a * b - u) * (G * (gq * a\<^sup>2 + gm * b\<^sup>2))) / (2 * a * b * y\<^sup>2)"
proof -
  have ne: "a \<noteq> 0" "b \<noteq> 0" "y \<noteq> 0" using assms(1,2,3) by simp_all
  have key: "(G * (- gq * a\<^sup>2 - 2 * u) * b + (gq - gm) / 4 * (- gm * b\<^sup>2 + 2 * u) * a) * y
        + (gq + gm) / 4 * G * ((- gm * b\<^sup>2 + 2 * u) * a\<^sup>2 - (- gq * a\<^sup>2 - 2 * u) * b\<^sup>2)
        + (G * a * b - u) * (G * (gq * a\<^sup>2 + gm * b\<^sup>2))
        = - a * b * (- gm * b\<^sup>2 + 2 * u) * (G\<^sup>2 - (gq - gm)\<^sup>2 / 16)"
    by (simp add: assms(5) field_simps power2_eq_square)
  have z: "G\<^sup>2 - (gq - gm)\<^sup>2 / 16 = 0" using assms(4) by simp
  have num: "(G * (- gq * a\<^sup>2 - 2 * u) * b + (gq - gm) / 4 * (- gm * b\<^sup>2 + 2 * u) * a) * y
        + (gq + gm) / 4 * G * ((- gm * b\<^sup>2 + 2 * u) * a\<^sup>2 - (- gq * a\<^sup>2 - 2 * u) * b\<^sup>2)
        = - ((G * a * b - u) * (G * (gq * a\<^sup>2 + gm * b\<^sup>2)))"
    using key z by simp
  have s1: "(- gm * b\<^sup>2 + 2 * u) / (2 * b) * y
           - b * (G * ((- gq * a\<^sup>2 - 2 * u) / (2 * a)) + (gq - gm) / 4 * ((- gm * b\<^sup>2 + 2 * u) / (2 * b)))
         = G * ((- gm * b\<^sup>2 + 2 * u) * a\<^sup>2 - (- gq * a\<^sup>2 - 2 * u) * b\<^sup>2) / (2 * a * b)"
    using ne(1,2) by (simp add: assms(5) field_simps power2_eq_square)
  have e: "(G * ((- gq * a\<^sup>2 - 2 * u) / (2 * a)) + (gq - gm) / 4 * ((- gm * b\<^sup>2 + 2 * u) / (2 * b))) / y
      + (gq + gm) / 4 * (((- gm * b\<^sup>2 + 2 * u) / (2 * b) * y
           - b * (G * ((- gq * a\<^sup>2 - 2 * u) / (2 * a)) + (gq - gm) / 4 * ((- gm * b\<^sup>2 + 2 * u) / (2 * b)))) / y\<^sup>2)
      = ((G * (- gq * a\<^sup>2 - 2 * u) * b + (gq - gm) / 4 * (- gm * b\<^sup>2 + 2 * u) * a) * y
        + (gq + gm) / 4 * G * ((- gm * b\<^sup>2 + 2 * u) * a\<^sup>2 - (- gq * a\<^sup>2 - 2 * u) * b\<^sup>2)) / (2 * a * b * y\<^sup>2)"
    unfolding s1 using ne by (simp add: field_simps power2_eq_square)
  show ?thesis unfolding e num by simp
qed

lemma dV:
  fixes a b :: "real \<Rightarrow> real" and a' b' G c gh t :: real
  assumes "0 < G * a t + c * b t"
    and "(a has_real_derivative a') (at t)" and "(b has_real_derivative b') (at t)"
  shows "((\<lambda>s. ln (G * a s + c * b s) + gh * (b s / (G * a s + c * b s))) has_real_derivative
      ((G * a' + c * b') / (G * a t + c * b t)
       + gh * ((b' * (G * a t + c * b t) - b t * (G * a' + c * b')) / (G * a t + c * b t)\<^sup>2))) (at t)"
proof -
  have ne: "G * a t + c * b t \<noteq> 0" using assms(1) by simp
  have dy: "((\<lambda>s. G * a s + c * b s) has_real_derivative G * a' + c * b') (at t)"
    by (intro DERIV_add DERIV_cmult assms(2,3))
  have l1: "((\<lambda>s. ln (G * a s + c * b s)) has_real_derivative
      (1 / (G * a t + c * b t)) * (G * a' + c * b')) (at t)"
    by (rule DERIV_chain'[OF dy DERIV_ln_divide[OF assms(1)]])
  have qd: "((\<lambda>s. b s / (G * a s + c * b s)) has_real_derivative
      (b' * (G * a t + c * b t) - (G * a' + c * b') * b t) / (G * a t + c * b t)\<^sup>2) (at t)"
    by (rule DERIV_cong[OF DERIV_quotient[OF assms(3) dy ne]]) (simp add: power2_eq_square)
  have "((\<lambda>s. ln (G * a s + c * b s) + gh * (b s / (G * a s + c * b s))) has_real_derivative
      (1 / (G * a t + c * b t)) * (G * a' + c * b')
      + gh * ((b' * (G * a t + c * b t) - (G * a' + c * b') * b t) / (G * a t + c * b t)\<^sup>2)) (at t)"
    by (rule DERIV_add[OF l1 DERIV_cmult[OF qd]])
  then show ?thesis by (rule DERIV_cong) (simp add: mult.commute)
qed

section \<open>B. The model without a relation between G and the rates\<close>

text \<open>Same model as locale @{text pulse} of Memory_Access_All_Pulses, without the hypothesis on
  @{text "|gq - gm|/4"}: the regularised amplitudes and their derivatives do not use it.\<close>

locale pulse_open =
  fixes G gq gm T :: real and A B u :: "real \<Rightarrow> real"
  assumes G: "0 < G" and gq: "0 \<le> gq" and gm: "0 \<le> gm" and T: "0 \<le> T"
    and dA: "\<And>t. t \<in> {0..T} \<Longrightarrow> (A has_real_derivative (- gq * A t - 2 * u t)) (at t within {0..T})"
    and dB: "\<And>t. t \<in> {0..T} \<Longrightarrow> (B has_real_derivative (- gm * B t + 2 * u t)) (at t within {0..T})"
    and A_nn: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> A t"
    and B_nn: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> B t"
    and uineq: "\<And>t. t \<in> {0..T} \<Longrightarrow> (u t)\<^sup>2 \<le> G\<^sup>2 * A t * B t"
    and A_0: "A 0 = 1" and B_0: "B 0 = 0"
begin

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

lemma sqrt_pa0:
  assumes "0 < \<eta>"
  shows "sqrt (pa (\<eta>\<^sup>2) 0) = sqrt (1 + \<eta>\<^sup>2)" and "sqrt (pb (\<eta>\<^sup>2) 0) = \<eta>"
proof -
  show "sqrt (pa (\<eta>\<^sup>2) 0) = sqrt (1 + \<eta>\<^sup>2)" by (simp add: pa_def A_0)
  have "pb (\<eta>\<^sup>2) 0 = \<eta>\<^sup>2" by (simp add: pb_def B_0)
  then show "sqrt (pb (\<eta>\<^sup>2) 0) = \<eta>" using assms by simp
qed

lemma cont_sqrt_pa:
  assumes "0 < d"
  shows "continuous_on {0..T} (\<lambda>s. sqrt (pa d s))"
proof -
  have "continuous_on {0..T} (pa d)" unfolding pa_eq by (intro continuous_intros contA)
  then show ?thesis by (intro continuous_intros)
qed

lemma cont_sqrt_pb:
  assumes "0 < d"
  shows "continuous_on {0..T} (\<lambda>s. sqrt (pb d s))"
proof -
  have "continuous_on {0..T} (pb d)" unfolding pb_eq by (intro continuous_intros contB)
  then show ?thesis by (intro continuous_intros)
qed

lemma persist:
  assumes "0 < d" and "t \<in> {0..T}" and "c \<le> 0"
    and "m - gq / 2 = - c" and "c * (m - gm / 2) = G\<^sup>2"
    and "0 < G * sqrt (pa d 0) + c * sqrt (pb d 0)"
  shows "exp (- m * t) * (G * sqrt (pa d 0) + c * sqrt (pb d 0)) \<le> G * sqrt (pa d t) + c * sqrt (pb d t)"
proof (cases "t = 0")
  case True then show ?thesis by simp
next
  case False
  then have t0: "0 < t" using assms(2) by simp
  have tT: "t \<le> T" using assms(2) by simp
  define q where "q = (\<lambda>s. G * sqrt (pa d s) + c * sqrt (pb d s))"
  define h where "h = (\<lambda>s. exp (m * s) * q s)"
  have step: "\<exists>D. (h has_real_derivative D) (at s) \<and> 0 \<le> D" if s: "s \<in> {0<..<t}" for s
  proof -
    have s0: "0 < s" and sT: "s < T" and sI: "s \<in> {0..T}" using s tT by auto
    have a0: "0 < sqrt (pa d s)" using pa_pos[OF assms(1) sI] by simp
    have b0: "0 < sqrt (pb d s)" using pb_pos[OF assms(1) sI] by simp
    define E where "E = G * ((- gq * (sqrt (pa d s))\<^sup>2 - 2 * u s) / (2 * sqrt (pa d s)))
        + c * ((- gm * (sqrt (pb d s))\<^sup>2 + 2 * u s) / (2 * sqrt (pb d s)))"
    define W where "W = (G * sqrt (pb d s) - c * sqrt (pa d s)) * (G * sqrt (pa d s) * sqrt (pb d s) - u s)
          / (sqrt (pa d s) * sqrt (pb d s))"
    have dq: "(q has_real_derivative E) (at s)"
      unfolding q_def E_def
      by (intro DERIV_add DERIV_cmult sqrt_pa_deriv[OF assms(1) s0 sT] sqrt_pb_deriv[OF assms(1) s0 sT])
    have de: "((\<lambda>x. exp (m * x)) has_real_derivative exp (m * s) * m) (at s)"
      by (auto intro!: derivative_eq_intros)
    have dh: "(h has_real_derivative exp (m * s) * m * q s + exp (m * s) * E) (at s)"
      unfolding h_def by (rule DERIV_cong[OF DERIV_mult[OF de dq]]) (simp add: algebra_simps)
    have pe: "E + m * q s = W"
      unfolding E_def W_def q_def by (rule persist_alg[OF a0 b0 assms(4,5)])
    have nn: "0 \<le> W"
    proof -
      have h1: "0 \<le> - c * sqrt (pa d s)" using assms(3) a0 by (intro mult_nonneg_nonneg) simp_all
      have h2: "0 < G * sqrt (pb d s)" using G b0 by simp
      have "0 \<le> G * sqrt (pb d s) - c * sqrt (pa d s)" using h1 h2 by linarith
      moreover have "0 \<le> G * sqrt (pa d s) * sqrt (pb d s) - u s" using u_le[OF assms(1) sI] by simp
      ultimately show ?thesis unfolding W_def using a0 b0 by (intro divide_nonneg_pos mult_nonneg_nonneg) simp_all
    qed
    have eq: "exp (m * s) * m * q s + exp (m * s) * E = exp (m * s) * W"
      by (simp add: pe[symmetric] algebra_simps)
    have pos: "0 \<le> exp (m * s) * m * q s + exp (m * s) * E" unfolding eq using nn by simp
    show ?thesis using dh pos by blast
  qed
  have cq: "continuous_on {0..t} q"
  proof -
    have "continuous_on {0..T} q"
      unfolding q_def by (intro continuous_intros cont_sqrt_pa[OF assms(1)] cont_sqrt_pb[OF assms(1)])
    then show ?thesis by (rule continuous_on_subset) (use tT in auto)
  qed
  have ch: "continuous_on {0..t} h" unfolding h_def by (intro continuous_intros cq)
  have hh: "h 0 \<le> h t" by (rule mono_open[OF t0 ch]) (use step in blast)
  have h0: "q 0 \<le> exp (m * t) * q t" using hh unfolding h_def by simp
  have e: "exp (- m * t) * exp (m * t) = 1" by (simp flip: exp_add)
  have "exp (- m * t) * q 0 \<le> exp (- m * t) * (exp (m * t) * q t)" by (intro mult_left_mono h0) simp
  also have "\<dots> = (exp (- m * t) * exp (m * t)) * q t" by (rule mult.assoc[symmetric])
  also have "\<dots> = q t" by (subst e) simp
  finally show ?thesis unfolding q_def .
qed

lemma persist_limit:
  assumes "t \<in> {0..T}" and "c < 0"
    and "m - gq / 2 = - c" and "c * (m - gm / 2) = G\<^sup>2"
  shows "exp (- m * t) * G \<le> G * sqrt (A t) + c * sqrt (B t)"
proof -
  define e where "e = G / (- c)"
  have e0: "0 < e" unfolding e_def by (rule divide_pos_pos[OF G]) (use assms(2) in simp)
  have lhs: "((\<lambda>x. exp (- m * t) * (G * sqrt (1 + x\<^sup>2) + c * x)) \<longlongrightarrow> exp (- m * t) * G) (at_right 0)"
  proof -
    have "isCont (\<lambda>x. exp (- m * t) * (G * sqrt (1 + x\<^sup>2) + c * x)) 0" by (intro continuous_intros)
    then have "((\<lambda>x. exp (- m * t) * (G * sqrt (1 + x\<^sup>2) + c * x)) \<longlongrightarrow>
        exp (- m * t) * (G * sqrt (1 + 0\<^sup>2) + c * 0)) (at_right 0)" by (rule cont_right)
    then show ?thesis by simp
  qed
  have rhs: "((\<lambda>x. G * sqrt (pa (x\<^sup>2) t) + c * sqrt (pb (x\<^sup>2) t)) \<longlongrightarrow> G * sqrt (A t) + c * sqrt (B t)) (at_right 0)"
  proof -
    have "isCont (\<lambda>x. G * sqrt (A t + x\<^sup>2 * exp (- gq * t)) + c * sqrt (B t + x\<^sup>2 * exp (- gm * t))) 0"
      by (intro continuous_intros)
    then have "((\<lambda>x. G * sqrt (A t + x\<^sup>2 * exp (- gq * t)) + c * sqrt (B t + x\<^sup>2 * exp (- gm * t))) \<longlongrightarrow>
        G * sqrt (A t + 0\<^sup>2 * exp (- gq * t)) + c * sqrt (B t + 0\<^sup>2 * exp (- gm * t))) (at_right 0)" by (rule cont_right)
    then show ?thesis by (simp add: pa_def pb_def)
  qed
  have ev: "\<forall>\<^sub>F x in at_right (0::real). exp (- m * t) * (G * sqrt (1 + x\<^sup>2) + c * x)
        \<le> G * sqrt (pa (x\<^sup>2) t) + c * sqrt (pb (x\<^sup>2) t)"
  proof (rule ev_right[OF e0])
    show "\<forall>x. 0 < x \<and> x < e \<longrightarrow> exp (- m * t) * (G * sqrt (1 + x\<^sup>2) + c * x)
        \<le> G * sqrt (pa (x\<^sup>2) t) + c * sqrt (pb (x\<^sup>2) t)"
    proof (intro allI impI)
      fix x :: real assume x: "0 < x \<and> x < e"
      have xd: "0 < x\<^sup>2" using x by simp
      have s1: "1 \<le> sqrt (1 + x\<^sup>2)" by (rule real_le_rsqrt) simp
      have "- c * x < G" using x assms(2) unfolding e_def by (simp add: less_divide_eq field_simps)
      then have "0 < G + c * x" by simp
      moreover have "G \<le> G * sqrt (1 + x\<^sup>2)" using mult_left_mono[OF s1 less_imp_le[OF G]] by simp
      ultimately have q0: "0 < G * sqrt (pa (x\<^sup>2) 0) + c * sqrt (pb (x\<^sup>2) 0)"
        unfolding sqrt_pa0(1)[OF conjunct1[OF x]] sqrt_pa0(2)[OF conjunct1[OF x]] by linarith
      show "exp (- m * t) * (G * sqrt (1 + x\<^sup>2) + c * x) \<le> G * sqrt (pa (x\<^sup>2) t) + c * sqrt (pb (x\<^sup>2) t)"
        using persist[OF xd assms(1) less_imp_le[OF assms(2)] assms(3,4) q0]
        unfolding sqrt_pa0(1)[OF conjunct1[OF x]] sqrt_pa0(2)[OF conjunct1[OF x]] .
    qed
  qed
  show ?thesis by (rule tendsto_le[OF _ rhs lhs ev]) simp
qed

end


context pulse_open
begin

text \<open>Positivity of @{text "G a + c b"} along the regularised trajectory, for a linear form whose
  coefficient @{text c} satisfies the two relations of the eigen-coordinates (any @{text c} of either sign).\<close>

lemma qpos_gen:
  assumes "m - gq / 2 = - c" and "c * (m - gm / 2) = G\<^sup>2"
  shows "\<exists>e>0. \<forall>x. 0 < x \<and> x < e \<longrightarrow> (\<forall>s\<in>{0..T}. 0 < G * sqrt (pa (x\<^sup>2) s) + c * sqrt (pb (x\<^sup>2) s))"
proof (cases "0 \<le> c")
  case True
  have "\<forall>x. 0 < x \<and> x < 1 \<longrightarrow> (\<forall>s\<in>{0..T}. 0 < G * sqrt (pa (x\<^sup>2) s) + c * sqrt (pb (x\<^sup>2) s))"
  proof (intro allI impI ballI)
    fix x s :: real assume x: "0 < x \<and> x < 1" and s: "s \<in> {0..T}"
    have xd: "0 < x\<^sup>2" using x by simp
    have sp: "0 < sqrt (pa (x\<^sup>2) s)" using pa_pos[OF xd s] by simp
    have h1: "0 < G * sqrt (pa (x\<^sup>2) s)" by (rule mult_pos_pos[OF G sp])
    have h2: "0 \<le> c * sqrt (pb (x\<^sup>2) s)"
      by (rule mult_nonneg_nonneg[OF True]) (use pb_pos[OF xd s] in simp)
    show "0 < G * sqrt (pa (x\<^sup>2) s) + c * sqrt (pb (x\<^sup>2) s)" using h1 h2 by simp
  qed
  then show ?thesis by (intro exI[of _ 1]) simp
next
  case False
  then have cn: "c < 0" by simp
  define e where "e = G / (- c)"
  have e0: "0 < e" unfolding e_def by (rule divide_pos_pos[OF G]) (use cn in simp)
  have "\<forall>x. 0 < x \<and> x < e \<longrightarrow> (\<forall>s\<in>{0..T}. 0 < G * sqrt (pa (x\<^sup>2) s) + c * sqrt (pb (x\<^sup>2) s))"
  proof (intro allI impI ballI)
    fix x s :: real assume x: "0 < x \<and> x < e" and s: "s \<in> {0..T}"
    have xd: "0 < x\<^sup>2" using x by simp
    have s1: "1 \<le> sqrt (1 + x\<^sup>2)" by (rule real_le_rsqrt) simp
    have "- c * x < G" using x cn unfolding e_def by (simp add: less_divide_eq field_simps)
    then have "0 < G + c * x" by simp
    moreover have "G \<le> G * sqrt (1 + x\<^sup>2)" using mult_left_mono[OF s1 less_imp_le[OF G]] by simp
    ultimately have q0: "0 < G * sqrt (pa (x\<^sup>2) 0) + c * sqrt (pb (x\<^sup>2) 0)"
      unfolding sqrt_pa0(1)[OF conjunct1[OF x]] sqrt_pa0(2)[OF conjunct1[OF x]] by linarith
    have "exp (- m * s) * (G * sqrt (pa (x\<^sup>2) 0) + c * sqrt (pb (x\<^sup>2) 0)) \<le> G * sqrt (pa (x\<^sup>2) s) + c * sqrt (pb (x\<^sup>2) s)"
      by (rule persist[OF xd s less_imp_le[OF cn] assms q0])
    moreover have "0 < exp (- m * s) * (G * sqrt (pa (x\<^sup>2) 0) + c * sqrt (pb (x\<^sup>2) 0))" using q0 by simp
    ultimately show "0 < G * sqrt (pa (x\<^sup>2) s) + c * sqrt (pb (x\<^sup>2) s)" by linarith
  qed
  then show ?thesis using e0 by blast
qed

lemma qhat_gen:
  assumes "t \<in> {0..T}" and "0 < B t" and "m - gq / 2 = - c" and "c * (m - gm / 2) = G\<^sup>2"
  shows "0 < G * sqrt (A t) + c * sqrt (B t)"
proof -
  have bs: "0 < sqrt (B t)" using assms(2) by simp
  have an: "0 \<le> A t" using A_nn[OF assms(1)] .
  have as: "0 \<le> sqrt (A t)" using an by simp
  have cne: "c \<noteq> 0" using assms(4) G by auto
  show ?thesis
  proof (cases "0 < c")
    case True
    have h1: "0 \<le> G * sqrt (A t)" using G as by simp
    have h2: "0 < c * sqrt (B t)" by (rule mult_pos_pos[OF True bs])
    show ?thesis using h1 h2 by simp
  next
    case False
    then have cn: "c < 0" using cne by simp
    have "exp (- m * t) * G \<le> G * sqrt (A t) + c * sqrt (B t)"
      by (rule persist_limit[OF assms(1) cn assms(3,4)])
    moreover have "0 < exp (- m * t) * G" using G by simp
    ultimately show ?thesis by linarith
  qed
qed

end


section \<open>C. From the Lyapunov inequality to the bound\<close>

lemma exp_sq_exp:
  fixes x :: real
  shows "exp (2 * x) = (exp x)\<^sup>2"
  by (simp add: exp_double)

lemma hyp_final:
  fixes G k g4 q p b :: real
  assumes "0 < G" and "0 < k" and "k < g4" and "0 < b" and "0 < q" and "p = q + 2 * k * b"
    and "- (2 * k) * ln G \<le> (g4 - k) * ln q - (g4 + k) * ln p"
  shows "\<exists>\<tau>. 0 \<le> \<tau> \<and> b\<^sup>2 \<le> pulse_over G (2 * g4) k \<tau>"
proof -
  define m1 where "m1 = g4 - k"
  define m2 where "m2 = g4 + k"
  have m1pos: "0 < m1" unfolding m1_def using assms(3) by simp
  have kb1: "0 < k * b" using assms(2,4) by (rule mult_pos_pos)
  have pp: "0 < p" using assms(5,6) kb1 by linarith
  define \<tau> where "\<tau> = (ln G - ln p) / m1"
  have lp: "ln p = ln G - m1 * \<tau>" unfolding \<tau>_def using m1pos by simp
  have pexp: "p = G * exp (- m1 * \<tau>)"
  proof -
    have "p = exp (ln p)" using pp by simp
    also have "\<dots> = exp (ln G - m1 * \<tau>)" using lp by simp
    also have "\<dots> = G * exp (- m1 * \<tau>)" using assms(1) by (simp add: exp_diff exp_minus field_simps)
    finally show ?thesis .
  qed
  have e2: "m2 * ln p = m2 * ln G - m2 * m1 * \<tau>"
  proof -
    have "m2 * ln p = m2 * (ln G - m1 * \<tau>)" by (simp only: lp)
    then show ?thesis by (simp add: algebra_simps)
  qed
  have e3: "m2 * ln G - 2 * k * ln G = m1 * ln G" unfolding m1_def m2_def by (simp add: algebra_simps)
  have hyp: "- (2 * k) * ln G \<le> m1 * ln q - m2 * ln p" using assms(7) unfolding m1_def m2_def .
  have "m1 * (ln G - m2 * \<tau>) \<le> m1 * ln q" using hyp e2 e3 by (simp add: algebra_simps; linarith)
  then have lq: "ln G - m2 * \<tau> \<le> ln q" using m1pos by (simp add: mult_le_cancel_left_pos)
  have qge: "G * exp (- m2 * \<tau>) \<le> q"
  proof -
    have "exp (ln G - m2 * \<tau>) \<le> exp (ln q)" using lq by simp
    then show ?thesis using assms(1,5) by (simp add: exp_diff exp_minus field_simps)
  qed
  have difm: "m1 = g4 - k" and difp: "m2 = g4 + k" using m1_def m2_def by simp_all
  have step: "exp (- m1 * \<tau>) - exp (- m2 * \<tau>) = 2 * exp (- g4 * \<tau>) * sinh (k * \<tau>)"
  proof -
    have e1: "- m1 * \<tau> = - g4 * \<tau> + k * \<tau>" unfolding difm by (simp add: algebra_simps)
    have e2': "- m2 * \<tau> = - g4 * \<tau> + - (k * \<tau>)" unfolding difp by (simp add: algebra_simps)
    have x1: "exp (- m1 * \<tau>) = exp (- g4 * \<tau>) * exp (k * \<tau>)" by (simp only: e1 exp_add)
    have x2: "exp (- m2 * \<tau>) = exp (- g4 * \<tau>) * exp (- (k * \<tau>))" by (simp only: e2' exp_add)
    show ?thesis by (simp only: x1 x2 sinh_def) (simp add: field_simps)
  qed
  define R where "R = G * exp (- g4 * \<tau>) * sinh (k * \<tau>)"
  have kb: "k * b \<le> R"
  proof -
    have "2 * k * b = p - q" using assms(6) by simp
    also have "\<dots> \<le> G * exp (- m1 * \<tau>) - G * exp (- m2 * \<tau>)" using pexp qge by simp
    also have "\<dots> = G * (2 * exp (- g4 * \<tau>) * sinh (k * \<tau>))" using step by (simp add: right_diff_distrib[symmetric])
    finally show ?thesis unfolding R_def by simp
  qed
  have kb0: "0 < k * b" using assms(2,4) by simp
  have Rpos: "0 < R" using kb kb0 by simp
  have sh: "0 < sinh (k * \<tau>)"
  proof -
    have gp: "0 < G * exp (- g4 * \<tau>)" using assms(1) by simp
    have "0 < G * exp (- g4 * \<tau>) * sinh (k * \<tau>)" using Rpos unfolding R_def .
    then show ?thesis using gp by (rule zero_less_mult_pos)
  qed
  have kt: "0 < k * \<tau>" using sh by (simp add: sinh_real_pos_iff)
  have tpos0: "0 < \<tau>" by (rule zero_less_mult_pos[OF kt assms(2)])
  have tpos: "0 \<le> \<tau>" using tpos0 by simp
  have sq: "(k * b)\<^sup>2 \<le> R\<^sup>2" by (rule power_mono[OF kb less_imp_le[OF kb0]])
  have ee: "exp (- (2 * g4) * \<tau>) = (exp (- g4 * \<tau>))\<^sup>2"
  proof -
    have a: "- (2 * g4) * \<tau> = 2 * (- g4 * \<tau>)" by (simp add: algebra_simps)
    show ?thesis by (simp only: a exp_sq_exp)
  qed
  have "b\<^sup>2 = (k * b)\<^sup>2 / k\<^sup>2" using assms(2) by (simp add: power_mult_distrib field_simps)
  also have "\<dots> \<le> R\<^sup>2 / k\<^sup>2" using sq by (intro divide_right_mono) simp_all
  also have "\<dots> = pulse_over G (2 * g4) k \<tau>"
    unfolding R_def pulse_over_def ee using assms(2) by (simp add: power_mult_distrib power_divide field_simps)
  finally show ?thesis using tpos by blast
qed

lemma crit_final:
  fixes G g2 y b :: real
  assumes "0 < G" and "0 < g2" and "0 < y" and "0 \<le> b" and "ln y + g2 * (b / y) \<le> ln G"
  shows "b\<^sup>2 \<le> G\<^sup>2 * (b / y)\<^sup>2 * exp (- (2 * g2) * (b / y))"
proof -
  define \<rho> where "\<rho> = b / y"
  have r0: "0 \<le> \<rho>" unfolding \<rho>_def using assms(3,4) by simp
  have "ln y \<le> ln G - g2 * \<rho>" using assms(5) unfolding \<rho>_def by simp
  then have "exp (ln y) \<le> exp (ln G - g2 * \<rho>)" by (rule exp_le_cancel_iff[THEN iffD2])
  then have yle: "y \<le> G * exp (- g2 * \<rho>)"
    using assms(1,3) by (simp add: exp_diff exp_minus field_simps)
  have bb: "b = \<rho> * y" unfolding \<rho>_def using assms(3) by simp
  have "b \<le> \<rho> * (G * exp (- g2 * \<rho>))" unfolding bb using yle r0 by (intro mult_left_mono) simp_all
  then have sq: "b\<^sup>2 \<le> (\<rho> * (G * exp (- g2 * \<rho>)))\<^sup>2" by (rule power_mono) (use assms(4) in simp)
  have ee: "exp (- (2 * g2) * \<rho>) = (exp (- g2 * \<rho>))\<^sup>2"
  proof -
    have a: "- (2 * g2) * \<rho> = 2 * (- g2 * \<rho>)" by (simp add: algebra_simps)
    show ?thesis by (simp only: a exp_sq_exp)
  qed
  show ?thesis unfolding \<rho>_def[symmetric] ee using sq by (simp add: power_mult_distrib mult.assoc mult.left_commute)
qed


section \<open>D. The over-damped regime\<close>

text \<open>Eigen-coordinates of the resonant matrix: with @{text "kap = sqrt (d^2/16 - G^2)"}, @{text "d = gq - gm"},
  @{text "p = G a + (d/4 + kap) b"}, @{text "q = G a + (d/4 - kap) b"} satisfy @{text "p' = -m1 p"},
  @{text "q' = -m2 q"} for the resonant pulse, and the function
  @{text "J = m1 ln q - m2 ln p"} does not decrease for any admissible control.\<close>

locale pulses_over = pulse_open +
  assumes Ov: "G < \<bar>gq - gm\<bar> / 4"
begin

definition kap :: real where "kap = sqrt ((gq - gm)\<^sup>2 / 16 - G\<^sup>2)"
definition cq :: real where "cq = (gq - gm) / 4 - kap"
definition cp :: real where "cp = (gq - gm) / 4 + kap"
definition m1 :: real where "m1 = (gq + gm) / 4 - kap"
definition m2 :: real where "m2 = (gq + gm) / 4 + kap"

lemma kap_facts:
  shows "0 < kap" and "kap\<^sup>2 = (gq - gm)\<^sup>2 / 16 - G\<^sup>2" and "0 < (gq + gm) / 2"
    and "2 * kap < (gq + gm) / 2" and "0 < 4 * G\<^sup>2 + gq * gm"
  using overdamped_parameters[OF G gq gm refl refl Ov kap_def] by simp_all

lemma m1_pos: "0 < m1" unfolding m1_def using kap_facts(4) by simp

lemma cp_cq: "cp * cq = G\<^sup>2"
proof -
  have "cp * cq = ((gq - gm) / 4)\<^sup>2 - kap\<^sup>2" unfolding cp_def cq_def by (simp add: power2_eq_square algebra_simps)
  also have "\<dots> = G\<^sup>2" using kap_facts(2) by (simp add: power_divide)
  finally show ?thesis .
qed

lemma persist_consts:
  shows "m2 - gq / 2 = - cq" and "cq * (m2 - gm / 2) = G\<^sup>2"
proof -
  show "m2 - gq / 2 = - cq" unfolding m2_def cq_def by argo
  have h: "m2 - gm / 2 = cp" unfolding m2_def cp_def by argo
  have "cq * cp = G\<^sup>2" by (metis cp_cq mult.commute)
  then show "cq * (m2 - gm / 2) = G\<^sup>2" unfolding h .
qed

definition Jr :: "real \<Rightarrow> real \<Rightarrow> real" where
  "Jr a b = m1 * ln (G * a + cq * b) - m2 * ln (G * a + cp * b)"

lemma p_pos:
  assumes "0 < d" and "s \<in> {0..T}" and "0 < G * sqrt (pa d s) + cq * sqrt (pb d s)"
  shows "0 < G * sqrt (pa d s) + cp * sqrt (pb d s)"
proof -
  have hb: "0 < sqrt (pb d s)" using pb_pos[OF assms(1,2)] by simp
  have eq: "G * sqrt (pa d s) + cp * sqrt (pb d s) = (G * sqrt (pa d s) + cq * sqrt (pb d s)) + 2 * kap * sqrt (pb d s)"
    unfolding cp_def cq_def by (simp add: algebra_simps)
  have "0 < 2 * kap * sqrt (pb d s)" using kap_facts(1) hb by (intro mult_pos_pos) simp_all
  then show ?thesis using assms(3) eq by linarith
qed

lemma Jr_mono:
  assumes "0 < d" and "t \<in> {0..T}" and "\<forall>s\<in>{0..T}. 0 < G * sqrt (pa d s) + cq * sqrt (pb d s)"
  shows "Jr (sqrt (pa d 0)) (sqrt (pb d 0)) \<le> Jr (sqrt (pa d t)) (sqrt (pb d t))"
proof (cases "t = 0")
  case True then show ?thesis by simp
next
  case False
  then have t0: "0 < t" using assms(2) by simp
  have tT: "t \<le> T" using assms(2) by simp
  define g where "g = (\<lambda>s. m1 * ln (G * sqrt (pa d s) + cq * sqrt (pb d s)) - m2 * ln (G * sqrt (pa d s) + cp * sqrt (pb d s)))"
  have step: "\<exists>D. (g has_real_derivative D) (at s) \<and> 0 \<le> D" if s: "s \<in> {0<..<t}" for s
  proof -
    have s0: "0 < s" and sT: "s < T" and sI: "s \<in> {0..T}" using s tT by auto
    have a0: "0 < sqrt (pa d s)" using pa_pos[OF assms(1) sI] by simp
    have b0: "0 < sqrt (pb d s)" using pb_pos[OF assms(1) sI] by simp
    have qp: "0 < G * sqrt (pa d s) + cq * sqrt (pb d s)" using assms(3) sI by blast
    have pp: "0 < G * sqrt (pa d s) + cp * sqrt (pb d s)" by (rule p_pos[OF assms(1) sI qp])
    have h: "(g has_real_derivative
        (m1 * (G * ((- gq * (sqrt (pa d s))\<^sup>2 - 2 * u s) / (2 * sqrt (pa d s)))
               + cq * ((- gm * (sqrt (pb d s))\<^sup>2 + 2 * u s) / (2 * sqrt (pb d s)))) / (G * sqrt (pa d s) + cq * sqrt (pb d s))
         - m2 * (G * ((- gq * (sqrt (pa d s))\<^sup>2 - 2 * u s) / (2 * sqrt (pa d s)))
               + cp * ((- gm * (sqrt (pb d s))\<^sup>2 + 2 * u s) / (2 * sqrt (pb d s)))) / (G * sqrt (pa d s) + cp * sqrt (pb d s)))) (at s)"
      unfolding g_def
      by (rule dJ[where a = "\<lambda>x. sqrt (pa d x)" and b = "\<lambda>x. sqrt (pb d x)" and t = s, OF qp pp
          sqrt_pa_deriv[OF assms(1) s0 sT] sqrt_pb_deriv[OF assms(1) s0 sT]])
    have nn: "0 \<le> m1 * (G * ((- gq * (sqrt (pa d s))\<^sup>2 - 2 * u s) / (2 * sqrt (pa d s)))
               + cq * ((- gm * (sqrt (pb d s))\<^sup>2 + 2 * u s) / (2 * sqrt (pb d s)))) / (G * sqrt (pa d s) + cq * sqrt (pb d s))
         - m2 * (G * ((- gq * (sqrt (pa d s))\<^sup>2 - 2 * u s) / (2 * sqrt (pa d s)))
               + cp * ((- gm * (sqrt (pb d s))\<^sup>2 + 2 * u s) / (2 * sqrt (pb d s)))) / (G * sqrt (pa d s) + cp * sqrt (pb d s))"
      by (rule hyp_deriv_nonneg[OF a0 b0 G gq gm kap_facts(1) pp qp u_le[OF assms(1) sI] kap_facts(2)
            cp_def cq_def m1_def m2_def refl refl])
    show ?thesis using h nn by blast
  qed
  have cg: "continuous_on {0..t} g"
  proof -
    have q1: "continuous_on {0..T} (\<lambda>s. G * sqrt (pa d s) + cq * sqrt (pb d s))"
      by (intro continuous_intros cont_sqrt_pa[OF assms(1)] cont_sqrt_pb[OF assms(1)])
    have p1: "continuous_on {0..T} (\<lambda>s. G * sqrt (pa d s) + cp * sqrt (pb d s))"
      by (intro continuous_intros cont_sqrt_pa[OF assms(1)] cont_sqrt_pb[OF assms(1)])
    have ppos: "\<forall>s\<in>{0..T}. 0 < G * sqrt (pa d s) + cp * sqrt (pb d s)" using p_pos[OF assms(1)] assms(3) by blast
    have "continuous_on {0..T} g"
      unfolding g_def by (intro continuous_intros cont_on_ln q1 p1 assms(3) ppos)
    then show ?thesis by (rule continuous_on_subset) (use tT in auto)
  qed
  have "g 0 \<le> g t" by (rule mono_open[OF t0 cg]) (use step in blast)
  then show ?thesis unfolding g_def Jr_def by simp
qed

lemma hyp_limit:
  assumes tI: "t \<in> {0..T}" and qh: "0 < G * sqrt (A t) + cq * sqrt (B t)"
  shows "- (2 * kap) * ln G \<le> m1 * ln (G * sqrt (A t) + cq * sqrt (B t)) - m2 * ln (G * sqrt (A t) + cp * sqrt (B t))"
proof -
  obtain e where e0: "0 < e" and qs: "\<forall>x. 0 < x \<and> x < e \<longrightarrow> (\<forall>s\<in>{0..T}. 0 < G * sqrt (pa (x\<^sup>2) s) + cq * sqrt (pb (x\<^sup>2) s))"
    using qpos_gen[OF persist_consts(1) persist_consts(2)] by blast
  have ph: "0 < G * sqrt (A t) + cp * sqrt (B t)"
  proof -
    have bs: "0 \<le> sqrt (B t)" using B_nn[OF tI] by simp
    have eq: "G * sqrt (A t) + cp * sqrt (B t) = (G * sqrt (A t) + cq * sqrt (B t)) + 2 * kap * sqrt (B t)"
      unfolding cp_def cq_def by (simp add: algebra_simps)
    have "0 \<le> 2 * kap * sqrt (B t)" using kap_facts(1) bs by (intro mult_nonneg_nonneg) simp_all
    then show ?thesis using qh eq by linarith
  qed
  define f where "f = (\<lambda>x::real. m1 * ln (G * sqrt (A t + x\<^sup>2 * exp (- gq * t)) + cq * sqrt (B t + x\<^sup>2 * exp (- gm * t)))
      - m2 * ln (G * sqrt (A t + x\<^sup>2 * exp (- gq * t)) + cp * sqrt (B t + x\<^sup>2 * exp (- gm * t))))"
  define g where "g = (\<lambda>x::real. m1 * ln (G * sqrt (1 + x\<^sup>2) + cq * x) - m2 * ln (G * sqrt (1 + x\<^sup>2) + cp * x))"
  have fc: "isCont f 0"
  proof -
    have c1: "isCont (\<lambda>x::real. G * sqrt (A t + x\<^sup>2 * exp (- gq * t)) + cq * sqrt (B t + x\<^sup>2 * exp (- gm * t))) 0"
      by (intro continuous_intros)
    have c2: "isCont (\<lambda>x::real. G * sqrt (A t + x\<^sup>2 * exp (- gq * t)) + cp * sqrt (B t + x\<^sup>2 * exp (- gm * t))) 0"
      by (intro continuous_intros)
    have l1: "isCont (\<lambda>x::real. ln (G * sqrt (A t + x\<^sup>2 * exp (- gq * t)) + cq * sqrt (B t + x\<^sup>2 * exp (- gm * t)))) 0"
      by (rule isCont_ln_pos[OF c1]) (use qh in simp)
    have l2: "isCont (\<lambda>x::real. ln (G * sqrt (A t + x\<^sup>2 * exp (- gq * t)) + cp * sqrt (B t + x\<^sup>2 * exp (- gm * t)))) 0"
      by (rule isCont_ln_pos[OF c2]) (use ph in simp)
    show ?thesis unfolding f_def by (intro isCont_diff isCont_mult continuous_const l1 l2)
  qed
  have gc: "isCont g 0"
  proof -
    have c1: "isCont (\<lambda>x::real. G * sqrt (1 + x\<^sup>2) + cq * x) 0" by (intro continuous_intros)
    have c2: "isCont (\<lambda>x::real. G * sqrt (1 + x\<^sup>2) + cp * x) 0" by (intro continuous_intros)
    have l1: "isCont (\<lambda>x::real. ln (G * sqrt (1 + x\<^sup>2) + cq * x)) 0" by (rule isCont_ln_pos[OF c1]) (use G in simp)
    have l2: "isCont (\<lambda>x::real. ln (G * sqrt (1 + x\<^sup>2) + cp * x)) 0" by (rule isCont_ln_pos[OF c2]) (use G in simp)
    show ?thesis unfolding g_def by (intro isCont_diff isCont_mult continuous_const l1 l2)
  qed
  have fl: "(f \<longlongrightarrow> f 0) (at_right 0)" by (rule cont_right[OF fc])
  have gl: "(g \<longlongrightarrow> g 0) (at_right 0)" by (rule cont_right[OF gc])
  have ev: "\<forall>\<^sub>F x in at_right (0::real). g x \<le> f x"
  proof (rule ev_right[OF e0])
    show "\<forall>x. 0 < x \<and> x < e \<longrightarrow> g x \<le> f x"
    proof (intro allI impI)
      fix x :: real assume x: "0 < x \<and> x < e"
      have xd: "0 < x\<^sup>2" using x by simp
      have "Jr (sqrt (pa (x\<^sup>2) 0)) (sqrt (pb (x\<^sup>2) 0)) \<le> Jr (sqrt (pa (x\<^sup>2) t)) (sqrt (pb (x\<^sup>2) t))"
        by (rule Jr_mono[OF xd tI]) (use qs x in blast)
      then show "g x \<le> f x"
        unfolding Jr_def g_def f_def sqrt_pa0(1)[OF conjunct1[OF x]] sqrt_pa0(2)[OF conjunct1[OF x]] pa_def pb_def by (simp add: A_0 B_0 abs_of_pos[OF conjunct1[OF x]])
    qed
  qed
  have "g 0 \<le> f 0" by (rule tendsto_le[OF _ fl gl ev]) simp
  moreover have "g 0 = - (2 * kap) * ln G" unfolding g_def m1_def m2_def by (simp add: algebra_simps)
  moreover have "f 0 = m1 * ln (G * sqrt (A t) + cq * sqrt (B t)) - m2 * ln (G * sqrt (A t) + cp * sqrt (B t))"
    unfolding f_def by simp
  ultimately show ?thesis by simp
qed

theorem over_all_pulses:
  assumes "t \<in> {0..T}"
  shows "B t \<le> 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm)
            * exp (- ((gq + gm) / 2) * (artanh (2 * kap / ((gq + gm) / 2)) / kap))"
proof (cases "B t = 0")
  case True
  have "0 \<le> 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- ((gq + gm) / 2) * (artanh (2 * kap / ((gq + gm) / 2)) / kap))"
    by (intro mult_nonneg_nonneg divide_nonneg_pos) (use kap_facts(5) in simp_all)
  then show ?thesis using True by simp
next
  case False
  then have bpos: "0 < B t" using B_nn[OF assms] by simp
  have qh: "0 < G * sqrt (A t) + cq * sqrt (B t)" by (rule qhat_gen[OF assms bpos persist_consts(1) persist_consts(2)])
  have J: "- (2 * kap) * ln G \<le> m1 * ln (G * sqrt (A t) + cq * sqrt (B t)) - m2 * ln (G * sqrt (A t) + cp * sqrt (B t))"
    by (rule hyp_limit[OF assms qh])
  have pq: "G * sqrt (A t) + cp * sqrt (B t) = (G * sqrt (A t) + cq * sqrt (B t)) + 2 * kap * sqrt (B t)"
    unfolding cp_def cq_def by (simp add: algebra_simps)
  have k4: "kap < (gq + gm) / 4" using kap_facts(4) by simp
  have bs: "0 < sqrt (B t)" using bpos by simp
  have J': "- (2 * kap) * ln G \<le> ((gq + gm) / 4 - kap) * ln (G * sqrt (A t) + cq * sqrt (B t))
      - ((gq + gm) / 4 + kap) * ln (G * sqrt (A t) + cp * sqrt (B t))"
    using J unfolding m1_def m2_def .
  obtain \<tau> where tau: "0 \<le> \<tau>" and pb: "(sqrt (B t))\<^sup>2 \<le> pulse_over G (2 * ((gq + gm) / 4)) kap \<tau>"
    using hyp_final[OF G kap_facts(1) k4 bs qh pq J'] by blast
  have "B t = (sqrt (B t))\<^sup>2" using bpos by (simp add: real_sqrt_pow2)
  also have "\<dots> \<le> pulse_over G ((gq + gm) / 2) kap \<tau>"
  proof -
    have e: "2 * ((gq + gm) / 4) = (gq + gm) / 2" by simp
    show ?thesis using pb unfolding e .
  qed
  also have "\<dots> \<le> 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- ((gq + gm) / 2) * (artanh (2 * kap / ((gq + gm) / 2)) / kap))"
    using over_pulse_max_bound[OF G gq gm refl refl Ov kap_def tau] by simp
  finally show ?thesis .
qed

end


section \<open>E. The critical regime\<close>

text \<open>For @{text "G = |gq - gm|/4"} the matrix of the resonant pulse is a Jordan block.  With
  @{text "y = G a + (d/4) b"}, the resonant pulse gives @{text "y' = -(gb/2) y"} and
  @{text "(b/y)' = 1"}, and @{text "V = ln y + (gb/2) (b/y)"} does not increase for any admissible control.\<close>

locale pulses_crit = pulse_open +
  assumes Cr: "G = \<bar>gq - gm\<bar> / 4"
begin

lemma G2: "G\<^sup>2 = (gq - gm)\<^sup>2 / 16"
proof -
  have "G\<^sup>2 = (\<bar>gq - gm\<bar> / 4)\<^sup>2" using Cr by simp
  then show ?thesis by (simp add: power_divide power2_abs)
qed

lemma gbar_pos: "0 < (gq + gm) / 2"
  using critical_pulse_max(1)[OF G gq gm refl refl Cr] .

lemma crit_consts:
  shows "(gq + gm) / 4 - gq / 2 = - ((gq - gm) / 4)"
    and "(gq - gm) / 4 * ((gq + gm) / 4 - gm / 2) = G\<^sup>2"
proof -
  show "(gq + gm) / 4 - gq / 2 = - ((gq - gm) / 4)" by argo
  have h: "(gq + gm) / 4 - gm / 2 = (gq - gm) / 4" by argo
  show "(gq - gm) / 4 * ((gq + gm) / 4 - gm / 2) = G\<^sup>2" unfolding h using G2 by (simp add: field_simps power2_eq_square)
qed

definition Vc :: "real \<Rightarrow> real \<Rightarrow> real" where
  "Vc a b = ln (G * a + (gq - gm) / 4 * b) + (gq + gm) / 4 * (b / (G * a + (gq - gm) / 4 * b))"

lemma Vc_mono:
  assumes "0 < d" and "t \<in> {0..T}" and "\<forall>s\<in>{0..T}. 0 < G * sqrt (pa d s) + (gq - gm) / 4 * sqrt (pb d s)"
  shows "Vc (sqrt (pa d t)) (sqrt (pb d t)) \<le> Vc (sqrt (pa d 0)) (sqrt (pb d 0))"
proof (cases "t = 0")
  case True then show ?thesis by simp
next
  case False
  then have t0: "0 < t" using assms(2) by simp
  have tT: "t \<le> T" using assms(2) by simp
  define g where "g = (\<lambda>s. - (ln (G * sqrt (pa d s) + (gq - gm) / 4 * sqrt (pb d s))
      + (gq + gm) / 4 * (sqrt (pb d s) / (G * sqrt (pa d s) + (gq - gm) / 4 * sqrt (pb d s)))))"
  have step: "\<exists>D. (g has_real_derivative D) (at s) \<and> 0 \<le> D" if s: "s \<in> {0<..<t}" for s
  proof -
    have s0: "0 < s" and sT: "s < T" and sI: "s \<in> {0..T}" using s tT by auto
    have a0: "0 < sqrt (pa d s)" using pa_pos[OF assms(1) sI] by simp
    have b0: "0 < sqrt (pb d s)" using pb_pos[OF assms(1) sI] by simp
    have qp: "0 < G * sqrt (pa d s) + (gq - gm) / 4 * sqrt (pb d s)" using assms(3) sI by blast
    note h = dV[where a = "\<lambda>x. sqrt (pa d x)" and b = "\<lambda>x. sqrt (pb d x)" and t = s
          and G = G and c = "(gq - gm) / 4" and gh = "(gq + gm) / 4", OF qp
          sqrt_pa_deriv[OF assms(1) s0 sT] sqrt_pb_deriv[OF assms(1) s0 sT]]
    note ca = crit_alg[OF a0 b0 qp G2 refl, of "u s"]
    have w0: "0 \<le> G * sqrt (pa d s) * sqrt (pb d s) - u s" using u_le[OF assms(1) sI] by simp
    have X: "0 \<le> (G * sqrt (pa d s) * sqrt (pb d s) - u s) * (G * (gq * (sqrt (pa d s))\<^sup>2 + gm * (sqrt (pb d s))\<^sup>2))"
      using w0 G gq gm by (intro mult_nonneg_nonneg add_nonneg_nonneg) simp_all
    have den: "0 < 2 * sqrt (pa d s) * sqrt (pb d s) * (G * sqrt (pa d s) + (gq - gm) / 4 * sqrt (pb d s))\<^sup>2"
      using a0 b0 qp by simp
    have nn: "0 \<le> (G * sqrt (pa d s) * sqrt (pb d s) - u s) * (G * (gq * (sqrt (pa d s))\<^sup>2 + gm * (sqrt (pb d s))\<^sup>2))
        / (2 * sqrt (pa d s) * sqrt (pb d s) * (G * sqrt (pa d s) + (gq - gm) / 4 * sqrt (pb d s))\<^sup>2)"
      by (rule divide_nonneg_pos[OF X den])
    note m1 = DERIV_minus[OF h]
    note m2 = m1[unfolded ca]
    have hm: "(g has_real_derivative ((G * sqrt (pa d s) * sqrt (pb d s) - u s) * (G * (gq * (sqrt (pa d s))\<^sup>2 + gm * (sqrt (pb d s))\<^sup>2))
        / (2 * sqrt (pa d s) * sqrt (pb d s) * (G * sqrt (pa d s) + (gq - gm) / 4 * sqrt (pb d s))\<^sup>2))) (at s)"
      unfolding g_def by (rule DERIV_cong[OF m2]) (simp only: minus_divide_left minus_minus)
    show ?thesis using hm nn by blast
  qed
  have cg: "continuous_on {0..t} g"
  proof -
    have q1: "continuous_on {0..T} (\<lambda>s. G * sqrt (pa d s) + (gq - gm) / 4 * sqrt (pb d s))"
      by (intro continuous_intros cont_sqrt_pa[OF assms(1)] cont_sqrt_pb[OF assms(1)])
    have ne: "\<forall>s\<in>{0..T}. G * sqrt (pa d s) + (gq - gm) / 4 * sqrt (pb d s) \<noteq> 0" using assms(3) by force
    have "continuous_on {0..T} g"
      unfolding g_def by (intro continuous_intros cont_on_ln q1 assms(3) cont_sqrt_pb[OF assms(1)] continuous_on_divide ne)
    then show ?thesis by (rule continuous_on_subset) (use tT in auto)
  qed
  have "g 0 \<le> g t" by (rule mono_open[OF t0 cg]) (use step in blast)
  then show ?thesis unfolding g_def Vc_def by simp
qed

lemma crit_limit:
  assumes tI: "t \<in> {0..T}" and qh: "0 < G * sqrt (A t) + (gq - gm) / 4 * sqrt (B t)"
  shows "ln (G * sqrt (A t) + (gq - gm) / 4 * sqrt (B t))
      + (gq + gm) / 4 * (sqrt (B t) / (G * sqrt (A t) + (gq - gm) / 4 * sqrt (B t))) \<le> ln G"
proof -
  obtain e where e0: "0 < e" and qs: "\<forall>x. 0 < x \<and> x < e \<longrightarrow> (\<forall>s\<in>{0..T}. 0 < G * sqrt (pa (x\<^sup>2) s) + (gq - gm) / 4 * sqrt (pb (x\<^sup>2) s))"
    using qpos_gen[OF crit_consts(1) crit_consts(2)] by blast
  define f where "f = (\<lambda>x::real. ln (G * sqrt (A t + x\<^sup>2 * exp (- gq * t)) + (gq - gm) / 4 * sqrt (B t + x\<^sup>2 * exp (- gm * t)))
      + (gq + gm) / 4 * (sqrt (B t + x\<^sup>2 * exp (- gm * t)) / (G * sqrt (A t + x\<^sup>2 * exp (- gq * t)) + (gq - gm) / 4 * sqrt (B t + x\<^sup>2 * exp (- gm * t)))))"
  define g where "g = (\<lambda>x::real. ln (G * sqrt (1 + x\<^sup>2) + (gq - gm) / 4 * x)
      + (gq + gm) / 4 * (x / (G * sqrt (1 + x\<^sup>2) + (gq - gm) / 4 * x)))"
  have fc: "isCont f 0"
  proof -
    have c1: "isCont (\<lambda>x::real. G * sqrt (A t + x\<^sup>2 * exp (- gq * t)) + (gq - gm) / 4 * sqrt (B t + x\<^sup>2 * exp (- gm * t))) 0"
      by (intro continuous_intros)
    have c2: "isCont (\<lambda>x::real. sqrt (B t + x\<^sup>2 * exp (- gm * t))) 0" by (intro continuous_intros)
    have l1: "isCont (\<lambda>x::real. ln (G * sqrt (A t + x\<^sup>2 * exp (- gq * t)) + (gq - gm) / 4 * sqrt (B t + x\<^sup>2 * exp (- gm * t)))) 0"
      by (rule isCont_ln_pos[OF c1]) (use qh in simp)
    have dv: "isCont (\<lambda>x::real. sqrt (B t + x\<^sup>2 * exp (- gm * t)) / (G * sqrt (A t + x\<^sup>2 * exp (- gq * t)) + (gq - gm) / 4 * sqrt (B t + x\<^sup>2 * exp (- gm * t)))) 0"
      by (rule isCont_divide[OF c2 c1]) (use qh in simp)
    show ?thesis unfolding f_def by (intro isCont_add isCont_mult continuous_const l1 dv)
  qed
  have gc: "isCont g 0"
  proof -
    have c1: "isCont (\<lambda>x::real. G * sqrt (1 + x\<^sup>2) + (gq - gm) / 4 * x) 0" by (intro continuous_intros)
    have c2: "isCont (\<lambda>x::real. x) 0" by (intro continuous_intros)
    have l1: "isCont (\<lambda>x::real. ln (G * sqrt (1 + x\<^sup>2) + (gq - gm) / 4 * x)) 0" by (rule isCont_ln_pos[OF c1]) (use G in simp)
    have dv: "isCont (\<lambda>x::real. x / (G * sqrt (1 + x\<^sup>2) + (gq - gm) / 4 * x)) 0"
      by (rule isCont_divide[OF c2 c1]) (use G in simp)
    show ?thesis unfolding g_def by (intro isCont_add isCont_mult continuous_const l1 dv)
  qed
  have fl: "(f \<longlongrightarrow> f 0) (at_right 0)" by (rule cont_right[OF fc])
  have gl: "(g \<longlongrightarrow> g 0) (at_right 0)" by (rule cont_right[OF gc])
  have ev: "\<forall>\<^sub>F x in at_right (0::real). f x \<le> g x"
  proof (rule ev_right[OF e0])
    show "\<forall>x. 0 < x \<and> x < e \<longrightarrow> f x \<le> g x"
    proof (intro allI impI)
      fix x :: real assume x: "0 < x \<and> x < e"
      have xd: "0 < x\<^sup>2" using x by simp
      have "Vc (sqrt (pa (x\<^sup>2) t)) (sqrt (pb (x\<^sup>2) t)) \<le> Vc (sqrt (pa (x\<^sup>2) 0)) (sqrt (pb (x\<^sup>2) 0))"
        by (rule Vc_mono[OF xd tI]) (use qs x in blast)
      then show "f x \<le> g x"
        unfolding Vc_def g_def f_def sqrt_pa0(1)[OF conjunct1[OF x]] sqrt_pa0(2)[OF conjunct1[OF x]] pa_def pb_def by (simp add: A_0 B_0 abs_of_pos[OF conjunct1[OF x]])
    qed
  qed
  have "f 0 \<le> g 0" by (rule tendsto_le[OF _ gl fl ev]) simp
  moreover have "g 0 = ln G" unfolding g_def by simp
  moreover have "f 0 = ln (G * sqrt (A t) + (gq - gm) / 4 * sqrt (B t))
      + (gq + gm) / 4 * (sqrt (B t) / (G * sqrt (A t) + (gq - gm) / 4 * sqrt (B t)))"
    unfolding f_def by simp
  ultimately show ?thesis by simp
qed

theorem critical_all_pulses:
  assumes "t \<in> {0..T}"
  shows "B t \<le> 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- 2)"
proof (cases "B t = 0")
  case True
  have "0 < 4 * G\<^sup>2 + gq * gm" using G gq gm by (intro add_pos_nonneg mult_nonneg_nonneg) simp_all
  then have "0 \<le> 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- 2)"
    by (intro mult_nonneg_nonneg divide_nonneg_pos) simp_all
  then show ?thesis using True by simp
next
  case False
  then have bpos: "0 < B t" using B_nn[OF assms] by simp
  have yh: "0 < G * sqrt (A t) + (gq - gm) / 4 * sqrt (B t)" by (rule qhat_gen[OF assms bpos crit_consts(1) crit_consts(2)])
  have J: "ln (G * sqrt (A t) + (gq - gm) / 4 * sqrt (B t))
      + (gq + gm) / 4 * (sqrt (B t) / (G * sqrt (A t) + (gq - gm) / 4 * sqrt (B t))) \<le> ln G"
    by (rule crit_limit[OF assms yh])
  have g4: "0 < (gq + gm) / 4" using gbar_pos by simp
  have fin: "(sqrt (B t))\<^sup>2 \<le> G\<^sup>2 * (sqrt (B t) / (G * sqrt (A t) + (gq - gm) / 4 * sqrt (B t)))\<^sup>2
      * exp (- (2 * ((gq + gm) / 4)) * (sqrt (B t) / (G * sqrt (A t) + (gq - gm) / 4 * sqrt (B t))))"
    by (rule crit_final[OF G g4 yh _ J]) (use bpos in simp)
  define \<rho> where "\<rho> = sqrt (B t) / (G * sqrt (A t) + (gq - gm) / 4 * sqrt (B t))"
  have r0: "0 \<le> \<rho>" unfolding \<rho>_def using yh bpos by simp
  have "B t = (sqrt (B t))\<^sup>2" using bpos by (simp add: real_sqrt_pow2)
  also have "\<dots> \<le> G\<^sup>2 * \<rho>\<^sup>2 * exp (- ((gq + gm) / 2) * \<rho>)"
  proof -
    have e: "2 * ((gq + gm) / 4) = (gq + gm) / 2" by simp
    show ?thesis unfolding \<rho>_def using fin[unfolded e] .
  qed
  also have "\<dots> \<le> 4 * G\<^sup>2 / ((gq + gm) / 2)\<^sup>2 * exp (- 2)" by (rule critical_pulse_max_bound[OF gbar_pos r0])
  also have "4 * G\<^sup>2 / ((gq + gm) / 2)\<^sup>2 = 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm)"
    using critical_pulse_max(2)[OF G gq gm refl refl Cr] .
  finally show ?thesis .
qed

end

section \<open>F. Theorem 1 in the two regimes, free of the locales\<close>

theorem memory_access_over:
  fixes G gq gm T :: real and A B u :: "real \<Rightarrow> real"
  assumes G: "0 < G" and gq: "0 \<le> gq" and gm: "0 \<le> gm" and Ov: "G < \<bar>gq - gm\<bar> / 4" and T: "0 \<le> T"
    and dA: "\<And>t. t \<in> {0..T} \<Longrightarrow> (A has_real_derivative (- gq * A t - 2 * u t)) (at t within {0..T})"
    and dB: "\<And>t. t \<in> {0..T} \<Longrightarrow> (B has_real_derivative (- gm * B t + 2 * u t)) (at t within {0..T})"
    and A_nn: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> A t" and B_nn: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> B t"
    and uineq: "\<And>t. t \<in> {0..T} \<Longrightarrow> (u t)\<^sup>2 \<le> G\<^sup>2 * A t * B t"
    and A0: "A 0 = 1" and B0: "B 0 = 0" and t: "t \<in> {0..T}"
  shows "B t \<le> 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm)
      * exp (- ((gq + gm) / 2) * (artanh (2 * sqrt ((gq - gm)\<^sup>2 / 16 - G\<^sup>2) / ((gq + gm) / 2))
          / sqrt ((gq - gm)\<^sup>2 / 16 - G\<^sup>2)))"
proof -
  interpret pulses_over G gq gm T A B u
    by unfold_locales (use assms in \<open>blast+\<close>)
  show ?thesis using over_all_pulses[OF t] unfolding kap_def by simp
qed

theorem memory_access_critical:
  fixes G gq gm T :: real and A B u :: "real \<Rightarrow> real"
  assumes G: "0 < G" and gq: "0 \<le> gq" and gm: "0 \<le> gm" and Cr: "G = \<bar>gq - gm\<bar> / 4" and T: "0 \<le> T"
    and dA: "\<And>t. t \<in> {0..T} \<Longrightarrow> (A has_real_derivative (- gq * A t - 2 * u t)) (at t within {0..T})"
    and dB: "\<And>t. t \<in> {0..T} \<Longrightarrow> (B has_real_derivative (- gm * B t + 2 * u t)) (at t within {0..T})"
    and A_nn: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> A t" and B_nn: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> B t"
    and uineq: "\<And>t. t \<in> {0..T} \<Longrightarrow> (u t)\<^sup>2 \<le> G\<^sup>2 * A t * B t"
    and A0: "A 0 = 1" and B0: "B 0 = 0" and t: "t \<in> {0..T}"
  shows "B t \<le> 4 * G\<^sup>2 / (4 * G\<^sup>2 + gq * gm) * exp (- 2)"
proof -
  interpret pulses_crit G gq gm T A B u
    by unfold_locales (use assms in \<open>blast+\<close>)
  show ?thesis by (rule critical_all_pulses[OF t])
qed

end
