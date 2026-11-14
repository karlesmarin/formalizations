(*  Title:      Dubins_U_Turn.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    From "Exact limits for writing a quantum memory" (C. Marín, draft, November 2026): the comparison of the
    eight Dubins candidate lengths for a U-turn between two parallel lines at axial displacement s (unit
    turning radius).  The closed forms of the lengths of the words LSL, RSR, LSR, RSL, LRL and RLR (the
    latter two with the central circle on either side) are taken as definitions; that they are the lengths
    of the corresponding paths is geometry and is not formalised here.  The result is that the shortest one
    is the CCC word for s <= 2 and the CSC word (LSR, RSL) for s >= 2.
*)

theory Dubins_U_Turn
  imports "HOL-Analysis.Analysis"
begin

section \<open>A. Definitions\<close>

definition q :: "real \<Rightarrow> real" where
  "q s = arcsin (sqrt (4 + s\<^sup>2) / 4)"

text \<open>The words LSL and RSR.\<close>

definition Lout :: "real \<Rightarrow> real" where
  "Lout s = 3 * pi + sqrt (4 + s\<^sup>2)"

text \<open>The words LSR and RSL; at @{text "s = 2"} the value is the limit @{text "2 * pi"}.\<close>

definition Lin :: "real \<Rightarrow> real" where
  "Lin s = (if s = 2 then 2 * pi
    else pi + 2 * arctan (2 / sqrt (s\<^sup>2 - 4)) + sqrt (s\<^sup>2 - 4))"

text \<open>The words LRL and RLR; the central circle on one side or on the other.\<close>

definition Lccc_a :: "real \<Rightarrow> real" where
  "Lccc_a s = (if s \<le> 2 then 3 * pi - 4 * q s else 5 * pi - 4 * q s)"

definition Lccc_b :: "real \<Rightarrow> real" where
  "Lccc_b s = (if s \<le> 2 then 3 * pi + 4 * q s else pi + 4 * q s)"

definition Lstar :: "real \<Rightarrow> real" where
  "Lstar s = (if s \<le> 2 then Lccc_a s else Lin s)"

text \<open>An auxiliary form of the CSC branch which is continuous at @{text "s = 2"}.\<close>

definition Hh :: "real \<Rightarrow> real" where
  "Hh s = 2 * pi - 2 * arctan (sqrt (s\<^sup>2 - 4) / 2) + sqrt (s\<^sup>2 - 4)"

section \<open>B. The CSC branch\<close>

lemma sq_minus4_pos:
  fixes u :: real
  assumes "2 < u"
  shows "0 < u\<^sup>2 - 4"
proof -
  have "u\<^sup>2 - 4 = (u - 2) * (u + 2)" by (simp add: power2_eq_square algebra_simps)
  moreover have "0 < (u - 2) * (u + 2)" using assms by (intro mult_pos_pos) auto
  ultimately show ?thesis by simp
qed

lemma sqrt_deriv:
  fixes u :: real
  assumes "2 < u"
  shows "((\<lambda>x. sqrt (x\<^sup>2 - 4)) has_real_derivative u / sqrt (u\<^sup>2 - 4)) (at u)"
proof -
  have pos: "0 < u\<^sup>2 - 4" by (rule sq_minus4_pos[OF assms])
  have h1: "((\<lambda>x::real. x\<^sup>2 - 4) has_real_derivative 2 * u) (at u)"
    by (rule derivative_eq_intros | simp)+
  have h2: "(sqrt has_real_derivative inverse (sqrt (u\<^sup>2 - 4)) / 2) (at (u\<^sup>2 - 4))"
    by (rule DERIV_real_sqrt[OF pos])
  have h3: "((\<lambda>x. sqrt (x\<^sup>2 - 4)) has_real_derivative inverse (sqrt (u\<^sup>2 - 4)) / 2 * (2 * u)) (at u)"
    by (rule DERIV_chain2[where f=sqrt and g="\<lambda>x::real. x\<^sup>2 - 4", OF h2 h1])
  have "inverse (sqrt (u\<^sup>2 - 4)) / 2 * (2 * u) = u / sqrt (u\<^sup>2 - 4)"
    by (simp add: field_simps)
  with h3 show ?thesis by simp
qed

lemma Hh_derivative:
  fixes u :: real
  assumes "2 < u"
  shows "(Hh has_real_derivative sqrt (u\<^sup>2 - 4) / u) (at u)"
proof -
  define r where "r = sqrt (u\<^sup>2 - 4)"
  have pos: "0 < u\<^sup>2 - 4" by (rule sq_minus4_pos[OF assms])
  have r0: "0 < r" using pos by (simp add: r_def)
  have r2: "r\<^sup>2 = u\<^sup>2 - 4" unfolding r_def by (rule real_sqrt_pow2) (use pos in simp)
  have u0: "0 < u" using assms by simp
  have hr: "((\<lambda>x. sqrt (x\<^sup>2 - 4)) has_real_derivative u / r) (at u)"
    using sqrt_deriv[OF assms] by (simp add: r_def)
  have hr2: "((\<lambda>x. sqrt (x\<^sup>2 - 4) / 2) has_real_derivative u / r / 2) (at u)"
    by (rule DERIV_cdivide[OF hr])
  have ha: "(arctan has_real_derivative inverse (1 + (sqrt (u\<^sup>2 - 4) / 2)\<^sup>2)) (at (sqrt (u\<^sup>2 - 4) / 2))"
    by (rule DERIV_arctan)
  have hb: "((\<lambda>x. arctan (sqrt (x\<^sup>2 - 4) / 2)) has_real_derivative
      inverse (1 + (sqrt (u\<^sup>2 - 4) / 2)\<^sup>2) * (u / r / 2)) (at u)"
    by (rule DERIV_chain2[where f=arctan and g="\<lambda>x. sqrt (x\<^sup>2 - 4) / 2", OF ha hr2])
  have hc: "(Hh has_real_derivative
      0 - 2 * (inverse (1 + (sqrt (u\<^sup>2 - 4) / 2)\<^sup>2) * (u / r / 2)) + u / r) (at u)"
    unfolding Hh_def
    by (rule DERIV_add[OF DERIV_diff[OF DERIV_const DERIV_cmult[OF hb]] hr])
  have hc2: "(Hh has_real_derivative
      0 - 2 * (inverse (1 + (r / 2)\<^sup>2) * (u / r / 2)) + u / r) (at u)"
    using hc by (simp add: r_def)
  have e: "1 + (r / 2)\<^sup>2 = u\<^sup>2 / 4"
  proof -
    have "(r / 2)\<^sup>2 = r\<^sup>2 / 4" by (simp add: power_divide)
    then show ?thesis using r2 by linarith
  qed
  have nu: "u \<noteq> 0" using u0 by simp
  have nr: "r \<noteq> 0" using r0 by simp
  have s1: "0 - 2 * (inverse (1 + (r / 2)\<^sup>2) * (u / r / 2)) + u / r = (u\<^sup>2 - 4) / (u * r)"
    unfolding e
    by ((simp add: inverse_divide field_simps nu nr; fail)
      | (simp add: inverse_divide divide_simps nu nr power2_eq_square algebra_simps; fail)
      | (simp add: inverse_divide divide_simps nu nr; algebra))
  have s2: "(u\<^sup>2 - 4) / (u * r) = r / u"
    unfolding r2[symmetric]
    by ((simp add: power2_eq_square nu nr; fail)
      | (simp add: power2_eq_square divide_simps nu nr; fail)
      | (simp add: power2_eq_square divide_simps nu nr algebra_simps; fail))
  have "0 - 2 * (inverse (1 + (r / 2)\<^sup>2) * (u / r / 2)) + u / r = r / u" using s1 s2 by simp
  with hc2 show ?thesis by (simp add: r_def)
qed

lemma Lin_eq_Hh:
  fixes s :: real
  assumes "2 \<le> s"
  shows "Lin s = Hh s"
proof (cases "s = 2")
  case True
  then show ?thesis by (simp add: Lin_def Hh_def)
next
  case False
  with assms have lt: "2 < s" by simp
  have pos: "0 < s\<^sup>2 - 4" by (rule sq_minus4_pos[OF lt])
  define r where "r = sqrt (s\<^sup>2 - 4)"
  have r0: "0 < r" using pos by (simp add: r_def)
  have "arctan (2 / r) = pi / 2 - arctan (r / 2)"
  proof -
    have "arctan (inverse (r / 2)) = pi / 2 - arctan (r / 2)"
      using r0 by (intro arctan_inverse) auto
    moreover have "inverse (r / 2) = 2 / r" by (simp add: inverse_eq_divide)
    ultimately show ?thesis by simp
  qed
  then show ?thesis using False by (simp add: Lin_def Hh_def r_def)
qed

lemma isCont_Hh: "isCont Hh (x::real)"
  unfolding Hh_def by (intro continuous_intros; simp)

section \<open>C. Elementary facts\<close>

lemma sq_le_12:
  fixes s :: real
  assumes "0 \<le> s" and "s \<le> sqrt 12"
  shows "s\<^sup>2 \<le> 12"
proof -
  have "s\<^sup>2 \<le> (sqrt 12)\<^sup>2" using assms by (intro power_mono) auto
  then show ?thesis by simp
qed

lemma sqrt_le_4:
  fixes s :: real
  assumes "s\<^sup>2 \<le> 12"
  shows "sqrt (4 + s\<^sup>2) \<le> 4"
proof (rule power2_le_imp_le)
  have p: "0 \<le> 4 + s\<^sup>2" by simp
  have e: "(sqrt (4 + s\<^sup>2))\<^sup>2 = 4 + s\<^sup>2" by (rule real_sqrt_pow2[OF p])
  have f: "(4::real)\<^sup>2 = 16" by simp
  show "(sqrt (4 + s\<^sup>2))\<^sup>2 \<le> 4\<^sup>2" using e f assms by linarith
  show "0 \<le> (4::real)" by simp
qed

lemma q_pos:
  fixes s :: real
  assumes "s\<^sup>2 \<le> 12"
  shows "0 < q s"
proof -
  have p: "0 < 4 + s\<^sup>2" by (rule add_pos_nonneg) simp_all
  have a: "0 < sqrt (4 + s\<^sup>2) / 4" using p by simp
  have b: "sqrt (4 + s\<^sup>2) / 4 \<le> 1" using sqrt_le_4[OF assms] by simp
  have "arcsin 0 < arcsin (sqrt (4 + s\<^sup>2) / 4)"
    by (rule arcsin_less_arcsin) (use a b in linarith)+
  then show ?thesis by (simp add: q_def)
qed

lemma q_two: "q 2 = pi / 4"
proof -
  define y where "y = sin (pi / 4)"
  have y0: "0 < y" unfolding y_def by (rule sin_gt_zero) (use pi_gt_zero in auto)
  have e: "sin (pi / 4) = cos (pi / 4)"
  proof -
    have "pi / 2 - pi / 4 = pi / 4" by simp
    then show ?thesis using sin_cos_eq[of "pi / 4"] by simp
  qed
  have "y\<^sup>2 + y\<^sup>2 = 1"
    using sin_cos_squared_add[of "pi / 4"] e by (simp add: y_def)
  then have y2: "y\<^sup>2 = 1 / 2" by simp
  have "sqrt (4 + 2\<^sup>2) = 4 * y"
  proof (rule real_sqrt_unique)
    show "(4 * y)\<^sup>2 = 4 + 2\<^sup>2" using y2 by (simp add: power_mult_distrib)
    show "0 \<le> 4 * y" using y0 by simp
  qed
  then have "arcsin (sqrt (4 + 2\<^sup>2) / 4) = pi / 4"
    using y_def pi_gt_zero by (simp add: arcsin_sin)
  then show ?thesis by (simp add: q_def)
qed

lemma Lin_two: "Lin 2 = 2 * pi"
  by (simp add: Lin_def)

lemma Lccc_a_two: "Lccc_a 2 = 2 * pi"
  by (simp add: Lccc_a_def q_two)

lemma Hh_bound:
  fixes s :: real
  assumes "2 \<le> s"
  shows "Hh s \<le> 2 * pi + sqrt (s\<^sup>2 - 4)"
proof -
  have s4: "(2::real)\<^sup>2 \<le> s\<^sup>2" using assms by (intro power_mono) auto
  have r0: "0 \<le> sqrt (s\<^sup>2 - 4) / 2" using s4 by simp
  have "arctan 0 \<le> arctan (sqrt (s\<^sup>2 - 4) / 2)" by (rule arctan_monotone') (use r0 in simp)
  then have "0 \<le> arctan (sqrt (s\<^sup>2 - 4) / 2)" by simp
  then show ?thesis by (simp add: Hh_def)
qed

lemma sqrt_minus4_lt_pi:
  fixes s :: real
  assumes "2 \<le> s" and "s\<^sup>2 \<le> 12"
  shows "sqrt (s\<^sup>2 - 4) < pi"
proof (rule ccontr)
  assume "\<not> sqrt (s\<^sup>2 - 4) < pi"
  then have h: "pi \<le> sqrt (s\<^sup>2 - 4)" by simp
  have p3: "3 < pi" by (rule pi_gt3)
  have "(3::real)\<^sup>2 \<le> (sqrt (s\<^sup>2 - 4))\<^sup>2" using h p3 by (intro power_mono) auto
  moreover have "(sqrt (s\<^sup>2 - 4))\<^sup>2 \<le> 8"
  proof -
    have s4: "(2::real)\<^sup>2 \<le> s\<^sup>2" using assms(1) by (intro power_mono) auto
    have "0 \<le> s\<^sup>2 - 4" using s4 by simp
    then show ?thesis using assms(2) by (simp add: real_sqrt_pow2)
  qed
  ultimately show False by simp
qed

section \<open>D. The derivative of q and the CCC word against the CSC word\<close>

lemma q_deriv:
  fixes u :: real
  assumes "u\<^sup>2 < 12"
  shows "(q has_real_derivative u / sqrt ((12 - u\<^sup>2) * (4 + u\<^sup>2))) (at u)"
proof -
  define s where "s = sqrt (4 + u\<^sup>2)"
  define t where "t = sqrt (1 - (s / 4)\<^sup>2)"
  define w where "w = sqrt ((12 - u\<^sup>2) * (4 + u\<^sup>2))"
  have p4: "0 < 4 + u\<^sup>2" by (rule add_pos_nonneg) simp_all
  have s0: "0 < s" using p4 by (simp add: s_def)
  have s2: "s\<^sup>2 = 4 + u\<^sup>2" unfolding s_def by (rule real_sqrt_pow2) (use p4 in simp)
  have s4: "s < 4"
  proof (rule ccontr)
    assume "\<not> s < 4"
    then have "4\<^sup>2 \<le> s\<^sup>2" by (intro power_mono) auto
    with s2 assms show False by simp
  qed
  have t2a: "1 - (s / 4)\<^sup>2 = (12 - u\<^sup>2) / 16" by (simp add: power_divide s2 field_simps)
  have t0: "0 < 1 - (s / 4)\<^sup>2" using t2a assms by simp
  have tt: "0 < t" using t0 by (simp add: t_def)
  have t2: "t\<^sup>2 = (12 - u\<^sup>2) / 16"
  proof -
    have "t\<^sup>2 = 1 - (s / 4)\<^sup>2" unfolding t_def by (rule real_sqrt_pow2) (use t0 in simp)
    then show ?thesis using t2a by simp
  qed
  have w4: "w = 4 * s * t"
    unfolding w_def
  proof (rule real_sqrt_unique)
    show "(4 * s * t)\<^sup>2 = (12 - u\<^sup>2) * (4 + u\<^sup>2)"
      by (simp add: power_mult_distrib s2 t2)
    show "0 \<le> 4 * s * t" using s0 tt by simp
  qed
  have h2: "(sqrt has_real_derivative inverse (sqrt (4 + u\<^sup>2)) / 2) (at (4 + u\<^sup>2))"
    by (rule DERIV_real_sqrt[OF p4])
  have h1: "((\<lambda>x::real. 4 + x\<^sup>2) has_real_derivative 2 * u) (at u)"
    by (rule derivative_eq_intros | simp)+
  have h3: "((\<lambda>x. sqrt (4 + x\<^sup>2)) has_real_derivative inverse (sqrt (4 + u\<^sup>2)) / 2 * (2 * u)) (at u)"
    by (rule DERIV_chain2[where f=sqrt and g="\<lambda>x::real. 4 + x\<^sup>2", OF h2 h1])
  have h4: "((\<lambda>x. sqrt (4 + x\<^sup>2) / 4) has_real_derivative inverse (sqrt (4 + u\<^sup>2)) / 2 * (2 * u) / 4) (at u)"
    by (rule DERIV_cdivide[OF h3])
  have h5: "(arcsin has_real_derivative inverse (sqrt (1 - (sqrt (4 + u\<^sup>2) / 4)\<^sup>2))) (at (sqrt (4 + u\<^sup>2) / 4))"
    by (rule DERIV_arcsin) (use s0 s4 s_def in linarith)+
  have h6: "((\<lambda>x. arcsin (sqrt (4 + x\<^sup>2) / 4)) has_real_derivative
      inverse (sqrt (1 - (sqrt (4 + u\<^sup>2) / 4)\<^sup>2)) * (inverse (sqrt (4 + u\<^sup>2)) / 2 * (2 * u) / 4)) (at u)"
    by (rule DERIV_chain2[where f=arcsin and g="\<lambda>x. sqrt (4 + x\<^sup>2) / 4", OF h5 h4])
  have h7: "(q has_real_derivative inverse (sqrt (1 - (sqrt (4 + u\<^sup>2) / 4)\<^sup>2)) *
      (inverse (sqrt (4 + u\<^sup>2)) / 2 * (2 * u) / 4)) (at u)"
    unfolding q_def by (rule h6)
  have val: "inverse (sqrt (1 - (sqrt (4 + u\<^sup>2) / 4)\<^sup>2)) * (inverse (sqrt (4 + u\<^sup>2)) / 2 * (2 * u) / 4)
      = u / w"
  proof -
    have f: "inverse (sqrt (1 - (sqrt (4 + u\<^sup>2) / 4)\<^sup>2)) * (inverse (sqrt (4 + u\<^sup>2)) / 2 * (2 * u) / 4)
        = inverse t * (inverse s / 2 * (2 * u) / 4)"
      by (simp only: s_def[symmetric] t_def[symmetric])
    have ns: "s \<noteq> 0" using s0 by simp
    have nt: "t \<noteq> 0" using tt by simp
    have g: "inverse t * (inverse s / 2 * (2 * u) / 4) = u / (4 * s * t)"
      by ((simp add: field_simps ns nt; fail)
        | (simp add: divide_simps ns nt algebra_simps; fail)
        | (simp add: divide_simps ns nt; algebra))
    have h: "u / (4 * s * t) = u / w" by (simp only: w4)
    show ?thesis by (rule trans[OF f trans[OF g h]])
  qed
  show ?thesis using h7 val by (simp add: w_def)
qed

definition gdiff :: "real \<Rightarrow> real" where
  "gdiff x = pi + 4 * q x - Hh x"

lemma gdiff_two: "gdiff 2 = 0"
  by (simp add: gdiff_def q_two Hh_def)

lemma gdiff_derivative:
  fixes u :: real
  assumes "2 < u" and "u\<^sup>2 < 12"
  shows "(gdiff has_real_derivative 4 * (u / sqrt ((12 - u\<^sup>2) * (4 + u\<^sup>2))) - sqrt (u\<^sup>2 - 4) / u) (at u)"
proof -
  have "(gdiff has_real_derivative 0 + 4 * (u / sqrt ((12 - u\<^sup>2) * (4 + u\<^sup>2))) - sqrt (u\<^sup>2 - 4) / u) (at u)"
    unfolding gdiff_def
    by (rule DERIV_diff[OF DERIV_add[OF DERIV_const DERIV_cmult[OF q_deriv[OF assms(2)]]]
        Hh_derivative[OF assms(1)]])
  then show ?thesis by simp
qed

lemma gdiff_slope_nonneg:
  fixes u :: real
  assumes "2 < u" and "u\<^sup>2 < 12"
  shows "0 \<le> 4 * (u / sqrt ((12 - u\<^sup>2) * (4 + u\<^sup>2))) - sqrt (u\<^sup>2 - 4) / u"
proof -
  define w where "w = sqrt ((12 - u\<^sup>2) * (4 + u\<^sup>2))"
  define r where "r = sqrt (u\<^sup>2 - 4)"
  have u0: "0 < u" using assms by simp
  have pos: "0 < u\<^sup>2 - 4" by (rule sq_minus4_pos[OF assms(1)])
  have r2: "r\<^sup>2 = u\<^sup>2 - 4" unfolding r_def by (rule real_sqrt_pow2) (use pos in simp)
  have r0: "0 \<le> r" using pos by (simp add: r_def)
  have prod: "0 < (12 - u\<^sup>2) * (4 + u\<^sup>2)"
  proof (rule mult_pos_pos)
    show "0 < 12 - u\<^sup>2" using assms by simp
    show "0 < 4 + u\<^sup>2" by (rule add_pos_nonneg) simp_all
  qed
  have w0: "0 < w" unfolding w_def using prod by simp
  have w2: "w\<^sup>2 = (12 - u\<^sup>2) * (4 + u\<^sup>2)" unfolding w_def by (rule real_sqrt_pow2) (use prod in simp)
  have key: "(4 * u)\<^sup>2 - w\<^sup>2 = (u\<^sup>2 - 4) * (u\<^sup>2 + 12)"
    using w2 by (simp add: power_mult_distrib algebra_simps)
  have key0: "0 \<le> (u\<^sup>2 - 4) * (u\<^sup>2 + 12)" using pos by (intro mult_nonneg_nonneg) auto
  have wle: "w \<le> 4 * u"
  proof (rule power2_le_imp_le)
    show "w\<^sup>2 \<le> (4 * u)\<^sup>2" using key key0 by linarith
    show "0 \<le> 4 * u" using u0 by simp
  qed
  have one: "1 \<le> 4 * (u / w)"
  proof -
    have "1 \<le> 4 * u / w" using wle w0 by (simp add: pos_le_divide_eq)
    then show ?thesis by simp
  qed
  have rle: "r \<le> u"
  proof (rule power2_le_imp_le)
    show "r\<^sup>2 \<le> u\<^sup>2" using r2 by simp
    show "0 \<le> u" using u0 by simp
  qed
  have two: "r / u \<le> 1" using rle u0 by (simp add: pos_divide_le_eq)
  show ?thesis unfolding w_def[symmetric] r_def[symmetric] using one two by linarith
qed

lemma gdiff_nonneg:
  fixes d :: real
  assumes "2 \<le> d" and "d\<^sup>2 \<le> 12"
  shows "0 \<le> gdiff d"
proof (cases "d = 2")
  case True
  then show ?thesis using gdiff_two by simp
next
  case False
  with assms(1) have lt: "2 < d" by simp
  have cq: "continuous_on {2..d} q"
  proof -
    have c1: "continuous_on {2..d} (\<lambda>x. sqrt (4 + x\<^sup>2) / 4)" by (intro continuous_intros) simp
    have bd: "-1 \<le> sqrt (4 + x\<^sup>2) / 4 \<and> sqrt (4 + x\<^sup>2) / 4 \<le> 1" if x: "x \<in> {2..d}" for x :: real
    proof -
      have x0: "0 \<le> x" and xd: "x \<le> d" using x by simp_all
      have "x\<^sup>2 \<le> d\<^sup>2" using x0 xd by (intro power_mono) auto
      then have "sqrt (4 + x\<^sup>2) \<le> 4" using sqrt_le_4[of x] assms(2) by simp
      moreover have "0 \<le> sqrt (4 + x\<^sup>2)" by simp
      ultimately show ?thesis by linarith
    qed
    have "continuous_on {2..d} (\<lambda>x. arcsin (sqrt (4 + x\<^sup>2) / 4))"
      by (rule continuous_on_arcsin[OF c1]) (use bd in blast)
    then show ?thesis by (simp add: q_def)
  qed
  have cont: "continuous_on {2..d} gdiff"
    unfolding gdiff_def
    by (intro continuous_intros cq continuous_at_imp_continuous_on ballI isCont_Hh)
  have dif: "gdiff differentiable (at x)" if hx: "2 < x" "x < d" for x
  proof -
    have x0: "0 < x" using hx by simp
    have "x\<^sup>2 < d\<^sup>2" using hx x0 by (intro power_strict_mono) auto
    then have "x\<^sup>2 < 12" using assms(2) by simp
    from gdiff_derivative[OF hx(1) this] show "gdiff differentiable (at x)"
      by (auto simp: real_differentiable_def)
  qed
  from MVT[OF lt cont dif]
  obtain z l where z: "2 < z" "z < d" and dz: "DERIV gdiff z :> l"
      and eq: "gdiff d - gdiff 2 = (d - 2) * l" by blast
  have z0: "0 < z" using z by simp
  have "z\<^sup>2 < d\<^sup>2" using z z0 by (intro power_strict_mono) auto
  then have z12: "z\<^sup>2 < 12" using assms(2) by simp
  have l: "l = 4 * (z / sqrt ((12 - z\<^sup>2) * (4 + z\<^sup>2))) - sqrt (z\<^sup>2 - 4) / z"
    by (rule DERIV_unique[OF dz gdiff_derivative[OF z(1) z12]])
  have "0 \<le> l" using gdiff_slope_nonneg[OF z(1) z12] l by simp
  then have "0 \<le> (d - 2) * l" using lt by (intro mult_nonneg_nonneg) auto
  then show ?thesis using eq gdiff_two by simp
qed

section \<open>E. The five statements\<close>

theorem small_s:
  fixes s :: real
  assumes "0 \<le> s" and "s \<le> 2"
  shows "Lstar s \<le> Lout s" and "Lstar s \<le> Lccc_b s" and "Lstar s < 3 * pi"
proof -
  have s4: "s\<^sup>2 \<le> 2\<^sup>2" using assms by (intro power_mono) auto
  have qp: "0 < q s" by (rule q_pos) (use s4 in simp)
  have L: "Lstar s = 3 * pi - 4 * q s" using assms by (simp add: Lstar_def Lccc_a_def)
  have sq: "0 \<le> sqrt (4 + s\<^sup>2)" by simp
  show "Lstar s \<le> Lout s" unfolding Lout_def using L qp sq by linarith
  have Lb: "Lccc_b s = 3 * pi + 4 * q s" using assms by (simp add: Lccc_b_def)
  show "Lstar s \<le> Lccc_b s" using L Lb qp by linarith
  show "Lstar s < 3 * pi" using L qp by simp
qed

theorem lin_below_3pi:
  fixes s :: real
  assumes "2 \<le> s" and "s \<le> sqrt 12"
  shows "Lin s \<le> 2 * pi + sqrt (s\<^sup>2 - 4)" and "2 * pi + sqrt (s\<^sup>2 - 4) < 3 * pi"
proof -
  have s12: "s\<^sup>2 \<le> 12" using sq_le_12 assms by simp
  show "Lin s \<le> 2 * pi + sqrt (s\<^sup>2 - 4)" using Lin_eq_Hh[OF assms(1)] Hh_bound[OF assms(1)] by simp
  show "2 * pi + sqrt (s\<^sup>2 - 4) < 3 * pi" using sqrt_minus4_lt_pi[OF assms(1) s12] by simp
qed

theorem lin_le_ccc_a:
  fixes s :: real
  assumes "2 \<le> s" and "s \<le> sqrt 12"
  shows "Lin s \<le> Lccc_a s" and "Lin s \<le> Lout s"
proof -
  have s12: "s\<^sup>2 \<le> 12" using sq_le_12 assms by simp
  have l1: "Lin s \<le> 2 * pi + sqrt (s\<^sup>2 - 4)" using lin_below_3pi(1)[OF assms] .
  have l2: "2 * pi + sqrt (s\<^sup>2 - 4) < 3 * pi" using lin_below_3pi(2)[OF assms] .
  show "Lin s \<le> Lccc_a s"
  proof (cases "s = 2")
    case True
    then show ?thesis using Lin_two Lccc_a_two by simp
  next
    case False
    with assms(1) have lt: "2 < s" by simp
    have a0: "0 \<le> sqrt (4 + s\<^sup>2)" by simp
    have a1: "-1 \<le> sqrt (4 + s\<^sup>2) / 4" using a0 by linarith
    have a2: "sqrt (4 + s\<^sup>2) / 4 \<le> 1" using sqrt_le_4[OF s12] by simp
    have qle: "q s \<le> pi / 2" unfolding q_def using arcsin_bounded[OF a1 a2] by simp
    have "Lccc_a s = 5 * pi - 4 * q s" using lt by (simp add: Lccc_a_def)
    then show ?thesis using l1 l2 qle by linarith
  qed
  show "Lin s \<le> Lout s"
  proof -
    have "0 \<le> sqrt (4 + s\<^sup>2)" by simp
    moreover have "sqrt (s\<^sup>2 - 4) \<le> sqrt (4 + s\<^sup>2)" by (rule real_sqrt_le_mono) simp
    ultimately show ?thesis unfolding Lout_def using l1 l2 pi_gt_zero by linarith
  qed
qed

theorem ccc_b_above_lin:
  fixes s :: real
  assumes "2 \<le> s" and "s \<le> sqrt 12"
  shows "Lin s \<le> Lccc_b s"
proof -
  have s12: "s\<^sup>2 \<le> 12" using sq_le_12 assms by simp
  have g: "0 \<le> gdiff s" by (rule gdiff_nonneg[OF assms(1) s12])
  have h: "Hh s \<le> pi + 4 * q s" using g by (simp add: gdiff_def)
  have qp: "0 < q s" by (rule q_pos[OF s12])
  show ?thesis
  proof (cases "s \<le> 2")
    case True
    then have "Lccc_b s = 3 * pi + 4 * q s" by (simp add: Lccc_b_def)
    then show ?thesis using h qp pi_gt_zero Lin_eq_Hh[OF assms(1)] by linarith
  next
    case False
    then have "Lccc_b s = pi + 4 * q s" by (simp add: Lccc_b_def)
    then show ?thesis using h Lin_eq_Hh[OF assms(1)] by linarith
  qed
qed

theorem large_s:
  fixes s :: real
  assumes "2 \<le> s"
  shows "Lin s \<le> Lout s"
proof -
  have "Lin s = Hh s" by (rule Lin_eq_Hh[OF assms])
  also have "\<dots> \<le> 2 * pi + sqrt (s\<^sup>2 - 4)" by (rule Hh_bound[OF assms])
  also have "\<dots> \<le> Lout s"
  proof -
    have "sqrt (s\<^sup>2 - 4) \<le> sqrt (4 + s\<^sup>2)" by (rule real_sqrt_le_mono) simp
    then show ?thesis unfolding Lout_def using pi_gt_zero by linarith
  qed
  finally show ?thesis .
qed

theorem lstar_le_out:
  fixes s :: real
  assumes "0 \<le> s"
  shows "Lstar s \<le> Lout s"
proof (cases "s \<le> 2")
  case True
  then show ?thesis using small_s(1)[OF assms] by simp
next
  case False
  then have "Lstar s = Lin s" by (simp add: Lstar_def)
  then show ?thesis using large_s[of s] False by simp
qed

theorem lstar_le_lin:
  fixes s :: real
  assumes "2 \<le> s"
  shows "Lstar s \<le> Lin s"
proof (cases "s \<le> 2")
  case True
  with assms have "s = 2" by simp
  then show ?thesis using Lin_two Lccc_a_two by (simp add: Lstar_def)
next
  case False
  then show ?thesis by (simp add: Lstar_def)
qed

theorem lstar_le_ccc_a:
  fixes s :: real
  assumes "0 \<le> s" and "s \<le> sqrt 12"
  shows "Lstar s \<le> Lccc_a s"
proof (cases "s \<le> 2")
  case True
  then show ?thesis by (simp add: Lstar_def)
next
  case False
  then have "2 \<le> s" by simp
  then show ?thesis using lin_le_ccc_a(1)[OF _ assms(2)] False by (simp add: Lstar_def)
qed

theorem lstar_le_ccc_b:
  fixes s :: real
  assumes "0 \<le> s" and "s \<le> sqrt 12"
  shows "Lstar s \<le> Lccc_b s"
proof (cases "s \<le> 2")
  case True
  then show ?thesis using small_s(2)[OF assms(1)] by simp
next
  case False
  then have "2 \<le> s" by simp
  then show ?thesis using ccc_b_above_lin[OF _ assms(2)] False by (simp add: Lstar_def)
qed

text \<open>Summary: @{thm lstar_le_out}, @{thm lstar_le_lin}, @{thm lstar_le_ccc_a} and @{thm lstar_le_ccc_b}
  say that @{term Lstar} is at most each of the candidate lengths where that candidate is defined.\<close>

end
