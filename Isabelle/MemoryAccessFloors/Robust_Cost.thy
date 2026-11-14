(*  Title:      Robust_Cost.thy
    Author:     Carles Marín Muñoz
    Copyright:  Carles Marín Muñoz
    License:    BSD-3-Clause

    encaje: sesion 188; coste exacto de anular la fuga para pulsos de fase fija (seccion "Robustness costs time and
    exposure" de "Exact limits for writing a quantum memory", memory-floors.tex; datos en dubins_robusto.py);
    modelo de estilo: sesion 187; no es herramienta.
*)

theory Robust_Cost
  imports "HOL-Analysis.Analysis"
begin

text \<open>The minimal duration @{text "L(u)"} of a U-turn with zero leakage is taken as a definition (that it is
  the minimum is Dubins' theorem and is not formalised here).  With rates @{text "a \<ge> b \<ge> 0"} the cost in the
  favourable direction is @{text "f(u) = ((a+b) L(u) - (a-b) u)/2 - (a+b) \<pi>/2"}.\<close>

section \<open>A. Definitions\<close>

definition Lccc :: "real \<Rightarrow> real" where
  "Lccc u = 3 * pi - 4 * arcsin (sqrt (4 + u\<^sup>2) / 4)"

definition Lcsc :: "real \<Rightarrow> real" where
  "Lcsc u = pi + 2 * arctan (2 / sqrt (u\<^sup>2 - 4)) + sqrt (u\<^sup>2 - 4)"

definition Lmin :: "real \<Rightarrow> real" where
  "Lmin u = (if u \<le> 2 then Lccc u else Lcsc u)"

definition cost :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "cost a b u = ((a + b) * Lmin u - (a - b) * u) / 2 - (a + b) * pi / 2"

text \<open>An auxiliary form of the CSC branch which is continuous at @{text "u = 2"}.\<close>

definition Hh :: "real \<Rightarrow> real" where
  "Hh u = 2 * pi - 2 * arctan (sqrt (u\<^sup>2 - 4) / 2) + sqrt (u\<^sup>2 - 4)"

lemma unfavourable_ge:
  fixes a b u :: real
  assumes "b \<le> a" and "0 \<le> u"
  shows "cost a b u \<le> cost a b u + (a - b) * u"
  using assms by (simp add: mult_nonneg_nonneg)

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

lemma Lcsc_eq_Hh:
  fixes u :: real
  assumes "2 < u"
  shows "Lcsc u = Hh u"
proof -
  have pos: "0 < u\<^sup>2 - 4" by (rule sq_minus4_pos[OF assms])
  define r where "r = sqrt (u\<^sup>2 - 4)"
  have r0: "0 < r" using pos by (simp add: r_def)
  have "arctan (2 / r) = pi / 2 - arctan (r / 2)"
  proof -
    have "arctan (inverse (r / 2)) = pi / 2 - arctan (r / 2)"
      using r0 by (intro arctan_inverse) auto
    moreover have "inverse (r / 2) = 2 / r" by (simp add: inverse_eq_divide)
    ultimately show ?thesis by simp
  qed
  then show ?thesis by (simp add: Lcsc_def Hh_def r_def)
qed

theorem csc_derivative:
  fixes u :: real
  assumes "2 < u"
  shows "(Lcsc has_real_derivative sqrt (u\<^sup>2 - 4) / u) (at u)"
proof -
  have ev: "eventually (\<lambda>x. Hh x = Lcsc x) (nhds u)"
    unfolding eventually_nhds
    by (rule exI[of _ "{2<..}"]) (use assms Lcsc_eq_Hh in auto)
  show ?thesis
    by (rule iffD1[OF DERIV_cong_ev[OF refl ev refl] Hh_derivative[OF assms]])
qed

section \<open>C. The closed form at the optimum\<close>

lemma arctan_arccos:
  fixes k :: real
  assumes "0 < k" and "k < 1"
  shows "arctan (sqrt (1 - k\<^sup>2) / k) = arccos k"
proof -
  define x where "x = arccos k"
  have c: "cos x = k" using assms by (simp add: x_def cos_arccos)
  have s: "sin x = sqrt (1 - k\<^sup>2)" using assms by (simp add: x_def sin_arccos)
  have x0: "0 \<le> x" unfolding x_def by (rule arccos_lbound) (use assms in auto)
  have x1: "x < pi / 2"
  proof (rule ccontr)
    assume "\<not> x < pi / 2"
    then have hx: "pi / 2 \<le> x" by simp
    have hp: "x \<le> pi" unfolding x_def by (rule arccos_ubound) (use assms in auto)
    define y where "y = x - pi / 2"
    have y0: "0 \<le> y" using hx unfolding y_def by linarith
    have y1: "y \<le> pi" using hp pi_gt_zero unfolding y_def by linarith
    have e1: "cos x = cos (y + pi / 2)" by (simp add: y_def)
    have e2: "cos (y + pi / 2) = - sin y" by (simp add: cos_add)
    have sy: "0 \<le> sin y" by (rule sin_ge_zero[OF y0]) (use y1 pi_gt_zero in linarith)
    have "cos x \<le> 0" using e1 e2 sy by simp
    with c assms show False by simp
  qed
  have "tan x = sqrt (1 - k\<^sup>2) / k" by (simp add: tan_def c s)
  moreover have "arctan (tan x) = x"
    using x0 x1 pi_gt_zero by (intro arctan_tan) auto
  ultimately show ?thesis by (simp add: x_def)
qed

lemma ustar_facts:
  fixes a b :: real
  assumes "b < a" and "0 < b"
  shows "2 < (a + b) / sqrt (a * b)"
    and "sqrt (((a + b) / sqrt (a * b))\<^sup>2 - 4) = (a - b) / sqrt (a * b)"
proof -
  define s where "s = sqrt (a * b)"
  have a0: "0 < a" using assms by simp
  have ab: "0 < a * b" using a0 assms by simp
  have s0: "0 < s" using ab by (simp add: s_def)
  have s2: "s\<^sup>2 = a * b" unfolding s_def by (rule real_sqrt_pow2) (use ab in simp)
  have sne: "s\<^sup>2 \<noteq> 0" using s0 by simp
  have e1: "(a + b)\<^sup>2 = (a - b)\<^sup>2 + 4 * s\<^sup>2"
  proof -
    have "(a + b)\<^sup>2 = (a - b)\<^sup>2 + 4 * (a * b)" by (simp add: power2_eq_square algebra_simps)
    then show ?thesis using s2 by simp
  qed
  have e4: "4 * s\<^sup>2 / s\<^sup>2 = 4" using sne by (rule nonzero_mult_div_cancel_right)
  have key: "((a + b) / s)\<^sup>2 - 4 = ((a - b) / s)\<^sup>2"
  proof -
    have "((a + b) / s)\<^sup>2 = ((a - b)\<^sup>2 + 4 * s\<^sup>2) / s\<^sup>2" by (simp add: power_divide e1)
    also have "\<dots> = ((a - b) / s)\<^sup>2 + 4" by (simp only: add_divide_distrib e4 power_divide)
    finally show ?thesis by simp
  qed
  have pos: "0 < ((a - b) / s)\<^sup>2"
  proof -
    have "0 < (a - b) / s" using assms s0 by (intro divide_pos_pos) auto
    then show ?thesis by (rule zero_less_power)
  qed
  show "sqrt (((a + b) / sqrt (a * b))\<^sup>2 - 4) = (a - b) / sqrt (a * b)"
    unfolding s_def[symmetric] using key assms s0 by (simp add: real_sqrt_unique)
  have "2 < (a + b) / s"
  proof (rule ccontr)
    assume "\<not> 2 < (a + b) / s"
    then have "(a + b) / s \<le> 2" by simp
    moreover have "0 \<le> (a + b) / s" using a0 assms s0 by simp
    ultimately have "((a + b) / s)\<^sup>2 \<le> 2\<^sup>2" by (intro power_mono) auto
    then have "((a + b) / s)\<^sup>2 \<le> 4" by simp
    with key pos show False by linarith
  qed
  then show "2 < (a + b) / sqrt (a * b)" by (simp add: s_def)
qed

theorem closed_form_value:
  fixes a b :: real
  assumes "b < a" and "0 < b"
  shows "sqrt (((a + b) / sqrt (a * b))\<^sup>2 - 4) = (a - b) / sqrt (a * b)"
    and "cost a b ((a + b) / sqrt (a * b)) = (a + b) * arccos ((a - b) / (a + b))"
proof -
  show "sqrt (((a + b) / sqrt (a * b))\<^sup>2 - 4) = (a - b) / sqrt (a * b)"
    by (rule ustar_facts(2)[OF assms])
  define s where "s = sqrt (a * b)"
  define r where "r = (a - b) / s"
  define us where "us = (a + b) / s"
  define k where "k = (a - b) / (a + b)"
  have a0: "0 < a" using assms by simp
  have ab: "0 < a * b" using a0 assms by simp
  have s0: "0 < s" using ab by (simp add: s_def)
  have s2: "s\<^sup>2 = a * b" unfolding s_def by (rule real_sqrt_pow2) (use ab in simp)
  have us2: "2 < us" using ustar_facts(1)[OF assms] by (simp add: us_def s_def)
  have rr: "sqrt (us\<^sup>2 - 4) = r" using ustar_facts(2)[OF assms] by (simp add: us_def r_def s_def)
  have k0: "0 < k" using assms by (simp add: k_def)
  have k1: "k < 1" using assms by (simp add: k_def divide_less_eq)
  have r0: "0 < r" using assms s0 by (simp add: r_def)
  have ne: "a + b \<noteq> 0" using a0 assms by simp
  have ne2: "(a + b)\<^sup>2 \<noteq> 0" using ne by simp
  have sq1: "(2 * s / (a + b))\<^sup>2 = 4 * (a * b) / (a + b)\<^sup>2"
    by (simp add: power_divide power_mult_distrib s2)
  have sq3: "(a + b)\<^sup>2 - (a - b)\<^sup>2 = 4 * (a * b)"
    by (simp add: power2_eq_square algebra_simps)
  have sq2: "1 - k\<^sup>2 = 4 * (a * b) / (a + b)\<^sup>2"
  proof -
    have "1 - k\<^sup>2 = ((a + b)\<^sup>2 - (a - b)\<^sup>2) / (a + b)\<^sup>2"
      by (simp only: k_def power_divide) (simp add: diff_divide_distrib ne ne2)
    then show ?thesis using sq3 by simp
  qed
  have sq: "sqrt (1 - k\<^sup>2) = 2 * s / (a + b)"
  proof (rule real_sqrt_unique)
    show "(2 * s / (a + b))\<^sup>2 = 1 - k\<^sup>2" using sq1 sq2 by simp
    show "0 \<le> 2 * s / (a + b)" using a0 assms s0 by simp
  qed
  have nab: "a - b \<noteq> 0" using assms by simp
  have ratio: "2 / r = sqrt (1 - k\<^sup>2) / k"
  proof -
    have "sqrt (1 - k\<^sup>2) / k = (2 * s / (a + b)) / k" by (simp only: sq)
    also have "\<dots> = 2 * s / (a - b)" unfolding k_def
      by ((simp add: field_simps ne nab; fail)
        | (simp add: divide_simps ne nab; fail)
        | (simp add: divide_simps ne nab algebra_simps; fail))
    also have "\<dots> = 2 / r" unfolding r_def
      by ((simp add: field_simps nab s0; fail)
        | (simp add: divide_simps nab; fail))
    finally show ?thesis by simp
  qed
  have "cost a b us = ((a + b) * Lcsc us - (a - b) * us) / 2 - (a + b) * pi / 2"
    using us2 by (simp add: cost_def Lmin_def)
  also have "\<dots> = (a + b) * arctan (2 / r) + ((a + b) * r - (a - b) * us) / 2"
    by ((simp add: Lcsc_def rr algebra_simps field_simps; fail) | (simp add: Lcsc_def rr; algebra))
  also have "(a + b) * r - (a - b) * us = 0"
    using s0 by (simp add: r_def us_def field_simps)
  also have "arctan (2 / r) = arccos k"
    using ratio arctan_arccos[OF k0 k1] by simp
  finally show "cost a b ((a + b) / sqrt (a * b)) = (a + b) * arccos ((a - b) / (a + b))"
    by (simp add: us_def s_def k_def)
qed

section \<open>D. The minimum on the CSC side\<close>

lemma Lmin_two: "Lmin 2 = 2 * pi"
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
  then show ?thesis by (simp add: Lmin_def Lccc_def)
qed

lemma Lmin_Hh:
  fixes u :: real
  assumes "2 \<le> u"
  shows "Lmin u = Hh u"
proof (cases "u = 2")
  case True
  then show ?thesis by (simp add: Lmin_two Hh_def)
next
  case False
  with assms have "2 < u" by simp
  then show ?thesis by (simp add: Lmin_def Lcsc_eq_Hh)
qed

definition gcost :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "gcost a b u = ((a + b) * Hh u - (a - b) * u) / 2 - (a + b) * pi / 2"

lemma cost_gcost:
  fixes u :: real
  assumes "2 \<le> u"
  shows "cost a b u = gcost a b u"
  using assms by (simp add: cost_def gcost_def Lmin_Hh)

lemma isCont_Hh: "isCont Hh (x::real)"
  unfolding Hh_def by (intro continuous_intros; simp)

lemma gcost_derivative:
  fixes a b u :: real
  assumes "2 < u"
  shows "(gcost a b has_real_derivative ((a + b) * (sqrt (u\<^sup>2 - 4) / u) - (a - b)) / 2) (at u)"
proof -
  have "(gcost a b has_real_derivative
      ((a + b) * (sqrt (u\<^sup>2 - 4) / u) - (a - b) * 1) / 2 - 0) (at u)"
    unfolding gcost_def
    by (rule DERIV_diff[OF DERIV_cdivide[OF DERIV_diff[OF DERIV_cmult[OF Hh_derivative[OF assms]]
        DERIV_cmult[OF DERIV_ident]]] DERIV_const])
  then show ?thesis by simp
qed

text \<open>Mean value theorem on @{text "[c, d]"} with @{text "2 \<le> c < d"}.\<close>

lemma gcost_mvt:
  fixes a b c d :: real
  assumes "2 \<le> c" and "c < d"
  shows "\<exists>z. c < z \<and> z < d \<and>
    gcost a b d - gcost a b c = (d - c) * (((a + b) * (sqrt (z\<^sup>2 - 4) / z) - (a - b)) / 2)"
proof -
  have cont: "\<forall>x. c \<le> x \<and> x \<le> d \<longrightarrow> isCont (gcost a b) x"
    unfolding gcost_def by (auto intro!: continuous_intros isCont_Hh)
  have cont2: "continuous_on {c..d} (gcost a b)"
    by (rule continuous_at_imp_continuous_on) (use cont in auto)
  have dif: "\<And>x. c < x \<Longrightarrow> x < d \<Longrightarrow> gcost a b differentiable (at x)"
  proof -
    fix x assume "c < x" "x < d"
    then have "2 < x" using assms by simp
    from gcost_derivative[OF this] show "gcost a b differentiable (at x)"
      by (auto simp: real_differentiable_def)
  qed
  from MVT[OF assms(2) cont2 dif]
  obtain l z where z: "c < z" "z < d" and dz: "DERIV (gcost a b) z :> l"
      and eq: "gcost a b d - gcost a b c = (d - c) * l" by blast
  have "2 < z" using z assms by simp
  from DERIV_unique[OF dz gcost_derivative[OF this]] eq z
  show ?thesis by auto
qed

lemma slope_sign:
  fixes a b z :: real
  assumes "b < a" and "0 < b" and "2 < z"
  shows "z \<le> (a + b) / sqrt (a * b) \<Longrightarrow> (a + b) * (sqrt (z\<^sup>2 - 4) / z) - (a - b) \<le> 0"
    and "(a + b) / sqrt (a * b) \<le> z \<Longrightarrow> 0 \<le> (a + b) * (sqrt (z\<^sup>2 - 4) / z) - (a - b)"
proof -
  define s where "s = sqrt (a * b)"
  define r where "r = sqrt (z\<^sup>2 - 4)"
  have a0: "0 < a" using assms by simp
  have ab: "0 < a * b" using a0 assms by simp
  have s0: "0 < s" using ab by (simp add: s_def)
  have s2: "s\<^sup>2 = a * b" unfolding s_def by (rule real_sqrt_pow2) (use ab in simp)
  have pos: "0 < z\<^sup>2 - 4" by (rule sq_minus4_pos[OF assms(3)])
  have r0: "0 < r" using pos by (simp add: r_def)
  have r2: "r\<^sup>2 = z\<^sup>2 - 4" unfolding r_def by (rule real_sqrt_pow2) (use pos in simp)
  have z0: "0 < z" using assms by simp
  have diff: "((a - b) * z)\<^sup>2 - ((a + b) * r)\<^sup>2 = 4 * (a + b)\<^sup>2 - 4 * (a * b) * z\<^sup>2"
  proof -
    have "((a - b) * z)\<^sup>2 - ((a + b) * r)\<^sup>2 = (a - b)\<^sup>2 * z\<^sup>2 - (a + b)\<^sup>2 * r\<^sup>2"
      by (simp add: power_mult_distrib)
    also have "\<dots> = (a - b)\<^sup>2 * z\<^sup>2 - (a + b)\<^sup>2 * (z\<^sup>2 - 4)" by (simp add: r2)
    also have "\<dots> = 4 * (a + b)\<^sup>2 - 4 * (a * b) * z\<^sup>2" by (simp add: power2_eq_square algebra_simps)
    finally show ?thesis .
  qed
  have eqn: "(a + b) * (r / z) - (a - b) = ((a + b) * r - (a - b) * z) / z"
    using z0 by (simp add: field_simps)
  have ab1: "0 < a + b" using a0 assms by simp
  have ab2: "0 < a - b" using assms by simp
  show "z \<le> (a + b) / s \<Longrightarrow> (a + b) * (r / z) - (a - b) \<le> 0"
  proof -
    assume h: "z \<le> (a + b) / s"
    then have "z * s \<le> a + b" using s0 by (simp add: pos_le_divide_eq)
    then have "(z * s)\<^sup>2 \<le> (a + b)\<^sup>2" using z0 s0 by (intro power_mono) auto
    then have "(a * b) * z\<^sup>2 \<le> (a + b)\<^sup>2" by (simp add: power_mult_distrib s2 algebra_simps)
    with diff have "((a + b) * r)\<^sup>2 \<le> ((a - b) * z)\<^sup>2" by simp
    then have "(a + b) * r \<le> (a - b) * z"
    proof (rule power2_le_imp_le)
      show "0 \<le> (a - b) * z" using ab2 z0 by (rule mult_nonneg_nonneg[OF less_imp_le less_imp_le])
    qed
    then have "(a + b) * r - (a - b) * z \<le> 0" by simp
    then show ?thesis unfolding eqn by (rule divide_nonpos_pos[OF _ z0])
  qed
  show "(a + b) / s \<le> z \<Longrightarrow> 0 \<le> (a + b) * (r / z) - (a - b)"
  proof -
    assume h: "(a + b) / s \<le> z"
    then have "a + b \<le> z * s" using s0 by (simp add: divide_le_eq)
    then have "(a + b)\<^sup>2 \<le> (z * s)\<^sup>2" using ab1 by (intro power_mono) auto
    then have "(a + b)\<^sup>2 \<le> (a * b) * z\<^sup>2" by (simp add: power_mult_distrib s2 algebra_simps)
    with diff have "((a - b) * z)\<^sup>2 \<le> ((a + b) * r)\<^sup>2" by simp
    then have "(a - b) * z \<le> (a + b) * r"
    proof (rule power2_le_imp_le)
      show "0 \<le> (a + b) * r" using ab1 r0 by (rule mult_nonneg_nonneg[OF less_imp_le less_imp_le])
    qed
    then have "0 \<le> (a + b) * r - (a - b) * z" by simp
    then show ?thesis unfolding eqn by (rule divide_nonneg_pos[OF _ z0])
  qed
qed

theorem csc_minimum:
  fixes a b u :: real
  assumes "b < a" and "0 < b" and "2 \<le> u"
  shows "(a + b) * arccos ((a - b) / (a + b)) \<le> cost a b u"
proof -
  define us where "us = (a + b) / sqrt (a * b)"
  have us2: "2 < us" using ustar_facts(1)[OF assms(1,2)] by (simp add: us_def)
  have val: "gcost a b us = (a + b) * arccos ((a - b) / (a + b))"
    using closed_form_value(2)[OF assms(1,2)] cost_gcost[where a=a and b=b and u=us, OF less_imp_le[OF us2]]
    by (simp add: us_def)
  have "(a + b) * arccos ((a - b) / (a + b)) \<le> gcost a b u"
  proof (cases "u \<le> us")
    case True
    show ?thesis
    proof (cases "u = us")
      case True
      then show ?thesis using val by simp
    next
      case False
      with \<open>u \<le> us\<close> have lt: "u < us" by simp
      obtain z where z: "u < z" "z < us"
          and eq: "gcost a b us - gcost a b u = (us - u) * (((a + b) * (sqrt (z\<^sup>2 - 4) / z) - (a - b)) / 2)"
        using gcost_mvt[OF assms(3) lt] by blast
      have z2: "2 < z" using z assms(3) by simp
      have "(a + b) * (sqrt (z\<^sup>2 - 4) / z) - (a - b) \<le> 0"
        using slope_sign(1)[OF assms(1,2) z2] z us_def by simp
      then have "(us - u) * (((a + b) * (sqrt (z\<^sup>2 - 4) / z) - (a - b)) / 2) \<le> 0"
        using lt by (intro mult_nonneg_nonpos) auto
      with eq val show ?thesis by simp
    qed
  next
    case False
    then have lt: "us < u" by simp
    obtain z where z: "us < z" "z < u"
        and eq: "gcost a b u - gcost a b us = (u - us) * (((a + b) * (sqrt (z\<^sup>2 - 4) / z) - (a - b)) / 2)"
      using gcost_mvt[where a=a and b=b and c=us and d=u, OF less_imp_le[OF us2] lt] by auto
    have z2: "2 < z" using z us2 by simp
    have "0 \<le> (a + b) * (sqrt (z\<^sup>2 - 4) / z) - (a - b)"
      using slope_sign(2)[OF assms(1,2) z2] z us_def by simp
    then have "0 \<le> (u - us) * (((a + b) * (sqrt (z\<^sup>2 - 4) / z) - (a - b)) / 2)"
      using lt by (intro mult_nonneg_nonneg) auto
    with eq val show ?thesis by simp
  qed
  then show ?thesis using cost_gcost[OF assms(3)] by simp
qed

section \<open>E. The CCC branch\<close>

lemma ccc_alg:
  fixes u :: real
  assumes "0 \<le> u" and "u \<le> 2"
  shows "16 * u\<^sup>2 \<le> (12 - u\<^sup>2) * (4 + u\<^sup>2)"
proof -
  have u4: "u\<^sup>2 \<le> 2\<^sup>2" using assms by (intro power_mono) auto
  have "(12 - u\<^sup>2) * (4 + u\<^sup>2) - 16 * u\<^sup>2 = (12 + u\<^sup>2) * (4 - u\<^sup>2)"
    by (simp add: power2_eq_square algebra_simps)
  moreover have "0 \<le> (12 + u\<^sup>2) * (4 - u\<^sup>2)" using u4 by (intro mult_nonneg_nonneg) auto
  ultimately show ?thesis by simp
qed

theorem ccc_slope:
  fixes u :: real
  assumes "0 \<le> u" and "u \<le> 2"
  shows "(Lccc has_real_derivative - 4 * u / sqrt ((12 - u\<^sup>2) * (4 + u\<^sup>2))) (at u)"
    and "\<bar>- 4 * u / sqrt ((12 - u\<^sup>2) * (4 + u\<^sup>2))\<bar> \<le> 1"
    and "- 4 * u / sqrt ((12 - u\<^sup>2) * (4 + u\<^sup>2)) \<le> 0"
proof -
  define s where "s = sqrt (4 + u\<^sup>2)"
  define t where "t = sqrt (1 - (s / 4)\<^sup>2)"
  define q where "q = sqrt ((12 - u\<^sup>2) * (4 + u\<^sup>2))"
  have u4: "u\<^sup>2 \<le> 2\<^sup>2" using assms by (intro power_mono) auto
  have p4: "0 < 4 + u\<^sup>2" by (rule add_pos_nonneg) simp_all
  have s0: "0 < s" using p4 by (simp add: s_def)
  have s2: "s\<^sup>2 = 4 + u\<^sup>2" unfolding s_def by (rule real_sqrt_pow2) (use p4 in simp)
  have s4: "s < 4"
  proof (rule ccontr)
    assume "\<not> s < 4"
    then have "4\<^sup>2 \<le> s\<^sup>2" by (intro power_mono) auto
    with s2 u4 show False by simp
  qed
  have t2a: "1 - (s / 4)\<^sup>2 = (12 - u\<^sup>2) / 16" by (simp add: power_divide s2 field_simps)
  have t0: "0 < 1 - (s / 4)\<^sup>2" using t2a u4 by simp
  have tt: "0 < t" using t0 by (simp add: t_def)
  have t2: "t\<^sup>2 = (12 - u\<^sup>2) / 16"
  proof -
    have "t\<^sup>2 = 1 - (s / 4)\<^sup>2" unfolding t_def by (rule real_sqrt_pow2) (use t0 in simp)
    then show ?thesis using t2a by simp
  qed
  have q4: "q = 4 * s * t"
    unfolding q_def
  proof (rule real_sqrt_unique)
    show "(4 * s * t)\<^sup>2 = (12 - u\<^sup>2) * (4 + u\<^sup>2)"
      by (simp add: power_mult_distrib s2 t2)
    show "0 \<le> 4 * s * t" using s0 tt by simp
  qed
  have q0: "0 < q" using q4 s0 tt by simp
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
  have h7: "(Lccc has_real_derivative 0 - 4 * (inverse (sqrt (1 - (sqrt (4 + u\<^sup>2) / 4)\<^sup>2)) *
      (inverse (sqrt (4 + u\<^sup>2)) / 2 * (2 * u) / 4))) (at u)"
    unfolding Lccc_def by (rule DERIV_diff[OF DERIV_const DERIV_cmult[OF h6]])
  have val: "0 - 4 * (inverse (sqrt (1 - (sqrt (4 + u\<^sup>2) / 4)\<^sup>2)) *
      (inverse (sqrt (4 + u\<^sup>2)) / 2 * (2 * u) / 4)) = - 4 * u / q"
  proof -
    have f: "0 - 4 * (inverse (sqrt (1 - (sqrt (4 + u\<^sup>2) / 4)\<^sup>2)) *
        (inverse (sqrt (4 + u\<^sup>2)) / 2 * (2 * u) / 4)) = 0 - 4 * (inverse t * (inverse s / 2 * (2 * u) / 4))"
      by (simp only: s_def[symmetric] t_def[symmetric])
    have ns: "s \<noteq> 0" using s0 by simp
    have nt: "t \<noteq> 0" using tt by simp
    have g: "0 - 4 * (inverse t * (inverse s / 2 * (2 * u) / 4)) = - 4 * u / (4 * s * t)"
      by ((simp add: field_simps ns nt; fail)
        | (simp add: divide_simps ns nt algebra_simps; fail)
        | (simp add: divide_simps ns nt; algebra))
    have h: "- 4 * u / (4 * s * t) = - 4 * u / q" by (simp only: q4)
    show ?thesis by (rule trans[OF f trans[OF g h]])
  qed
  show "(Lccc has_real_derivative - 4 * u / q) (at u)"
    using h7 val by (simp add: q_def)
  have u0: "0 \<le> 4 * u / q" using assms q0 by simp
  show "- 4 * u / q \<le> 0" using u0 by (simp add: divide_nonpos_pos assms q0)
  have "4 * u \<le> q"
  proof (rule power2_le_imp_le)
    show "(4 * u)\<^sup>2 \<le> q\<^sup>2" using ccc_alg[OF assms] q0
      by (simp add: q_def power_mult_distrib power2_eq_square)
    show "0 \<le> q" using q0 by simp
  qed
  then have "4 * u / q \<le> 1" using q0 by (simp add: divide_le_eq)
  then show "\<bar>- 4 * u / q\<bar> \<le> 1" using u0 by (simp add: abs_of_nonpos divide_nonneg_pos)
qed

lemma Lccc_two: "Lccc 2 = 2 * pi"
  using Lmin_two by (simp add: Lmin_def)

lemma Lccc_antitone:
  fixes u :: real
  assumes "0 \<le> u" and "u \<le> 2"
  shows "Lccc 2 \<le> Lccc u"
proof (rule DERIV_nonpos_imp_nonincreasing[OF assms(2)])
  fix x :: real assume x: "u \<le> x" "x \<le> 2"
  then have "0 \<le> x" using assms by simp
  from ccc_slope[OF this x(2)] show "\<exists>y. DERIV Lccc x :> y \<and> y \<le> 0" by blast
qed

lemma cost_two:
  fixes a b :: real
  shows "cost a b 2 = (a + b) * pi / 2 - (a - b)"
  unfolding cost_def Lmin_two
  by ((simp add: algebra_simps field_simps; fail) | algebra)

theorem ccc_branch:
  fixes a b u :: real
  assumes "0 \<le> b" and "b \<le> a" and "0 \<le> u" and "u \<le> 2"
  shows "cost a b 2 \<le> cost a b u" and "cost a b 2 = (a + b) * pi / 2 - (a - b)"
proof -
  show "cost a b 2 = (a + b) * pi / 2 - (a - b)" by (rule cost_two)
  have ab: "0 \<le> a + b" using assms by simp
  have l: "Lccc 2 \<le> Lccc u" by (rule Lccc_antitone[OF assms(3,4)])
  have m1: "0 \<le> (a + b) * (Lccc u - Lccc 2)" using ab l by (intro mult_nonneg_nonneg) auto
  have m2: "0 \<le> (a - b) * (2 - u)" using assms by (intro mult_nonneg_nonneg) auto
  have c1: "cost a b u = ((a + b) * Lccc u - (a - b) * u) / 2 - (a + b) * pi / 2"
    using assms by (simp add: cost_def Lmin_def)
  have c2: "cost a b 2 = ((a + b) * Lccc 2 - (a - b) * 2) / 2 - (a + b) * pi / 2"
    by (simp add: cost_def Lmin_def)
  have "cost a b u - cost a b 2 = ((a + b) * (Lccc u - Lccc 2) + (a - b) * (2 - u)) / 2"
    unfolding c1 c2 by ((simp add: algebra_simps field_simps; fail) | algebra)
  moreover have "0 \<le> ((a + b) * (Lccc u - Lccc 2) + (a - b) * (2 - u)) / 2"
    using m1 m2 by simp
  ultimately show "cost a b 2 \<le> cost a b u" by linarith
qed

section \<open>F. Equal rates and the total minimum\<close>

theorem equal_rates:
  fixes a u :: real
  assumes "0 < a" and "0 \<le> u"
  shows "pi * a \<le> cost a a u"
    and "cost a a 2 = pi * a"
    and "(a + a) * arccos ((a - a) / (a + a)) = pi * a"
proof -
  have c2: "cost a a 2 = pi * a" using cost_two[where a=a and b=a] by (simp add: algebra_simps)
  show "cost a a 2 = pi * a" by (rule c2)
  show "(a + a) * arccos ((a - a) / (a + a)) = pi * a" by (simp add: arccos_0)
  show "pi * a \<le> cost a a u"
  proof (cases "u \<le> 2")
    case True
    have "cost a a 2 \<le> cost a a u" by (rule ccc_branch(1)) (use assms True in auto)
    then show ?thesis using c2 by simp
  next
    case False
    then have u2: "2 < u" by simp
    obtain z where z: "2 < z" "z < u"
        and eq: "gcost a a u - gcost a a 2 = (u - 2) * (((a + a) * (sqrt (z\<^sup>2 - 4) / z) - (a - a)) / 2)"
      using gcost_mvt[where a=a and b=a and c=2 and d=u, OF order_refl u2] by auto
    have pz: "0 < z\<^sup>2 - 4" by (rule sq_minus4_pos[OF z(1)])
    have q0: "0 \<le> sqrt (z\<^sup>2 - 4) / z"
      by (rule divide_nonneg_pos[OF real_sqrt_ge_zero[OF less_imp_le[OF pz]]]) (use z in linarith)
    have "0 \<le> (a + a) * (sqrt (z\<^sup>2 - 4) / z)" using assms q0 by (intro mult_nonneg_nonneg) auto
    then have "0 \<le> (u - 2) * (((a + a) * (sqrt (z\<^sup>2 - 4) / z) - (a - a)) / 2)"
      using z by (intro mult_nonneg_nonneg) auto
    with eq have g1: "gcost a a 2 \<le> gcost a a u" by simp
    have g2: "gcost a a 2 = pi * a" using cost_gcost[where a=a and b=a and u=2] c2 by simp
    have g3: "cost a a u = gcost a a u" by (rule cost_gcost[OF less_imp_le[OF u2]])
    show ?thesis using g1 g2 g3 by simp
  qed
qed

theorem total_minimum:
  fixes a b u :: real
  assumes "b < a" and "0 < b" and "0 \<le> u"
  shows "(a + b) * arccos ((a - b) / (a + b)) \<le> cost a b u"
    and "cost a b ((a + b) / sqrt (a * b)) = (a + b) * arccos ((a - b) / (a + b))"
proof -
  show "cost a b ((a + b) / sqrt (a * b)) = (a + b) * arccos ((a - b) / (a + b))"
    by (rule closed_form_value(2)[OF assms(1,2)])
  show "(a + b) * arccos ((a - b) / (a + b)) \<le> cost a b u"
  proof (cases "2 \<le> u")
    case True
    then show ?thesis by (rule csc_minimum[OF assms(1,2)])
  next
    case False
    then have u2: "u \<le> 2" by simp
    have "(a + b) * arccos ((a - b) / (a + b)) \<le> cost a b 2"
      by (rule csc_minimum[OF assms(1,2)]) simp
    also have "\<dots> \<le> cost a b u" by (rule ccc_branch(1)) (use assms u2 in auto)
    finally show ?thesis .
  qed
qed

end
