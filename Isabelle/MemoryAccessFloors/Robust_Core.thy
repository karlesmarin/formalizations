(*  Title:      Robust_Core.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Core of the duration-leakage frontier for a complete transfer: a curve n on the unit sphere with
    speed at most nu, starting at the north pole and ending at the south pole.
    We prove the angle bound n(t).n(t') >= cos(nu|t-t'|) for nu|t-t'| <= pi, the existence of an equatorial
    crossing, and the frontier cos((nu T - pi)/2) <= nu |zeta| for nu T - pi <= pi.
    If the curve stays strictly between the poles in the interior, we also prove the exposure inequality
    Q - 2/nu <= 2 sqrt((A - pi/(2 nu)) (B - pi/(2 nu))), where A and B are the times spent near the north
    and south pole and Q is the integral of the equatorial part.
*)

theory Robust_Core
  imports Memory_Robust
begin

section \<open>A. A barrier lemma\<close>

text \<open>A continuous function that starts non-positive cannot become positive when its derivative is
  negative wherever it is positive.\<close>

lemma barrier:
  fixes D D' :: "real \<Rightarrow> real" and a b :: real
  assumes "a \<le> b" and "continuous_on {a..b} D" and "D a \<le> 0"
    and "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> 0 < D x \<Longrightarrow> (D has_real_derivative D' x) (at x) \<and> D' x < 0"
  shows "\<forall>x\<in>{a..b}. D x \<le> 0"
proof (rule ccontr)
  assume "\<not> (\<forall>x\<in>{a..b}. D x \<le> 0)"
  then obtain c where c: "c \<in> {a..b}" "0 < D c" by (auto simp: not_le)
  define S where "S = {x\<in>{a..c}. D x \<le> 0}"
  have Sne: "a \<in> S" using c assms(3) by (auto simp: S_def)
  have Sbdd: "bdd_above S" by (auto simp: S_def intro!: bdd_aboveI[of _ c])
  have cont_ac: "continuous_on {a..c} D"
    using assms(2) c by (intro continuous_on_subset[OF assms(2)]) auto
  have Scl: "closed S"
  proof -
    have cv: "\<forall>B. closed B \<longrightarrow> closed (D -` B \<inter> {a..c})"
      by (rule iffD1[OF continuous_on_closed_vimage[OF closed_atLeastAtMost[of a c]] cont_ac])
    have "closed (D -` {..0} \<inter> {a..c})" using cv closed_atMost by blast
    moreover have "S = D -` {..0} \<inter> {a..c}" by (auto simp: S_def)
    ultimately show ?thesis by simp
  qed
  define t2 where "t2 = Sup S"
  have Sne': "S \<noteq> {}" using Sne by auto
  have t2S: "t2 \<in> S" unfolding t2_def by (rule closed_contains_Sup[OF Sne' Sbdd Scl])
  then have t2a: "a \<le> t2" and t2c: "t2 \<le> c" and Dt2: "D t2 \<le> 0" by (auto simp: S_def)
  have t2lt: "t2 < c"
  proof (rule ccontr)
    assume "\<not> t2 < c"
    then have "t2 = c" using t2c by simp
    then show False using Dt2 c(2) by simp
  qed
  have pos: "\<And>x. t2 < x \<Longrightarrow> x < c \<Longrightarrow> 0 < D x"
  proof (rule ccontr)
    fix x assume x: "t2 < x" "x < c" and "\<not> 0 < D x"
    then have "x \<in> S" using t2a unfolding S_def by auto
    then have "x \<le> t2" unfolding t2_def by (intro cSup_upper Sbdd)
    then show False using x(1) by simp
  qed
  have cont2: "continuous_on {t2..c} D"
    using cont_ac t2a by (intro continuous_on_subset[OF cont_ac]) auto
  have derf: "\<And>x. t2 < x \<Longrightarrow> x < c \<Longrightarrow> (D has_derivative (\<lambda>h. D' x * h)) (at x)"
  proof -
    fix x assume x: "t2 < x" "x < c"
    have "(D has_real_derivative D' x) (at x)"
      using assms(4)[of x] pos[of x] t2a c(1) x by auto
    then show "(D has_derivative (\<lambda>h. D' x * h)) (at x)" by (simp add: has_field_derivative_def)
  qed
  have ex: "\<exists>z. t2 < z \<and> z < c \<and> D c - D t2 = D' z * (c - t2)"
    by (rule mvt[OF t2lt cont2 derf]) auto
  then obtain z where z: "t2 < z" "z < c" and mv: "D c - D t2 = D' z * (c - t2)" by blast
  have "D' z < 0" using assms(4)[of z] pos[of z] t2a c(1) z by auto
  then have "D' z * (c - t2) < 0" using t2lt by (intro mult_neg_pos) auto
  then show False using mv c(2) Dt2 by linarith
qed

section \<open>B. Curves of bounded speed on the sphere\<close>

locale bounded_speed_curve =
  fixes n n' :: "real \<Rightarrow> 'a::real_inner" and T nu :: real
  assumes nu_pos: "0 < nu"
    and cont: "continuous_on {0..T} n"
    and der: "\<And>t. 0 < t \<Longrightarrow> t < T \<Longrightarrow> (n has_vector_derivative n' t) (at t)"
    and unit: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> T \<Longrightarrow> norm (n t) = 1"
    and speed: "\<And>t. 0 < t \<Longrightarrow> t < T \<Longrightarrow> norm (n' t) \<le> nu"
begin

lemma inner_le1:
  assumes "0 \<le> s" "s \<le> T" "0 \<le> t" "t \<le> T"
  shows "inner (n s) (n t) \<le> 1"
proof -
  have "\<bar>inner (n s) (n t)\<bar> \<le> norm (n s) * norm (n t)" by (rule Cauchy_Schwarz_ineq2)
  then show ?thesis using unit assms by simp
qed

lemma orth:
  assumes t: "0 < t" "t < T"
  shows "inner (n t) (n' t) = 0"
proof -
  have D: "(n has_derivative (\<lambda>h. h *\<^sub>R n' t)) (at t)"
    using der[OF t] by (simp add: has_vector_derivative_def)
  have d1: "((\<lambda>x. inner (n x) (n x)) has_derivative
      (\<lambda>h. inner (n t) (h *\<^sub>R n' t) + inner (h *\<^sub>R n' t) (n t))) (at t)"
    by (rule has_derivative_inner[OF D D])
  have eq: "\<And>y. y \<in> {0<..<T} \<Longrightarrow> inner (n y) (n y) = (1::real)"
  proof -
    fix y assume y: "y \<in> {0<..<T}"
    then have "norm (n y) = 1" by (intro unit) auto
    then show "inner (n y) (n y) = (1::real)" by (simp add: power2_norm_eq_inner[symmetric])
  qed
  have d2: "((\<lambda>x. (1::real)) has_derivative
      (\<lambda>h. inner (n t) (h *\<^sub>R n' t) + inner (h *\<^sub>R n' t) (n t))) (at t)"
    by (rule has_derivative_transform_within_open[OF d1 open_greaterThanLessThan _ eq]) (use t in auto)
  have d3: "((\<lambda>x. (1::real)) has_derivative (\<lambda>h. 0)) (at t)" by (rule has_derivative_const)
  have "(\<lambda>h. inner (n t) (h *\<^sub>R n' t) + inner (h *\<^sub>R n' t) (n t)) = (\<lambda>h::real. 0)"
    by (rule has_derivative_unique[OF d2 d3])
  then have "inner (n t) (1 *\<^sub>R n' t) + inner (1 *\<^sub>R n' t) (n t) = 0" by (metis (no_types))
  then show ?thesis by (simp add: inner_commute)
qed

lemma u_derivative:
  assumes t: "0 < t" "t < T"
  shows "((\<lambda>x. inner (n x) e) has_real_derivative inner (n' t) e) (at t)"
proof -
  have D: "(n has_derivative (\<lambda>h. h *\<^sub>R n' t)) (at t)"
    using der[OF t] by (simp add: has_vector_derivative_def)
  have d: "((\<lambda>x. inner (n x) e) has_derivative (\<lambda>h. inner (h *\<^sub>R n' t) e)) (at t)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_inner_left D])
  have eq: "(\<lambda>h. inner (h *\<^sub>R n' t) e) = (*) (inner (n' t) e)"
    by (rule ext) (simp add: inner_scaleR_left)
  show ?thesis unfolding has_field_derivative_def by (subst eq[symmetric]) (rule d)
qed

lemma u_square_bound:
  assumes t: "0 < t" "t < T" and e: "norm e = 1"
  shows "(inner (n' t) e)\<^sup>2 \<le> nu\<^sup>2 * (1 - (inner (n t) e)\<^sup>2)"
proof -
  define u where "u = inner (n t) e"
  define w where "w = e - u *\<^sub>R n t"
  have nt: "inner (n t) (n t) = 1" using unit[of t] t by (simp add: power2_norm_eq_inner[symmetric])
  have ee: "inner e e = 1" using e by (simp add: power2_norm_eq_inner[symmetric])
  have o: "inner (n' t) (n t) = 0" using orth[OF t] by (simp add: inner_commute)
  have ie: "inner (n' t) e = inner (n' t) w"
    unfolding w_def by (simp add: inner_diff_right o)
  have nw: "(norm w)\<^sup>2 = 1 - u\<^sup>2"
  proof -
    have "(norm w)\<^sup>2 = inner w w" by (simp add: power2_norm_eq_inner)
    also have "\<dots> = inner e e - 2 * u * inner e (n t) + u\<^sup>2 * inner (n t) (n t)"
      unfolding w_def by (simp add: inner_diff_left inner_diff_right inner_scaleR_left inner_scaleR_right
          power2_eq_square algebra_simps inner_commute)
    also have "\<dots> = 1 - u\<^sup>2" using ee nt by (simp add: u_def inner_commute power2_eq_square)
    finally show ?thesis .
  qed
  have cs: "\<bar>inner (n' t) w\<bar> \<le> norm (n' t) * norm w" by (rule Cauchy_Schwarz_ineq2)
  have "\<bar>inner (n' t) w\<bar>\<^sup>2 \<le> (norm (n' t) * norm w)\<^sup>2" by (rule power_mono[OF cs abs_ge_zero])
  then have "(inner (n' t) w)\<^sup>2 \<le> (norm (n' t) * norm w)\<^sup>2" by simp
  also have "\<dots> = (norm (n' t))\<^sup>2 * (norm w)\<^sup>2" by (simp add: power_mult_distrib)
  also have "\<dots> \<le> nu\<^sup>2 * (norm w)\<^sup>2"
    by (intro mult_right_mono power_mono speed[OF t]) auto
  finally show ?thesis using ie nw unfolding u_def by simp
qed

lemma angle_fwd:
  assumes t0: "0 \<le> t0" and t01: "t0 \<le> t1" and t1: "t1 \<le> T" and pi: "nu * (t1 - t0) \<le> pi"
  shows "cos (nu * (t1 - t0)) \<le> inner (n t1) (n t0)"
proof -
  define e where "e = n t0"
  have e1: "norm e = 1" using unit t0 t01 t1 by (simp add: e_def)
  define u where "u = (\<lambda>x. inner (n x) e)"
  define q where "q = (\<lambda>x. sqrt ((1 - u x) / 2))"
  define sg where "sg = (\<lambda>x. sin (nu * (x - t0) / 2))"
  define D where "D = (\<lambda>x. q x - sg x)"
  define D' where "D' = (\<lambda>x. inverse (2 * q x) * (- inner (n' x) e / 2) - (nu / 2) * cos (nu * (x - t0) / 2))"
  have inT: "\<And>x. t0 \<le> x \<Longrightarrow> x \<le> t1 \<Longrightarrow> 0 \<le> x \<and> x \<le> T" using t0 t1 by auto
  have u1: "\<And>x. t0 \<le> x \<Longrightarrow> x \<le> t1 \<Longrightarrow> u x \<le> 1"
    unfolding u_def e_def using inT t0 t01 t1 by (intro inner_le1) auto
  have u0: "u t0 = 1" unfolding u_def e_def using unit[of t0] t0 t01 t1
    by (simp add: power2_norm_eq_inner[symmetric])
  have cont_u: "continuous_on {t0..t1} u"
  proof -
    have "continuous_on {0..T} u" unfolding u_def by (intro continuous_intros cont)
    then show ?thesis by (rule continuous_on_subset) (use t0 t1 in auto)
  qed
  have cont_D: "continuous_on {t0..t1} D"
    unfolding D_def q_def sg_def by (intro continuous_intros cont_u) simp_all
  have D0: "D t0 \<le> 0" unfolding D_def q_def sg_def using u0 by simp
  have sg_nn: "\<And>x. t0 \<le> x \<Longrightarrow> x \<le> t1 \<Longrightarrow> 0 \<le> sg x \<and> 0 \<le> cos (nu * (x - t0) / 2)"
  proof -
    fix x assume x: "t0 \<le> x" "x \<le> t1"
    have a0: "0 \<le> nu * (x - t0) / 2" using nu_pos x by simp
    have "nu * (x - t0) \<le> nu * (t1 - t0)" using nu_pos x by (intro mult_left_mono) auto
    then have a1: "nu * (x - t0) / 2 \<le> pi / 2" using pi by linarith
    have "0 \<le> sin (nu * (x - t0) / 2)" using a0 a1 pi_gt_zero by (intro sin_ge_zero) auto
    moreover have "0 \<le> cos (nu * (x - t0) / 2)" using a0 a1 by (intro cos_ge_zero) auto
    ultimately show "0 \<le> sg x \<and> 0 \<le> cos (nu * (x - t0) / 2)" by (simp add: sg_def)
  qed
  have step: "\<And>x. t0 < x \<Longrightarrow> x < t1 \<Longrightarrow> 0 < D x \<Longrightarrow> (D has_real_derivative D' x) (at x) \<and> D' x < 0"
  proof -
    fix x assume x: "t0 < x" "x < t1" "0 < D x"
    have x0: "0 < x" "x < T" using t0 t1 x by auto
    have s0: "0 \<le> sg x" and c0: "0 \<le> cos (nu * (x - t0) / 2)" using sg_nn[of x] x by auto
    have qx: "sg x < q x" using x(3) by (simp add: D_def)
    have qpos: "0 < q x" using qx s0 by linarith
    have gpos: "0 < (1 - u x) / 2" using qpos by (simp add: q_def)
    have q2: "(q x)\<^sup>2 = (1 - u x) / 2" unfolding q_def using gpos by simp
    have du: "(u has_real_derivative inner (n' x) e) (at x)" unfolding u_def by (rule u_derivative[OF x0])
    have dg0: "((\<lambda>y. (1 - u y) / 2) has_real_derivative (0 - inner (n' x) e) / 2) (at x)"
      by (rule DERIV_cdivide[OF DERIV_diff[OF DERIV_const du]])
    then have dg: "((\<lambda>y. (1 - u y) / 2) has_real_derivative (- inner (n' x) e / 2)) (at x)" by simp
    have dq: "(q has_real_derivative inverse (2 * q x) * (- inner (n' x) e / 2)) (at x)"
      unfolding q_def using DERIV_chain2[OF DERIV_real_sqrt[OF gpos[unfolded q_def[symmetric]]] dg] unfolding q_def
      by simp
    have dsg: "(sg has_real_derivative (nu / 2) * cos (nu * (x - t0) / 2)) (at x)"
      unfolding sg_def by (rule derivative_eq_intros refl | simp)+
    have dD: "(D has_real_derivative D' x) (at x)"
      unfolding D_def D'_def by (rule DERIV_diff[OF dq dsg])
    have sb: "(inner (n' x) e)\<^sup>2 \<le> nu\<^sup>2 * (1 - (u x)\<^sup>2)" unfolding u_def by (rule u_square_bound[OF x0 e1])
    have ux: "u x = 1 - 2 * (q x)\<^sup>2" using q2 by simp
    have onemu: "1 - (u x)\<^sup>2 = 4 * (q x)\<^sup>2 * (1 - (q x)\<^sup>2)"
      by (subst ux) (simp add: power2_eq_square algebra_simps)
    have cs: "(cos (nu * (x - t0) / 2))\<^sup>2 = 1 - (sg x)\<^sup>2"
      unfolding sg_def using sin_cos_squared_add[of "nu * (x - t0) / 2"] by linarith
    have qs: "(sg x)\<^sup>2 < (q x)\<^sup>2" using qx s0 by (intro power_strict_mono) auto
    have lt: "(inner (n' x) e)\<^sup>2 < (2 * nu * q x * cos (nu * (x - t0) / 2))\<^sup>2"
    proof -
      have p: "0 < nu\<^sup>2 * (4 * (q x)\<^sup>2)" using nu_pos qpos by simp
      have "nu\<^sup>2 * (1 - (u x)\<^sup>2) = nu\<^sup>2 * (4 * (q x)\<^sup>2) * (1 - (q x)\<^sup>2)" using onemu by simp
      also have "\<dots> < nu\<^sup>2 * (4 * (q x)\<^sup>2) * (1 - (sg x)\<^sup>2)"
        using p qs by (intro mult_strict_left_mono) auto
      also have "\<dots> = (2 * nu * q x * cos (nu * (x - t0) / 2))\<^sup>2"
      proof -
        have e: "(2 * nu * q x * cos (nu * (x - t0) / 2))\<^sup>2
            = nu\<^sup>2 * (4 * (q x)\<^sup>2) * (cos (nu * (x - t0) / 2))\<^sup>2"
          by (simp add: power2_eq_square algebra_simps)
        show ?thesis by (simp only: e cs)
      qed
      finally show ?thesis using sb by linarith
    qed
    have rhs0: "0 \<le> 2 * nu * q x * cos (nu * (x - t0) / 2)"
      using nu_pos qpos c0 by (intro mult_nonneg_nonneg) auto
    have "\<bar>inner (n' x) e\<bar> < 2 * nu * q x * cos (nu * (x - t0) / 2)"
      by (rule power2_less_imp_less[OF _ rhs0]) (simp add: lt)
    then have lt2: "- inner (n' x) e < 2 * nu * q x * cos (nu * (x - t0) / 2)" by linarith
    have iq: "0 < inverse (2 * q x)" using qpos by simp
    have "inverse (2 * q x) * (- inner (n' x) e / 2) < inverse (2 * q x) * (nu * q x * cos (nu * (x - t0) / 2))"
      using lt2 iq by (intro mult_strict_left_mono) auto
    also have "\<dots> = (nu / 2) * cos (nu * (x - t0) / 2)" using qpos by (simp add: field_simps)
    finally have "D' x < 0" unfolding D'_def by simp
    then show "(D has_real_derivative D' x) (at x) \<and> D' x < 0" using dD by simp
  qed
  have "\<forall>x\<in>{t0..t1}. D x \<le> 0" by (rule barrier[OF t01 cont_D D0 step])
  then have "D t1 \<le> 0" using t01 by simp
  then have qs1: "q t1 \<le> sg t1" by (simp add: D_def)
  have q0: "0 \<le> q t1" unfolding q_def using u1[OF t01 order_refl] by simp
  have h1: "(q t1)\<^sup>2 \<le> (sg t1)\<^sup>2" using qs1 q0 by (intro power_mono) auto
  have h2: "(q t1)\<^sup>2 = (1 - u t1) / 2"
    unfolding q_def using u1[OF t01 order_refl] by (simp add: real_sqrt_pow2)
  have h3: "cos (nu * (t1 - t0)) = 1 - 2 * (sg t1)\<^sup>2"
  proof -
    have "cos (2 * (nu * (t1 - t0) / 2)) = 1 - 2 * (sin (nu * (t1 - t0) / 2))\<^sup>2" by (rule cos_double_sin)
    then show ?thesis by (simp add: sg_def)
  qed
  have h2': "2 * (q t1)\<^sup>2 = 1 - u t1" using h2 by (simp add: field_simps)
  have key: "\<And>a b uu c. (a::real) \<le> b \<Longrightarrow> 2 * a = 1 - uu \<Longrightarrow> c = 1 - 2 * b \<Longrightarrow> c \<le> uu"
  proof -
    fix a b uu c :: real
    assume "a \<le> b" "2 * a = 1 - uu" "c = 1 - 2 * b"
    then show "c \<le> uu" by linarith
  qed
  have "cos (nu * (t1 - t0)) \<le> u t1" by (rule key[OF h1 h2' h3])
  then show ?thesis unfolding u_def e_def by simp
qed

lemma angle_bound_gen:
  assumes "0 \<le> s" "s \<le> T" "0 \<le> t" "t \<le> T" and "nu * \<bar>s - t\<bar> \<le> pi"
  shows "cos (nu * \<bar>s - t\<bar>) \<le> inner (n s) (n t)"
proof (cases "s \<le> t")
  case True
  then have "cos (nu * (t - s)) \<le> inner (n t) (n s)"
    using assms by (intro angle_fwd) (auto simp: abs_minus_commute)
  then show ?thesis using True by (simp add: abs_minus_commute inner_commute)
next
  case False
  then have "cos (nu * (s - t)) \<le> inner (n s) (n t)"
    using assms by (intro angle_fwd) auto
  then show ?thesis using False by simp
qed

end

section \<open>C. The tent on the right\<close>

lemma tent_right:
  fixes nu b p q :: real
  assumes "0 < nu" and "0 \<le> b" and "q = p + (pi / 2 + b) / nu"
  shows "((\<lambda>t. cos (min (nu * (t - p)) (pi / 2 + nu * (q - t)))) has_integral
           (2 * cos (b / 2) - 1) / nu) {p..q}"
proof -
  define tc where "tc = q - b / (2 * nu)"
  have nu: "nu \<noteq> 0" using assms(1) by simp
  have qp: "nu * (q - p) = pi / 2 + b" using assms(3) nu by (simp add: field_simps)
  have nutc: "nu * (q - tc) = b / 2" using nu by (simp add: tc_def field_simps)
  have ntp: "nu * (tc - p) = pi / 2 + b / 2"
  proof -
    have "nu * (tc - p) = nu * (q - p) - nu * (q - tc)" by (simp add: algebra_simps)
    then show ?thesis using qp nutc by linarith
  qed
  have ptc: "p \<le> tc"
  proof -
    have "0 \<le> nu * (tc - p)" using ntp assms(2) pi_gt_zero by linarith
    then show ?thesis using assms(1) by (simp add: zero_le_mult_iff)
  qed
  have tcq: "tc \<le> q"
  proof -
    have "0 \<le> nu * (q - tc)" using nutc assms(2) by linarith
    then show ?thesis using assms(1) by (simp add: zero_le_mult_iff)
  qed
  have I1: "((\<lambda>t. cos (nu * (t - p))) has_integral
        (sin (nu * (tc - p)) / nu - sin (nu * (p - p)) / nu)) {p..tc}"
  proof (rule fundamental_theorem_of_calculus)
    show "p \<le> tc" by fact
    fix x :: real
    assume "x \<in> {p..tc}"
    have "((\<lambda>t. sin (nu * (t - p)) / nu) has_real_derivative cos (nu * (x - p))) (at x)"
      by (rule derivative_eq_intros refl | simp add: nu)+
    then have hd: "((\<lambda>t. sin (nu * (t - p)) / nu) has_vector_derivative cos (nu * (x - p))) (at x)"
      by (simp add: has_real_derivative_iff_has_vector_derivative)
    show "((\<lambda>t. sin (nu * (t - p)) / nu) has_vector_derivative cos (nu * (x - p))) (at x within {p..tc})"
      by (rule has_vector_derivative_at_within[OF hd])
  qed
  have I2: "((\<lambda>t. cos (pi / 2 + nu * (q - t))) has_integral
        (- sin (pi / 2 + nu * (q - q)) / nu - (- sin (pi / 2 + nu * (q - tc)) / nu))) {tc..q}"
  proof (rule fundamental_theorem_of_calculus)
    show "tc \<le> q" by fact
    fix x :: real
    assume "x \<in> {tc..q}"
    have "((\<lambda>t. - sin (pi / 2 + nu * (q - t)) / nu) has_real_derivative cos (pi / 2 + nu * (q - x))) (at x)"
      by (rule derivative_eq_intros refl | simp add: nu)+
    then have hd: "((\<lambda>t. - sin (pi / 2 + nu * (q - t)) / nu) has_vector_derivative
        cos (pi / 2 + nu * (q - x))) (at x)"
      by (simp add: has_real_derivative_iff_has_vector_derivative)
    show "((\<lambda>t. - sin (pi / 2 + nu * (q - t)) / nu) has_vector_derivative cos (pi / 2 + nu * (q - x)))
        (at x within {tc..q})"
      by (rule has_vector_derivative_at_within[OF hd])
  qed
  have v1: "sin (nu * (tc - p)) / nu - sin (nu * (p - p)) / nu = cos (b / 2) / nu"
    using ntp by (simp add: sin_add)
  have v2: "- sin (pi / 2 + nu * (q - q)) / nu - (- sin (pi / 2 + nu * (q - tc)) / nu)
      = (cos (b / 2) - 1) / nu"
  proof -
    have s: "sin (pi / 2 + nu * (q - tc)) = cos (b / 2)" by (simp add: sin_add nutc)
    show ?thesis by (simp add: s diff_divide_distrib)
  qed
  have J1: "((\<lambda>t. cos (min (nu * (t - p)) (pi / 2 + nu * (q - t)))) has_integral cos (b / 2) / nu) {p..tc}"
  proof (rule has_integral_eq[OF _ I1[unfolded v1]])
    fix x :: real
    assume "x \<in> {p..tc}"
    then have "x \<le> tc" by simp
    then have "nu * (x - p) \<le> pi / 2 + nu * (q - x)"
    proof -
      have "nu * x \<le> nu * tc" using assms(1) \<open>x \<le> tc\<close> by simp
      then show ?thesis using ntp qp by (simp add: algebra_simps)
    qed
    then show "cos (nu * (x - p)) = cos (min (nu * (x - p)) (pi / 2 + nu * (q - x)))"
      by (simp add: min_def)
  qed
  have J2: "((\<lambda>t. cos (min (nu * (t - p)) (pi / 2 + nu * (q - t)))) has_integral (cos (b / 2) - 1) / nu) {tc..q}"
  proof (rule has_integral_eq[OF _ I2[unfolded v2]])
    fix x :: real
    assume "x \<in> {tc..q}"
    then have "tc \<le> x" by simp
    then have "pi / 2 + nu * (q - x) \<le> nu * (x - p)"
    proof -
      have "nu * tc \<le> nu * x" using assms(1) \<open>tc \<le> x\<close> by simp
      then show ?thesis using ntp qp by (simp add: algebra_simps)
    qed
    then show "cos (pi / 2 + nu * (q - x)) = cos (min (nu * (x - p)) (pi / 2 + nu * (q - x)))"
      by (simp add: min_def)
  qed
  have "((\<lambda>t. cos (min (nu * (t - p)) (pi / 2 + nu * (q - t)))) has_integral
      (cos (b / 2) / nu + (cos (b / 2) - 1) / nu)) {p..q}"
    by (rule has_integral_combine[OF ptc tcq J1 J2])
  moreover have "cos (b / 2) / nu + (cos (b / 2) - 1) / nu = (2 * cos (b / 2) - 1) / nu"
    using nu by (simp add: field_simps)
  ultimately show ?thesis by simp
qed

section \<open>D. The sphere in three dimensions\<close>

locale sphere_curve = bounded_speed_curve n n' T nu
  for n n' :: "real \<Rightarrow> real^3" and T nu :: real +
  assumes T_pos: "0 < T" and north: "n 0 = axis 3 1" and south: "n T = - axis 3 1"
begin

lemma norm3:
  assumes "0 \<le> t" "t \<le> T"
  shows "(n t $ 1)\<^sup>2 + (n t $ 2)\<^sup>2 + (n t $ 3)\<^sup>2 = 1"
proof -
  have "inner (n t) (n t) = 1" using unit assms by (simp add: power2_norm_eq_inner[symmetric])
  then show ?thesis by (simp add: inner_vec_def sum_3 power2_eq_square)
qed

lemma inner_north: "inner (n t) (n 0) = n t $ 3" using north by (simp add: inner_axis)

lemma inner_south: "inner (n t) (n T) = - n t $ 3" using south by (simp add: inner_axis)

lemma crossing: "\<exists>ts. 0 \<le> ts \<and> ts \<le> T \<and> n ts $ 3 = 0"
proof -
  have c: "continuous_on {0..T} (\<lambda>t. n t $ 3)" by (intro continuous_intros cont)
  have a: "n T $ 3 = -1" "n 0 $ 3 = 1" using north south by (simp_all add: axis_def)
  have "\<exists>x. 0 \<le> x \<and> x \<le> T \<and> n x $ 3 = 0"
    using IVT2'[where f = "\<lambda>t. n t $ 3" and a = 0 and b = T and y = 0] a T_pos c by auto
  then show ?thesis by blast
qed

lemma perp_bound:
  assumes t: "0 \<le> t" "t \<le> T" and c: "0 \<le> c" "c \<le> pi / 2" and nz: "cos c \<le> \<bar>n t $ 3\<bar>"
    and e: "e1\<^sup>2 + e2\<^sup>2 = 1"
  shows "- sin c \<le> n t $ 1 * e1 + n t $ 2 * e2"
proof -
  define X where "X = n t $ 1 * e1 + n t $ 2 * e2"
  have n3: "(n t $ 1)\<^sup>2 + (n t $ 2)\<^sup>2 = 1 - (n t $ 3)\<^sup>2" using norm3[OF t] by linarith
  have c0: "0 \<le> cos c" using c by (intro cos_ge_zero) (use pi_gt_zero in auto)
  have "(cos c)\<^sup>2 \<le> \<bar>n t $ 3\<bar>\<^sup>2" using nz c0 by (intro power_mono) auto
  then have cc: "(cos c)\<^sup>2 \<le> (n t $ 3)\<^sup>2" by simp
  have sc: "(sin c)\<^sup>2 = 1 - (cos c)\<^sup>2" using sin_cos_squared_add[of c] by linarith
  have s2: "(n t $ 1)\<^sup>2 + (n t $ 2)\<^sup>2 \<le> (sin c)\<^sup>2" using n3 cc sc by linarith
  have id: "((n t $ 1)\<^sup>2 + (n t $ 2)\<^sup>2) * (e1\<^sup>2 + e2\<^sup>2) - X\<^sup>2 = (n t $ 1 * e2 - n t $ 2 * e1)\<^sup>2"
    unfolding X_def by (simp add: power2_eq_square algebra_simps)
  have "X\<^sup>2 \<le> (n t $ 1)\<^sup>2 + (n t $ 2)\<^sup>2"
  proof -
    have "(n t $ 1)\<^sup>2 + (n t $ 2)\<^sup>2 - X\<^sup>2 = (n t $ 1 * e2 - n t $ 2 * e1)\<^sup>2" using id e by simp
    moreover have "0 \<le> (n t $ 1 * e2 - n t $ 2 * e1)\<^sup>2" by simp
    ultimately show ?thesis by linarith
  qed
  then have "(- X)\<^sup>2 \<le> (sin c)\<^sup>2" using s2 by simp
  moreover have "0 \<le> sin c" using c pi_gt_zero by (intro sin_ge_zero) auto
  ultimately have "- X \<le> sin c" by (rule power2_le_imp_le)
  then show ?thesis unfolding X_def by linarith
qed

theorem frontier_core:
  assumes "nu * T - pi \<le> pi"
  shows "cos ((nu * T - pi) / 2) \<le>
    nu * (sqrt ((integral {0..T} (\<lambda>t. n t $ 1))\<^sup>2 + (integral {0..T} (\<lambda>t. n t $ 2))\<^sup>2) / 2)"
proof -
  obtain ts where ts: "0 \<le> ts" "ts \<le> T" and nz0: "n ts $ 3 = 0" using crossing by blast
  define e1 where "e1 = n ts $ 1"
  define e2 where "e2 = n ts $ 2"
  have e12: "e1\<^sup>2 + e2\<^sup>2 = 1" using norm3[OF ts] nz0 by (simp add: e1_def e2_def)
  define x where "x = (\<lambda>t. n t $ 1 * e1 + n t $ 2 * e2)"
  have xin: "\<And>t. x t = inner (n t) (n ts)"
    using nz0 by (simp add: x_def e1_def e2_def inner_vec_def sum_3 mult.commute)
  define al where "al = nu * ts - pi / 2"
  define be where "be = nu * (T - ts) - pi / 2"
  have al0: "0 \<le> al"
  proof (rule ccontr)
    assume "\<not> 0 \<le> al"
    then have lt: "nu * ts < pi / 2" by (simp add: al_def)
    have ab: "\<bar>0 - ts\<bar> = ts" using ts by simp
    have le: "nu * \<bar>0 - ts\<bar> \<le> pi" unfolding ab using lt pi_gt_zero by linarith
    have "cos (nu * \<bar>0 - ts\<bar>) \<le> inner (n 0) (n ts)"
      by (rule angle_bound_gen[OF _ _ _ _ le]) (use ts T_pos in auto)
    moreover have "inner (n 0) (n ts) = 0" using inner_north[of ts] nz0 by (simp add: inner_commute)
    moreover have "0 < cos (nu * \<bar>0 - ts\<bar>)"
    proof (rule cos_gt_zero_pi)
      have "0 \<le> nu * ts" using nu_pos ts by (intro mult_nonneg_nonneg) auto
      then show "- (pi / 2) < nu * \<bar>0 - ts\<bar>" unfolding ab using pi_gt_zero by linarith
      show "nu * \<bar>0 - ts\<bar> < pi / 2" unfolding ab by (rule lt)
    qed
    ultimately show False by simp
  qed
  have be0: "0 \<le> be"
  proof (rule ccontr)
    assume "\<not> 0 \<le> be"
    then have lt: "nu * (T - ts) < pi / 2" by (simp add: be_def)
    have ab: "\<bar>T - ts\<bar> = T - ts" using ts by simp
    have le: "nu * \<bar>T - ts\<bar> \<le> pi" unfolding ab using lt pi_gt_zero by linarith
    have "cos (nu * \<bar>T - ts\<bar>) \<le> inner (n T) (n ts)"
      by (rule angle_bound_gen[OF _ _ _ _ le]) (use ts T_pos in auto)
    moreover have "inner (n T) (n ts) = 0" using inner_south[of ts] nz0 by (simp add: inner_commute)
    moreover have "0 < cos (nu * \<bar>T - ts\<bar>)"
    proof (rule cos_gt_zero_pi)
      have "0 \<le> nu * (T - ts)" using nu_pos ts by (intro mult_nonneg_nonneg) auto
      then show "- (pi / 2) < nu * \<bar>T - ts\<bar>" unfolding ab using pi_gt_zero by linarith
      show "nu * \<bar>T - ts\<bar> < pi / 2" unfolding ab by (rule lt)
    qed
    ultimately show False by simp
  qed
  have sab: "al + be = nu * T - pi" unfolding al_def be_def by (simp add: algebra_simps)
  have al_le: "al \<le> pi" and be_le: "be \<le> pi" using sab al0 be0 assms by linarith+
  have nts: "nu * ts = pi / 2 + al" by (simp add: al_def)
  have nTs: "nu * (T - ts) = pi / 2 + be" by (simp add: be_def)
  have left: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> ts \<Longrightarrow> cos (min (nu * (ts - t)) (pi / 2 + nu * t)) \<le> x t"
  proof -
    fix t assume t: "0 \<le> t" "t \<le> ts"
    have tT: "t \<le> T" using t ts by linarith
    have nt: "0 \<le> nu * t" using nu_pos t by simp
    show "cos (min (nu * (ts - t)) (pi / 2 + nu * t)) \<le> x t"
    proof (cases "nu * (ts - t) \<le> pi / 2 + nu * t")
      case True
      then have m: "min (nu * (ts - t)) (pi / 2 + nu * t) = nu * (ts - t)" by (simp add: min_def)
      have "nu * (ts - t) \<le> pi" using True nts al_le by (simp add: algebra_simps)
      then have "cos (nu * \<bar>t - ts\<bar>) \<le> inner (n t) (n ts)"
        using t tT ts by (intro angle_bound_gen) (auto simp: abs_minus_commute)
      then show ?thesis using t m by (simp add: xin abs_minus_commute)
    next
      case False
      then have m: "min (nu * (ts - t)) (pi / 2 + nu * t) = pi / 2 + nu * t" by (simp add: min_def)
      have ntp: "nu * t \<le> pi / 2" using False nts al_le by (simp add: algebra_simps)
      have ab: "\<bar>t - 0\<bar> = t" using t by simp
      have le: "nu * \<bar>t - 0\<bar> \<le> pi" unfolding ab using ntp pi_gt_zero by linarith
      have "cos (nu * \<bar>t - 0\<bar>) \<le> inner (n t) (n 0)"
        by (rule angle_bound_gen[OF _ _ _ _ le]) (use t tT ts in auto)
      then have "cos (nu * t) \<le> n t $ 3" using t inner_north[of t] by simp
      then have "cos (nu * t) \<le> \<bar>n t $ 3\<bar>" by linarith
      from perp_bound[OF t(1) tT nt ntp this e12] have "- sin (nu * t) \<le> x t" unfolding x_def by blast
      then show ?thesis using m by (simp add: cos_add)
    qed
  qed
  have right: "\<And>t. ts \<le> t \<Longrightarrow> t \<le> T \<Longrightarrow> cos (min (nu * (t - ts)) (pi / 2 + nu * (T - t))) \<le> x t"
  proof -
    fix t assume t: "ts \<le> t" "t \<le> T"
    have t0: "0 \<le> t" using t ts by linarith
    have nt: "0 \<le> nu * (T - t)" using nu_pos t by simp
    show "cos (min (nu * (t - ts)) (pi / 2 + nu * (T - t))) \<le> x t"
    proof (cases "nu * (t - ts) \<le> pi / 2 + nu * (T - t)")
      case True
      then have m: "min (nu * (t - ts)) (pi / 2 + nu * (T - t)) = nu * (t - ts)" by (simp add: min_def)
      have "nu * (t - ts) \<le> pi" using True nTs be_le by (simp add: algebra_simps)
      then have "cos (nu * \<bar>t - ts\<bar>) \<le> inner (n t) (n ts)"
        using t t0 ts by (intro angle_bound_gen) auto
      then show ?thesis using t m by (simp add: xin)
    next
      case False
      then have m: "min (nu * (t - ts)) (pi / 2 + nu * (T - t)) = pi / 2 + nu * (T - t)"
        by (simp add: min_def)
      have ntp: "nu * (T - t) \<le> pi / 2" using False nTs be_le by (simp add: algebra_simps)
      have ab: "\<bar>t - T\<bar> = T - t" using t by simp
      have le: "nu * \<bar>t - T\<bar> \<le> pi" unfolding ab using ntp pi_gt_zero by linarith
      have "cos (nu * \<bar>t - T\<bar>) \<le> inner (n t) (n T)"
        by (rule angle_bound_gen[OF _ _ _ _ le]) (use t t0 ts in auto)
      then have "cos (nu * (T - t)) \<le> - n t $ 3" using t inner_south[of t] by (simp add: abs_minus_commute)
      then have "cos (nu * (T - t)) \<le> \<bar>n t $ 3\<bar>" by linarith
      from perp_bound[OF t0 t(2) nt ntp this e12] have "- sin (nu * (T - t)) \<le> x t" unfolding x_def by blast
      then show ?thesis using m by (simp add: cos_add)
    qed
  qed
  have contx: "continuous_on {0..T} x" unfolding x_def by (intro continuous_intros cont)
  have cxL: "continuous_on {0..ts} x" by (rule continuous_on_subset[OF contx]) (use ts in auto)
  have cxR: "continuous_on {ts..T} x" by (rule continuous_on_subset[OF contx]) (use ts in auto)
  have xL: "(x has_integral integral {0..ts} x) {0..ts}"
    by (rule integrable_integral[OF integrable_continuous_real[OF cxL]])
  have xR: "(x has_integral integral {ts..T} x) {ts..T}"
    by (rule integrable_integral[OF integrable_continuous_real[OF cxR]])
  have tL: "((\<lambda>t. cos (min (nu * (ts - t)) (pi / 2 + nu * t))) has_integral (2 * cos (al / 2) - 1) / nu) {0..ts}"
    by (rule tent_integral[OF nu_pos al0]) (use nts nu_pos in \<open>simp add: field_simps\<close>)
  have tR: "((\<lambda>t. cos (min (nu * (t - ts)) (pi / 2 + nu * (T - t)))) has_integral
      (2 * cos (be / 2) - 1) / nu) {ts..T}"
    by (rule tent_right[OF nu_pos be0]) (use nTs nu_pos in \<open>simp add: field_simps\<close>)
  have iL: "(2 * cos (al / 2) - 1) / nu \<le> integral {0..ts} x"
    by (rule has_integral_le[OF tL xL]) (use left in auto)
  have iR: "(2 * cos (be / 2) - 1) / nu \<le> integral {ts..T} x"
    by (rule has_integral_le[OF tR xR]) (use right in auto)
  have xT: "(x has_integral integral {0..ts} x + integral {ts..T} x) {0..T}"
    by (rule has_integral_combine[OF ts(1) ts(2) xL xR])
  define M1 where "M1 = integral {0..T} (\<lambda>t. n t $ 1)"
  define M2 where "M2 = integral {0..T} (\<lambda>t. n t $ 2)"
  have c1: "continuous_on {0..T} (\<lambda>t. n t $ 1)" and c2: "continuous_on {0..T} (\<lambda>t. n t $ 2)"
    by (intro continuous_intros cont)+
  have h1: "((\<lambda>t. n t $ 1) has_integral M1) {0..T}" unfolding M1_def
    by (intro integrable_integral integrable_continuous_real c1)
  have h2: "((\<lambda>t. n t $ 2) has_integral M2) {0..T}" unfolding M2_def
    by (intro integrable_integral integrable_continuous_real c2)
  have xT2: "(x has_integral e1 * M1 + e2 * M2) {0..T}" unfolding x_def
  proof (rule has_integral_add)
    show "((\<lambda>t. n t $ 1 * e1) has_integral e1 * M1) {0..T}"
      using has_integral_mult_right[OF h1, of e1] by (simp add: mult.commute)
    show "((\<lambda>t. n t $ 2 * e2) has_integral e2 * M2) {0..T}"
      using has_integral_mult_right[OF h2, of e2] by (simp add: mult.commute)
  qed
  have eq: "integral {0..ts} x + integral {ts..T} x = e1 * M1 + e2 * M2"
    by (rule has_integral_unique[OF xT xT2])
  have cs: "(e1 * M1 + e2 * M2)\<^sup>2 \<le> M1\<^sup>2 + M2\<^sup>2"
  proof -
    have "(M1\<^sup>2 + M2\<^sup>2) * (e1\<^sup>2 + e2\<^sup>2) - (e1 * M1 + e2 * M2)\<^sup>2 = (e1 * M2 - e2 * M1)\<^sup>2"
      by (simp add: power2_eq_square algebra_simps)
    then have "(M1\<^sup>2 + M2\<^sup>2) - (e1 * M1 + e2 * M2)\<^sup>2 = (e1 * M2 - e2 * M1)\<^sup>2" using e12 by simp
    moreover have "0 \<le> (e1 * M2 - e2 * M1)\<^sup>2" by simp
    ultimately show ?thesis by linarith
  qed
  have ub: "e1 * M1 + e2 * M2 \<le> sqrt (M1\<^sup>2 + M2\<^sup>2)" by (rule real_le_rsqrt[OF cs])
  have p1: "0 \<le> al + be" using al0 be0 by linarith
  have p3: "al \<le> al + be" using be0 by linarith
  have s_le: "al + be \<le> pi" using sab assms by linarith
  have c0: "1 + cos ((al + be) / 2) \<le> cos (al / 2) + cos ((al + be - al) / 2)"
    by (rule concavity_step[OF p1 s_le al0 p3])
  have conc: "1 + cos ((al + be) / 2) \<le> cos (al / 2) + cos (be / 2)" using c0 by simp
  define R where "R = sqrt (M1\<^sup>2 + M2\<^sup>2)"
  have st0: "(2 * cos (al / 2) - 1) / nu + (2 * cos (be / 2) - 1) / nu \<le> R"
    using iL iR eq ub unfolding R_def by linarith
  have st1: "((2 * cos (al / 2) - 1) + (2 * cos (be / 2) - 1)) / nu \<le> R"
    using st0 by (simp only: add_divide_distrib)
  have st2: "(2 * cos (al / 2) - 1) + (2 * cos (be / 2) - 1) \<le> R * nu"
    using st1 by (simp only: pos_divide_le_eq[OF nu_pos])
  have st3: "2 * cos ((al + be) / 2) \<le> nu * R" using st2 conc mult.commute[of R nu] by linarith
  have e: "cos ((nu * T - pi) / 2) = cos ((al + be) / 2)" using sab by simp
  have "cos ((nu * T - pi) / 2) \<le> nu * (R / 2)" using st3 e by linarith
  then show ?thesis unfolding R_def M1_def M2_def .
qed

end

section \<open>E. The exposure inequality\<close>

lemma lambda_min:
  fixes X Y R :: real
  assumes "0 \<le> X" "0 \<le> Y" and "\<And>l. 0 < l \<Longrightarrow> R \<le> l * X + Y / l"
  shows "R \<le> 2 * sqrt (X * Y)"
proof (cases "X = 0")
  case True
  have "R \<le> 0"
  proof (rule ccontr)
    assume "\<not> R \<le> 0"
    then have R: "0 < R" by simp
    define l where "l = (Y + 1) / R"
    have l: "0 < l" unfolding l_def using R assms(2) by simp
    have "R \<le> l * X + Y / l" by (rule assms(3)[OF l])
    then have "R \<le> Y * R / (Y + 1)" using True unfolding l_def by (simp add: field_simps)
    then have "R * (Y + 1) \<le> Y * R" using assms(2) by (simp add: pos_le_divide_eq)
    then show False using R by (simp add: algebra_simps)
  qed
  then show ?thesis using True by simp
next
  case False
  then have X: "0 < X" using assms(1) by simp
  show ?thesis
  proof (cases "Y = 0")
    case True
    have "R \<le> 0"
    proof (rule ccontr)
      assume "\<not> R \<le> 0"
      then have R: "0 < R" by simp
      define l where "l = R / (2 * X)"
      have l: "0 < l" unfolding l_def using R X by simp
      have "R \<le> l * X + Y / l" by (rule assms(3)[OF l])
      then have "R \<le> R / 2" using True X unfolding l_def by (simp add: field_simps)
      then show False using R by simp
    qed
    then show ?thesis using True by simp
  next
    case False
    then have Y: "0 < Y" using assms(2) by simp
    define l where "l = sqrt Y / sqrt X"
    have l: "0 < l" unfolding l_def using X Y by simp
    have sx: "sqrt X * sqrt X = X" using X by simp
    have sy: "sqrt Y * sqrt Y = Y" using Y by simp
    have "l * X = sqrt Y * sqrt X" unfolding l_def using X sx by (simp add: field_simps)
    moreover have "Y / l = sqrt Y * sqrt X" unfolding l_def using X Y sy by (simp add: field_simps)
    ultimately have "l * X + Y / l = 2 * (sqrt Y * sqrt X)" by simp
    moreover have "sqrt X * sqrt Y = sqrt (X * Y)" by (simp add: real_sqrt_mult)
    ultimately show ?thesis using assms(3)[OF l] by (simp add: mult.commute)
  qed
qed

locale sphere_open = sphere_curve n n' T nu
  for n n' :: "real \<Rightarrow> real^3" and T nu :: real +
  assumes inside: "\<And>t. 0 < t \<Longrightarrow> t < T \<Longrightarrow> - 1 < n t $ 3 \<and> n t $ 3 < 1"
begin

theorem exposure_core:
  "integral {0..T} (\<lambda>t. sqrt ((n t $ 1)\<^sup>2 + (n t $ 2)\<^sup>2)) - 2 / nu \<le>
    2 * sqrt ((integral {0..T} (\<lambda>t. (1 + n t $ 3) / 2) - pi / (2 * nu)) *
              (integral {0..T} (\<lambda>t. (1 - n t $ 3) / 2) - pi / (2 * nu)))"
proof -
  define z where "z = (\<lambda>t. n t $ 3)"
  have T0: "0 \<le> T" using T_pos by simp
  have zr: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> T \<Longrightarrow> - 1 \<le> z t \<and> z t \<le> 1"
  proof -
    fix t assume t: "0 \<le> t" "t \<le> T"
    have h: "(z t)\<^sup>2 \<le> 1" using norm3[OF t] zero_le_power2[of "n t $ 1"] zero_le_power2[of "n t $ 2"]
      unfolding z_def by linarith
    have "z t \<le> 1" by (rule power2_le_imp_le[of "z t" 1]) (use h in simp_all)
    moreover have "- z t \<le> 1" by (rule power2_le_imp_le[of "- z t" 1]) (use h in simp_all)
    ultimately show "- 1 \<le> z t \<and> z t \<le> 1" by simp
  qed
  have zc: "continuous_on {0..T} z" unfolding z_def by (intro continuous_intros cont)
  have e1: "norm (axis 3 (1::real) :: real^3) = 1" by simp
  have zd: "\<And>t. 0 < t \<Longrightarrow> t < T \<Longrightarrow> (z has_real_derivative n' t $ 3) (at t)"
  proof -
    fix t assume t: "0 < t" "t < T"
    have "((\<lambda>x. inner (n x) (axis 3 (1::real))) has_real_derivative inner (n' t) (axis 3 (1::real))) (at t)"
      by (rule u_derivative[OF t])
    then show "(z has_real_derivative n' t $ 3) (at t)" by (simp add: inner_axis z_def)
  qed
  have zb: "\<And>t. 0 < t \<Longrightarrow> t < T \<Longrightarrow> (n' t $ 3)\<^sup>2 \<le> nu\<^sup>2 * (1 - (z t)\<^sup>2)"
  proof -
    fix t assume t: "0 < t" "t < T"
    have "(inner (n' t) (axis 3 (1::real)))\<^sup>2 \<le> nu\<^sup>2 * (1 - (inner (n t) (axis 3 (1::real)))\<^sup>2)"
      by (rule u_square_bound[OF t e1])
    then show "(n' t $ 3)\<^sup>2 \<le> nu\<^sup>2 * (1 - (z t)\<^sup>2)" by (simp add: inner_axis z_def)
  qed
  have z0: "z 0 = 1" and zT: "z T = - 1" using north south unfolding z_def by (simp_all add: axis_def)
  define th where "th = (\<lambda>t. arccos (z t))"
  define th' where "th' = (\<lambda>t. if 0 < t \<and> t < T then - (n' t $ 3) / sqrt (1 - (z t)\<^sup>2) else 0)"
  have thc: "continuous_on {0..T} th" unfolding th_def using zc zr by (intro continuous_intros) auto
  have thd: "\<And>t. 0 < t \<Longrightarrow> t < T \<Longrightarrow> (th has_real_derivative th' t) (at t)"
  proof -
    fix t assume t: "0 < t" "t < T"
    have "- 1 < z t" "z t < 1" using inside[OF t] unfolding z_def by auto
    from DERIV_chain2[OF DERIV_arccos[OF this] zd[OF t]]
    have "((\<lambda>x. arccos (z x)) has_real_derivative inverse (- sqrt (1 - (z t)\<^sup>2)) * n' t $ 3) (at t)" .
    moreover have "inverse (- sqrt (1 - (z t)\<^sup>2)) * n' t $ 3 = th' t"
      using t by (simp add: th'_def inverse_eq_divide divide_minus_left)
    ultimately show "(th has_real_derivative th' t) (at t)" unfolding th_def by simp
  qed
  have ftc: "\<And>Phi Phi'. (\<And>y. (Phi has_real_derivative Phi' y) (at y)) \<Longrightarrow>
      ((\<lambda>t. Phi' (th t) * th' t) has_integral Phi pi - Phi 0) {0..T}"
  proof -
    fix Phi Phi' assume d: "\<And>y. (Phi has_real_derivative Phi' y) (at y)"
    have cP: "continuous_on UNIV Phi" using d by (intro DERIV_continuous_on) auto
    have c: "continuous_on {0..T} (\<lambda>t. Phi (th t))"
      by (rule continuous_on_compose2[OF cP thc]) auto
    have der: "\<And>t. t \<in> {0<..<T} \<Longrightarrow> ((\<lambda>t. Phi (th t)) has_vector_derivative Phi' (th t) * th' t) (at t)"
    proof -
      fix t assume t: "t \<in> {0<..<T}"
      have "((\<lambda>t. Phi (th t)) has_real_derivative Phi' (th t) * th' t) (at t)"
        by (rule DERIV_chain2[OF d thd]) (use t in auto)
      then show "((\<lambda>t. Phi (th t)) has_vector_derivative Phi' (th t) * th' t) (at t)"
        by (simp add: has_real_derivative_iff_has_vector_derivative)
    qed
    have "((\<lambda>t. Phi' (th t) * th' t) has_integral Phi (th T) - Phi (th 0)) {0..T}"
      by (rule fundamental_theorem_of_calculus_interior[OF T0 c der])
    moreover have "th T = pi" "th 0 = 0" unfolding th_def using zT z0 by simp_all
    ultimately show "((\<lambda>t. Phi' (th t) * th' t) has_integral Phi pi - Phi 0) {0..T}" by simp
  qed
  have cth: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> T \<Longrightarrow> cos (th t) = z t" unfolding th_def using zr by simp
  have nu0: "nu \<noteq> 0" using nu_pos by simp
  define a1 where "a1 = (\<lambda>t. (1 + z t) / 2)"
  define a2 where "a2 = (\<lambda>t. (1 - z t) / 2)"
  define s where "s = (\<lambda>t. sqrt ((n t $ 1)\<^sup>2 + (n t $ 2)\<^sup>2))"
  define h where "h = (\<lambda>t. 1 - th' t / nu)"
  define A where "A = integral {0..T} a1"
  define B where "B = integral {0..T} a2"
  define Q where "Q = integral {0..T} s"
  have sz: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> T \<Longrightarrow> s t = sqrt (1 - (z t)\<^sup>2)"
  proof -
    fix t assume t: "0 \<le> t" "t \<le> T"
    have "(n t $ 1)\<^sup>2 + (n t $ 2)\<^sup>2 = 1 - (z t)\<^sup>2" using norm3[OF t] unfolding z_def by linarith
    then show "s t = sqrt (1 - (z t)\<^sup>2)" unfolding s_def by simp
  qed
  have ca1: "continuous_on {0..T} a1" unfolding a1_def by (intro continuous_intros zc; simp)
  have ca2: "continuous_on {0..T} a2" unfolding a2_def by (intro continuous_intros zc; simp)
  have cs: "continuous_on {0..T} s" unfolding s_def by (intro continuous_intros cont)
  have hA: "(a1 has_integral A) {0..T}" unfolding A_def by (intro integrable_integral integrable_continuous_real ca1)
  have hB: "(a2 has_integral B) {0..T}" unfolding B_def by (intro integrable_integral integrable_continuous_real ca2)
  have hQ: "(s has_integral Q) {0..T}" unfolding Q_def by (intro integrable_integral integrable_continuous_real cs)
  have dP1: "\<And>y::real. ((\<lambda>y. (y + sin y) / 2) has_real_derivative (1 + cos y) / 2) (at y)"
    by (rule derivative_eq_intros refl | simp)+
  have dP2: "\<And>y::real. ((\<lambda>y. (y - sin y) / 2) has_real_derivative (1 - cos y) / 2) (at y)"
    by (rule derivative_eq_intros refl | simp)+
  have dP0: "\<And>y::real. ((\<lambda>y. - cos y) has_real_derivative sin y) (at y)"
    by (rule derivative_eq_intros refl | simp)+
  have K1: "((\<lambda>t. a1 t * th' t) has_integral pi / 2) {0..T}"
  proof -
    have I: "((\<lambda>t. (1 + cos (th t)) / 2 * th' t) has_integral pi / 2) {0..T}"
      using ftc[OF dP1] by simp
    show ?thesis
    proof (rule has_integral_eq[OF _ I])
      fix x assume x: "x \<in> {0..T}"
      then have "cos (th x) = z x" by (intro cth) auto
      then show "(1 + cos (th x)) / 2 * th' x = a1 x * th' x" by (simp add: a1_def)
    qed
  qed
  have K2: "((\<lambda>t. a2 t * th' t) has_integral pi / 2) {0..T}"
  proof -
    have I: "((\<lambda>t. (1 - cos (th t)) / 2 * th' t) has_integral pi / 2) {0..T}"
      using ftc[OF dP2] by simp
    show ?thesis
    proof (rule has_integral_eq[OF _ I])
      fix x assume x: "x \<in> {0..T}"
      then have "cos (th x) = z x" by (intro cth) auto
      then show "(1 - cos (th x)) / 2 * th' x = a2 x * th' x" by (simp add: a2_def)
    qed
  qed
  have K0: "((\<lambda>t. s t * th' t) has_integral 2) {0..T}"
  proof -
    have I: "((\<lambda>t. sin (th t) * th' t) has_integral 2) {0..T}"
      using ftc[OF dP0] by simp
    show ?thesis
    proof (rule has_integral_eq[OF _ I])
      fix x assume x: "x \<in> {0..T}"
      then have x': "0 \<le> x" "x \<le> T" by auto
      have "\<bar>z x\<bar> \<le> 1" using zr[OF x'] by (simp add: abs_le_iff)
      then have "sin (th x) = sqrt (1 - (z x)\<^sup>2)" unfolding th_def by (rule sin_arccos_abs)
      then show "sin (th x) * th' x = s x * th' x" using sz[OF x'] by simp
    qed
  qed
  have hle: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> T \<Longrightarrow> th' t \<le> nu"
  proof -
    fix t assume t: "0 \<le> t" "t \<le> T"
    show "th' t \<le> nu"
    proof (cases "0 < t \<and> t < T")
      case True
      then have t': "0 < t" "t < T" by auto
      have zi: "- 1 < z t" "z t < 1" using inside[OF t'] unfolding z_def by auto
      have pos: "0 < 1 - (z t)\<^sup>2"
      proof -
        have "0 < (1 - z t) * (1 + z t)" using zi by (intro mult_pos_pos; linarith)
        then show ?thesis by (simp add: power2_eq_square algebra_simps)
      qed
      have sp: "0 < sqrt (1 - (z t)\<^sup>2)" using pos by simp
      have sq: "(- (n' t $ 3))\<^sup>2 \<le> (nu * sqrt (1 - (z t)\<^sup>2))\<^sup>2"
        using zb[OF t'] pos by (simp add: power_mult_distrib)
      have nn: "0 \<le> nu * sqrt (1 - (z t)\<^sup>2)" using sp nu_pos by simp
      have h1: "- (n' t $ 3) \<le> nu * sqrt (1 - (z t)\<^sup>2)" by (rule power2_le_imp_le[OF sq nn])
      have eq: "th' t = - (n' t $ 3) / sqrt (1 - (z t)\<^sup>2)" unfolding th'_def by (rule if_P[OF True])
      show ?thesis unfolding eq by (subst pos_divide_le_eq[OF sp]) (rule h1)
    next
      case False
      have eq0: "th' t = 0" unfolding th'_def by (rule if_not_P[OF False])
      show ?thesis unfolding eq0 using nu_pos by simp
    qed
  qed
  have hpos: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> T \<Longrightarrow> 0 \<le> h t"
  proof -
    fix t assume t: "0 \<le> t" "t \<le> T"
    have "th' t / nu \<le> 1" using hle[OF t] nu_pos by (simp add: divide_le_eq)
    then show "0 \<le> h t" unfolding h_def by simp
  qed
  have P1: "((\<lambda>t. a1 t * h t) has_integral A - pi / (2 * nu)) {0..T}"
  proof -
    have hh: "((\<lambda>t. a1 t - (1 / nu) *\<^sub>R (a1 t * th' t)) has_integral A - (1 / nu) *\<^sub>R (pi / 2)) {0..T}"
      by (rule has_integral_diff[OF hA has_integral_cmul[OF K1]])
    have e1': "(\<lambda>t. a1 t - (1 / nu) *\<^sub>R (a1 t * th' t)) = (\<lambda>t. a1 t * h t)"
      by (rule ext) (simp add: h_def real_scaleR_def field_simps)
    have e2': "A - (1 / nu) *\<^sub>R (pi / 2) = A - pi / (2 * nu)" by (simp add: real_scaleR_def field_simps)
    show ?thesis using hh unfolding e1' e2' .
  qed
  have P2: "((\<lambda>t. a2 t * h t) has_integral B - pi / (2 * nu)) {0..T}"
  proof -
    have hh: "((\<lambda>t. a2 t - (1 / nu) *\<^sub>R (a2 t * th' t)) has_integral B - (1 / nu) *\<^sub>R (pi / 2)) {0..T}"
      by (rule has_integral_diff[OF hB has_integral_cmul[OF K2]])
    have e1': "(\<lambda>t. a2 t - (1 / nu) *\<^sub>R (a2 t * th' t)) = (\<lambda>t. a2 t * h t)"
      by (rule ext) (simp add: h_def real_scaleR_def field_simps)
    have e2': "B - (1 / nu) *\<^sub>R (pi / 2) = B - pi / (2 * nu)" by (simp add: real_scaleR_def field_simps)
    show ?thesis using hh unfolding e1' e2' .
  qed
  have P0: "((\<lambda>t. s t * h t) has_integral Q - 2 / nu) {0..T}"
  proof -
    have hh: "((\<lambda>t. s t - (1 / nu) *\<^sub>R (s t * th' t)) has_integral Q - (1 / nu) *\<^sub>R 2) {0..T}"
      by (rule has_integral_diff[OF hQ has_integral_cmul[OF K0]])
    have e1': "(\<lambda>t. s t - (1 / nu) *\<^sub>R (s t * th' t)) = (\<lambda>t. s t * h t)"
      by (rule ext) (simp add: h_def real_scaleR_def field_simps)
    have e2': "Q - (1 / nu) *\<^sub>R 2 = Q - 2 / nu" by (simp add: real_scaleR_def field_simps)
    show ?thesis using hh unfolding e1' e2' .
  qed
  have a1h: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> T \<Longrightarrow> 0 \<le> a1 t * h t"
  proof -
    fix t assume t: "0 \<le> t" "t \<le> T"
    have "0 \<le> a1 t" using zr[OF t] unfolding a1_def by simp
    then show "0 \<le> a1 t * h t" by (rule mult_nonneg_nonneg[OF _ hpos[OF t]])
  qed
  have a2h: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> T \<Longrightarrow> 0 \<le> a2 t * h t"
  proof -
    fix t assume t: "0 \<le> t" "t \<le> T"
    have "0 \<le> a2 t" using zr[OF t] unfolding a2_def by simp
    then show "0 \<le> a2 t * h t" by (rule mult_nonneg_nonneg[OF _ hpos[OF t]])
  qed
  have X0: "0 \<le> A - pi / (2 * nu)" by (rule has_integral_nonneg[OF P1]) (use a1h in auto)
  have Y0: "0 \<le> B - pi / (2 * nu)" by (rule has_integral_nonneg[OF P2]) (use a2h in auto)
  have amgm: "\<And>l t. 0 < l \<Longrightarrow> 0 \<le> t \<Longrightarrow> t \<le> T \<Longrightarrow> s t * h t \<le> l * (a1 t * h t) + (1 / l) * (a2 t * h t)"
  proof -
    fix l t :: real
    assume l: "0 < l" and t: "0 \<le> t" "t \<le> T"
    have h0: "0 \<le> h t" by (rule hpos[OF t])
    have zz: "- 1 \<le> z t" "z t \<le> 1" using zr[OF t] by auto
    have a10: "0 \<le> a1 t" and a20: "0 \<le> a2 t" unfolding a1_def a2_def using zz by auto
    have s0: "0 \<le> s t" unfolding s_def by simp
    have s2: "(s t)\<^sup>2 = 4 * (a1 t * a2 t)"
    proof -
      have "(s t)\<^sup>2 = (n t $ 1)\<^sup>2 + (n t $ 2)\<^sup>2" unfolding s_def by simp
      also have "\<dots> = 1 - (z t)\<^sup>2" using norm3[OF t] unfolding z_def by linarith
      also have "\<dots> = 4 * (a1 t * a2 t)" unfolding a1_def a2_def by (simp add: power2_eq_square algebra_simps)
      finally show ?thesis .
    qed
    define m where "m = a2 t / l"
    have a2m: "a2 t = l * m" unfolding m_def using l by simp
    have m0: "0 \<le> m" unfolding m_def using a20 l by simp
    have sq: "(s t)\<^sup>2 \<le> (l * a1 t + m)\<^sup>2"
    proof -
      have "(l * a1 t + m)\<^sup>2 - (s t)\<^sup>2 = (l * a1 t - m)\<^sup>2" using s2 a2m by (simp add: power2_eq_square algebra_simps)
      moreover have "0 \<le> (l * a1 t - m)\<^sup>2" by simp
      ultimately show ?thesis by linarith
    qed
    have "s t \<le> l * a1 t + m" by (rule power2_le_imp_le[OF sq]) (use l a10 m0 in \<open>simp add: add_nonneg_nonneg\<close>)
    then have "s t * h t \<le> (l * a1 t + m) * h t" using h0 by (intro mult_right_mono)
    also have "\<dots> = l * (a1 t * h t) + (1 / l) * (a2 t * h t)" unfolding m_def by (simp add: field_simps)
    finally show "s t * h t \<le> l * (a1 t * h t) + (1 / l) * (a2 t * h t)" .
  qed
  have key: "\<And>l. 0 < l \<Longrightarrow> Q - 2 / nu \<le> l * (A - pi / (2 * nu)) + (B - pi / (2 * nu)) / l"
  proof -
    fix l :: real
    assume l: "0 < l"
    have "((\<lambda>t. l *\<^sub>R (a1 t * h t) + (1 / l) *\<^sub>R (a2 t * h t)) has_integral
        l *\<^sub>R (A - pi / (2 * nu)) + (1 / l) *\<^sub>R (B - pi / (2 * nu))) {0..T}"
      by (rule has_integral_add[OF has_integral_cmul[OF P1] has_integral_cmul[OF P2]])
    then have "((\<lambda>t. l * (a1 t * h t) + (1 / l) * (a2 t * h t)) has_integral
        l * (A - pi / (2 * nu)) + (1 / l) * (B - pi / (2 * nu))) {0..T}" by (simp add: real_scaleR_def)
    then have "Q - 2 / nu \<le> l * (A - pi / (2 * nu)) + (1 / l) * (B - pi / (2 * nu))"
      by (rule has_integral_le[OF P0]) (use amgm[OF l] in auto)
    then show "Q - 2 / nu \<le> l * (A - pi / (2 * nu)) + (B - pi / (2 * nu)) / l" by simp
  qed
  have "Q - 2 / nu \<le> 2 * sqrt ((A - pi / (2 * nu)) * (B - pi / (2 * nu)))"
    by (rule lambda_min[OF X0 Y0 key])
  then show ?thesis unfolding A_def B_def Q_def a1_def a2_def s_def z_def .
qed

end

section \<open>F. Statements\<close>

theorem angle_bound:
  assumes "bounded_speed_curve n n' T nu"
    and "0 \<le> s" "s \<le> T" "0 \<le> t" "t \<le> T" and "nu * \<bar>s - t\<bar> \<le> pi"
  shows "cos (nu * \<bar>s - t\<bar>) \<le> inner (n s) (n t)"
proof -
  interpret bounded_speed_curve n n' T nu by fact
  show ?thesis by (rule angle_bound_gen) fact+
qed

theorem equatorial_crossing:
  assumes "sphere_curve n n' T nu"
  shows "\<exists>ts. 0 \<le> ts \<and> ts \<le> T \<and> n ts $ 3 = 0"
proof -
  interpret sphere_curve n n' T nu by fact
  show ?thesis by (rule crossing)
qed

theorem frontier_general:
  assumes "sphere_curve n n' T nu" and "nu * T - pi \<le> pi"
  shows "cos ((nu * T - pi) / 2) \<le>
    nu * (sqrt ((integral {0..T} (\<lambda>t. n t $ 1))\<^sup>2 + (integral {0..T} (\<lambda>t. n t $ 2))\<^sup>2) / 2)"
proof -
  interpret sphere_curve n n' T nu by fact
  show ?thesis by (rule frontier_core) fact
qed

theorem exposure_bound:
  assumes "sphere_open n n' T nu"
  shows "integral {0..T} (\<lambda>t. sqrt ((n t $ 1)\<^sup>2 + (n t $ 2)\<^sup>2)) - 2 / nu \<le>
    2 * sqrt ((integral {0..T} (\<lambda>t. (1 + n t $ 3) / 2) - pi / (2 * nu)) *
              (integral {0..T} (\<lambda>t. (1 - n t $ 3) / 2) - pi / (2 * nu)))"
proof -
  interpret sphere_open n n' T nu by fact
  show ?thesis by (rule exposure_core)
qed

end
