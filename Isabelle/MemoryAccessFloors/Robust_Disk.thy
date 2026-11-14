(*  Title:      Robust_Disk.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License: BSD
*)

theory Robust_Disk
  imports Robust_Core
begin

text \<open>Part (a) of the robustness theorem for a complete transfer, for every curve of speed at most
  @{text "\<nu>"} from the north to the south pole, with no hypothesis on the poles in the interior.
  With @{text "A = \<int>(1+n\<^sub>z)/2"}, @{text "B = \<int>(1-n\<^sub>z)/2"}, @{text "\<zeta> = |\<int>n\<^sub>\<perp>|/2"},
  @{text "A\<^sub>0 = \<pi>/(2\<nu>)"}, @{text "z\<^sub>0 = 1/\<nu>"} we show @{text "A \<ge> A\<^sub>0"}, @{text "B \<ge> A\<^sub>0"} and
  @{text "(\<zeta> - z\<^sub>0)\<^sup>2 \<le> (A - A\<^sub>0)(B - A\<^sub>0)"}.  The proof avoids @{text "\<theta> = arccos n\<^sub>z"} on the whole
  interval: a barrier argument is run up to the first arrival at the south pole.\<close>

section \<open>A. Elementary lemmas\<close>

lemma deriv_indef:
  fixes f :: "real \<Rightarrow> real" and a b x :: real
  assumes "continuous_on {a..b} f" and "a < x" and "x < b"
  shows "((\<lambda>v. integral {a..v} f) has_real_derivative f x) (at x)"
proof -
  have xin: "x \<in> {a..b}" using assms(2,3) by simp
  have "((\<lambda>v. integral {a..v} f) has_vector_derivative f x) (at x within {a..b})"
    by (rule integral_has_vector_derivative[OF assms(1) xin])
  moreover have "{a<..<b} \<subseteq> {a..b}" by auto
  ultimately have h2: "((\<lambda>v. integral {a..v} f) has_vector_derivative f x) (at x within {a<..<b})"
    by (rule has_vector_derivative_within_subset)
  have uo: "x \<in> {a<..<b}" using assms(2,3) by simp
  have "at x within {a<..<b} = at x" by (rule at_within_open[OF uo open_greaterThanLessThan])
  then have "((\<lambda>v. integral {a..v} f) has_vector_derivative f x) (at x)" using h2 by simp
  then show ?thesis by (simp add: has_real_derivative_iff_has_vector_derivative)
qed

definition expo :: "real \<Rightarrow> real \<Rightarrow> real" where
  "expo l y = l * ((1 + y) / 2) + ((1 - y) / 2) / l - sqrt (1 - y\<^sup>2)"

definition expo_th :: "real \<Rightarrow> real \<Rightarrow> real" where
  "expo_th l th = l * ((1 + cos th) / 2) + (1 / l) * ((1 - cos th) / 2) - sin th"

definition expo_prim :: "real \<Rightarrow> real \<Rightarrow> real" where
  "expo_prim l th = l * ((th + sin th) / 2) + (1 / l) * ((th - sin th) / 2) - (1 - cos th)"

lemma expo_nonneg:
  fixes l y :: real
  assumes "0 < l" and "- 1 \<le> y" and "y \<le> 1"
  shows "0 \<le> expo l y"
proof -
  define a1 where "a1 = (1 + y) / 2"
  define a2 where "a2 = (1 - y) / 2"
  have a10: "0 \<le> a1" and a20: "0 \<le> a2" using assms(2,3) by (simp_all add: a1_def a2_def)
  have y2: "0 \<le> 1 - y\<^sup>2"
  proof -
    have "0 \<le> (1 - y) * (1 + y)" using assms(2,3) by (intro mult_nonneg_nonneg) auto
    then show ?thesis by (simp add: power2_eq_square algebra_simps)
  qed
  have s2: "(sqrt (1 - y\<^sup>2))\<^sup>2 = 4 * (a1 * a2)"
  proof -
    have "(sqrt (1 - y\<^sup>2))\<^sup>2 = 1 - y\<^sup>2" using y2 by simp
    also have "\<dots> = 4 * (a1 * a2)" unfolding a1_def a2_def by (simp add: power2_eq_square algebra_simps)
    finally show ?thesis .
  qed
  define m where "m = a2 / l"
  have a2m: "a2 = l * m" unfolding m_def using assms(1) by simp
  have m0: "0 \<le> m" unfolding m_def using a20 assms(1) by simp
  have sq: "(sqrt (1 - y\<^sup>2))\<^sup>2 \<le> (l * a1 + m)\<^sup>2"
  proof -
    have "(l * a1 + m)\<^sup>2 - (sqrt (1 - y\<^sup>2))\<^sup>2 = (l * a1 - m)\<^sup>2"
      using s2 a2m by (simp add: power2_eq_square algebra_simps)
    moreover have "0 \<le> (l * a1 - m)\<^sup>2" by simp
    ultimately show ?thesis by linarith
  qed
  have nn: "0 \<le> l * a1 + m" using assms(1) a10 m0 by (intro add_nonneg_nonneg mult_nonneg_nonneg) auto
  have "sqrt (1 - y\<^sup>2) \<le> l * a1 + m" by (rule power2_le_imp_le[OF sq nn])
  then show ?thesis unfolding expo_def a1_def[symmetric] a2_def[symmetric] m_def by simp
qed

lemma expo_th_arccos:
  fixes l y :: real
  assumes "- 1 \<le> y" and "y \<le> 1"
  shows "expo_th l (arccos y) = expo l y"
  using assms by (simp add: expo_th_def expo_def cos_arccos sin_arccos field_simps)

lemma expo_prim_deriv:
  fixes l y :: real
  assumes "0 < l"
  shows "(expo_prim l has_real_derivative expo_th l y) (at y)"
proof -
  have l_ne: "l \<noteq> 0" using assms by simp
  show ?thesis unfolding expo_prim_def expo_th_def
    by (rule derivative_eq_intros refl | simp add: field_simps l_ne)+
qed

lemma expo_prim_zero: "expo_prim l 0 = 0"
  by (simp add: expo_prim_def)

lemma expo_prim_pi:
  fixes l :: real
  assumes "0 < l"
  shows "expo_prim l pi = l * pi / 2 + pi / (2 * l) - 2"
  using assms by (simp add: expo_prim_def field_simps)

lemma lam_nonneg:
  fixes R X Y :: real
  assumes "0 \<le> R" and "\<And>l. 0 < l \<Longrightarrow> R \<le> l * X + Y / l"
  shows "0 \<le> X"
proof (rule ccontr)
  assume "\<not> 0 \<le> X"
  then have X: "X < 0" by simp
  define m where "m = (\<bar>Y\<bar> + 1) / (- X)"
  have m0: "0 \<le> m" unfolding m_def using X by (intro divide_nonneg_pos) auto
  define l where "l = 1 + m"
  have l1: "1 \<le> l" unfolding l_def by (simp add: m0)
  have l0: "0 < l" using l1 by simp
  have mX: "m * X = - (\<bar>Y\<bar> + 1)" unfolding m_def using X by (simp add: field_simps)
  have lX: "l * X = X - (\<bar>Y\<bar> + 1)" unfolding l_def using mX by (simp add: algebra_simps)
  have Yl: "Y / l \<le> \<bar>Y\<bar>"
  proof -
    have "Y \<le> \<bar>Y\<bar> * l" using l1 by (smt (verit) abs_ge_zero abs_ge_self mult_le_cancel_left1 mult_nonneg_nonneg)
    then show ?thesis using l0 by (simp add: pos_divide_le_eq)
  qed
  have "R \<le> l * X + Y / l" by (rule assms(2)[OF l0])
  then show False using lX Yl X assms(1) by linarith
qed

lemma cs_abs:
  fixes a b e1 e2 :: real
  assumes "e1\<^sup>2 + e2\<^sup>2 = 1"
  shows "\<bar>a * e1 + b * e2\<bar> \<le> sqrt (a\<^sup>2 + b\<^sup>2)"
proof -
  have id: "(a\<^sup>2 + b\<^sup>2) * (e1\<^sup>2 + e2\<^sup>2) - (a * e1 + b * e2)\<^sup>2 = (a * e2 - b * e1)\<^sup>2"
    by (simp add: power2_eq_square algebra_simps)
  have "(a\<^sup>2 + b\<^sup>2) - (a * e1 + b * e2)\<^sup>2 = (a * e2 - b * e1)\<^sup>2" using id assms by simp
  then have "(a * e1 + b * e2)\<^sup>2 \<le> a\<^sup>2 + b\<^sup>2" by (smt (verit) zero_le_power2)
  then have "\<bar>a * e1 + b * e2\<bar>\<^sup>2 \<le> (sqrt (a\<^sup>2 + b\<^sup>2))\<^sup>2" by simp
  then show ?thesis by (rule power2_le_imp_le) simp
qed

section \<open>B. The exposure inequality without the pole hypothesis\<close>

context sphere_curve
begin

lemma z_range:
  assumes "0 \<le> t" "t \<le> T"
  shows "- 1 \<le> n t $ 3 \<and> n t $ 3 \<le> 1"
proof -
  have h: "(n t $ 3)\<^sup>2 \<le> 1" using norm3[OF assms] zero_le_power2[of "n t $ 1"] zero_le_power2[of "n t $ 2"]
    by linarith
  have "n t $ 3 \<le> 1" by (rule power2_le_imp_le[of "n t $ 3" 1]) (use h in simp_all)
  moreover have "- (n t $ 3) \<le> 1" by (rule power2_le_imp_le[of "- (n t $ 3)" 1]) (use h in simp_all)
  ultimately show ?thesis by simp
qed

lemma z_cont: "continuous_on {0..T} (\<lambda>t. n t $ 3)"
  by (intro continuous_intros cont)

lemma z_deriv:
  assumes t: "0 < t" "t < T"
  shows "((\<lambda>x. n x $ 3) has_real_derivative n' t $ 3) (at t)"
proof -
  have "((\<lambda>x. inner (n x) (axis 3 (1::real))) has_real_derivative inner (n' t) (axis 3 (1::real))) (at t)"
    by (rule u_derivative[OF t])
  then show ?thesis by (simp add: inner_axis)
qed

lemma z_speed:
  assumes t: "0 < t" "t < T"
  shows "(n' t $ 3)\<^sup>2 \<le> nu\<^sup>2 * (1 - (n t $ 3)\<^sup>2)"
proof -
  have e1: "norm (axis 3 (1::real) :: real^3) = 1" by simp
  have "(inner (n' t) (axis 3 (1::real)))\<^sup>2 \<le> nu\<^sup>2 * (1 - (inner (n t) (axis 3 (1::real)))\<^sup>2)"
    by (rule u_square_bound[OF t e1])
  then show ?thesis by (simp add: inner_axis)
qed

lemma theta_speed:
  assumes t: "0 < t" "t < T" and zi: "- 1 < n t $ 3" "n t $ 3 < 1"
  shows "inverse (- sqrt (1 - (n t $ 3)\<^sup>2)) * n' t $ 3 \<le> nu"
proof -
  have pos: "0 < 1 - (n t $ 3)\<^sup>2"
  proof -
    have "0 < (1 - n t $ 3) * (1 + n t $ 3)" using zi by (intro mult_pos_pos; linarith)
    then show ?thesis by (simp add: power2_eq_square algebra_simps)
  qed
  have sp: "0 < sqrt (1 - (n t $ 3)\<^sup>2)" using pos by simp
  have sq: "(- (n' t $ 3))\<^sup>2 \<le> (nu * sqrt (1 - (n t $ 3)\<^sup>2))\<^sup>2"
    using z_speed[OF t] pos by (simp add: power_mult_distrib)
  have nn: "0 \<le> nu * sqrt (1 - (n t $ 3)\<^sup>2)" using sp nu_pos by simp
  have h1: "- (n' t $ 3) \<le> nu * sqrt (1 - (n t $ 3)\<^sup>2)" by (rule power2_le_imp_le[OF sq nn])
  have eq: "inverse (- sqrt (1 - (n t $ 3)\<^sup>2)) * n' t $ 3 = - (n' t $ 3) / sqrt (1 - (n t $ 3)\<^sup>2)"
    by (simp add: inverse_eq_divide divide_minus_left)
  show ?thesis unfolding eq by (subst pos_divide_le_eq[OF sp]) (rule h1)
qed

lemma pole_free_eps:
  fixes l eps :: real
  assumes l: "0 < l" and eps: "0 < eps"
  shows "l * pi / 2 + pi / (2 * l) - 2 \<le>
    nu * integral {0..T} (\<lambda>t. expo l (n t $ 3)) + nu * eps * T"
proof -
  have l_ne: "l \<noteq> 0" using l by simp
  define z where "z = (\<lambda>t. n t $ 3)"
  define E where "E = (\<lambda>t. expo l (z t))"
  have zc: "continuous_on {0..T} z" unfolding z_def by (rule z_cont)
  have zr: "- 1 \<le> z t \<and> z t \<le> 1" if "0 \<le> t" "t \<le> T" for t
    unfolding z_def using z_range[OF that] by simp
  have z0: "z 0 = 1" and zT: "z T = - 1" using north south unfolding z_def by (simp_all add: axis_def)
  have cE: "continuous_on {0..T} E" unfolding E_def expo_def
    by (intro continuous_intros zc) (simp_all add: l_ne)
  have E0: "0 \<le> E t" if "0 \<le> t" "t \<le> T" for t
    unfolding E_def using expo_nonneg[OF l] zr[OF that] by simp
  have intE: "E integrable_on {0..T}" by (rule integrable_continuous_real[OF cE])
  define Fi where "Fi = (\<lambda>t. integral {0..t} E)"
  have Fc: "continuous_on {0..T} Fi" unfolding Fi_def by (rule indefinite_integral_continuous_1[OF intE])
  have Fnn: "0 \<le> Fi t" if tt: "0 \<le> t" "t \<le> T" for t
  proof -
    have sub: "E integrable_on {0..t}" by (rule integrable_on_subinterval[OF intE]) (use tt in auto)
    have hh: "(E has_integral Fi t) {0..t}" unfolding Fi_def by (rule integrable_integral[OF sub])
    have nn: "0 \<le> E x" if "x \<in> {0..t}" for x using E0[of x] that tt(2) by auto
    show ?thesis by (rule has_integral_nonneg[OF hh]) (use nn in auto)
  qed
  define S where "S = {t \<in> {0..T}. z t = - 1}"
  have Scl: "closed S"
  proof -
    have cv: "\<forall>B. closed B \<longrightarrow> closed (z -` B \<inter> {0..T})"
      by (rule iffD1[OF continuous_on_closed_vimage[OF closed_atLeastAtMost[of 0 T]] zc])
    have "closed (z -` {- 1} \<inter> {0..T})" using cv closed_singleton by blast
    moreover have "S = z -` {- 1} \<inter> {0..T}" by (auto simp: S_def)
    ultimately show ?thesis by simp
  qed
  have TS: "T \<in> S" using zT T_pos unfolding S_def by simp
  have Sne: "S \<noteq> {}" using TS by auto
  have Sbdd: "bdd_below S" by (auto simp: S_def intro!: bdd_belowI[of _ 0])
  define tau where "tau = Inf S"
  have tauS: "tau \<in> S" unfolding tau_def by (rule closed_contains_Inf[OF Sne Sbdd Scl])
  then have tau0: "0 \<le> tau" and tauT: "tau \<le> T" and ztau: "z tau = - 1" by (auto simp: S_def)
  have before: "z x \<noteq> - 1" if "0 \<le> x" "x < tau" for x
  proof
    assume "z x = - 1"
    then have "x \<in> S" using that tauT unfolding S_def by auto
    then have "tau \<le> x" unfolding tau_def by (intro cInf_lower Sbdd)
    then show False using that(2) by simp
  qed
  define thp where "thp = (\<lambda>x. inverse (- sqrt (1 - (z x)\<^sup>2)) * n' x $ 3)"
  define D where "D = (\<lambda>t. expo_prim l (arccos (z t)) - nu * Fi t - nu * eps * t)"
  define D' where "D' = (\<lambda>x. E x * thp x - nu * E x - nu * eps)"
  have c1: "continuous_on {0..T} (\<lambda>t. arccos (z t))" using zc zr by (intro continuous_intros) auto
  have cG: "continuous_on {0..T} (\<lambda>t. expo_prim l (arccos (z t)))"
    unfolding expo_prim_def by (intro continuous_intros c1) (simp_all add: l_ne)
  have cD: "continuous_on {0..tau} D"
  proof -
    have "continuous_on {0..T} D" unfolding D_def by (intro continuous_intros cG Fc)
    then show ?thesis by (rule continuous_on_subset) (use tauT in auto)
  qed
  have D0: "D 0 \<le> 0" unfolding D_def using z0 by (simp add: Fi_def expo_prim_zero)
  have step: "(D has_real_derivative D' x) (at x) \<and> D' x < 0" if xx: "0 < x" "x < tau" "0 < D x" for x
  proof -
    have xT: "x < T" using xx(2) tauT by linarith
    have z1: "z x \<noteq> 1"
    proof
      assume h: "z x = 1"
      have a: "0 \<le> nu * Fi x" using nu_pos Fnn[of x] xx(1) xT by (intro mult_nonneg_nonneg) auto
      have b: "0 \<le> nu * eps * x" using nu_pos eps xx(1) by (intro mult_nonneg_nonneg) auto
      have "D x = - (nu * Fi x) - nu * eps * x" unfolding D_def using h by (simp add: expo_prim_zero)
      then show False using a b xx(3) by linarith
    qed
    have z2: "z x \<noteq> - 1" by (rule before) (use xx(1,2) in auto)
    have zrx: "- 1 \<le> z x" "z x \<le> 1" using zr[of x] xx(1) xT by auto
    have zi: "- 1 < z x" "z x < 1" using zrx z1 z2 by auto
    have dz: "(z has_real_derivative n' x $ 3) (at x)" unfolding z_def by (rule z_deriv[OF xx(1) xT])
    have dth: "((\<lambda>t. arccos (z t)) has_real_derivative thp x) (at x)"
      using DERIV_chain2[OF DERIV_arccos[OF zi(1) zi(2)] dz] unfolding thp_def .
    have dG0: "((\<lambda>t. expo_prim l (arccos (z t))) has_real_derivative
        expo_th l (arccos (z x)) * thp x) (at x)"
      by (rule DERIV_chain2[OF expo_prim_deriv[OF l] dth])
    have eth: "expo_th l (arccos (z x)) = E x" unfolding E_def by (rule expo_th_arccos[OF zrx])
    have dG: "((\<lambda>t. expo_prim l (arccos (z t))) has_real_derivative E x * thp x) (at x)"
      using dG0 eth by simp
    have dF: "(Fi has_real_derivative E x) (at x)" unfolding Fi_def by (rule deriv_indef[OF cE xx(1) xT])
    have dF2: "((\<lambda>t. nu * Fi t) has_real_derivative nu * E x) (at x)" by (rule DERIV_cmult[OF dF])
    have d4: "((\<lambda>t. nu * eps * t) has_real_derivative nu * eps) (at x)"
      by (rule derivative_eq_intros refl | simp)+
    have "((\<lambda>t. expo_prim l (arccos (z t)) - nu * Fi t - nu * eps * t) has_real_derivative
        E x * thp x - nu * E x - nu * eps) (at x)"
      by (rule DERIV_diff[OF DERIV_diff[OF dG dF2] d4])
    then have dD: "(D has_real_derivative D' x) (at x)" unfolding D_def D'_def by simp
    have bd: "thp x \<le> nu" unfolding thp_def z_def by (rule theta_speed[OF xx(1) xT]) (use zi in \<open>simp_all add: z_def\<close>)
    have Ex: "0 \<le> E x" by (rule E0) (use xx(1) xT in auto)
    have h: "E x * thp x \<le> nu * E x" using Ex bd mult_left_mono[OF bd Ex] by (simp add: mult.commute)
    have pe: "0 < nu * eps" using nu_pos eps by (rule mult_pos_pos)
    then have "D' x < 0" unfolding D'_def using h by linarith
    then show ?thesis using dD by simp
  qed
  have Dle: "\<forall>x\<in>{0..tau}. D x \<le> 0" by (rule barrier[OF tau0 cD D0 step])
  then have Dtau: "D tau \<le> 0" using tau0 by simp
  have "D tau = l * pi / 2 + pi / (2 * l) - 2 - nu * Fi tau - nu * eps * tau"
    unfolding D_def using ztau expo_prim_pi[OF l] by simp
  then have m1: "l * pi / 2 + pi / (2 * l) - 2 \<le> nu * Fi tau + nu * eps * tau" using Dtau by linarith
  have hT: "(E has_integral Fi T) {0..T}" unfolding Fi_def by (rule integrable_integral[OF intE])
  have ht: "(E has_integral Fi tau) {0..tau}" unfolding Fi_def
    by (rule integrable_integral[OF integrable_on_subinterval[OF intE]]) (use tau0 tauT in auto)
  have FiT: "Fi tau \<le> Fi T"
    by (rule has_integral_subset_le[OF _ ht hT]) (use tauT E0 in \<open>auto simp: atLeastAtMost_iff\<close>)
  have "nu * Fi tau \<le> nu * Fi T" using FiT nu_pos by (intro mult_left_mono) auto
  moreover have "nu * eps * tau \<le> nu * eps * T" using tauT nu_pos eps by (intro mult_left_mono) auto
  ultimately show ?thesis using m1 unfolding Fi_def E_def z_def by linarith
qed

theorem pole_free_exposure:
  fixes l :: real
  assumes "0 < l"
  shows "l * pi / 2 + pi / (2 * l) - 2 \<le> nu * integral {0..T} (\<lambda>t. expo l (n t $ 3))"
proof -
  have "l * pi / 2 + pi / (2 * l) - 2 \<le> nu * integral {0..T} (\<lambda>t. expo l (n t $ 3)) + e" if e: "0 < e" for e
  proof -
    define eps where "eps = e / (nu * T)"
    have eps: "0 < eps" unfolding eps_def using e nu_pos T_pos by simp
    have "nu * eps * T = e" unfolding eps_def using nu_pos T_pos by (simp add: field_simps)
    then show ?thesis using pole_free_eps[OF assms eps] by simp
  qed
  then show ?thesis by (rule field_le_epsilon)
qed

theorem exposure_lambda:
  fixes l :: real
  assumes l: "0 < l"
  shows "integral {0..T} (\<lambda>t. sqrt ((n t $ 1)\<^sup>2 + (n t $ 2)\<^sup>2)) - 2 / nu \<le>
    l * (integral {0..T} (\<lambda>t. (1 + n t $ 3) / 2) - pi / (2 * nu)) +
      (integral {0..T} (\<lambda>t. (1 - n t $ 3) / 2) - pi / (2 * nu)) / l"
proof -
  have l_ne: "l \<noteq> 0" using l by simp
  have nu0: "nu \<noteq> 0" using nu_pos by simp
  define a1 where "a1 = (\<lambda>t. (1 + n t $ 3) / 2)"
  define a2 where "a2 = (\<lambda>t. (1 - n t $ 3) / 2)"
  define s where "s = (\<lambda>t. sqrt ((n t $ 1)\<^sup>2 + (n t $ 2)\<^sup>2))"
  define A where "A = integral {0..T} a1"
  define B where "B = integral {0..T} a2"
  define Q where "Q = integral {0..T} s"
  have ca1: "continuous_on {0..T} a1" unfolding a1_def by (intro continuous_intros cont; simp)
  have ca2: "continuous_on {0..T} a2" unfolding a2_def by (intro continuous_intros cont; simp)
  have cs: "continuous_on {0..T} s" unfolding s_def by (intro continuous_intros cont)
  have hA: "(a1 has_integral A) {0..T}" unfolding A_def by (intro integrable_integral integrable_continuous_real ca1)
  have hB: "(a2 has_integral B) {0..T}" unfolding B_def by (intro integrable_integral integrable_continuous_real ca2)
  have hQ: "(s has_integral Q) {0..T}" unfolding Q_def by (intro integrable_integral integrable_continuous_real cs)
  have sz: "s t = sqrt (1 - (n t $ 3)\<^sup>2)" if "0 \<le> t" "t \<le> T" for t
  proof -
    have "(n t $ 1)\<^sup>2 + (n t $ 2)\<^sup>2 = 1 - (n t $ 3)\<^sup>2" using norm3[OF that] by linarith
    then show ?thesis unfolding s_def by simp
  qed
  have eqE: "expo l (n t $ 3) = l * a1 t + (1 / l) * a2 t - s t" if "0 \<le> t" "t \<le> T" for t
    unfolding expo_def a1_def a2_def using sz[OF that] by (simp add: field_simps l_ne)
  have hE0: "((\<lambda>t. l * a1 t + (1 / l) * a2 t - s t) has_integral l * A + (1 / l) * B - Q) {0..T}"
  proof -
    have "((\<lambda>t. l *\<^sub>R a1 t + (1 / l) *\<^sub>R a2 t - s t) has_integral
        l *\<^sub>R A + (1 / l) *\<^sub>R B - Q) {0..T}"
      by (rule has_integral_diff[OF has_integral_add[OF has_integral_cmul[OF hA] has_integral_cmul[OF hB]] hQ])
    then show ?thesis by (simp add: real_scaleR_def)
  qed
  have hE: "((\<lambda>t. expo l (n t $ 3)) has_integral l * A + (1 / l) * B - Q) {0..T}"
    by (rule has_integral_eq[OF _ hE0]) (use eqE in auto)
  have K: "l * pi / 2 + pi / (2 * l) - 2 \<le> nu * (l * A + (1 / l) * B - Q)"
    using pole_free_exposure[OF l] integral_unique[OF hE] by simp
  have id: "nu * (l * (A - pi / (2 * nu)) + (B - pi / (2 * nu)) / l - (Q - 2 / nu))
      = nu * (l * A + (1 / l) * B - Q) - (l * pi / 2 + pi / (2 * l) - 2)"
    by (simp add: field_simps l_ne nu0)
  have W0: "0 \<le> nu * (l * (A - pi / (2 * nu)) + (B - pi / (2 * nu)) / l - (Q - 2 / nu))"
    using id K by linarith
  have "0 \<le> l * (A - pi / (2 * nu)) + (B - pi / (2 * nu)) / l - (Q - 2 / nu)"
    using W0 nu_pos by (simp add: zero_le_mult_iff)
  then have "Q - 2 / nu \<le> l * (A - pi / (2 * nu)) + (B - pi / (2 * nu)) / l" by simp
  then show ?thesis unfolding A_def B_def Q_def a1_def a2_def s_def .
qed

section \<open>C. The window around the equatorial crossing\<close>

lemma crossing_window:
  assumes ts: "0 \<le> ts" "ts \<le> T" and nz0: "n ts $ 3 = 0"
  shows "pi / 2 \<le> nu * ts" and "pi / 2 \<le> nu * (T - ts)"
proof -
  show "pi / 2 \<le> nu * ts"
  proof (rule ccontr)
    assume "\<not> pi / 2 \<le> nu * ts"
    then have lt: "nu * ts < pi / 2" by simp
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
  show "pi / 2 \<le> nu * (T - ts)"
  proof (rule ccontr)
    assume "\<not> pi / 2 \<le> nu * (T - ts)"
    then have lt: "nu * (T - ts) < pi / 2" by simp
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
qed

lemma window_integral:
  assumes ts: "0 \<le> ts" "ts \<le> T" and nz0: "n ts $ 3 = 0"
  shows "2 / nu \<le> integral {0..T} (\<lambda>t. (inner (n t) (n ts) + \<bar>inner (n t) (n ts)\<bar>) / 2)"
proof -
  have nu: "nu \<noteq> 0" using nu_pos by simp
  define xp where "xp = (\<lambda>t. (inner (n t) (n ts) + \<bar>inner (n t) (n ts)\<bar>) / 2)"
  define w1 where "w1 = ts - pi / (2 * nu)"
  define w2 where "w2 = ts + pi / (2 * nu)"
  have cw1: "pi / 2 \<le> nu * ts" and cw2: "pi / 2 \<le> nu * (T - ts)" using crossing_window[OF ts nz0] by auto
  have pn: "0 < pi / (2 * nu)" using nu_pos by simp
  have np: "nu * (pi / (2 * nu)) = pi / 2" using nu by (simp add: field_simps)
  have w10: "0 \<le> w1"
  proof -
    have "nu * (pi / (2 * nu)) \<le> nu * ts" using np cw1 by simp
    then have "pi / (2 * nu) \<le> ts" using nu_pos by (rule mult_left_le_imp_le)
    then show ?thesis unfolding w1_def by simp
  qed
  have w2T: "w2 \<le> T"
  proof -
    have "nu * (pi / (2 * nu)) \<le> nu * (T - ts)" using np cw2 by simp
    then have "pi / (2 * nu) \<le> T - ts" using nu_pos by (rule mult_left_le_imp_le)
    then show ?thesis unfolding w2_def by simp
  qed
  have w12: "w1 \<le> w2" unfolding w1_def w2_def using pn by simp
  have e2: "nu * (w2 - ts) = pi / 2" unfolding w2_def using np by simp
  have e1: "nu * (w1 - ts) = - (pi / 2)" unfolding w1_def using np by (simp add: algebra_simps)
  have cxp: "continuous_on {0..T} xp" unfolding xp_def by (intro continuous_intros cont; simp)
  have intT: "xp integrable_on {0..T}" by (rule integrable_continuous_real[OF cxp])
  have xp0: "0 \<le> xp t" for t
  proof -
    have "- inner (n t) (n ts) \<le> \<bar>inner (n t) (n ts)\<bar>" by (rule abs_ge_minus_self)
    then have "0 \<le> inner (n t) (n ts) + \<bar>inner (n t) (n ts)\<bar>" by linarith
    then show ?thesis unfolding xp_def by (simp add: zero_le_divide_iff)
  qed
  have hc0: "((\<lambda>t. cos (nu * (t - ts))) has_integral
      (sin (nu * (w2 - ts)) / nu - sin (nu * (w1 - ts)) / nu)) {w1..w2}"
  proof (rule fundamental_theorem_of_calculus)
    show "w1 \<le> w2" by fact
    fix x :: real
    assume "x \<in> {w1..w2}"
    have "((\<lambda>t. sin (nu * (t - ts)) / nu) has_real_derivative cos (nu * (x - ts))) (at x)"
      by (rule derivative_eq_intros refl | simp add: nu)+
    then have hd: "((\<lambda>t. sin (nu * (t - ts)) / nu) has_vector_derivative cos (nu * (x - ts))) (at x)"
      by (simp add: has_real_derivative_iff_has_vector_derivative)
    show "((\<lambda>t. sin (nu * (t - ts)) / nu) has_vector_derivative cos (nu * (x - ts))) (at x within {w1..w2})"
      by (rule has_vector_derivative_at_within[OF hd])
  qed
  have hc: "((\<lambda>t. cos (nu * (t - ts))) has_integral 2 / nu) {w1..w2}"
  proof -
    have "sin (nu * (w2 - ts)) / nu - sin (nu * (w1 - ts)) / nu = 2 / nu"
      unfolding e1 e2 by (simp add: field_simps)
    then show ?thesis using hc0 by simp
  qed
  have xge: "cos (nu * (t - ts)) \<le> xp t" if tw: "t \<in> {w1..w2}" for t
  proof -
    have tt: "0 \<le> t" "t \<le> T" using w10 w2T tw by auto
    have d1: "t - ts \<le> pi / (2 * nu)" and d2: "- (pi / (2 * nu)) \<le> t - ts"
      using tw unfolding w1_def w2_def by auto
    have "\<bar>t - ts\<bar> \<le> pi / (2 * nu)" using d1 d2 by (simp add: abs_le_iff)
    then have "nu * \<bar>t - ts\<bar> \<le> nu * (pi / (2 * nu))" using nu_pos by (intro mult_left_mono) auto
    then have bd: "nu * \<bar>t - ts\<bar> \<le> pi" using np pi_gt_zero by linarith
    have "cos (nu * \<bar>t - ts\<bar>) \<le> inner (n t) (n ts)"
      by (rule angle_bound_gen[OF _ _ _ _ bd]) (use tt ts in auto)
    moreover have "cos (nu * \<bar>t - ts\<bar>) = cos (nu * (t - ts))"
    proof -
      have "nu * \<bar>t - ts\<bar> = \<bar>nu * (t - ts)\<bar>" using nu_pos by (simp add: abs_mult)
      then show ?thesis by simp
    qed
    ultimately have "cos (nu * (t - ts)) \<le> inner (n t) (n ts)" by simp
    moreover have "inner (n t) (n ts) \<le> xp t"
    proof -
      have "2 * xp t = inner (n t) (n ts) + \<bar>inner (n t) (n ts)\<bar>" unfolding xp_def by simp
      then show ?thesis using abs_ge_self[of "inner (n t) (n ts)"] by linarith
    qed
    ultimately show ?thesis by simp
  qed
  have sub1: "xp integrable_on {w1..w2}"
    by (rule integrable_on_subinterval[OF intT]) (use w10 w2T in auto)
  have hxp1: "(xp has_integral integral {w1..w2} xp) {w1..w2}" by (rule integrable_integral[OF sub1])
  have hxpT: "(xp has_integral integral {0..T} xp) {0..T}" by (rule integrable_integral[OF intT])
  have i1: "2 / nu \<le> integral {w1..w2} xp" by (rule has_integral_le[OF hc hxp1]) (use xge in auto)
  have i2: "integral {w1..w2} xp \<le> integral {0..T} xp"
    by (rule has_integral_subset_le[OF _ hxp1 hxpT]) (use w10 w2T xp0 in auto)
  show ?thesis using i1 i2 unfolding xp_def by linarith
qed

section \<open>D. The disk inequality\<close>

theorem disk_main:
  shows "integral {0..T} (\<lambda>t. sqrt ((n t $ 1)\<^sup>2 + (n t $ 2)\<^sup>2)) - 2 / nu \<le>
      2 * sqrt ((integral {0..T} (\<lambda>t. (1 + n t $ 3) / 2) - pi / (2 * nu)) *
                (integral {0..T} (\<lambda>t. (1 - n t $ 3) / 2) - pi / (2 * nu)))"
    and "pi / (2 * nu) \<le> integral {0..T} (\<lambda>t. (1 + n t $ 3) / 2)"
    and "pi / (2 * nu) \<le> integral {0..T} (\<lambda>t. (1 - n t $ 3) / 2)"
    and "(sqrt ((integral {0..T} (\<lambda>t. n t $ 1))\<^sup>2 + (integral {0..T} (\<lambda>t. n t $ 2))\<^sup>2) / 2 - 1 / nu)\<^sup>2
      \<le> (integral {0..T} (\<lambda>t. (1 + n t $ 3) / 2) - pi / (2 * nu)) *
         (integral {0..T} (\<lambda>t. (1 - n t $ 3) / 2) - pi / (2 * nu))"
proof -
  obtain ts where ts: "0 \<le> ts" "ts \<le> T" and nz0: "n ts $ 3 = 0" using crossing by blast
  define e1 where "e1 = n ts $ 1"
  define e2 where "e2 = n ts $ 2"
  have e12: "e1\<^sup>2 + e2\<^sup>2 = 1" using norm3[OF ts] nz0 by (simp add: e1_def e2_def)
  define x where "x = (\<lambda>t. n t $ 1 * e1 + n t $ 2 * e2)"
  have xin: "x t = inner (n t) (n ts)" for t
    using nz0 by (simp add: x_def e1_def e2_def inner_vec_def sum_3 mult.commute)
  define s where "s = (\<lambda>t. sqrt ((n t $ 1)\<^sup>2 + (n t $ 2)\<^sup>2))"
  define a1 where "a1 = (\<lambda>t. (1 + n t $ 3) / 2)"
  define a2 where "a2 = (\<lambda>t. (1 - n t $ 3) / 2)"
  define M1 where "M1 = integral {0..T} (\<lambda>t. n t $ 1)"
  define M2 where "M2 = integral {0..T} (\<lambda>t. n t $ 2)"
  define A where "A = integral {0..T} a1"
  define B where "B = integral {0..T} a2"
  define Q where "Q = integral {0..T} s"
  define R where "R = sqrt (M1\<^sup>2 + M2\<^sup>2)"
  define X where "X = A - pi / (2 * nu)"
  define Y where "Y = B - pi / (2 * nu)"
  have c1: "continuous_on {0..T} (\<lambda>t. n t $ 1)" and c2: "continuous_on {0..T} (\<lambda>t. n t $ 2)"
    by (intro continuous_intros cont)+
  have ca1: "continuous_on {0..T} a1" unfolding a1_def by (intro continuous_intros cont; simp)
  have ca2: "continuous_on {0..T} a2" unfolding a2_def by (intro continuous_intros cont; simp)
  have cs: "continuous_on {0..T} s" unfolding s_def by (intro continuous_intros cont)
  have h1: "((\<lambda>t. n t $ 1) has_integral M1) {0..T}" unfolding M1_def
    by (intro integrable_integral integrable_continuous_real c1)
  have h2: "((\<lambda>t. n t $ 2) has_integral M2) {0..T}" unfolding M2_def
    by (intro integrable_integral integrable_continuous_real c2)
  have hQ: "(s has_integral Q) {0..T}" unfolding Q_def by (intro integrable_integral integrable_continuous_real cs)
  have lin: "((\<lambda>t. n t $ 1 * u1 + n t $ 2 * u2) has_integral u1 * M1 + u2 * M2) {0..T}" for u1 u2
  proof (rule has_integral_add)
    show "((\<lambda>t. n t $ 1 * u1) has_integral u1 * M1) {0..T}"
      using has_integral_mult_right[OF h1, of u1] by (simp add: mult.commute)
    show "((\<lambda>t. n t $ 2 * u2) has_integral u2 * M2) {0..T}"
      using has_integral_mult_right[OF h2, of u2] by (simp add: mult.commute)
  qed
  have sge: "\<bar>n t $ 1 * u1 + n t $ 2 * u2\<bar> \<le> s t" if "u1\<^sup>2 + u2\<^sup>2 = 1" for t u1 u2
    unfolding s_def by (rule cs_abs[OF that])
  have s0: "0 \<le> s t" for t unfolding s_def by simp
  have dirle: "u1 * M1 + u2 * M2 \<le> Q" if u: "u1\<^sup>2 + u2\<^sup>2 = 1" for u1 u2
  proof -
    have pw: "n t $ 1 * u1 + n t $ 2 * u2 \<le> s t" for t
      using sge[OF u, of t] abs_ge_self[of "n t $ 1 * u1 + n t $ 2 * u2"] by linarith
    show ?thesis by (rule has_integral_le[OF lin hQ]) (use pw in auto)
  qed
  have R0: "0 \<le> R" unfolding R_def by simp
  have Q0: "0 \<le> Q" by (rule has_integral_nonneg[OF hQ]) (use s0 in auto)
  have R2: "R * R = M1 * M1 + M2 * M2"
  proof -
    have "R\<^sup>2 = M1\<^sup>2 + M2\<^sup>2" unfolding R_def by (rule real_sqrt_pow2) simp
    then show ?thesis by (simp add: power2_eq_square)
  qed
  have RleQ: "R \<le> Q"
  proof (cases "R = 0")
    case True
    then show ?thesis using Q0 by simp
  next
    case False
    then have Rp: "0 < R" using R0 by simp
    define u1 where "u1 = M1 / R"
    define u2 where "u2 = M2 / R"
    have RR: "R * R \<noteq> 0" using Rp by simp
    have u12: "u1\<^sup>2 + u2\<^sup>2 = 1"
    proof -
      have "u1\<^sup>2 + u2\<^sup>2 = (M1 * M1 + M2 * M2) / (R * R)"
        unfolding u1_def u2_def by (simp add: power2_eq_square add_divide_distrib)
      also have "\<dots> = (R * R) / (R * R)" using R2 by simp
      also have "\<dots> = 1" using RR by simp
      finally show ?thesis .
    qed
    have "u1 * M1 + u2 * M2 = R" unfolding u1_def u2_def using Rp R2 by (simp add: field_simps)
    then show ?thesis using dirle[OF u12] by simp
  qed
  have ub: "e1 * M1 + e2 * M2 \<le> R"
  proof -
    have "\<bar>M1 * e1 + M2 * e2\<bar> \<le> sqrt (M1\<^sup>2 + M2\<^sup>2)" by (rule cs_abs[OF e12])
    moreover have "M1 * e1 + M2 * e2 \<le> \<bar>M1 * e1 + M2 * e2\<bar>" by (rule abs_ge_self)
    ultimately show ?thesis unfolding R_def by (simp add: mult.commute)
  qed
  define xp where "xp = (\<lambda>t. (x t + \<bar>x t\<bar>) / 2)"
  have cxp: "continuous_on {0..T} xp" unfolding xp_def x_def by (intro continuous_intros cont; simp)
  have hxp: "(xp has_integral integral {0..T} xp) {0..T}"
    by (intro integrable_integral integrable_continuous_real cxp)
  have win: "2 / nu \<le> integral {0..T} xp" unfolding xp_def using window_integral[OF ts nz0] by (simp add: xin)
  have hs: "((\<lambda>t. s t + x t) has_integral Q + (e1 * M1 + e2 * M2)) {0..T}"
    unfolding x_def by (rule has_integral_add[OF hQ lin])
  have h2x: "((\<lambda>t. 2 * xp t) has_integral 2 * integral {0..T} xp) {0..T}"
  proof -
    have "((\<lambda>t. 2 *\<^sub>R xp t) has_integral 2 *\<^sub>R integral {0..T} xp) {0..T}" by (rule has_integral_cmul[OF hxp])
    then show ?thesis by (simp add: real_scaleR_def)
  qed
  have pw2: "2 * xp t \<le> s t + x t" if "0 \<le> t" "t \<le> T" for t
  proof -
    have "\<bar>x t\<bar> \<le> s t" unfolding x_def by (rule sge[OF e12])
    moreover have "2 * xp t = x t + \<bar>x t\<bar>" unfolding xp_def by simp
    ultimately show ?thesis by linarith
  qed
  have i1: "2 * integral {0..T} xp \<le> Q + (e1 * M1 + e2 * M2)"
    by (rule has_integral_le[OF h2x hs]) (use pw2 in auto)
  have four: "4 / nu \<le> Q + R"
  proof -
    have "2 * (2 / nu) \<le> 2 * integral {0..T} xp" using win by simp
    then have "2 * (2 / nu) \<le> Q + R" using i1 ub by linarith
    then show ?thesis by simp
  qed
  have absf: "\<bar>2 * (R / 2) - 2 / nu\<bar> \<le> Q - 2 / nu"
  proof -
    have f1: "2 * (R / 2) - 2 / nu \<le> Q - 2 / nu" using RleQ by simp
    have f2: "- (2 * (R / 2) - 2 / nu) \<le> Q - 2 / nu"
    proof -
      have "4 / nu = 2 / nu + 2 / nu" by simp
      then show ?thesis using four by linarith
    qed
    show ?thesis using f1 f2 by (simp add: abs_le_iff)
  qed
  have Qnn: "0 \<le> Q - 2 / nu" using absf abs_ge_zero[of "2 * (R / 2) - 2 / nu"] by linarith
  have key: "Q - 2 / nu \<le> l * X + Y / l" if l: "0 < l" for l
    unfolding X_def Y_def A_def B_def Q_def a1_def a2_def s_def by (rule exposure_lambda[OF l])
  have keyY: "Q - 2 / nu \<le> l * Y + X / l" if l: "0 < l" for l
  proof -
    have l1: "0 < 1 / l" using l by simp
    have k: "Q - 2 / nu \<le> (1 / l) * X + Y / (1 / l)" by (rule key[OF l1])
    have "(1 / l) * X + Y / (1 / l) = l * Y + X / l" using l by (simp add: field_simps)
    then show ?thesis using k by (simp add: mult.commute)
  qed
  have X0: "0 \<le> X" by (rule lam_nonneg[OF Qnn key])
  have Y0: "0 \<le> Y" by (rule lam_nonneg[OF Qnn keyY])
  have Qex: "Q - 2 / nu \<le> 2 * sqrt (X * Y)" by (rule lambda_min[OF X0 Y0 key])
  have nuh: "0 < nu / 2" using nu_pos by simp
  have nu2: "nu = 2 * (nu / 2)" by simp
  have z02: "1 / nu = 1 / (2 * (nu / 2))" by simp
  have disk: "(R / 2 - 1 / nu)\<^sup>2 \<le> X * Y"
    by (rule disk_from_two_bounds[OF nuh nu2 z02 absf Qex X0 Y0])
  show "integral {0..T} (\<lambda>t. sqrt ((n t $ 1)\<^sup>2 + (n t $ 2)\<^sup>2)) - 2 / nu \<le>
      2 * sqrt ((integral {0..T} (\<lambda>t. (1 + n t $ 3) / 2) - pi / (2 * nu)) *
                (integral {0..T} (\<lambda>t. (1 - n t $ 3) / 2) - pi / (2 * nu)))"
    using Qex unfolding X_def Y_def A_def B_def Q_def a1_def a2_def s_def .
  show "pi / (2 * nu) \<le> integral {0..T} (\<lambda>t. (1 + n t $ 3) / 2)"
    using X0 unfolding X_def A_def a1_def by simp
  show "pi / (2 * nu) \<le> integral {0..T} (\<lambda>t. (1 - n t $ 3) / 2)"
    using Y0 unfolding Y_def B_def a2_def by simp
  show "(sqrt ((integral {0..T} (\<lambda>t. n t $ 1))\<^sup>2 + (integral {0..T} (\<lambda>t. n t $ 2))\<^sup>2) / 2 - 1 / nu)\<^sup>2
      \<le> (integral {0..T} (\<lambda>t. (1 + n t $ 3) / 2) - pi / (2 * nu)) *
         (integral {0..T} (\<lambda>t. (1 - n t $ 3) / 2) - pi / (2 * nu))"
    using disk unfolding R_def M1_def M2_def X_def Y_def A_def B_def a1_def a2_def .
qed

end

section \<open>E. Statements\<close>

theorem exposure_bound_general:
  assumes "sphere_curve n n' T nu"
  shows "integral {0..T} (\<lambda>t. sqrt ((n t $ 1)\<^sup>2 + (n t $ 2)\<^sup>2)) - 2 / nu \<le>
    2 * sqrt ((integral {0..T} (\<lambda>t. (1 + n t $ 3) / 2) - pi / (2 * nu)) *
              (integral {0..T} (\<lambda>t. (1 - n t $ 3) / 2) - pi / (2 * nu)))"
proof -
  interpret sphere_curve n n' T nu by fact
  show ?thesis by (rule disk_main)
qed

theorem robust_disk:
  assumes "sphere_curve n n' T nu"
  shows "pi / (2 * nu) \<le> integral {0..T} (\<lambda>t. (1 + n t $ 3) / 2)"
    and "pi / (2 * nu) \<le> integral {0..T} (\<lambda>t. (1 - n t $ 3) / 2)"
    and "(sqrt ((integral {0..T} (\<lambda>t. n t $ 1))\<^sup>2 + (integral {0..T} (\<lambda>t. n t $ 2))\<^sup>2) / 2 - 1 / nu)\<^sup>2
      \<le> (integral {0..T} (\<lambda>t. (1 + n t $ 3) / 2) - pi / (2 * nu)) *
         (integral {0..T} (\<lambda>t. (1 - n t $ 3) / 2) - pi / (2 * nu))"
proof -
  interpret sphere_curve n n' T nu by fact
  show "pi / (2 * nu) \<le> integral {0..T} (\<lambda>t. (1 + n t $ 3) / 2)" by (rule disk_main)
  show "pi / (2 * nu) \<le> integral {0..T} (\<lambda>t. (1 - n t $ 3) / 2)" by (rule disk_main)
  show "(sqrt ((integral {0..T} (\<lambda>t. n t $ 1))\<^sup>2 + (integral {0..T} (\<lambda>t. n t $ 2))\<^sup>2) / 2 - 1 / nu)\<^sup>2
      \<le> (integral {0..T} (\<lambda>t. (1 + n t $ 3) / 2) - pi / (2 * nu)) *
         (integral {0..T} (\<lambda>t. (1 - n t $ 3) / 2) - pi / (2 * nu))"
    by (rule disk_main)
qed

theorem robust_disk_G:
  assumes "0 < G" and "sphere_curve n n' T (2 * G)"
  shows "pi / (4 * G) \<le> integral {0..T} (\<lambda>t. (1 + n t $ 3) / 2)"
    and "pi / (4 * G) \<le> integral {0..T} (\<lambda>t. (1 - n t $ 3) / 2)"
    and "(sqrt ((integral {0..T} (\<lambda>t. n t $ 1))\<^sup>2 + (integral {0..T} (\<lambda>t. n t $ 2))\<^sup>2) / 2 - 1 / (2 * G))\<^sup>2
      \<le> (integral {0..T} (\<lambda>t. (1 + n t $ 3) / 2) - pi / (4 * G)) *
         (integral {0..T} (\<lambda>t. (1 - n t $ 3) / 2) - pi / (4 * G))"
proof -
  have e: "pi / (2 * (2 * G)) = pi / (4 * G)" by simp
  show "pi / (4 * G) \<le> integral {0..T} (\<lambda>t. (1 + n t $ 3) / 2)"
    using robust_disk(1)[OF assms(2)] e by simp
  show "pi / (4 * G) \<le> integral {0..T} (\<lambda>t. (1 - n t $ 3) / 2)"
    using robust_disk(2)[OF assms(2)] e by simp
  show "(sqrt ((integral {0..T} (\<lambda>t. n t $ 1))\<^sup>2 + (integral {0..T} (\<lambda>t. n t $ 2))\<^sup>2) / 2 - 1 / (2 * G))\<^sup>2
      \<le> (integral {0..T} (\<lambda>t. (1 + n t $ 3) / 2) - pi / (4 * G)) *
         (integral {0..T} (\<lambda>t. (1 - n t $ 3) / 2) - pi / (4 * G))"
    using robust_disk(3)[OF assms(2)] e by simp
qed

end
