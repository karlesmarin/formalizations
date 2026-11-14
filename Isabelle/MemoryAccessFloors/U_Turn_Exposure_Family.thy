(*  Title:      U_Turn_Exposure_Family.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License: BSD

    From "Robustness to a static offset costs time and exposure" (C. Marín, draft, November 2026):
    the family "turn by pi + phi, wait w, turn back by phi" of the bounded-curvature U-turn.
    Units G = 1/2, z0 = 1, A0 = pi/2; z is the lateral displacement, 0 <= z < 1, d = arccos z.
    The exposures x = A - A0 and y = B - A0 of the member with angle phi are closed in phi, the member
    phi = d is the bang-bang control, the others lie strictly inside the disc xy > (1-z)^2 and strictly
    above the boundary x + y = 2d, and the branch is a curve from the bang-bang (phi = d) to the
    hyperbola xy = (1-z)^2 (phi -> 0+), with x increasing and y decreasing in phi.
*)

theory U_Turn_Exposure_Family
  imports "HOL-Analysis.Analysis"
begin

section \<open>A. The family\<close>

definition fam_w :: "real \<Rightarrow> real \<Rightarrow> real" where
  "fam_w z \<phi> = 2 * (cos \<phi> - z) / sin \<phi>"

definition fam_x :: "real \<Rightarrow> real \<Rightarrow> real" where
  "fam_x z \<phi> = \<phi> - sin \<phi> + fam_w z \<phi> * (1 - cos \<phi>) / 2"

definition fam_y :: "real \<Rightarrow> real \<Rightarrow> real" where
  "fam_y z \<phi> = \<phi> + sin \<phi> + fam_w z \<phi> * (1 + cos \<phi>) / 2"

lemma family_constraint:
  fixes z \<phi> :: real
  assumes "0 < \<phi>" and "\<phi> < pi"
  shows "z = cos \<phi> - fam_w z \<phi> / 2 * sin \<phi>"
proof -
  have "sin \<phi> \<noteq> 0" using sin_gt_zero assms by force
  then show ?thesis unfolding fam_w_def by (simp add: field_simps)
qed

lemma branch_facts:
  fixes z :: real
  assumes "0 \<le> z" and "z < 1"
  shows "0 < arccos z" and "arccos z \<le> pi / 2" and "cos (arccos z) = z"
    and "0 < sin (arccos z)"
proof -
  have c: "cos (arccos z) = z" using assms by (intro cos_arccos) auto
  show "cos (arccos z) = z" by (rule c)
  show "arccos z \<le> pi / 2" using assms by (intro arccos_le_pi2) auto
  have "0 \<le> arccos z" using assms by (intro arccos_lbound) auto
  moreover have "arccos z \<noteq> 0"
  proof
    assume "arccos z = 0"
    then have "z = 1" using c by simp
    then show False using assms by simp
  qed
  ultimately show pos: "0 < arccos z" by simp
  show "0 < sin (arccos z)"
    by (rule sin_gt_zero) (use pos \<open>arccos z \<le> pi / 2\<close> pi_gt_zero in linarith)+
qed

lemma cos_open_range:
  fixes t :: real
  assumes "0 < t" and "t < pi"
  shows "- 1 < cos t" and "cos t < 1"
proof -
  have s: "0 < sin t" using assms by (intro sin_gt_zero)
  have sq: "(sin t)\<^sup>2 = (1 - cos t) * (1 + cos t)" unfolding power2_eq_square using sin_cos_squared_add[of t] by algebra
  have "0 < (sin t)\<^sup>2" using s by (rule zero_less_power)
  then have pos: "0 < (1 - cos t) * (1 + cos t)" using sq by simp
  have a: "cos t \<le> 1" and b: "- 1 \<le> cos t" by simp_all
  show "- 1 < cos t"
  proof (rule ccontr)
    assume "\<not> - 1 < cos t"
    then have "cos t = - 1" using b by simp
    then show False using pos by simp
  qed
  show "cos t < 1"
  proof (rule ccontr)
    assume "\<not> cos t < 1"
    then have "cos t = 1" using a by simp
    then show False using pos by simp
  qed
qed

lemma cos_above_z:
  fixes z t :: real
  assumes "0 \<le> z" and "z < 1" and "0 \<le> t" and "t \<le> arccos z"
  shows "z \<le> cos t"
proof -
  have "cos (arccos z) \<le> cos t"
    using assms branch_facts(2)[OF assms(1,2)] pi_gt_zero by (intro cos_monotone_0_pi_le) linarith+
  then show ?thesis using branch_facts(3)[OF assms(1,2)] by simp
qed

lemma cos_strictly_above_z:
  fixes z t :: real
  assumes "0 \<le> z" and "z < 1" and "0 \<le> t" and "t < arccos z"
  shows "z < cos t"
proof -
  have "cos (arccos z) < cos t"
    using assms branch_facts(2)[OF assms(1,2)] pi_gt_zero by (intro cos_monotone_0_pi) linarith+
  then show ?thesis using branch_facts(3)[OF assms(1,2)] by simp
qed

lemma wait_nonneg:
  fixes z \<phi> :: real
  assumes "0 \<le> z" and "z < 1" and "0 < \<phi>" and "\<phi> \<le> arccos z"
  shows "0 \<le> fam_w z \<phi>"
proof -
  have "0 < sin \<phi>"
    using assms branch_facts(2)[OF assms(1,2)] pi_gt_zero by (intro sin_gt_zero) linarith+
  moreover have "0 \<le> cos \<phi> - z" using cos_above_z[OF assms(1,2) _ assms(4)] assms(3) by simp
  ultimately show ?thesis unfolding fam_w_def by simp
qed

section \<open>B. F1: the member phi = arccos z is the bang-bang\<close>

lemma family_bang_bang:
  fixes z d :: real
  assumes "0 \<le> z" and "z < 1" and "d = arccos z"
  shows "fam_w z d = 0" and "fam_x z d = d - sin d" and "fam_y z d = d + sin d"
    and "fam_x z d + fam_y z d = 2 * d"
proof -
  have "cos d = z" using branch_facts(3)[OF assms(1,2)] assms(3) by simp
  then show w: "fam_w z d = 0" unfolding fam_w_def by simp
  show "fam_x z d = d - sin d" unfolding fam_x_def w by simp
  show "fam_y z d = d + sin d" unfolding fam_y_def w by simp
  show "fam_x z d + fam_y z d = 2 * d" unfolding fam_x_def fam_y_def w by simp
qed

lemma family_x_alt:
  fixes z t :: real
  assumes "0 < t" and "t < pi"
  shows "fam_x z t = t - sin t + (cos t - z) * (sin t / (1 + cos t))"
proof -
  have s: "0 < sin t" using assms by (intro sin_gt_zero)
  have c1: "1 + cos t \<noteq> 0" using cos_open_range[OF assms] by linarith
  have sq: "(sin t)\<^sup>2 = (1 - cos t) * (1 + cos t)"
    unfolding power2_eq_square using sin_cos_squared_add[of t] by algebra
  have su: "sin t * inverse (sin t) = 1" using s by simp
  have cw: "(1 + cos t) * inverse (1 + cos t) = 1" using c1 by simp
  have h2: "(2::real) * inverse 2 = 1" by simp
  show ?thesis unfolding fam_x_def fam_w_def divide_inverse using su cw sq h2 by algebra
qed

lemma family_y_alt:
  fixes z t :: real
  assumes "0 < t" and "t < pi"
  shows "fam_y z t = (t + sin t) + ((cos t - z) * (1 + cos t)) * inverse (sin t)"
proof -
  have e: "fam_w z t * (1 + cos t) = 2 * ((cos t - z) * (1 + cos t) * inverse (sin t))"
    unfolding fam_w_def by (simp add: divide_inverse mult_ac)
  show ?thesis unfolding fam_y_def using e by linarith
qed

section \<open>C. Derivatives along the branch\<close>

lemma family_derivatives:
  fixes z t :: real
  assumes "0 < t" and "t < pi"
  shows "(fam_x z has_real_derivative (cos t - z) / (1 + cos t)) (at t)"
    and "(fam_y z has_real_derivative - (cos t - z) / (1 - cos t)) (at t)"
proof -
  have s: "0 < sin t" using assms by (intro sin_gt_zero)
  have c1: "1 + cos t \<noteq> 0" and c2: "1 - cos t \<noteq> 0" using cos_open_range[OF assms] by linarith+
  have sq: "(sin t)\<^sup>2 = (1 - cos t) * (1 + cos t)" unfolding power2_eq_square using sin_cos_squared_add[of t] by algebra
  have sne: "sin t \<noteq> 0" using s by simp
  have c3: "cos t \<noteq> 1" using c2 by simp
  show "(fam_x z has_real_derivative (cos t - z) / (1 + cos t)) (at t)"
    unfolding fam_x_def fam_w_def
    by (auto intro!: derivative_eq_intros simp: sne c1 field_simps) (use sq in algebra)
  show "(fam_y z has_real_derivative - (cos t - z) / (1 - cos t)) (at t)"
    unfolding fam_y_def fam_w_def
    by (auto intro!: derivative_eq_intros simp: sne c2 c3 field_simps) (use sq in algebra)
qed

lemma increasing_from_derivative:
  fixes f f' :: "real \<Rightarrow> real" and r s :: real
  assumes "r < s"
    and "\<And>t. r \<le> t \<Longrightarrow> t \<le> s \<Longrightarrow> (f has_real_derivative f' t) (at t)"
    and "\<And>t. r < t \<Longrightarrow> t < s \<Longrightarrow> 0 < f' t"
  shows "f r < f s"
proof -
  have d1: "\<exists>y. DERIV f t :> y \<and> 0 < y" if t: "r < t" "t < s" for t
  proof -
    have "r \<le> t" "t \<le> s" using t by simp_all
    then have "DERIV f t :> f' t" by (rule assms(2))
    then show ?thesis using assms(3)[OF t] by blast
  qed
  have d2: "isCont f t" if t: "r \<le> t" "t \<le> s" for t
  proof -
    have "DERIV f t :> f' t" by (rule assms(2)[OF t])
    then show ?thesis by (rule DERIV_isCont)
  qed
  have d3: "continuous_on {r..s} f"
    by (rule continuous_at_imp_continuous_on) (use d2 in auto)
  show ?thesis
    by (rule DERIV_pos_imp_increasing_open[OF assms(1) d1 d3])
qed

lemma decreasing_from_derivative:
  fixes f f' :: "real \<Rightarrow> real" and r s :: real
  assumes "r < s"
    and "\<And>t. r \<le> t \<Longrightarrow> t \<le> s \<Longrightarrow> (f has_real_derivative f' t) (at t)"
    and "\<And>t. r < t \<Longrightarrow> t < s \<Longrightarrow> f' t < 0"
  shows "f s < f r"
proof -
  have d1: "\<exists>y. DERIV f t :> y \<and> y < 0" if t: "r < t" "t < s" for t
  proof -
    have "r \<le> t" "t \<le> s" using t by simp_all
    then have "DERIV f t :> f' t" by (rule assms(2))
    then show ?thesis using assms(3)[OF t] by blast
  qed
  have d2: "isCont f t" if t: "r \<le> t" "t \<le> s" for t
  proof -
    have "DERIV f t :> f' t" by (rule assms(2)[OF t])
    then show ?thesis by (rule DERIV_isCont)
  qed
  have d3: "continuous_on {r..s} f"
    by (rule continuous_at_imp_continuous_on) (use d2 in auto)
  show ?thesis
    by (rule DERIV_neg_imp_decreasing_open[OF assms(1) d1 d3])
qed

lemma sin_exceeds_arg_cos:
  fixes t :: real
  assumes "0 < t" and "t < pi"
  shows "t * cos t < sin t"
proof -
  have "(\<lambda>u. sin u - u * cos u) 0 < (\<lambda>u. sin u - u * cos u) t"
  proof (rule increasing_from_derivative[OF assms(1), of _ "\<lambda>u. u * sin u"])
    fix u :: real
    assume "0 \<le> u" "u \<le> t"
    show "((\<lambda>u. sin u - u * cos u) has_real_derivative u * sin u) (at u)"
      by (auto intro!: derivative_eq_intros simp: algebra_simps)
  next
    fix u :: real
    assume u: "0 < u" "u < t"
    then show "0 < u * sin u" using assms(2) by (intro mult_pos_pos sin_gt_zero) auto
  qed
  then show ?thesis by simp
qed

section \<open>D. F4: monotonicity along the branch\<close>

lemma branch_below_pi:
  fixes z t :: real
  assumes "0 \<le> z" and "z < 1" and "t \<le> arccos z"
  shows "t < pi"
  using assms branch_facts(2)[OF assms(1,2)] pi_gt_zero by linarith

lemma branch_mid:
  fixes z r t s :: real
  assumes "0 \<le> z" and "z < 1" and "0 < r" and "r \<le> t" and "t \<le> s" and "s \<le> arccos z"
  shows "0 < t" and "t < pi"
proof -
  show "0 < t" using assms by linarith
  show "t < pi" by (rule branch_below_pi[OF assms(1,2)]) (use assms in linarith)
qed

lemma family_x_increasing:
  fixes z r s :: real
  assumes "0 \<le> z" and "z < 1" and "0 < r" and "r < s" and "s \<le> arccos z"
  shows "fam_x z r < fam_x z s"
proof (rule increasing_from_derivative[OF assms(4), of _ "\<lambda>t. (cos t - z) / (1 + cos t)"])
  fix t :: real
  assume t: "r \<le> t" "t \<le> s"
  then have "0 < t" "t < pi" using branch_mid[OF assms(1,2,3)] assms(5) by auto
  then show "(fam_x z has_real_derivative (cos t - z) / (1 + cos t)) (at t)"
    by (rule family_derivatives(1))
next
  fix t :: real
  assume t: "r < t" "t < s"
  have t0: "0 < t" and tpi: "t < pi"
    using branch_mid[OF assms(1,2,3) less_imp_le[OF t(1)] less_imp_le[OF t(2)] assms(5)] by simp_all
  have "z < cos t" using cos_strictly_above_z[OF assms(1,2)] t0 t assms(5) by simp
  moreover have "0 < 1 + cos t" using cos_open_range[OF t0 tpi] by linarith
  ultimately show "0 < (cos t - z) / (1 + cos t)" by simp
qed

lemma family_y_decreasing:
  fixes z r s :: real
  assumes "0 \<le> z" and "z < 1" and "0 < r" and "r < s" and "s \<le> arccos z"
  shows "fam_y z s < fam_y z r"
proof (rule decreasing_from_derivative[OF assms(4), of _ "\<lambda>t. - (cos t - z) / (1 - cos t)"])
  fix t :: real
  assume t: "r \<le> t" "t \<le> s"
  then have "0 < t" "t < pi" using branch_mid[OF assms(1,2,3)] assms(5) by auto
  then show "(fam_y z has_real_derivative - (cos t - z) / (1 - cos t)) (at t)"
    by (rule family_derivatives(2))
next
  fix t :: real
  assume t: "r < t" "t < s"
  have t0: "0 < t" and tpi: "t < pi"
    using branch_mid[OF assms(1,2,3) less_imp_le[OF t(1)] less_imp_le[OF t(2)] assms(5)] by simp_all
  have "z < cos t" using cos_strictly_above_z[OF assms(1,2)] t0 t assms(5) by simp
  moreover have "0 < 1 - cos t" using cos_open_range[OF t0 tpi] by linarith
  ultimately have "0 < (cos t - z) / (1 - cos t)" by (intro divide_pos_pos) simp_all
  then show "- (cos t - z) / (1 - cos t) < 0" by (subst minus_divide_left[symmetric]) linarith
qed

section \<open>E. F2: strictly inside the disc and strictly above the boundary\<close>

text \<open>Boundary (b): the sum x + y has derivative -2 cos t (cos t - z) / sin^2 t, negative on the branch,
  and equals 2d at the bang-bang.\<close>

lemma family_sum_above_boundary:
  fixes z \<phi> :: real
  assumes "0 \<le> z" and "z < 1" and "0 < \<phi>" and "\<phi> < arccos z"
  shows "2 * arccos z < fam_x z \<phi> + fam_y z \<phi>"
proof -
  define d where "d = arccos z"
  define S where "S t = fam_x z t + fam_y z t" for t
  define S' where "S' t = (cos t - z) / (1 + cos t) + (- (cos t - z) / (1 - cos t))" for t
  have "S d < S \<phi>"
  proof (rule decreasing_from_derivative[OF assms(4)[folded d_def], of S S'])
    fix t :: real
    assume t: "\<phi> \<le> t" "t \<le> d"
    then have "0 < t" "t < pi" using branch_mid[OF assms(1,2,3) _ _ order_refl[of "arccos z"]] d_def by auto
    then show "(S has_real_derivative S' t) (at t)"
      unfolding S_def S'_def by (intro DERIV_add family_derivatives)
  next
    fix t :: real
    assume t: "\<phi> < t" "t < d"
    then have t0: "0 < t" and tpi: "t < pi"
      using branch_mid[OF assms(1,2,3) _ _ order_refl[of "arccos z"]] d_def by (auto simp: less_imp_le)
    have tz: "z < cos t" using cos_strictly_above_z[OF assms(1,2)] t0 t d_def by simp
    have "0 < cos t" using tz assms(1) by simp
    have c1: "0 < 1 + cos t" and c2: "0 < 1 - cos t" using cos_open_range[OF t0 tpi] by linarith+
    have "S' t = - 2 * cos t * (cos t - z) / ((1 + cos t) * (1 - cos t))"
      unfolding S'_def using c1 c2 by (simp add: field_simps)
    moreover have "0 < 2 * cos t * (cos t - z) / ((1 + cos t) * (1 - cos t))"
      using \<open>0 < cos t\<close> tz c1 c2 by (intro divide_pos_pos mult_pos_pos) auto
    ultimately show "S' t < 0" by simp
  qed
  moreover have "S d = 2 * d"
    unfolding S_def using family_bang_bang(4)[OF assms(1,2) d_def] by simp
  ultimately show ?thesis unfolding S_def d_def by simp
qed

text \<open>Disc (a): the product p = x y has derivative 2 (cos t - z)(sin t - t cos t) / sin^2 t > 0
  on the branch; together with the limit F3 below this gives p > (1-z)^2.\<close>

lemma family_product_derivative:
  fixes z t :: real
  assumes "0 < t" and "t < pi"
  shows "((\<lambda>u. fam_x z u * fam_y z u) has_real_derivative
      2 * (cos t - z) * (sin t - t * cos t) / (sin t)\<^sup>2) (at t)"
proof -
  have s: "0 < sin t" using assms by (intro sin_gt_zero)
  have c1: "1 + cos t \<noteq> 0" and c2: "1 - cos t \<noteq> 0" using cos_open_range[OF assms] by linarith+
  have sq: "(sin t)\<^sup>2 = (1 - cos t) * (1 + cos t)" unfolding power2_eq_square using sin_cos_squared_add[of t] by algebra
  have sne: "sin t \<noteq> 0" using s by simp
  have da: "(fam_x z has_real_derivative (cos t - z) / (1 + cos t)) (at t)"
    and db: "(fam_y z has_real_derivative - (cos t - z) / (1 - cos t)) (at t)"
    using family_derivatives[OF assms] by simp_all
  have "((\<lambda>u. fam_x z u * fam_y z u) has_real_derivative
      (cos t - z) / (1 + cos t) * fam_y z t + fam_x z t * (- (cos t - z) / (1 - cos t))) (at t)"
    using da db by (intro derivative_eq_intros) auto
  moreover have "(cos t - z) / (1 + cos t) * fam_y z t + fam_x z t * (- (cos t - z) / (1 - cos t))
      = 2 * (cos t - z) * (sin t - t * cos t) / (sin t)\<^sup>2"
  proof -
    have su: "sin t * inverse (sin t) = 1" using sne by simp
    have cw: "(1 + cos t) * inverse (1 + cos t) = 1" using c1 by simp
    have cv: "(1 - cos t) * inverse (1 - cos t) = 1" using c2 by simp
    have sinv2: "inverse ((sin t)\<^sup>2) = inverse (sin t) * inverse (sin t)"
      by (simp add: power2_eq_square inverse_mult_distrib)
    show ?thesis
      by (simp only: family_x_alt[OF assms] family_y_alt[OF assms] divide_inverse)
        (use su cw cv sq sinv2 in algebra)
  qed
  ultimately show ?thesis by simp
qed

lemma family_product_increasing:
  fixes z r s :: real
  assumes "0 \<le> z" and "z < 1" and "0 < r" and "r < s" and "s \<le> arccos z"
  shows "fam_x z r * fam_y z r < fam_x z s * fam_y z s"
proof (rule increasing_from_derivative[OF assms(4),
      of _ "\<lambda>t. 2 * (cos t - z) * (sin t - t * cos t) / (sin t)\<^sup>2"])
  fix t :: real
  assume t: "r \<le> t" "t \<le> s"
  then have "0 < t" "t < pi" using branch_mid[OF assms(1,2,3)] assms(5) by auto
  then show "((\<lambda>u. fam_x z u * fam_y z u) has_real_derivative
      2 * (cos t - z) * (sin t - t * cos t) / (sin t)\<^sup>2) (at t)"
    by (rule family_product_derivative)
next
  fix t :: real
  assume t: "r < t" "t < s"
  have t0: "0 < t" and tpi: "t < pi"
    using branch_mid[OF assms(1,2,3) less_imp_le[OF t(1)] less_imp_le[OF t(2)] assms(5)] by simp_all
  have tz: "z < cos t" using cos_strictly_above_z[OF assms(1,2)] t0 t assms(5) by simp
  have c0: "0 < cos t" using tz assms(1) by simp
  have "t * cos t < sin t" by (rule sin_exceeds_arg_cos[OF t0 tpi])
  moreover have "0 < sin t" using t0 tpi by (intro sin_gt_zero)
  ultimately show "0 < 2 * (cos t - z) * (sin t - t * cos t) / (sin t)\<^sup>2"
    using tz by (intro divide_pos_pos mult_pos_pos) auto
qed

section \<open>F. F3: the asymptote at phi -> 0+\<close>

lemma tendsto_at_right_of_at:
  fixes f :: "real \<Rightarrow> 'a::topological_space"
  assumes "(f \<longlongrightarrow> l) (at 0)"
  shows "(f \<longlongrightarrow> l) (at_right 0)"
  by (rule tendsto_mono[OF at_le]) (use assms in simp_all)

lemma tendsto_at_right_limit:
  fixes f :: "real \<Rightarrow> real"
  assumes "(f \<longlongrightarrow> a) (at 0)" and "a = l"
  shows "(f \<longlongrightarrow> l) (at_right 0)"
  using tendsto_at_right_of_at[OF assms(1)] assms(2) by simp

lemma in_open_range:
  "eventually (\<lambda>t::real. 0 < t \<and> t < pi) (at_right 0)"
  by (rule eventually_at_rightI[of 0 pi]) (use pi_gt_zero in auto)

lemma sin_over_arg_limit: "((\<lambda>t. sin t / t) \<longlongrightarrow> 1) (at_right (0::real))"
proof (rule tendsto_at_right_of_at)
  have "DERIV sin 0 :> cos 0" by (rule DERIV_sin)
  then show "((\<lambda>t. sin t / t) \<longlongrightarrow> 1) (at (0::real))" unfolding DERIV_def by simp
qed

lemma arg_over_sin_limit: "((\<lambda>t. t / sin t) \<longlongrightarrow> 1) (at_right (0::real))"
proof -
  have "((\<lambda>t. inverse (sin t / t)) \<longlongrightarrow> inverse 1) (at_right (0::real))"
    by (rule tendsto_inverse[OF sin_over_arg_limit]) simp
  then show ?thesis by (simp add: inverse_divide)
qed

lemma family_product_alt:
  fixes z t :: real
  assumes "0 < t" and "t < pi"
  shows "fam_x z t * fam_y z t =
    ((t\<^sup>2 - (sin t)\<^sup>2) + (t / sin t - 1) * ((cos t - z) * (1 + cos t)))
    + ((cos t - z) * (t + sin t) * (sin t / (1 + cos t)) + (cos t - z)\<^sup>2)"
proof -
  have s: "0 < sin t" using assms by (intro sin_gt_zero)
  have c1: "1 + cos t \<noteq> 0" using cos_open_range[OF assms] by linarith
  have su: "sin t * inverse (sin t) = 1" using s by simp
  have cw: "(1 + cos t) * inverse (1 + cos t) = 1" using c1 by simp
  show ?thesis
    by (simp only: family_x_alt[OF assms] family_y_alt[OF assms] divide_inverse) (use su cw in algebra)
qed

theorem family_x_tends_to_zero:
  fixes z :: real
  shows "(fam_x z \<longlongrightarrow> 0) (at_right 0)"
proof -
  have "((\<lambda>t. t - sin t + (cos t - z) * (sin t / (1 + cos t))) \<longlongrightarrow>
      0 - sin 0 + (cos 0 - z) * (sin 0 / (1 + cos 0))) (at (0::real))"
    by (intro tendsto_intros) simp
  then have "((\<lambda>t. t - sin t + (cos t - z) * (sin t / (1 + cos t))) \<longlongrightarrow> 0) (at_right (0::real))"
    by (intro tendsto_at_right_of_at) simp
  moreover have "eventually (\<lambda>t. t - sin t + (cos t - z) * (sin t / (1 + cos t)) = fam_x z t)
      (at_right 0)"
    using in_open_range by eventually_elim (auto simp: family_x_alt)
  ultimately show ?thesis by (rule Lim_transform_eventually)
qed

theorem family_y_to_infinity:
  fixes z :: real
  assumes "z < 1"
  shows "filterlim (fam_y z) at_top (at_right 0)"
proof -
  have sin0: "((\<lambda>t. sin t) \<longlongrightarrow> 0) (at_right (0::real))"
    by (rule tendsto_at_right_of_at) (use isCont_sin[of "0::real"] in \<open>simp add: isCont_def\<close>)
  have pos: "eventually (\<lambda>t. 0 < sin t) (at_right (0::real))"
    using in_open_range by eventually_elim (auto intro: sin_gt_zero)
  have inv: "LIM t at_right (0::real). inverse (sin t) :> at_top"
    by (rule filterlim_inverse_at_top[OF sin0 pos])
  have a1: "((\<lambda>t. (cos t - z) * (1 + cos t)) \<longlongrightarrow> (cos 0 - z) * (1 + cos 0)) (at (0::real))"
    by (intro tendsto_intros)
  have lim1: "((\<lambda>t. (cos t - z) * (1 + cos t)) \<longlongrightarrow> (1 - z) * 2) (at_right (0::real))"
    by (rule tendsto_at_right_limit[OF a1]) (simp add: algebra_simps)
  have a2: "((\<lambda>t. t + sin t) \<longlongrightarrow> 0 + sin 0) (at (0::real))"
    by (intro tendsto_intros)
  have lim2: "((\<lambda>t. t + sin t) \<longlongrightarrow> 0) (at_right (0::real))"
    by (rule tendsto_at_right_limit[OF a2]) simp
  have "LIM t at_right (0::real). (cos t - z) * (1 + cos t) * inverse (sin t) :> at_top"
    by (rule filterlim_tendsto_pos_mult_at_top[OF lim1 _ inv]) (use assms in simp)
  then have lim3: "LIM t at_right (0::real). (t + sin t) + (cos t - z) * (1 + cos t) * inverse (sin t)
      :> at_top"
    by (rule filterlim_tendsto_add_at_top[OF lim2])
  have ev: "eventually (\<lambda>t. fam_y z t = (t + sin t) + (cos t - z) * (1 + cos t) * inverse (sin t))
      (at_right 0)"
    using in_open_range by eventually_elim (auto simp: family_y_alt)
  show ?thesis by (subst filterlim_cong[OF refl refl ev]) (rule lim3)
qed

theorem family_product_tends_to_hyperbola:
  fixes z :: real
  shows "((\<lambda>t. fam_x z t * fam_y z t) \<longlongrightarrow> (1 - z)\<^sup>2) (at_right 0)"
proof -
  have a1: "((\<lambda>t. t\<^sup>2 - (sin t)\<^sup>2) \<longlongrightarrow> 0\<^sup>2 - (sin 0)\<^sup>2) (at (0::real))"
    by (intro tendsto_intros)
  have hA: "((\<lambda>t. t\<^sup>2 - (sin t)\<^sup>2) \<longlongrightarrow> 0) (at_right (0::real))"
    by (rule tendsto_at_right_limit[OF a1]) simp
  have a2: "((\<lambda>t. (cos t - z) * (1 + cos t)) \<longlongrightarrow> (cos 0 - z) * (1 + cos 0)) (at (0::real))"
    by (intro tendsto_intros)
  have hB: "((\<lambda>t. (cos t - z) * (1 + cos t)) \<longlongrightarrow> (1 - z) * 2) (at_right (0::real))"
    by (rule tendsto_at_right_limit[OF a2]) (simp add: algebra_simps)
  have a3: "((\<lambda>t. (cos t - z) * (t + sin t) * (sin t / (1 + cos t)) + (cos t - z)\<^sup>2)
      \<longlongrightarrow> (cos 0 - z) * (0 + sin 0) * (sin 0 / (1 + cos 0)) + (cos 0 - z)\<^sup>2) (at (0::real))"
    by (intro tendsto_intros) simp
  have hC: "((\<lambda>t. (cos t - z) * (t + sin t) * (sin t / (1 + cos t)) + (cos t - z)\<^sup>2)
      \<longlongrightarrow> (1 - z)\<^sup>2) (at_right (0::real))"
    by (rule tendsto_at_right_limit[OF a3]) simp
  have "((\<lambda>t. ((t\<^sup>2 - (sin t)\<^sup>2) + (t / sin t - 1) * ((cos t - z) * (1 + cos t)))
      + ((cos t - z) * (t + sin t) * (sin t / (1 + cos t)) + (cos t - z)\<^sup>2))
      \<longlongrightarrow> (0 + (1 - 1) * ((1 - z) * 2)) + (1 - z)\<^sup>2) (at_right 0)"
    by (rule tendsto_add[OF tendsto_add[OF hA tendsto_mult[OF tendsto_diff[OF arg_over_sin_limit
        tendsto_const] hB]] hC])
  moreover have "eventually (\<lambda>t. ((t\<^sup>2 - (sin t)\<^sup>2) + (t / sin t - 1) * ((cos t - z) * (1 + cos t)))
      + ((cos t - z) * (t + sin t) * (sin t / (1 + cos t)) + (cos t - z)\<^sup>2) = fam_x z t * fam_y z t)
      (at_right 0)"
    using in_open_range by eventually_elim (auto simp: family_product_alt)
  ultimately have "((\<lambda>t. fam_x z t * fam_y z t) \<longlongrightarrow> 0 + (1 - 1) * ((1 - z) * 2) + (1 - z)\<^sup>2)
      (at_right 0)"
    by (rule Lim_transform_eventually)
  then show ?thesis by simp
qed

section \<open>G. F2 continued: the product exceeds (1-z)^2\<close>

theorem family_inside_disc:
  fixes z \<phi> :: real
  assumes "0 \<le> z" and "z < 1" and "0 < \<phi>" and "\<phi> < arccos z"
  shows "(1 - z)\<^sup>2 < fam_x z \<phi> * fam_y z \<phi>"
proof -
  have half: "fam_x z (\<phi> / 2) * fam_y z (\<phi> / 2) < fam_x z \<phi> * fam_y z \<phi>"
    by (rule family_product_increasing[OF assms(1,2) _ _ less_imp_le[OF assms(4)]])
      (use assms(3) in simp_all)
  have lt: "(0::real) < \<phi> / 2" using assms(3) by simp
  have step: "fam_x z t * fam_y z t \<le> fam_x z (\<phi> / 2) * fam_y z (\<phi> / 2)"
    if t: "0 < t" "t < \<phi> / 2" for t
  proof (rule less_imp_le)
    show "fam_x z t * fam_y z t < fam_x z (\<phi> / 2) * fam_y z (\<phi> / 2)"
      by (rule family_product_increasing[OF assms(1,2) t(1) t(2)]) (use assms(3,4) in linarith)
  qed
  have ev: "eventually (\<lambda>t. fam_x z t * fam_y z t \<le> fam_x z (\<phi> / 2) * fam_y z (\<phi> / 2))
      (at_right 0)"
    by (rule eventually_at_rightI[of 0 "\<phi> / 2"]) (use step lt in auto)
  have "(1 - z)\<^sup>2 \<le> fam_x z (\<phi> / 2) * fam_y z (\<phi> / 2)"
    by (rule tendsto_upperbound[OF family_product_tends_to_hyperbola ev]) simp
  then show ?thesis using half by simp
qed

end
