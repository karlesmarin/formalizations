(*  Title:      Memory_Cycle_No_Reset.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    The mathematical core of Proposition prop:noreset of paper A (memory floors): the memory cycle without reset, to
    first order.  Two pieces:
      (a) a change-of-variables inequality: f continuous, f >= 0 on the path, |theta'| <= G give
          (1/G) |int_{theta a}^{theta b} f| <= int_a^b f (theta s) ds;
      (b) with rho(P) = [gq P + fq P (2-P) + gm (1-P) + fm (1-P^2)]/3 and
          F_t(th) = (2/G) int_0^th rho(cos^2 u) du + t rho(cos^2 th):  F_t'(pi/2) = (2/(3G)) (gm + fm), so if
          gm + fm > 0 every minimiser of F_t on [0,pi/2] lies below pi/2 and F_t (pi/2) is not the minimum.
    The physical reduction r_1 = int rho(P(s)) ds along the lossless path is a HYPOTHESIS of the model and is not
    formalised; the asymptotics t -> infinity (delta_* and the gain) is not formalised.
*)

theory Memory_Cycle_No_Reset
  imports "HOL-Analysis.Analysis"
begin

section \<open>Piece (a): change of variables\<close>

text \<open>The primitive of a continuous function on a compact interval, composed with a path.\<close>

lemma primitive_difference:
  fixes f :: "real \<Rightarrow> real" and R x y :: real
  assumes fc: "continuous_on UNIV f" and x: "-R \<le> x" and xy: "x \<le> y" and y: "y \<le> R"
  shows "integral {-R..y} f - integral {-R..x} f = integral {x..y} f"
proof -
  have "f integrable_on {-R..y}" using fc by (intro integrable_continuous_real continuous_on_subset[OF fc]) auto
  then have "integral {-R..x} f + integral {x..y} f = integral {-R..y} f"
    by (rule Henstock_Kurzweil_Integration.integral_combine[OF x xy])
  then show ?thesis by simp
qed

theorem change_of_variables_ineq:
  fixes f theta theta' :: "real \<Rightarrow> real" and a b G :: real
  assumes ab: "a \<le> b" and G: "0 < G" and fc: "continuous_on UNIV f"
    and f0: "\<forall>s\<in>{a..b}. 0 \<le> f (theta s)"
    and der: "\<forall>s\<in>{a..b}. (theta has_vector_derivative theta' s) (at s within {a..b})"
    and bd: "\<forall>s\<in>{a..b}. \<bar>theta' s\<bar> \<le> G"
  shows "(1 / G) * \<bar>integral {min (theta a) (theta b)..max (theta a) (theta b)} f\<bar>
           \<le> integral {a..b} (\<lambda>s. f (theta s))"
proof -
  have thc: "continuous_on {a..b} theta"
    unfolding continuous_on_eq_continuous_within
    using der by (auto intro: has_vector_derivative_continuous)
  have "bounded (theta ` {a..b})" by (intro compact_imp_bounded compact_continuous_image thc compact_Icc)
  then obtain R where Rb: "\<forall>y\<in>theta ` {a..b}. norm y \<le> R" unfolding bounded_iff by blast
  have inK: "\<And>s. s \<in> {a..b} \<Longrightarrow> theta s \<in> {-R..R}"
  proof -
    fix s assume s: "s \<in> {a..b}"
    then have "norm (theta s) \<le> R" using Rb by blast
    then show "theta s \<in> {-R..R}" by (simp add: abs_le_iff)
  qed
  define Phi where "Phi = (\<lambda>x. integral {-R..x} f)"
  have Phid: "\<And>x. x \<in> {-R..R} \<Longrightarrow> (Phi has_vector_derivative f x) (at x within {-R..R})"
    unfolding Phi_def by (rule integral_has_vector_derivative[OF continuous_on_subset[OF fc] ]) auto
  have chain: "\<And>s. s \<in> {a..b} \<Longrightarrow>
      ((Phi \<circ> theta) has_vector_derivative theta' s * f (theta s)) (at s within {a..b})"
  proof -
    fix s assume s: "s \<in> {a..b}"
    have 1: "(Phi has_vector_derivative f (theta s)) (at (theta s) within theta ` {a..b})"
      by (rule has_vector_derivative_within_subset[OF Phid[OF inK[OF s]]]) (use inK in auto)
    have "((Phi \<circ> theta) has_vector_derivative theta' s *\<^sub>R f (theta s)) (at s within {a..b})"
      by (rule vector_diff_chain_within[OF der[rule_format, OF s] 1])
    then show "((Phi \<circ> theta) has_vector_derivative theta' s * f (theta s)) (at s within {a..b})" by simp
  qed
  have ftc: "((\<lambda>s. theta' s * f (theta s)) has_integral (Phi (theta b) - Phi (theta a))) {a..b}"
    by (rule fundamental_theorem_of_calculus[OF ab, where f = "\<lambda>x. Phi (theta x)"]) (use chain in \<open>simp add: o_def\<close>)
  define D where "D = Phi (theta b) - Phi (theta a)"
  have fthc: "continuous_on {a..b} (\<lambda>s. f (theta s))"
    by (rule continuous_on_compose2[OF fc thc]) simp
  have hi: "((\<lambda>s. f (theta s)) has_integral integral {a..b} (\<lambda>s. f (theta s))) {a..b}"
    using fthc by (intro integrable_integral integrable_continuous_real)
  have key: "\<And>c. \<forall>s\<in>{a..b}. c * (theta' s * f (theta s)) \<le> f (theta s) \<Longrightarrow>
      c * D \<le> integral {a..b} (\<lambda>s. f (theta s))"
  proof -
    fix c assume pw: "\<forall>s\<in>{a..b}. c * (theta' s * f (theta s)) \<le> f (theta s)"
    have h1: "((\<lambda>s. c *\<^sub>R (theta' s * f (theta s))) has_integral c *\<^sub>R D) {a..b}"
      by (rule has_integral_cmul[OF ftc[folded D_def]])
    have "c *\<^sub>R D \<le> integral {a..b} (\<lambda>s. f (theta s))"
      by (rule has_integral_le[OF h1 hi]) (use pw in simp)
    then show "c * D \<le> integral {a..b} (\<lambda>s. f (theta s))" by simp
  qed
  have up: "(1 / G) * D \<le> integral {a..b} (\<lambda>s. f (theta s))"
  proof (rule key, rule ballI)
    fix s assume s: "s \<in> {a..b}"
    have f0s: "0 \<le> f (theta s)" using f0 s by blast
    have h: "theta' s \<le> G" using bd s by (auto simp: abs_le_iff)
    have h1: "f (theta s) * theta' s \<le> f (theta s) * G" by (rule mult_left_mono[OF h f0s])
    have h2: "(1 / G) * (f (theta s) * theta' s) \<le> (1 / G) * (f (theta s) * G)"
      by (rule mult_left_mono[OF h1]) (use G in simp)
    show "1 / G * (theta' s * f (theta s)) \<le> f (theta s)" using h2 G by (simp add: ac_simps)
  qed
  have lo: "- (1 / G) * D \<le> integral {a..b} (\<lambda>s. f (theta s))"
  proof (rule key, rule ballI)
    fix s assume s: "s \<in> {a..b}"
    have f0s: "0 \<le> f (theta s)" using f0 s by blast
    have h: "- theta' s \<le> G" using bd s by (auto simp: abs_le_iff)
    have h1: "f (theta s) * (- theta' s) \<le> f (theta s) * G" by (rule mult_left_mono[OF h f0s])
    have h2: "(1 / G) * (f (theta s) * (- theta' s)) \<le> (1 / G) * (f (theta s) * G)"
      by (rule mult_left_mono[OF h1]) (use G in simp)
    show "- (1 / G) * (theta' s * f (theta s)) \<le> f (theta s)" using h2 G by (simp add: ac_simps)
  qed
  have absD: "(1 / G) * \<bar>D\<bar> \<le> integral {a..b} (\<lambda>s. f (theta s))"
    using up lo by (cases "0 \<le> D") (simp_all add: abs_of_nonneg abs_of_neg)
  have ta: "theta a \<in> {-R..R}" and tb: "theta b \<in> {-R..R}" using inK ab by auto
  have "\<bar>D\<bar> = \<bar>integral {min (theta a) (theta b)..max (theta a) (theta b)} f\<bar>"
  proof (cases "theta a \<le> theta b")
    case True
    have "D = integral {theta a..theta b} f"
      unfolding D_def Phi_def using primitive_difference[OF fc _ True] ta tb by simp
    with True show ?thesis by simp
  next
    case False
    then have le: "theta b \<le> theta a" by simp
    have pd: "integral {-R..theta a} f - integral {-R..theta b} f = integral {theta b..theta a} f"
      by (rule primitive_difference[OF fc _ le _]) (use ta tb in auto)
    have "D = - integral {theta b..theta a} f"
      unfolding D_def Phi_def using pd by simp
    with le show ?thesis by simp
  qed
  with absD show ?thesis by simp
qed

section \<open>Piece (b): the first-order minimisation\<close>

locale cycle =
  fixes gq fq gm fm G t :: real
  assumes gq0: "0 \<le> gq" and fq0: "0 \<le> fq" and gm0: "0 \<le> gm" and fm0: "0 \<le> fm"
    and G0: "0 < G" and t0: "0 \<le> t"
begin

definition rho :: "real \<Rightarrow> real" where
  "rho P = (gq * P + fq * P * (2 - P) + gm * (1 - P) + fm * (1 - P^2)) / 3"

definition F :: "real \<Rightarrow> real" where
  "F th = (2 / G) * integral {0..th} (\<lambda>u. rho (cos u ^ 2)) + t * rho (cos th ^ 2)"

lemma rho_nonneg: assumes "0 \<le> P" "P \<le> 1" shows "0 \<le> rho P"
proof -
  have "0 \<le> 2 - P" using assms by simp
  have "P^2 \<le> 1" using assms by (simp add: power_le_one)
  have "0 \<le> gq * P" using gq0 assms by simp
  moreover have "0 \<le> fq * P * (2 - P)" using fq0 assms \<open>0 \<le> 2 - P\<close> by (intro mult_nonneg_nonneg) auto
  moreover have "0 \<le> gm * (1 - P)" using gm0 assms by simp
  moreover have "0 \<le> fm * (1 - P^2)" using fm0 \<open>P^2 \<le> 1\<close> by simp
  ultimately show ?thesis unfolding rho_def by simp
qed

lemma rho_zero: "rho 0 = (gm + fm) / 3" by (simp add: rho_def)

lemma rho_cos_continuous: "continuous_on UNIV (\<lambda>u. rho (cos u ^ 2))"
  unfolding rho_def by (intro continuous_intros) simp

lemma rho_cos_nonneg: "0 \<le> rho (cos u ^ 2)"
proof (rule rho_nonneg)
  show "0 \<le> cos u ^ 2" by simp
  show "cos u ^ 2 \<le> 1" using cos_squared_eq[of u] zero_le_power2[of "sin u"] by linarith
qed

text \<open>Application of piece (a) to the density rho along a path with speed at most G.\<close>

theorem noreset_lower_bound:
  fixes theta theta' :: "real \<Rightarrow> real" and a b :: real
  assumes ab: "a \<le> b"
    and der: "\<forall>s\<in>{a..b}. (theta has_vector_derivative theta' s) (at s within {a..b})"
    and bd: "\<forall>s\<in>{a..b}. \<bar>theta' s\<bar> \<le> G"
  shows "(1 / G) * \<bar>integral {min (theta a) (theta b)..max (theta a) (theta b)} (\<lambda>u. rho (cos u ^ 2))\<bar>
           \<le> integral {a..b} (\<lambda>s. rho (cos (theta s) ^ 2))"
  using change_of_variables_ineq[where f = "\<lambda>u. rho (cos u ^ 2)", OF ab G0 rho_cos_continuous _ der bd]
    rho_cos_nonneg by blast

text \<open>The derivative of F at pi/2.\<close>

lemma rho_cos_deriv_zero:
  "((\<lambda>th. rho (cos th ^ 2)) has_real_derivative 0) (at (pi / 2))"
proof -
  have m: "((\<lambda>th. cos th * cos th) has_real_derivative
      (- sin (pi / 2)) * cos (pi / 2) + cos (pi / 2) * (- sin (pi / 2))) (at (pi / 2))"
    by (auto intro!: derivative_eq_intros)
  have c2: "((\<lambda>th. cos th ^ 2) has_real_derivative 0) (at (pi / 2))"
    using m by (simp add: power2_eq_square)
  have "((\<lambda>P. (gq * P + fq * P * (2 - P) + gm * (1 - P) + fm * (1 - P^2)) / 3) has_real_derivative
          (gq + fq * (2 - 2 * (cos (pi / 2) ^ 2)) - gm - 2 * fm * cos (pi / 2) ^ 2) / 3) (at (cos (pi / 2) ^ 2))"
    by (auto intro!: derivative_eq_intros)
  from DERIV_chain[OF this c2] show ?thesis unfolding rho_def comp_def by simp
qed

theorem F_derivative_pi_half:
  "(F has_real_derivative (2 / (3 * G)) * (gm + fm)) (at (pi / 2))"
proof -
  define g where "g = (\<lambda>u. rho (cos u ^ 2))"
  have gc: "continuous_on {0..pi} g" unfolding g_def using rho_cos_continuous continuous_on_subset by blast
  have pm: "pi / 2 \<in> {0..pi}" using pi_gt_zero by auto
  have w: "((\<lambda>x. integral {0..x} g) has_vector_derivative g (pi / 2)) (at (pi / 2) within {0..pi})"
    by (rule integral_has_vector_derivative[OF gc pm])
  have "((\<lambda>x. integral {0..x} g) has_vector_derivative g (pi / 2)) (at (pi / 2) within {0<..<pi})"
    by (rule has_vector_derivative_within_subset[OF w]) auto
  then have "((\<lambda>x. integral {0..x} g) has_vector_derivative g (pi / 2)) (at (pi / 2))"
    using at_within_open[where S = "{0<..<pi}" and a = "pi / 2"] pi_gt_zero by simp
  then have i: "((\<lambda>x. integral {0..x} g) has_real_derivative g (pi / 2)) (at (pi / 2))"
  proof -
    have e: "(\<lambda>x::real. x * g (pi / 2)) = (*) (g (pi / 2))" by (rule ext) simp
    show ?thesis using \<open>(_ has_vector_derivative _) (at (pi / 2))\<close>
      by (simp add: has_vector_derivative_def has_field_derivative_def e)
  qed
  have "((\<lambda>th. (2 / G) * integral {0..th} g + t * rho (cos th ^ 2)) has_real_derivative
          (2 / G) * g (pi / 2) + t * 0) (at (pi / 2))"
    by (rule DERIV_add[OF DERIV_cmult[OF i] DERIV_cmult[OF rho_cos_deriv_zero]])
  moreover have "g (pi / 2) = (gm + fm) / 3" unfolding g_def by (simp add: rho_def)
  ultimately show ?thesis unfolding F_def g_def[symmetric] using G0 by (simp add: field_simps)
qed

theorem F_below_pi_half:
  assumes pos: "0 < gm + fm"
  shows "\<exists>th. 0 \<le> th \<and> th < pi / 2 \<and> F th < F (pi / 2)"
proof -
  have d: "0 < (2 / (3 * G)) * (gm + fm)" using G0 pos by simp
  obtain d0 where d0: "0 < d0" and h: "\<forall>h. 0 < h \<longrightarrow> h < d0 \<longrightarrow> F (pi / 2 - h) < F (pi / 2)"
    using DERIV_pos_inc_left[OF F_derivative_pi_half d] by blast
  define h0 where "h0 = min (d0 / 2) (pi / 4)"
  have h0: "0 < h0" "h0 < d0" "h0 \<le> pi / 4" unfolding h0_def using d0 pi_gt_zero by auto
  have "0 \<le> pi / 2 - h0" "pi / 2 - h0 < pi / 2" using h0 pi_gt_zero by linarith+
  moreover have "F (pi / 2 - h0) < F (pi / 2)" using h h0 by blast
  ultimately show ?thesis by blast
qed

lemma F_continuous: "continuous_on {0..pi / 2} F"
proof -
  define g where "g = (\<lambda>u. rho (cos u ^ 2))"
  have gc: "continuous_on {0..pi} g" unfolding g_def using rho_cos_continuous continuous_on_subset by blast
  have "continuous_on {0..pi} (\<lambda>x. integral {0..x} g)"
    unfolding continuous_on_eq_continuous_within
    using integral_has_vector_derivative[OF gc] has_vector_derivative_continuous by blast
  then have i1: "continuous_on {0..pi / 2} (\<lambda>x. integral {0..x} g)"
    by (rule continuous_on_subset) (use pi_gt_zero in auto)
  have i2: "continuous_on {0..pi / 2} (\<lambda>th. rho (cos th ^ 2))"
    by (rule continuous_on_subset[OF rho_cos_continuous]) simp
  have "continuous_on {0..pi / 2} (\<lambda>th. (2 / G) * integral {0..th} g + t * rho (cos th ^ 2))"
    by (rule continuous_on_add[OF continuous_on_mult_left[OF i1] continuous_on_mult_left[OF i2]])
  then show ?thesis unfolding F_def g_def .
qed

theorem minimiser_not_pi_half:
  assumes pos: "0 < gm + fm"
  shows "\<exists>th0\<in>{0..pi / 2}. (\<forall>th\<in>{0..pi / 2}. F th0 \<le> F th) \<and> th0 < pi / 2 \<and> F th0 < F (pi / 2)"
proof -
  have "\<exists>th0\<in>{0..pi / 2}. \<forall>th\<in>{0..pi / 2}. F th0 \<le> F th"
    by (rule continuous_attains_inf[OF compact_Icc _ F_continuous]) (use pi_gt_zero in auto)
  then obtain th0 where th0: "th0 \<in> {0..pi / 2}" "\<forall>th\<in>{0..pi / 2}. F th0 \<le> F th" by blast
  obtain th where th: "0 \<le> th" "th < pi / 2" "F th < F (pi / 2)" using F_below_pi_half[OF pos] by blast
  have "F th0 \<le> F th" using th0(2) th by auto
  then have lt: "F th0 < F (pi / 2)" using th(3) by simp
  then have "th0 \<noteq> pi / 2" by blast
  then have "th0 < pi / 2" using th0(1) by auto
  then show ?thesis using th0 lt by blast
qed

corollary every_minimiser_below_pi_half:
  assumes pos: "0 < gm + fm" and th0: "th0 \<in> {0..pi / 2}" and min: "\<forall>th\<in>{0..pi / 2}. F th0 \<le> F th"
  shows "th0 < pi / 2" and "F th0 < F (pi / 2)"
proof -
  obtain th where th: "0 \<le> th" "th < pi / 2" "F th < F (pi / 2)" using F_below_pi_half[OF pos] by blast
  have "F th0 \<le> F th" using min th by auto
  then show lt: "F th0 < F (pi / 2)" using th(3) by simp
  then have "th0 \<noteq> pi / 2" by blast
  then show "th0 < pi / 2" using th0 by auto
qed

end

end
