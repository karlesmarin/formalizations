(*  Title:      Dilog_Reflection_Landen.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín
*)

section \<open>Euler's reflection, Landen's identity and the duplication formula for the real dilogarithm\<close>

theory Dilog_Reflection_Landen
  imports
    "Polylog.Polylog"
    "Bernoulli.Bernoulli_Zeta"
begin

text \<open>
  We build on the Polylog entry of the AFP (M. Eberl, 2023), where \<open>polylog k z\<close> is the principal
  branch of the polylogarithm for integer \<open>k\<close>. For \<open>k = 2\<close> and real \<open>x < 1\<close> we take its real part
  (the imaginary part vanishes, but we never need it). At \<open>x = 1\<close> the Polylog entry uses the junk
  value \<open>0\<close>; here the value at \<open>1\<close> is the continuous one, \<open>\<pi>\<^sup>2 / 6\<close>, and we prove that it is
  the left limit.

  Cited result: C. Marín, \emph{The Clock That Never Ticks}, Zenodo, Theorem 1.
\<close>

subsection \<open>Definition and the power series\<close>

definition Li2 :: "real \<Rightarrow> real" where
  "Li2 x = (if x = 1 then pi\<^sup>2 / 6 else Re (polylog 2 (of_real x)))"

lemma Li2_eq: "x < 1 \<Longrightarrow> Li2 x = Re (polylog 2 (of_real x))"
  by (simp add: Li2_def)

lemma Li2_zero [simp]: "Li2 0 = 0"
  by (simp add: Li2_def)

lemma not_in_cut: "x < 1 \<Longrightarrow> (of_real x :: complex) \<in> - of_real ` {1..}"
  by (auto simp: complex_eq_iff)

lemma sums_Li2_polylog:
  assumes "\<bar>x\<bar> < 1"
  shows "(\<lambda>n. x ^ Suc n / real (Suc n) ^ 2) sums Li2 x"
proof -
  have "(\<lambda>n. of_nat (Suc n) powi (-2) * (of_real x :: complex) ^ Suc n) sums polylog 2 (of_real x)"
    using assms by (intro sums_polylog) simp
  hence "(\<lambda>n. Re (of_nat (Suc n) powi (-2) * (of_real x :: complex) ^ Suc n))
           sums Re (polylog 2 (of_real x))"
    by (rule bounded_linear.sums[OF bounded_linear_Re])
  also have "(\<lambda>n. Re (of_nat (Suc n) powi (-2) * (of_real x :: complex) ^ Suc n)) =
             (\<lambda>n. x ^ Suc n / real (Suc n) ^ 2)"
  proof
    fix n :: nat
    have "(of_nat (Suc n) powi (-2) * (of_real x :: complex) ^ Suc n) =
          of_real (x ^ Suc n / real (Suc n) ^ 2)"
      by (simp add: power_int_minus field_simps)
    thus "Re (of_nat (Suc n) powi (-2) * (of_real x :: complex) ^ Suc n) = x ^ Suc n / real (Suc n) ^ 2"
      by simp
  qed
  finally show ?thesis
    using assms by (simp add: Li2_eq)
qed

subsection \<open>The derivative\<close>

definition dLi2 :: "real \<Rightarrow> real" where
  "dLi2 x = (if x = 0 then 1 else - ln (1 - x) / x)"

lemma has_real_derivative_Li2_aux:
  assumes "x < 1"
  shows "((\<lambda>t. Re (polylog 2 (of_real t))) has_real_derivative dLi2 x) (at x)"
proof -
  let ?z = "of_real x :: complex"
  have z: "?z \<in> - of_real ` {1..}"
    using assms by (rule not_in_cut)
  have h: "(polylog 2 has_field_derivative (if ?z = 0 then 1 else polylog (2 - 1) ?z / ?z)) (at ?z)"
    using has_field_derivative_polylog[where z = ?z and k = 2 and A = UNIV] z by simp
  define d where "d = (if ?z = 0 then 1 else polylog (2 - 1) ?z / ?z)"
  have d_re: "Re d = dLi2 x"
  proof (cases "x = 0")
    case True
    thus ?thesis by (simp add: d_def dLi2_def)
  next
    case False
    have "polylog (2 - 1) ?z = - Ln (1 - ?z)"
      using polylog_1[where z = ?z] z by simp
    also have "1 - ?z = of_real (1 - x)"
      by simp
    also have "Ln \<dots> = of_real (ln (1 - x))"
      using assms by (intro Ln_of_real) simp
    finally have "d = of_real (- ln (1 - x) / x)"
      using False by (simp add: d_def)
    thus ?thesis
      using False by (simp add: dLi2_def)
  qed
  have h1: "(polylog 2 has_field_derivative d) (at ?z)"
    using h by (simp add: d_def)
  have h3: "((\<lambda>t. polylog 2 (of_real t)) has_derivative (\<lambda>u. d * of_real u)) (at x)"
    using has_vector_derivative_real_field[OF h1]
    by (simp add: has_vector_derivative_def scaleR_conv_of_real mult.commute)
  have h4: "((\<lambda>t. Re (polylog 2 (of_real t))) has_derivative (\<lambda>u. Re (d * of_real u))) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Re h3])
  have "(\<lambda>u. Re (d * of_real u)) = (\<lambda>u. dLi2 x * u)"
    using d_re by (auto simp: fun_eq_iff)
  thus ?thesis
    using h4 unfolding has_field_derivative_def by simp
qed

lemma has_real_derivative_Li2:
  assumes "x < 1"
  shows "(Li2 has_real_derivative dLi2 x) (at x)"
proof -
  have "((\<lambda>t. Re (polylog 2 (of_real t))) has_real_derivative dLi2 x) (at x)"
    by (rule has_real_derivative_Li2_aux[OF assms])
  moreover have "\<forall>\<^sub>F t in nhds x. t \<in> {..<1}"
    using assms by (intro eventually_nhds_in_open) auto
  hence ev: "\<forall>\<^sub>F t in nhds x. Re (polylog 2 (of_real t)) = Li2 t"
    by (rule eventually_mono) (simp add: Li2_eq)
  ultimately show ?thesis
    using DERIV_cong_ev[OF refl ev refl, of "dLi2 x"] by blast
qed

lemma isCont_Li2: "x < 1 \<Longrightarrow> isCont Li2 x"
  by (rule DERIV_continuous[OF has_real_derivative_Li2])

lemma has_real_derivative_Li2_comp:
  assumes "(h has_real_derivative h') (at y)" "h y < 1"
  shows "((\<lambda>t. Li2 (h t)) has_real_derivative dLi2 (h y) * h') (at y)"
  using DERIV_chain[OF has_real_derivative_Li2[OF assms(2)] assms(1)] by (simp add: o_def)

subsection \<open>The value at 1\<close>

lemma Li2_one: "Li2 1 = pi\<^sup>2 / 6"
  by (simp add: Li2_def)

lemma sums_Li2_one: "(\<lambda>n. 1 / real (Suc n) ^ 2) sums (pi\<^sup>2 / 6)"
  using nat_squares_sums by (simp add: add.commute)

text \<open>
  \<open>S x\<close> is the series \<open>\<Sum> x\<^sup>n\<^sup>+\<^sup>1 / (n+1)\<^sup>2\<close>, uniformly convergent on \<open>[-1, 1]\<close> (M-test).
\<close>

definition S2 :: "real \<Rightarrow> real" where
  "S2 x = (\<Sum>n. x ^ Suc n / real (Suc n) ^ 2)"

lemma continuous_on_S2: "continuous_on {-1..1} S2"
proof -
  have summ: "summable (\<lambda>n. 1 / real (Suc n) ^ 2)"
    using sums_Li2_one by (rule sums_summable)
  have ul: "uniform_limit {-1..1} (\<lambda>n x. \<Sum>i<n. x ^ Suc i / real (Suc i) ^ 2) S2 sequentially"
    unfolding S2_def
  proof (rule Weierstrass_m_test[OF _ summ])
    fix n :: nat and x :: real
    assume "x \<in> {-1..1}"
    hence "\<bar>x\<bar> \<le> 1" by auto
    hence "\<bar>x\<bar> ^ Suc n \<le> 1"
      by (intro power_le_one) simp_all
    hence "\<bar>x\<bar> ^ Suc n / real (Suc n) ^ 2 \<le> 1 / real (Suc n) ^ 2"
      by (intro divide_right_mono) simp_all
    moreover have "norm (x ^ Suc n / real (Suc n) ^ 2) = \<bar>x\<bar> ^ Suc n / real (Suc n) ^ 2"
      by (simp add: norm_divide norm_power abs_mult power_abs)
    ultimately show "norm (x ^ Suc n / real (Suc n) ^ 2) \<le> 1 / real (Suc n) ^ 2"
      by simp
  qed
  show ?thesis
    by (rule uniform_limit_theorem[OF _ ul]) (auto intro!: always_eventually continuous_intros)
qed

lemma S2_one: "S2 1 = pi\<^sup>2 / 6"
  using sums_Li2_one by (simp add: S2_def sums_iff)

lemma Li2_eq_S2: "\<bar>x\<bar> < 1 \<Longrightarrow> Li2 x = S2 x"
  using sums_Li2_polylog[where x = x] by (simp add: S2_def sums_iff)

lemma ev_right: "\<forall>\<^sub>F y in at_right (0::real). y \<in> {0<..<1}"
  by (rule eventually_at_right_real) simp

lemma ev_left: "\<forall>\<^sub>F x in at_left (1::real). x \<in> {0<..<1}"
  by (rule eventually_at_left_real) simp

lemma tendsto_Li2_one_minus: "((\<lambda>y. Li2 (1 - y)) \<longlongrightarrow> pi\<^sup>2 / 6) (at_right 0)"
proof -
  have "continuous_on {0..1} (\<lambda>y. S2 (1 - y))"
    by (rule continuous_on_compose2[OF continuous_on_S2]) (auto intro!: continuous_intros)
  from continuous_on_Icc_at_rightD[OF this zero_less_one]
  have "((\<lambda>y. S2 (1 - y)) \<longlongrightarrow> S2 1) (at_right 0)"
    by simp
  hence "((\<lambda>y. S2 (1 - y)) \<longlongrightarrow> pi\<^sup>2 / 6) (at_right 0)"
    by (simp add: S2_one)
  moreover have "\<forall>\<^sub>F y in at_right (0::real). S2 (1 - y) = Li2 (1 - y)"
    using ev_right by eventually_elim (auto intro!: Li2_eq_S2[symmetric] simp: abs_less_iff)
  ultimately show ?thesis
    by (rule Lim_transform_eventually)
qed

lemma tendsto_Li2_left_one: "(Li2 \<longlongrightarrow> pi\<^sup>2 / 6) (at_left 1)"
proof -
  have "continuous_on {0..1} S2"
    by (rule continuous_on_subset[OF continuous_on_S2]) auto
  from continuous_on_Icc_at_leftD[OF this zero_less_one]
  have "(S2 \<longlongrightarrow> S2 1) (at_left 1)"
    by simp
  hence "(S2 \<longlongrightarrow> pi\<^sup>2 / 6) (at_left 1)"
    by (simp add: S2_one)
  moreover have "\<forall>\<^sub>F x in at_left (1::real). S2 x = Li2 x"
    using ev_left by eventually_elim (auto intro!: Li2_eq_S2[symmetric] simp: abs_less_iff)
  ultimately show ?thesis
    by (rule Lim_transform_eventually)
qed

subsection \<open>Euler's reflection formula\<close>

theorem Li2_reflection:
  assumes "0 < x" "x < 1"
  shows "Li2 x + Li2 (1 - x) = pi\<^sup>2 / 6 - ln x * ln (1 - x)"
proof -
  define F where "F y = Li2 y + Li2 (1 - y) + ln y * ln (1 - y)" for y
  have deriv: "(F has_real_derivative 0) (at y)" if y: "y \<in> {0<..<1}" for y
  proof -
    have y0: "0 < y" and y1: "y < 1" using y by auto
    have a: "(Li2 has_real_derivative - ln (1 - y) / y) (at y)"
      using has_real_derivative_Li2[OF y1] y0 by (simp add: dLi2_def)
    have b: "((\<lambda>t. Li2 (1 - t)) has_real_derivative ln y / (1 - y)) (at y)"
    proof -
      have "((\<lambda>t. 1 - t) has_real_derivative -1) (at y)"
        by (intro derivative_eq_intros) auto
      from has_real_derivative_Li2_comp[OF this] y1 y0
      show ?thesis
        by (simp add: dLi2_def)
    qed
    have c: "((\<lambda>t. ln t * ln (1 - t)) has_real_derivative
              ln (1 - y) / y + ln y * (- (1 / (1 - y)))) (at y)"
      using y0 y1 by (auto intro!: derivative_eq_intros simp: divide_simps)
    have "(F has_real_derivative - ln (1 - y) / y + ln y / (1 - y) +
                (ln (1 - y) / y + ln y * (- (1 / (1 - y))))) (at y)"
      unfolding F_def by (intro DERIV_add a b c)
    thus ?thesis
      by (simp add: field_simps)
  qed
  have const: "F y = F x" if y: "y \<in> {0<..<1}" for y
    using DERIV_isconst3[where a = 0 and b = 1 and x = y and y = x and f = F] deriv y assms by auto
  have lim: "(F \<longlongrightarrow> pi\<^sup>2 / 6) (at_right 0)"
  proof -
    have t1: "(Li2 \<longlongrightarrow> 0) (at_right 0)"
    proof -
      have "isCont Li2 0"
        by (rule isCont_Li2) simp
      hence "continuous (at 0 within {0<..}) Li2"
        by (rule continuous_at_imp_continuous_within)
      thus ?thesis
        by (simp add: continuous_within)
    qed
    have t3: "((\<lambda>y. ln y * ln (1 - y)) \<longlongrightarrow> 0) (at_right (0::real))"
      by real_asymp
    have "((\<lambda>y. Li2 y + Li2 (1 - y) + ln y * ln (1 - y)) \<longlongrightarrow> 0 + pi\<^sup>2 / 6 + 0) (at_right 0)"
      by (intro tendsto_add t1 tendsto_Li2_one_minus t3)
    thus ?thesis
      unfolding F_def by simp
  qed
  have lx: "(F \<longlongrightarrow> F x) (at_right 0)"
  proof (rule Lim_transform_eventually[where f = "\<lambda>_. F x"])
    show "((\<lambda>_. F x) \<longlongrightarrow> F x) (at_right 0)" by simp
    show "\<forall>\<^sub>F y in at_right 0. F x = F y"
      using ev_right by eventually_elim (simp add: const)
  qed
  have "F x = pi\<^sup>2 / 6"
    by (rule tendsto_unique[OF _ lx lim]) simp
  thus ?thesis
    unfolding F_def by simp
qed

corollary Li2_one_half: "Li2 (1 / 2) = pi\<^sup>2 / 12 - (ln 2)\<^sup>2 / 2"
proof -
  have "Li2 (1 / 2) + Li2 (1 - 1 / 2) = pi\<^sup>2 / 6 - ln (1 / 2) * ln (1 - 1 / 2)"
    by (rule Li2_reflection) auto
  moreover have "1 - 1 / 2 = (1 / 2 :: real)" by simp
  moreover have "ln (1 / 2 :: real) = - ln 2"
    by (simp add: ln_div)
  ultimately show ?thesis
    by (simp add: power2_eq_square)
qed

subsection \<open>Landen's identity\<close>

theorem Li2_landen:
  assumes "x < 1"
  shows "Li2 x + Li2 (x / (x - 1)) = - (ln (1 - x))\<^sup>2 / 2"
proof -
  define G where "G y = Li2 y + Li2 (y / (y - 1)) + (ln (1 - y))\<^sup>2 / 2" for y
  have deriv: "(G has_real_derivative 0) (at y)" if y: "y \<in> {..<1}" for y
  proof -
    have y1: "y < 1" using y by simp
    have g: "((\<lambda>t. t / (t - 1)) has_real_derivative - 1 / (y - 1)\<^sup>2) (at y)"
      using y1 by (auto intro!: derivative_eq_intros simp: divide_simps power2_eq_square)
    have gy: "y / (y - 1) < 1"
      using y1 by (simp add: divide_simps)
    have a: "(Li2 has_real_derivative dLi2 y) (at y)"
      by (rule has_real_derivative_Li2[OF y1])
    have b: "((\<lambda>t. Li2 (t / (t - 1))) has_real_derivative dLi2 (y / (y - 1)) * (- 1 / (y - 1)\<^sup>2)) (at y)"
      by (rule has_real_derivative_Li2_comp[OF g gy])
    have c: "((\<lambda>t. (ln (1 - t))\<^sup>2 / 2) has_real_derivative - ln (1 - y) / (1 - y)) (at y)"
      using y1 by (auto intro!: derivative_eq_intros simp: divide_simps)
    have tot: "(G has_real_derivative dLi2 y + dLi2 (y / (y - 1)) * (- 1 / (y - 1)\<^sup>2)
                 + - ln (1 - y) / (1 - y)) (at y)"
      unfolding G_def by (intro DERIV_add a b c)
    have "dLi2 y + dLi2 (y / (y - 1)) * (- 1 / (y - 1)\<^sup>2) + - ln (1 - y) / (1 - y) = 0"
    proof (cases "y = 0")
      case True
      thus ?thesis by (simp add: dLi2_def)
    next
      case False
      have "1 - y / (y - 1) = inverse (1 - y)"
        using y1 by (simp add: divide_simps)
      hence l: "ln (1 - y / (y - 1)) = - ln (1 - y)"
        using y1 by (simp add: ln_inverse)
      show ?thesis
        using False y1 l
        by (simp add: dLi2_def divide_simps power2_eq_square)
           (simp add: algebra_simps)
    qed
    thus ?thesis
      using tot by simp
  qed
  have "G x = G 0"
    using DERIV_isconst3[where a = "min x 0 - 1" and b = 1 and x = x and y = 0 and f = G] deriv assms by auto
  thus ?thesis
    by (simp add: G_def)
qed

subsection \<open>Duplication formula\<close>

lemma Li2_duplication_open:
  assumes "\<bar>x\<bar> < 1"
  shows "Li2 x + Li2 (- x) = Li2 (x\<^sup>2) / 2"
proof -
  let ?z = "of_real x :: complex"
  have "?z \<notin> complex_of_real ` ({..-1} \<union> {1..})"
    using assms by (auto simp: complex_eq_iff)
  hence "polylog 2 ?z + polylog 2 (-?z) = 2 powi (1 - 2) * polylog 2 (?z\<^sup>2)"
    using polylog_duplication[where s = 2 and z = ?z] by simp
  hence "Re (polylog 2 (of_real x)) + Re (polylog 2 (of_real (-x))) =
         Re (polylog 2 (of_real (x\<^sup>2))) / 2"
    by (auto dest: arg_cong[where f = Re] simp: power_int_minus power2_eq_square)
  moreover have "x < 1" "-x < 1" "x\<^sup>2 < 1"
    using assms by (auto simp: abs_less_iff abs_square_less_1)
  ultimately show ?thesis
    by (simp add: Li2_eq)
qed

subsection \<open>The value at \<open>-1\<close> and the duplication formula on the closed interval\<close>

lemma tendsto_Li2_square_left_one:
  "((\<lambda>x. Li2 (x\<^sup>2)) \<longlongrightarrow> pi\<^sup>2 / 6) (at_left 1)"
proof -
  have sub: "x\<^sup>2 \<in> {-1..1}" if "x \<in> {0..1}" for x :: real
  proof -
    have "x\<^sup>2 \<le> 1"
      using that by (intro power_le_one) auto
    thus ?thesis
      unfolding atLeastAtMost_iff using zero_le_power2[where a = x] by linarith
  qed
  have "continuous_on {0..1} (\<lambda>x::real. S2 (x\<^sup>2))"
    by (rule continuous_on_compose2[OF continuous_on_S2])
       (use sub in \<open>auto intro!: continuous_intros simp: image_subset_iff\<close>)
  from continuous_on_Icc_at_leftD[OF this zero_less_one]
  have "((\<lambda>x. S2 (x\<^sup>2)) \<longlongrightarrow> S2 (1\<^sup>2)) (at_left 1)"
    by simp
  hence "((\<lambda>x. S2 (x\<^sup>2)) \<longlongrightarrow> pi\<^sup>2 / 6) (at_left 1)"
    by (simp add: S2_one)
  moreover have "\<forall>\<^sub>F x in at_left (1::real). S2 (x\<^sup>2) = Li2 (x\<^sup>2)"
    using ev_left by eventually_elim (auto intro!: Li2_eq_S2[symmetric] simp: abs_square_less_1 abs_less_iff)
  ultimately show ?thesis
    by (rule Lim_transform_eventually)
qed

lemma Li2_neg_one: "Li2 (-1) = - pi\<^sup>2 / 12"
proof -
  have c: "isCont (\<lambda>x. Li2 (- x)) 1"
    by (rule isCont_o2[OF _ isCont_Li2]) auto
  have t1: "((\<lambda>x. Li2 (- x)) \<longlongrightarrow> Li2 (-1)) (at_left 1)"
    using continuous_at_imp_continuous_within[OF c, of "{..<1}"]
    by (simp add: continuous_within)
  have t2: "((\<lambda>x. Li2 (x\<^sup>2) / 2) \<longlongrightarrow> pi\<^sup>2 / 6 / 2) (at_left 1)"
    by (intro tendsto_divide tendsto_Li2_square_left_one tendsto_const) simp
  have t3: "((\<lambda>x. Li2 x + Li2 (- x)) \<longlongrightarrow> pi\<^sup>2 / 6 + Li2 (-1)) (at_left 1)"
    by (intro tendsto_add tendsto_Li2_left_one t1)
  have "\<forall>\<^sub>F x in at_left (1::real). Li2 (x\<^sup>2) / 2 = Li2 x + Li2 (- x)"
    using ev_left
  proof eventually_elim
    fix x :: real
    assume "x \<in> {0<..<1}"
    hence "\<bar>x\<bar> < 1"
      by (auto simp: abs_less_iff)
    thus "Li2 (x\<^sup>2) / 2 = Li2 x + Li2 (- x)"
      by (simp add: Li2_duplication_open)
  qed
  hence t4: "((\<lambda>x. Li2 x + Li2 (- x)) \<longlongrightarrow> pi\<^sup>2 / 6 / 2) (at_left 1)"
    by (rule Lim_transform_eventually[OF t2])
  have "pi\<^sup>2 / 6 + Li2 (-1) = pi\<^sup>2 / 6 / 2"
    by (rule tendsto_unique[OF _ t3 t4]) simp
  thus ?thesis
    by simp
qed

theorem Li2_duplication:
  assumes "\<bar>x\<bar> \<le> 1"
  shows "Li2 x + Li2 (- x) = Li2 (x\<^sup>2) / 2"
proof (cases "\<bar>x\<bar> < 1")
  case True
  thus ?thesis by (rule Li2_duplication_open)
next
  case False
  with assms have "x = 1 \<or> x = -1" by auto
  thus ?thesis
    by (auto simp: Li2_one Li2_neg_one)
qed

end
