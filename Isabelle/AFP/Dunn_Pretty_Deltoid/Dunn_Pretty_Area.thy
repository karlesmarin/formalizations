theory Dunn_Pretty_Area
  imports "HOL-Analysis.Analysis"
begin

section \<open>Area of Dunn and Pretty's deltoid, in the reference triangle\<close>

text \<open>
Reference triangle (0,0), (1,0), (0,1) (area 1/2). Hyperbolas: A: x*y = 1/8; B: (1-x-y)*y = 1/8;
C: (1-x-y)*x = 1/8. The deltoid is bounded by arcs of these three, meeting tangentially at three
cusps. Its area is the cusp triangle (area 1/32) minus three curved segments; each segment has
the same integral 3/32 - (ln 2)/8.

What is covered: (1) cusps are double roots lying on the two hyperbolas; (2) the integral of the
segment of A (and its nonnegativity); (3) the segments of B and C as the same integral after the
explicit rewriting of the curve formula; (4) the final arithmetic and the positivity of the area.
What is NOT covered: that the deltoid region is exactly the cusp triangle minus the three
segments (geometry of the region), and the affine reduction from an arbitrary triangle.
\<close>

subsection \<open>(1) Cusps\<close>

text \<open>The quadratic obtained by intersecting two hyperbolas has discriminant zero (double root).\<close>

lemma cusp_quadratic_double_root:
  "2 * x\<^sup>2 - x + 1/8 = 2 * (x - 1/4)\<^sup>2" and "(1::real)\<^sup>2 - 4 * 2 * (1/8) = 0"
  for x :: real
  by (simp_all add: power2_eq_square algebra_simps)

lemma cusp_quadratic_root_iff:
  fixes x :: real
  shows "2 * x\<^sup>2 - x + 1/8 = 0 \<longleftrightarrow> x = 1/4"
proof -
  have "2 * x\<^sup>2 - x + 1/8 = 2 * (x - 1/4)\<^sup>2" by (simp add: power2_eq_square algebra_simps)
  thus ?thesis by auto
qed

definition hypA :: "real \<Rightarrow> real \<Rightarrow> bool" where "hypA x y \<longleftrightarrow> x * y = 1/8"
definition hypB :: "real \<Rightarrow> real \<Rightarrow> bool" where "hypB x y \<longleftrightarrow> (1 - x - y) * y = 1/8"
definition hypC :: "real \<Rightarrow> real \<Rightarrow> bool" where "hypC x y \<longleftrightarrow> (1 - x - y) * x = 1/8"

lemma cusp_AB: "hypA (1/4) (1/2)" "hypB (1/4) (1/2)"
  by (simp_all add: hypA_def hypB_def)

lemma cusp_AC: "hypA (1/2) (1/4)" "hypC (1/2) (1/4)"
  by (simp_all add: hypA_def hypC_def)

lemma cusp_BC: "hypB (1/4) (1/4)" "hypC (1/4) (1/4)"
  by (simp_all add: hypB_def hypC_def)

text \<open>The cusp of A and B is their only common point, at $x = 1/4$: on A, the curves A and B
intersect iff $2x^2 - x + 1/8 = 0$ (substituting $y = 1/(8x)$), which has a double root.\<close>

lemma AB_intersection:
  fixes x y :: real
  assumes "x \<noteq> 0" "hypA x y" "hypB x y"
  shows "x = 1/4 \<and> y = 1/2"
proof -
  have y: "y = 1 / (8 * x)" using assms(2) assms(1) by (auto simp: hypA_def field_simps)
  have "(1 - x - y) * y = 1/8" using assms(3) by (simp add: hypB_def)
  hence "y - x * y - y\<^sup>2 = 1/8" by (simp add: algebra_simps power2_eq_square)
  hence "y - 1/8 - y\<^sup>2 = 1/8" using assms(2) by (simp add: hypA_def)
  hence "(y - 1/2)\<^sup>2 = 0" by (simp add: power2_eq_square algebra_simps)
  hence y2: "y = 1/2" by simp
  with y have "x = 1/4" by (auto simp: field_simps)
  with y2 show ?thesis by simp
qed

subsection \<open>(2) The integral of the segment of A\<close>

definition seg :: "real \<Rightarrow> real" where
  "seg x = 3/4 - x - 1/(8 * x)"

definition prim :: "real \<Rightarrow> real" where
  "prim x = 3/4 * x - 1/2 * x ^ 2 - 1/8 * ln x"

lemma prim_deriv:
  assumes "0 < x"
  shows "(prim has_real_derivative seg x) (at x)"
proof -
  have sq: "((\<lambda>x::real. x ^ 2) has_real_derivative 2 * x) (at x)"
    using DERIV_pow[of 2 x] by simp
  have "((\<lambda>x. 3/4 * x - 1/2 * x ^ 2 - 1/8 * ln x) has_real_derivative
        3/4 * 1 - 1/2 * (2 * x) - 1/8 * inverse x) (at x)"
    using assms sq
    by (intro DERIV_diff DERIV_cmult DERIV_ln DERIV_ident) simp_all
  moreover have "3/4 * 1 - 1/2 * (2 * x) - 1/8 * inverse x = seg x"
    using assms by (simp add: seg_def inverse_eq_divide field_simps)
  ultimately have h: "((\<lambda>x. 3/4 * x - 1/2 * x ^ 2 - 1/8 * ln x) has_real_derivative seg x) (at x)"
    by (rule DERIV_cong)
  have "prim = (\<lambda>x. 3/4 * x - 1/2 * x ^ 2 - 1/8 * ln x)" by (rule ext) (simp add: prim_def)
  thus ?thesis using h by simp
qed

lemma seg_nonneg:
  assumes "1/4 \<le> x" "x \<le> 1/2"
  shows "0 \<le> seg x"
proof -
  have x0: "0 < x" using assms(1) by linarith
  have "seg x = (4 * x - 1) * (1 - 2 * x) / (8 * x)"
    using x0 by (simp add: seg_def field_simps)
  moreover have "0 \<le> (4 * x - 1) * (1 - 2 * x) / (8 * x)"
    using assms x0 by (intro divide_nonneg_pos mult_nonneg_nonneg) auto
  ultimately show ?thesis by simp
qed

lemma ln_half: "ln (1/2 :: real) = - ln 2"
  by (simp add: ln_div)

lemma ln_quarter: "ln (1/4 :: real) = - 2 * ln 2"
proof -
  have "ln (4 :: real) = ln 2 + ln 2" using ln_mult[of 2 2] by simp
  moreover have "ln (1/4 :: real) = - ln 4" by (simp add: ln_div)
  ultimately show ?thesis by simp
qed

lemma prim_diff: "prim (1/2) - prim (1/4) = 3/32 - ln 2 / 8"
  by (simp add: prim_def ln_half ln_quarter power2_eq_square)

theorem segment_A_integral:
  "(seg has_integral (3/32 - ln 2 / 8)) {1/4..1/2}"
proof -
  have "(seg has_integral prim (1/2) - prim (1/4)) {1/4..1/2}"
  proof (rule fundamental_theorem_of_calculus)
    show "(1/4 :: real) \<le> 1/2" by simp
    fix x :: real assume x: "x \<in> {1/4..1/2}"
    hence "0 < x" by auto
    from prim_deriv[OF this] show "(prim has_vector_derivative seg x) (at x within {1/4..1/2})"
      by (simp add: has_real_derivative_iff_has_vector_derivative[symmetric]
          has_field_derivative_at_within)
  qed
  moreover have "prim (1/2) - prim (1/4) = 3/32 - ln 2 / 8" by (rule prim_diff)
  ultimately show ?thesis by simp
qed

corollary segment_A_integral_eq:
  "integral {1/4..1/2} seg = 3/32 - ln 2 / 8"
  using segment_A_integral by (rule integral_unique)

subsection \<open>(3) The segments of B and C\<close>

text \<open>
B: the arc is x = 1 - y - 1/(8y) (from (1-x-y)*y = 1/8), the chord is x = 1/4, and y runs over
[1/4, 1/2]; the width of the segment is (1 - y - 1/(8y)) - 1/4.
C: the arc is y = 1 - x - 1/(8x), the chord is y = 1/4, x runs over [1/4, 1/2]; the height is
(1 - x - 1/(8x)) - 1/4.
\<close>

lemma B_arc: "y \<noteq> 0 \<Longrightarrow> hypB x y \<longleftrightarrow> x = 1 - y - 1/(8 * y)"
  by (auto simp: hypB_def field_simps)

lemma C_arc: "x \<noteq> 0 \<Longrightarrow> hypC x y \<longleftrightarrow> y = 1 - x - 1/(8 * x)"
  by (auto simp: hypC_def field_simps)

theorem segment_B_integral:
  "((\<lambda>y::real. (1 - y - 1/(8 * y)) - 1/4) has_integral (3/32 - ln 2 / 8)) {1/4..1/2}"
proof -
  have "(\<lambda>y::real. (1 - y - 1/(8 * y)) - 1/4) = seg" by (rule ext) (simp add: seg_def algebra_simps)
  thus ?thesis using segment_A_integral by metis
qed

theorem segment_C_integral:
  "((\<lambda>x::real. (1 - x - 1/(8 * x)) - 1/4) has_integral (3/32 - ln 2 / 8)) {1/4..1/2}"
proof -
  have "(\<lambda>x::real. (1 - x - 1/(8 * x)) - 1/4) = seg" by (rule ext) (simp add: seg_def algebra_simps)
  thus ?thesis using segment_A_integral by metis
qed

subsection \<open>(4) Final arithmetic\<close>

text \<open>Area of the cusp triangle (1/4,1/2), (1/2,1/4), (1/4,1/4) by the determinant formula.\<close>

lemma cusp_triangle_area:
  "\<bar>(1/2 - 1/4) * (1/4 - 1/2) - (1/4 - 1/4) * (1/4 - 1/2 :: real)\<bar> / 2 = 1/32"
  by simp

lemma ln2_gt: "2/3 < ln (2 :: real)"
proof -
  have "exp (2/3 :: real) < 2"
  proof -
    have a: "23/24 \<le> exp (-(1/24) :: real)" using exp_ge_add_one_self[of "-(1/24)"] by simp
    have e: "exp (1/24 :: real) = 1 / exp (-(1/24))" by (simp add: exp_minus inverse_eq_divide)
    have b: "exp (1/24 :: real) \<le> 24/23"
    proof -
      have p: "exp (1/24 :: real) * exp (-(1/24)) = 1" by (simp add: exp_minus_inverse)
      have "23 * exp (1/24 :: real) \<le> 24 * exp (-(1/24)) * exp (1/24)"
        using a by (intro mult_right_mono) simp_all
      also have "\<dots> = 24" using p by (simp add: algebra_simps)
      finally show ?thesis by simp
    qed
    have "exp (2/3 :: real) = exp (real 16 * (1/24)) ^ 1"
      by simp
    also have "\<dots> = exp (1/24 :: real) ^ 16"
      using exp_of_nat_mult[of 16 "1/24"] by simp
    also have "\<dots> \<le> (24/23) ^ 16" using b by (intro power_mono) simp_all
    also have "\<dots> < (2 :: real)" by (simp add: power_divide)
    finally show ?thesis .
  qed
  hence "ln (exp (2/3 :: real)) < ln 2" by (subst ln_less_cancel_iff) simp_all
  thus ?thesis by simp
qed

theorem deltoid_area_value:
  "1/32 - 3 * (3/32 - ln 2 / 8) = (3/4 * ln 2 - 1/2) * (1/2 :: real)"
  by (simp add: algebra_simps)

theorem deltoid_area_positive:
  "0 < (3/4 * ln 2 - 1/2) * (1/2 :: real)"
  using ln2_gt by simp

theorem deltoid_area_ratio:
  "(1/32 - 3 * (3/32 - ln 2 / 8)) / (1/2) = 3/4 * ln (2::real) - 1/2"
  by (simp add: field_simps)

end
