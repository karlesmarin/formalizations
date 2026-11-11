(*  Title:      Dunn_Pretty.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

theory Dunn_Pretty
  imports Complex_Main
begin

section \<open>Core of Dunn and Pretty's triangle-halving deltoid\<close>

text \<open>
Affine reduction (NOT formalized here, explained only). Ratios of areas are invariant under
affine maps of the plane, and a line meets a triangle in an affinely invariant way.
So for a triangle with a vertex O and the two sides through O we may choose affine coordinates
in which O is the origin, the two sides lie along the axes, and the triangle is the reference
triangle (0,0), (1,0), (0,1), of area 1/2. The hyperbola asymptotic to the two sides through O
is then of the form x*y = c; the one that matters is x*y = 1/8.

A line cutting the sides at (t,0) and (0,s) with 0 < t, s <= 1 cuts off, next to the origin,
the triangle (0,0), (t,0), (0,s).

What is covered: the three statements below (bisection iff t*s = 1/2; the bisecting line is
tangent to x*y = 1/8 at (t/2, s/2); every tangent to x*y = 1/8 at (p,q), p,q > 0, has
intercepts 2p, 2q), and their combination (equivalence) as one theorem.
What is NOT covered: the reduction to the reference triangle, the other two hyperbolae, and
the fact that the deltoid is the envelope of the three hyperbola branches.
\<close>

subsection \<open>(1) Area cut off and bisection\<close>

text \<open>Area of a triangle with vertices (x1,y1), (x2,y2), (x3,y3) by the determinant formula.\<close>

definition tri_area :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "tri_area x1 y1 x2 y2 x3 y3 = \<bar>(x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1)\<bar> / 2"

text \<open>Triangle cut off by the line through (t,0) and (0,s), next to the origin.\<close>

definition cut_area :: "real \<Rightarrow> real \<Rightarrow> real" where
  "cut_area t s = tri_area 0 0 t 0 0 s"

definition ref_area :: real where
  "ref_area = tri_area 0 0 1 0 0 1"

lemma ref_area_value: "ref_area = 1 / 2"
  by (simp add: ref_area_def tri_area_def)

lemma cut_area_value:
  fixes t s :: real
  assumes "0 < t" "0 < s"
  shows "cut_area t s = t * s / 2"
  using assms by (simp add: cut_area_def tri_area_def)

text \<open>The line bisects the area iff the cut-off triangle has half the area of the reference one.\<close>

definition bisects :: "real \<Rightarrow> real \<Rightarrow> bool" where
  "bisects t s \<longleftrightarrow> cut_area t s = ref_area / 2"

theorem bisects_iff:
  fixes t s :: real
  assumes "0 < t" "0 < s"
  shows "bisects t s \<longleftrightarrow> t * s = 1 / 2"
proof -
  have "bisects t s \<longleftrightarrow> t * s / 2 = 1 / 4"
    using assms by (simp add: bisects_def cut_area_value ref_area_value)
  also have "\<dots> \<longleftrightarrow> t * s = 1 / 2" by linarith
  finally show ?thesis .
qed

subsection \<open>(2) Tangency to the hyperbola x*y = 1/8\<close>

text \<open>The hyperbola branch is the graph of hyp x = 1/(8x); tangency is expressed with the
derivative (slope of the tangent at x).\<close>

definition hyp :: "real \<Rightarrow> real" where
  "hyp x = 1 / (8 * x)"

lemma hyp_deriv:
  fixes p :: real
  assumes "p \<noteq> 0"
  shows "DERIV hyp p :> - 1 / (8 * p\<^sup>2)"
proof -
  have D0: "DERIV (\<lambda>x::real. inverse x * (1/8)) p :> (- inverse (p * p)) * (1/8)"
    using assms by (auto intro!: derivative_eq_intros simp: power2_eq_square inverse_mult_distrib)
  have eq: "hyp = (\<lambda>x::real. inverse x * (1/8))"
    by (rule ext) (simp add: hyp_def field_simps)
  have D1: "DERIV hyp p :> (- inverse (p * p)) * (1/8)"
    by (subst eq) (rule D0)
  have X: "(- inverse (p * p)) * (1/8) = - 1 / (8 * p\<^sup>2)"
    by (simp add: field_simps power2_eq_square)
  show ?thesis by (subst X[symmetric]) (rule D1)
qed

text \<open>The line x/t + y/s = 1 touches the curve at (t/2, s/2): the point is on both and the
slope -s/t of the line is the derivative of the curve there.\<close>

theorem tangent_at_midpoint:
  fixes t s :: real
  assumes "0 < t" "0 < s" "t * s = 1 / 2"
  shows "(t/2) / t + (s/2) / s = 1"
    and "(t/2) * (s/2) = 1 / 8"
    and "s / 2 = hyp (t/2)"
    and "DERIV hyp (t/2) :> - s / t"
proof -
  show "(t/2) / t + (s/2) / s = 1" using assms by (simp add: field_simps)
  show "(t/2) * (s/2) = 1 / 8" using assms by (simp add: field_simps)
  show "s / 2 = hyp (t/2)"
    using assms by (simp add: hyp_def field_simps)
  have t0: "t \<noteq> 0" using assms by simp
  have "DERIV hyp (t/2) :> - 1 / (8 * (t/2)\<^sup>2)" using hyp_deriv[of "t/2"] t0 by simp
  moreover have "- 1 / (8 * (t/2)\<^sup>2) = - s / t"
  proof -
    have "s = 1 / (2 * t)" using assms t0 by (simp add: field_simps)
    thus ?thesis using t0 by (simp add: field_simps power2_eq_square)
  qed
  ultimately show "DERIV hyp (t/2) :> - s / t" by simp
qed

text \<open>Algebraic version: substituting the line into $xy = 1/8$ gives
$-(s/t) x^2 + s x - 1/8 = 0$, whose discriminant is $s^2 - 4 (s/t)(1/8)$; it vanishes
exactly when $ts = 1/2$ (double root, i.e. tangency).\<close>

theorem discriminant_zero_iff:
  fixes t s :: real
  assumes "0 < t" "0 < s"
  shows "s\<^sup>2 - 4 * (s / t) * (1 / 8) = 0 \<longleftrightarrow> t * s = 1 / 2"
proof -
  have "s\<^sup>2 - 4 * (s / t) * (1 / 8) = s * (2 * s * t - 1) / (2 * t)"
    using assms by (simp add: field_simps power2_eq_square)
  also have "\<dots> = 0 \<longleftrightarrow> 2 * s * t - 1 = 0" using assms by simp
  finally show ?thesis by (simp add: algebra_simps)
qed

subsection \<open>(3) Converse: every tangent has intercepts (2p,0) and (0,2q)\<close>

text \<open>Tangent line at (p,q), q = hyp p, with slope m: the points (x,y) with y - q = m*(x - p).\<close>

theorem tangent_intercepts:
  fixes p q m :: real
  assumes "0 < p" "0 < q" "p * q = 1 / 8" "DERIV hyp p :> m"
  shows "m = - q / p"
    and "\<And>x y. y - q = m * (x - p) \<longleftrightarrow> x / (2 * p) + y / (2 * q) = 1"
    and "0 - q = m * (2 * p - p)"
    and "(2 * q) - q = m * (0 - p)"
    and "(2 * p) * (2 * q) = 1 / 2"
proof -
  have p0: "p \<noteq> 0" using assms(1) by simp
  have "DERIV hyp p :> - 1 / (8 * p\<^sup>2)" using p0 by (rule hyp_deriv)
  hence m: "m = - 1 / (8 * p\<^sup>2)" by (rule DERIV_unique[OF assms(4)])
  have q: "q = 1 / (8 * p)" using assms p0 by (simp add: field_simps)
  have m1: "m * (8 * p\<^sup>2) = -1" using m p0 by (simp add: field_simps)
  have z: "(m * p + q) * (8 * p) = 0"
  proof -
    have "(m * p + q) * (8 * p) = m * (8 * p\<^sup>2) + 8 * (p * q)"
      by (simp add: algebra_simps power2_eq_square)
    also have "\<dots> = 0" using m1 assms(3) by simp
    finally show ?thesis .
  qed
  have "m * p + q = 0" using z p0 by simp
  hence "m * p = - q" by linarith
  hence mq: "m = - q / p" using p0 by (simp add: field_simps)
  show "m = - q / p" by (rule mq)
  show "y - q = m * (x - p) \<longleftrightarrow> x / (2 * p) + y / (2 * q) = 1" for x y
  proof -
    have q0: "q \<noteq> 0" using assms(2) by simp
    have hmp: "m * p = - q" using mq p0 by (simp add: field_simps)
    have key: "y - q = m * (x - p) \<longleftrightarrow> p * y + q * x = 2 * (p * q)"
    proof
      assume h: "y - q = m * (x - p)"
      show "p * y + q * x = 2 * (p * q)" using h hmp by algebra
    next
      assume h: "p * y + q * x = 2 * (p * q)"
      have "p * (y - q - m * (x - p)) = 0" using h hmp by algebra
      hence "y - q - m * (x - p) = 0" using p0 by simp
      thus "y - q = m * (x - p)" by linarith
    qed
    have fr: "x / (2 * p) + y / (2 * q) = (q * x + p * y) / (2 * p * q)"
      using p0 q0 by (simp add: field_simps)
    have "x / (2 * p) + y / (2 * q) = 1 \<longleftrightarrow> p * y + q * x = 2 * (p * q)"
      using fr p0 q0 by (simp add: divide_eq_eq algebra_simps)
    thus "y - q = m * (x - p) \<longleftrightarrow> x / (2 * p) + y / (2 * q) = 1" using key by simp
  qed
  show "0 - q = m * (2 * p - p)" using mq p0 by (simp add: field_simps)
  show "(2 * q) - q = m * (0 - p)" using mq p0 by (simp add: field_simps)
  show "(2 * p) * (2 * q) = 1 / 2" using assms by (simp add: field_simps)
qed

subsection \<open>(4) Bisection iff tangency, as one theorem\<close>

text \<open>The line x/t + y/s = 1 is tangent to the hyperbola at (p,q): the point lies on the curve
and on the line and the slope -s/t of the line is the derivative of the curve there.\<close>

definition tangent_at :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "tangent_at t s p q \<longleftrightarrow> p * q = 1 / 8 \<and> p / t + q / s = 1 \<and> DERIV hyp p :> - s / t"

theorem bisects_iff_tangent:
  fixes t s :: real
  assumes "1 / 2 \<le> t" "t \<le> 1" "0 < s" "s \<le> 1"
  shows "bisects t s \<longleftrightarrow> (\<exists>p q. 0 < p \<and> 0 < q \<and> tangent_at t s p q)"
proof -
  have t0: "0 < t" using assms(1) by simp
  have s0: "0 < s" by fact
  show ?thesis
  proof
    assume "bisects t s"
    hence ts: "t * s = 1 / 2" using bisects_iff t0 s0 by blast
    note h = tangent_at_midpoint[OF t0 s0 ts]
    have "tangent_at t s (t/2) (s/2)"
      using h(1,2,4) by (simp add: tangent_at_def)
    thus "\<exists>p q. 0 < p \<and> 0 < q \<and> tangent_at t s p q"
      using t0 s0 by (intro exI[of _ "t/2"] exI[of _ "s/2"]) simp
  next
    assume "\<exists>p q. 0 < p \<and> 0 < q \<and> tangent_at t s p q"
    then obtain p q where pq: "0 < p" "0 < q" and a: "p * q = 1 / 8" and b: "p / t + q / s = 1"
      and c: "DERIV hyp p :> - s / t" by (auto simp: tangent_at_def)
    have p0: "p \<noteq> 0" using pq(1) by simp
    have "DERIV hyp p :> - 1 / (8 * p\<^sup>2)" using p0 by (rule hyp_deriv)
    hence "- 1 / (8 * p\<^sup>2) = - s / t" by (rule DERIV_unique[OF _ c])
    hence d: "s * (8 * p\<^sup>2) = t" using t0 p0 by (simp add: field_simps)
    have e: "p * s + q * t = t * s" using b t0 s0 by (simp add: field_simps)
    have qd: "q = 1 / (8 * p)" using a p0 by (simp add: field_simps)
    have f: "q * t = s * p"
    proof -
      have "q * t = 1 / (8 * p) * (s * (8 * p\<^sup>2))" using d qd by simp
      thus ?thesis using p0 by (simp add: field_simps power2_eq_square)
    qed
    have f': "q * t = p * s" using f by (simp add: mult.commute)
    have z1: "(t - 2 * p) * s = t * s - 2 * (p * s)" by (simp add: algebra_simps)
    have z: "(t - 2 * p) * s = 0" using e f' z1 by linarith
    hence "t - 2 * p = 0 \<or> s = 0" by simp
    hence t2: "t = 2 * p" using s0 by auto
    have "q * (2 * p) = s * p" using f t2 by simp
    hence q2: "q = s / 2" using p0 by (simp add: field_simps)
    have "p * s = 1 / 4" using a q2 by (simp add: field_simps)
    hence "t * s = 1 / 2" using t2 by (simp add: algebra_simps)
    thus "bisects t s" using bisects_iff t0 s0 by blast
  qed
qed

end
