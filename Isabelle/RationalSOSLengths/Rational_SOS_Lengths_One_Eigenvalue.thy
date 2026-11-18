(*  Title:      Rational_SOS_Lengths_One_Eigenvalue.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Rational sums-of-squares lengths of biquadratic forms: Lagrange's identity, quaternion columns and
   skew determinants. Pieces of Section "One interior eigenvalue" of the paper
   "Rational sums-of-squares lengths of biquadratic forms and orthogonal dilations" (Carles Marín, in preparation).
   F1: Lagrange's identity, so a plane in I_3 has determinant a sum of three squares (Lemma 6.4).
   F2: the columns of the left multiplication by a quaternion are orthogonal of norm N, so N I_4 = I_4 when N is a
       sum of four squares (Theorem 6.11, upper bound).
   F3: det(delta I + S^2) for a skew 2x2 and 3x3 matrix S (Proposition 6.5 for d <= 3).
*)
theory Rational_SOS_Lengths_One_Eigenvalue
  imports Main
begin

section \<open>F1: planes in the sum of three squares\<close>

lemma lagrange_three:
  fixes a b c e f g :: "'a::comm_ring_1"
  shows "(a^2 + b^2 + c^2) * (e^2 + f^2 + g^2) - (a * e + b * f + c * g)^2
       = (b * g - c * f)^2 + (c * e - a * g)^2 + (a * f - b * e)^2"
  by (simp add: power2_eq_square algebra_simps)

corollary plane_gram_three_squares:
  fixes a b c e f g :: "'a::comm_ring_1"
  shows "\<exists>u v w. (a^2 + b^2 + c^2) * (e^2 + f^2 + g^2) - (a * e + b * f + c * g)^2 = u^2 + v^2 + w^2"
  using lagrange_three by blast

section \<open>F2: quaternion multiplication\<close>

definition dot4 :: "'a \<times> 'a \<times> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a \<times> 'a \<Rightarrow> 'a::comm_ring_1" where
  "dot4 u v = (case u of (u1, u2, u3, u4) \<Rightarrow> case v of (v1, v2, v3, v4) \<Rightarrow> u1 * v1 + u2 * v2 + u3 * v3 + u4 * v4)"

lemma quaternion_columns:
  fixes a b c d :: "'a::comm_ring_1"
  defines "N \<equiv> a^2 + b^2 + c^2 + d^2"
  shows "dot4 (a, b, c, d) (a, b, c, d) = N" and "dot4 (-b, a, d, -c) (-b, a, d, -c) = N"
    and "dot4 (-c, -d, a, b) (-c, -d, a, b) = N" and "dot4 (-d, c, -b, a) (-d, c, -b, a) = N"
    and "dot4 (a, b, c, d) (-b, a, d, -c) = 0" and "dot4 (a, b, c, d) (-c, -d, a, b) = 0"
    and "dot4 (a, b, c, d) (-d, c, -b, a) = 0" and "dot4 (-b, a, d, -c) (-c, -d, a, b) = 0"
    and "dot4 (-b, a, d, -c) (-d, c, -b, a) = 0" and "dot4 (-c, -d, a, b) (-d, c, -b, a) = 0"
  by (simp_all add: N_def dot4_def power2_eq_square algebra_simps)

section \<open>F3: the determinant of delta I + S^2 for small skew S\<close>

lemma skew_two:
  fixes d s :: "'a::comm_ring_1"
  shows "(d - s^2) * (d - s^2) - 0 * 0 = (d - s^2)^2"
  by (simp add: power2_eq_square)

text \<open>For $S$ with entries $S_{12}=x$, $S_{13}=y$, $S_{23}=z$ one has
  $S^2 = \begin{pmatrix}-x^2-y^2&-yz&xz\\-yz&-x^2-z^2&-xy\\xz&-xy&-y^2-z^2\end{pmatrix}$, and the cofactor expansion of
  $\delta I+S^2$ gives $\delta(\delta-x^2-y^2-z^2)^2$.\<close>

lemma skew_three:
  fixes d x y z :: "'a::comm_ring_1"
  defines "m11 \<equiv> d - x^2 - y^2" and "m12 \<equiv> - (y * z)" and "m13 \<equiv> x * z"
    and "m22 \<equiv> d - x^2 - z^2" and "m23 \<equiv> - (x * y)" and "m33 \<equiv> d - y^2 - z^2"
  shows "m11 * (m22 * m33 - m23 * m23) - m12 * (m12 * m33 - m23 * m13) + m13 * (m12 * m23 - m22 * m13)
       = d * (d - x^2 - y^2 - z^2)^2"
  by (simp add: m11_def m12_def m13_def m22_def m23_def m33_def power2_eq_square algebra_simps)

end
