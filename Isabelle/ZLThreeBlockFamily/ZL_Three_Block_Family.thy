(*  Title:      ZL_Three_Block_Family.thy
    Author:     Carles Marin
    Copyright (c) 2026 Carles Marin. All rights reserved.
    License:    BSD

    The algebraic part of Proposition 6.3 of C. Marin, Why three blocks? (Zenodo,
    doi:10.5281/zenodo.23778502): for the three-block family with block sizes x >= y >= z >= 1,
    n = x + y + z, the two closed forms of the deficit n/3 - 1/2 - M and their non-negativity.
    Not formalized here: that M is the value of the family (the construction and the weight bound)
    and the maximum over x + y + z = n with its maximizers.
*)
theory ZL_Three_Block_Family
  imports Complex_Main
begin

text \<open>Case 1 (regime z(x - 1) >= y(y - 1)): s = y + z, M = (s - 1)((x - 1)s + yz)/(s(n - 2)) and
eta = x - (y + z)/2. Case 2 (otherwise): u = x + y - 2, M = (u + 1)(zu + (x - 1)(y - 1))/(u(n - 1)) and
eta = (x + y)/2 - z.\<close>

definition M1 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "M1 x y z = ((y+z-1) * ((x-1)*(y+z) + y*z)) / ((y+z) * (x+y+z-2))"

definition M2 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "M2 x y z = ((x+y-2+1) * (z*(x+y-2) + (x-1)*(y-1))) / ((x+y-2) * (x+y+z-1))"

definition eta1 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "eta1 x y z = x - (y+z)/2"

definition eta2 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "eta2 x y z = (x+y)/2 - z"

section \<open>The two identities\<close>

theorem identity_case1:
  fixes x y z :: real
  assumes "x+y+z-2 \<noteq> 0" and "y+z \<noteq> 0"
  shows "(x+y+z)/3 - 1/2 - M1 x y z =
     eta1 x y z * (2 * eta1 x y z - 1) / (6 * (x+y+z-2))
     + (y+z-1) * (y-z)^2 / (4 * (y+z) * (x+y+z-2))"
  using assms unfolding M1_def eta1_def
  by (simp add: divide_simps) (simp add: algebra_simps power2_eq_square)

theorem identity_case2:
  fixes x y z :: real
  assumes "x+y+z-1 \<noteq> 0" and "x+y-2 \<noteq> 0"
  shows "(x+y+z)/3 - 1/2 - M2 x y z =
     eta2 x y z * (2 * eta2 x y z - 1) / (6 * (x+y+z-1))
     + (x+y-2+1) * (x-y)^2 / (4 * (x+y-2) * (x+y+z-1))"
  using assms unfolding M2_def eta2_def
  by (simp add: divide_simps) (simp add: algebra_simps power2_eq_square)

section \<open>Non-negativity of the terms\<close>

lemma half_integer_term:
  fixes e :: real and k :: nat
  assumes "2 * e = real k"
  shows "e * (2 * e - 1) \<ge> 0"
proof (cases "k = 0")
  case True
  with assms have "e = 0" by simp
  then show ?thesis by simp
next
  case False
  then have "real k \<ge> 1" by simp
  with assms have "e \<ge> 1/2" by simp
  moreover from assms have "2 * e - 1 = real k - 1" by simp
  ultimately show ?thesis using \<open>real k \<ge> 1\<close> assms by (simp add: mult_nonneg_nonneg)
qed

lemma quad_term:
  fixes s u d n :: real
  assumes "s > 1" and "n > 2" and "u > 0"
  shows "(s-1) * d^2 / (4 * s * (n-2)) \<ge> 0"
    and "(u+1) * d^2 / (4 * u * (n-1)) \<ge> 0"
proof -
  have "4 * s * (n-2) > 0" using assms by (simp add: mult_pos_pos)
  moreover have "(s-1) * d^2 \<ge> 0" using assms by simp
  ultimately show "(s-1) * d^2 / (4 * s * (n-2)) \<ge> 0" by (simp add: divide_nonneg_nonneg)
next
  have "4 * u * (n-1) > 0" using assms by (simp add: mult_pos_pos)
  moreover have "(u+1) * d^2 \<ge> 0" using assms by simp
  ultimately show "(u+1) * d^2 / (4 * u * (n-1)) \<ge> 0" by (simp add: divide_nonneg_nonneg)
qed

section \<open>The deficit is non-negative\<close>

text \<open>For integer block sizes x >= y >= z >= 1 (the ordering is a hypothesis, as in the paper).\<close>

theorem deficit_case1:
  fixes x y z :: nat
  assumes "x \<ge> y" and "y \<ge> z" and "z \<ge> 1"
  shows "(real x + real y + real z)/3 - 1/2 - M1 (real x) (real y) (real z) \<ge> 0"
proof -
  have s1: "real y + real z > 1" using assms by simp
  have n2: "real x + real y + real z > 2" using assms by simp
  have id: "(real x + real y + real z)/3 - 1/2 - M1 (real x) (real y) (real z) =
     eta1 (real x) (real y) (real z) * (2 * eta1 (real x) (real y) (real z) - 1) / (6 * (real x + real y + real z - 2))
     + (real y + real z - 1) * (real y - real z)^2 / (4 * (real y + real z) * (real x + real y + real z - 2))"
    using identity_case1[where x = "real x" and y = "real y" and z = "real z"] s1 n2 by simp
  have "2 * eta1 (real x) (real y) (real z) = real (2 * x - y - z)"
    using assms unfolding eta1_def by (simp add: of_nat_diff algebra_simps)
  then have h: "eta1 (real x) (real y) (real z) * (2 * eta1 (real x) (real y) (real z) - 1) \<ge> 0"
    by (rule half_integer_term)
  have t1: "eta1 (real x) (real y) (real z) * (2 * eta1 (real x) (real y) (real z) - 1) / (6 * (real x + real y + real z - 2)) \<ge> 0"
    using h n2 by (simp add: divide_nonneg_pos)
  have t2: "(real y + real z - 1) * (real y - real z)^2 / (4 * (real y + real z) * (real x + real y + real z - 2)) \<ge> 0"
    using quad_term(1)[where s = "real y + real z" and n = "real x + real y + real z" and u = 1 and d = "real y - real z"] s1 n2
    by (simp add: mult.assoc)
  show ?thesis using id t1 t2 by linarith
qed

theorem deficit_case2:
  fixes x y z :: nat
  assumes "x \<ge> y" and "y \<ge> z" and "z \<ge> 1" and "y \<ge> 2"
  shows "(real x + real y + real z)/3 - 1/2 - M2 (real x) (real y) (real z) \<ge> 0"
proof -
  have u0: "real x + real y - 2 > 0" using assms by simp
  have n1: "real x + real y + real z - 1 > 0" using assms by simp
  have id: "(real x + real y + real z)/3 - 1/2 - M2 (real x) (real y) (real z) =
     eta2 (real x) (real y) (real z) * (2 * eta2 (real x) (real y) (real z) - 1) / (6 * (real x + real y + real z - 1))
     + (real x + real y - 2 + 1) * (real x - real y)^2 / (4 * (real x + real y - 2) * (real x + real y + real z - 1))"
    using identity_case2[where x = "real x" and y = "real y" and z = "real z"] u0 n1 by simp
  have "2 * eta2 (real x) (real y) (real z) = real (x + y - 2 * z)"
    using assms unfolding eta2_def by (simp add: of_nat_diff algebra_simps)
  then have h: "eta2 (real x) (real y) (real z) * (2 * eta2 (real x) (real y) (real z) - 1) \<ge> 0"
    by (rule half_integer_term)
  have t1: "eta2 (real x) (real y) (real z) * (2 * eta2 (real x) (real y) (real z) - 1) / (6 * (real x + real y + real z - 1)) \<ge> 0"
    using h n1 by (simp add: divide_nonneg_pos)
  have t2: "(real x + real y - 2 + 1) * (real x - real y)^2 / (4 * (real x + real y - 2) * (real x + real y + real z - 1)) \<ge> 0"
    using quad_term(2)[where u = "real x + real y - 2" and n = "real x + real y + real z" and s = 2 and d = "real x - real y"] u0 n1
    by (simp add: mult.assoc)
  show ?thesis using id t1 t2 by linarith
qed

end
