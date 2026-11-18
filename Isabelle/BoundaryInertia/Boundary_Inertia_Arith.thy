(*  Title:      Boundary_Inertia_Arith.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   The arithmetic of the paper "Boundary inertia and sums of squares of biquadratic forms"
   (C. Marín, 2026, in preparation), reduced to its simplest form.

   (1) The boundary inertia inequality  N q <= M - 1 - C(N+1,2)  is the Barvinok--Pataki count shifted by the negative
       index:  N (q - 1) + C(N+2,2) <= M  (stated doubled, to stay in the integers).
   (2) For m x 4 biquadratic forms, M = 5 m (m+1) and N = 3 m - 1, the inequality becomes  2 (3m - 1)(q - 1) <= m (m + 7).
   (3) For m >= 5 this is equivalent to  6 q <= m + 13,  i.e.  q <= floor((m+13)/6).
   (4) The m-independent counts of the proof: singular-point incidence M - 2, compression 3m - 2, the Psi counts. *)
theory Boundary_Inertia_Arith
  imports Main
begin

text \<open>(1) Inertia inequality in Barvinok--Pataki form (doubled: 2 C(k,2) = k (k-1)).\<close>
lemma inertia_pataki_form:
  fixes N q M :: int
  shows "2*N*q \<le> 2*M - 2 - N*(N+1) \<longleftrightarrow> 2*N*(q-1) + (N+2)*(N+1) \<le> 2*M"
  by (auto simp: algebra_simps)

text \<open>With q = 1 the right-hand side is the Pataki condition C(N+2,2) <= M.\<close>
lemma inertia_q1_is_pataki:
  fixes N M :: int
  shows "2*N*(1-1) + (N+2)*(N+1) \<le> 2*M \<longleftrightarrow> (N+2)*(N+1) \<le> 2*M"
  by simp

text \<open>(2) The m x 4 specialisation: 2 M - (N+2)(N+1) = m (m+7) for M = 5 m (m+1), N = 3 m - 1.\<close>
lemma m4_room:
  fixes m :: int
  shows "2*(5*m*(m+1)) - (3*m+1)*(3*m) = m*(m+7)"
  by (simp add: algebra_simps)

lemma inertia_m4:
  fixes m q :: int
  shows "2*(3*m-1)*(q-1) + (3*m+1)*(3*m) \<le> 2*(5*m*(m+1)) \<longleftrightarrow> 2*(3*m-1)*(q-1) \<le> m*(m+7)"
  by (auto simp: algebra_simps)

text \<open>(3) For m >= 5 the bound is exactly 6 q <= m + 13. Put t = q - 1; then the claim is
  2 (3m-1) t <= m (m+7)  iff  6 t <= m + 7.\<close>
lemma floor_core:
  fixes m t :: int
  assumes m: "m \<ge> 5"
  shows "2*(3*m-1)*t \<le> m*(m+7) \<longleftrightarrow> 6*t \<le> m + 7"
proof
  assume h: "2*(3*m-1)*t \<le> m*(m+7)"
  show "6*t \<le> m + 7"
  proof (rule ccontr)
    assume "\<not> 6*t \<le> m + 7"
    then have a: "m + 8 \<le> 6*t" by simp
    have p: "0 \<le> 3*m - 1" using m by simp
    have b: "(3*m-1)*(m+8) \<le> (3*m-1)*(6*t)" using mult_left_mono[OF a p] .
    have c: "(3*m-1)*(m+8) = 3*(m*(m+7)) + (2*m - 8)" by (simp add: algebra_simps)
    have d: "(3*m-1)*(6*t) = 3*(2*(3*m-1)*t)" by (simp add: algebra_simps)
    from b c d have "3*(m*(m+7)) + (2*m - 8) \<le> 3*(2*(3*m-1)*t)" by simp
    with h m show False by simp
  qed
next
  assume h: "6*t \<le> m + 7"
  have p: "0 \<le> 3*m - 1" using m by simp
  have b: "(3*m-1)*(6*t) \<le> (3*m-1)*(m+7)" using mult_left_mono[OF h p] .
  have c: "(3*m-1)*(6*t) = 3*(2*(3*m-1)*t)" by (simp add: algebra_simps)
  have d: "(3*m-1)*(m+7) = 3*(m*(m+7)) - (m+7)" by (simp add: algebra_simps)
  from b c d have "3*(2*(3*m-1)*t) \<le> 3*(m*(m+7)) - (m+7)" by simp
  with m show "2*(3*m-1)*t \<le> m*(m+7)" by simp
qed

lemma inertia_m4_floor:
  fixes m q :: int
  assumes "m \<ge> 5"
  shows "2*(3*m-1)*(q-1) \<le> m*(m+7) \<longleftrightarrow> 6*q \<le> m + 13"
  using floor_core[OF assms, of "q-1"] by (simp add: algebra_simps)

text \<open>The values: q <= 3 for m = 5..10, q <= 4 for m = 11..16, and 5 at m = 17.\<close>
lemma q_values:
  "\<forall>m::int \<in> {5..10}. (m+13) div 6 = 3" "\<forall>m::int \<in> {11..16}. (m+13) div 6 = 4" "(17+13) div 6 = (5::int)"
  by eval+

text \<open>(4) Counts that do not depend on m.\<close>
lemma incidence: fixes M m :: int shows "M - 2*(m+3) + 2*((m-1)+3) = M - 2" by simp
lemma compression_count: fixes a m :: int shows "(4*a - (a+1)) + (3*(m-a) - 1) = 3*m - 2" by simp
lemma psi_counts: fixes m :: int shows "4*(m+1) - (m-1) = 3*m + 5" "4*m - (m-1) = 3*m + 1" by simp_all

end
