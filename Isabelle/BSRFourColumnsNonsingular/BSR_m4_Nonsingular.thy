(*  Title:      BSR_m4_Nonsingular.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Algebraic core of Lemma "Nonsingular slice" (label nonsingular) of
    the paper "Every m x 4 biquadratic sum of squares is a sum of 3m-1 squares (5 <= m <= 16)" (2026, in preparation):
      (4)  A_i^t = A_i,  [A_i, A_j] = u_j u_i^t - u_i u_j^t
      (5)  K_12 (.) u_3 + K_23 (.) u_1 + K_31 (.) u_2 = 0,  K_ij = A_i u_j - A_j u_i,  v (.) w = v w^t + w v^t
      if u_1, u_2, u_3 are independent then K_ij = t_i u_j - t_j u_i, and the bordered maps
      Ahat_i (x, s) = (A_i x + s u_i, u_i . x + t_i s) commute pairwise.
*)

theory BSR_m4_Nonsingular
  imports "HOL-Analysis.Finite_Cartesian_Product" "HOL-Analysis.Linear_Algebra" "HOL-Analysis.Cartesian_Space"
begin

text \<open>Outer product, symmetrised product and the bilinear dot product (no conjugation: the paper works with
  \<open>J = I\<close> over \<open>\<complex>\<close>, so everything is stated over an arbitrary commutative ring or field).\<close>

definition outer :: "'a::comm_ring_1^'n \<Rightarrow> 'a^'n \<Rightarrow> 'a^'n^'n" where
  "outer v w = (\<chi> i j. v$i * w$j)"

definition symp :: "'a::comm_ring_1^'n \<Rightarrow> 'a^'n \<Rightarrow> 'a^'n^'n" where
  "symp v w = outer v w + outer w v"

definition dotv :: "'a::comm_ring_1^'n \<Rightarrow> 'a^'n \<Rightarrow> 'a" where
  "dotv v w = (\<Sum>k\<in>UNIV. v$k * w$k)"

definition comm :: "'a::comm_ring_1^'n^'n \<Rightarrow> 'a^'n^'n \<Rightarrow> 'a^'n^'n" where
  "comm A B = A ** B - B ** A"

definition bord :: "'a::comm_ring_1^'n^'n \<Rightarrow> 'a^'n \<Rightarrow> 'a \<Rightarrow> (('a^'n) \<times> 'a) \<Rightarrow> (('a^'n) \<times> 'a)" where
  "bord A u t = (\<lambda>(x, s). (A *v x + s *s u, dotv u x + t * s))"

subsection \<open>Auxiliary lemmas on matrices, outer products and the dot product\<close>

lemma mm_diff_l:
  fixes A B C :: "'a::comm_ring_1^'n^'n"
  shows "A ** (B - C) = A ** B - A ** C"
  by (simp add: vec_eq_iff matrix_matrix_mult_def sum_subtractf algebra_simps)

lemma mm_diff_r:
  fixes A B C :: "'a::comm_ring_1^'n^'n"
  shows "(B - C) ** A = B ** A - C ** A"
  by (simp add: vec_eq_iff matrix_matrix_mult_def sum_subtractf algebra_simps)

lemma mv_add:
  fixes A :: "'a::comm_ring_1^'n^'n"
  shows "A *v (x + y) = A *v x + A *v y"
  by (simp add: vec_eq_iff matrix_vector_mult_def sum.distrib algebra_simps)

lemma mv_add_l:
  fixes A B :: "'a::comm_ring_1^'n^'n"
  shows "(A + B) *v y = A *v y + B *v y"
  by (simp add: vec_eq_iff matrix_vector_mult_def sum.distrib algebra_simps)

lemma mv_sub_l:
  fixes A B :: "'a::comm_ring_1^'n^'n"
  shows "(A - B) *v y = A *v y - B *v y"
  by (simp add: vec_eq_iff matrix_vector_mult_def sum_subtractf algebra_simps)

lemma mv_smul:
  fixes A :: "'a::comm_ring_1^'n^'n"
  shows "A *v (c *s x) = c *s (A *v x)"
  by (simp add: vec_eq_iff matrix_vector_mult_def sum_distrib_left mult_ac)

lemma outer_mv:
  fixes v w x :: "'a::comm_ring_1^'n"
  shows "outer v w *v x = dotv w x *s v"
  by (simp add: vec_eq_iff matrix_vector_mult_def outer_def dotv_def sum_distrib_left mult_ac)

lemma mm_outer_l:
  fixes A :: "'a::comm_ring_1^'n^'n" and v w :: "'a^'n"
  shows "A ** outer v w = outer (A *v v) w"
  by (simp add: vec_eq_iff matrix_matrix_mult_def outer_def matrix_vector_mult_def sum_distrib_left mult_ac)

lemma mm_outer_r:
  fixes A :: "'a::comm_ring_1^'n^'n" and v w :: "'a^'n"
  shows "outer v w ** A = outer v (transpose A *v w)"
  by (simp add: vec_eq_iff matrix_matrix_mult_def outer_def matrix_vector_mult_def transpose_def
      sum_distrib_left mult_ac)

lemma comm_outer:
  fixes A :: "'a::comm_ring_1^'n^'n" and p q :: "'a^'n"
  assumes "transpose A = A"
  shows "comm A (outer p q) = outer (A *v p) q - outer p (A *v q)"
  by (simp add: comm_def mm_outer_l mm_outer_r assms)

lemma comm_sub_r:
  fixes A X Y :: "'a::comm_ring_1^'n^'n"
  shows "comm A (X - Y) = comm A X - comm A Y"
  unfolding comm_def mm_diff_l mm_diff_r by (simp add: algebra_simps)

lemma outer_diff_l:
  fixes a b c :: "'a::comm_ring_1^'n"
  shows "outer (a - b) c = outer a c - outer b c"
  by (simp add: vec_eq_iff outer_def algebra_simps)

lemma outer_diff_r:
  fixes a b c :: "'a::comm_ring_1^'n"
  shows "outer c (a - b) = outer c a - outer c b"
  by (simp add: vec_eq_iff outer_def algebra_simps)

lemma jac_gen:
  fixes A B C :: "'a::comm_ring_1^'n^'n"
  shows "comm A (comm B C) + comm B (comm C A) + comm C (comm A B) = 0"
  unfolding comm_def mm_diff_l mm_diff_r matrix_mul_assoc by (simp add: algebra_simps)

lemma dotv_comm: "dotv v w = dotv w v"
  by (simp add: dotv_def mult_ac)

lemma dotv_add_l: "dotv (x + y) z = dotv x z + dotv y z"
  by (simp add: dotv_def algebra_simps sum.distrib)

lemma dotv_add_r: "dotv z (x + y) = dotv z x + dotv z y"
  by (simp add: dotv_def algebra_simps sum.distrib)

lemma dotv_diff_l: "dotv (x - y) z = dotv x z - dotv y z"
  by (simp add: dotv_def algebra_simps sum_subtractf)

lemma dotv_diff_r: "dotv z (x - y) = dotv z x - dotv z y"
  by (simp add: dotv_def algebra_simps sum_subtractf)

lemma dotv_smul_l: "dotv (c *s x) y = c * dotv x y"
  by (simp add: dotv_def sum_distrib_left mult_ac)

lemma dotv_smul_r: "dotv x (c *s y) = c * dotv x y"
  by (simp add: dotv_def sum_distrib_left mult_ac)

lemma dotv_zero_r: "dotv x 0 = 0"
  by (simp add: dotv_def)

lemma dotv_mv:
  fixes A :: "'a::comm_ring_1^'n^'n" and u x :: "'a^'n"
  shows "dotv u (A *v x) = dotv (transpose A *v u) x"
proof -
  have "dotv u (A *v x) = (\<Sum>k\<in>UNIV. \<Sum>l\<in>UNIV. u$k * (A$k$l * x$l))"
    by (simp add: dotv_def matrix_vector_mult_def sum_distrib_left)
  also have "\<dots> = (\<Sum>l\<in>UNIV. \<Sum>k\<in>UNIV. u$k * (A$k$l * x$l))" by (rule sum.swap)
  also have "\<dots> = dotv (transpose A *v u) x"
    by (simp add: dotv_def matrix_vector_mult_def transpose_def sum_distrib_right sum_distrib_left mult_ac)
  finally show ?thesis .
qed

lemma dotv_zero_iff:
  fixes V :: "'a::comm_ring_1^'n"
  assumes h: "\<forall>x. dotv x V = 0"
  shows "V = 0"
proof (rule vec_eq_iff[THEN iffD2], rule allI)
  fix k
  have "dotv (\<chi> i. if i = k then 1 else 0) V = (\<Sum>i\<in>UNIV. (if i = k then 1 else 0) * V$i)"
    by (simp add: dotv_def)
  also have "\<dots> = (\<Sum>i\<in>UNIV. if i = k then V$i else 0)" by (rule sum.cong) auto
  also have "\<dots> = V$k" by (simp add: sum.delta)
  finally have "V$k = 0" using h by simp
  then show "V$k = 0$k" by simp
qed

lemma symp_eval:
  fixes x v w y :: "'a::comm_ring_1^'n"
  shows "dotv x (symp v w *v y) = dotv x v * dotv w y + dotv x w * dotv v y"
  by (simp add: symp_def mv_add_l outer_mv dotv_add_r dotv_smul_r mult_ac)

subsection \<open>Step 1: Jacobi's identity turns (4) into (5)\<close>

theorem jacobi_gives_5:
  fixes A1 A2 A3 :: "'a::comm_ring_1^'n^'n" and u1 u2 u3 :: "'a^'n"
  assumes s1: "transpose A1 = A1" and s2: "transpose A2 = A2" and s3: "transpose A3 = A3"
    and c12: "comm A1 A2 = outer u2 u1 - outer u1 u2"
    and c23: "comm A2 A3 = outer u3 u2 - outer u2 u3"
    and c31: "comm A3 A1 = outer u1 u3 - outer u3 u1"
  shows "symp (A1 *v u2 - A2 *v u1) u3 + symp (A2 *v u3 - A3 *v u2) u1 + symp (A3 *v u1 - A1 *v u3) u2 = 0"
proof -
  have G: "symp (A1 *v u2 - A2 *v u1) u3 + symp (A2 *v u3 - A3 *v u2) u1 + symp (A3 *v u1 - A1 *v u3) u2
      = - (comm A1 (comm A2 A3) + comm A2 (comm A3 A1) + comm A3 (comm A1 A2))"
    by (simp only: c12 c23 c31 comm_sub_r comm_outer[OF s1] comm_outer[OF s2] comm_outer[OF s3]
        symp_def outer_diff_l outer_diff_r; simp add: algebra_simps)
  show ?thesis using G jac_gen[of A1 A2 A3] by simp
qed

subsection \<open>Step 2: with independent \<open>u_i\<close>, (5) forces \<open>K_ij = t_i u_j - t_j u_i\<close>\<close>

text \<open>Dual vectors: independent vectors over a field have a dual triple.\<close>

lemma dual3:
  fixes u1 u2 u3 :: "'a::field^'n"
  assumes ind: "\<forall>a b c. a *s u1 + b *s u2 + c *s u3 = 0 \<longrightarrow> a = 0 \<and> b = 0 \<and> c = 0"
  shows "\<exists>d1 d2 d3. dotv d1 u1 = 1 \<and> dotv d1 u2 = 0 \<and> dotv d1 u3 = 0
                  \<and> dotv d2 u1 = 0 \<and> dotv d2 u2 = 1 \<and> dotv d2 u3 = 0
                  \<and> dotv d3 u1 = 0 \<and> dotv d3 u2 = 0 \<and> dotv d3 u3 = 1"
proof -
  obtain A :: "'a^3^'n" where Adef: "A = (\<chi> i. (vector [u1$i, u2$i, u3$i] :: 'a^3))" by blast
  have A1: "\<And>i. A$i$1 = u1$i" by (simp add: Adef vector_3)
  have A2: "\<And>i. A$i$2 = u2$i" by (simp add: Adef vector_3)
  have A3: "\<And>i. A$i$3 = u3$i" by (simp add: Adef vector_3)
  have ker: "\<forall>x. A *v x = 0 \<longrightarrow> x = 0"
  proof (intro allI impI)
    fix x :: "'a^3"
    assume h: "A *v x = 0"
    have "x$1 *s u1 + x$2 *s u2 + x$3 *s u3 = 0"
    proof (rule vec_eq_iff[THEN iffD2], rule allI)
      fix i
      have "(A *v x)$i = (x$1 *s u1 + x$2 *s u2 + x$3 *s u3)$i"
        by (simp add: matrix_vector_mult_def sum_3 A1 A2 A3 mult_ac)
      then show "(x$1 *s u1 + x$2 *s u2 + x$3 *s u3)$i = 0$i" using h by simp
    qed
    then have hx: "x$1 = 0 \<and> x$2 = 0 \<and> x$3 = 0" using ind by blast
    show "x = 0" using hx by (auto simp: vec_eq_iff forall_3)
  qed
  then have "\<exists>B::'a^'n^3. B ** A = mat 1" by (simp add: matrix_left_invertible_ker)
  then obtain B :: "'a^'n^3" where B: "B ** A = mat 1" by blast
  have g1: "\<And>i. dotv (B$i) u1 = (B ** A)$i$1"
    by (simp add: dotv_def matrix_matrix_mult_def A1)
  have g2: "\<And>i. dotv (B$i) u2 = (B ** A)$i$2"
    by (simp add: dotv_def matrix_matrix_mult_def A2)
  have g3: "\<And>i. dotv (B$i) u3 = (B ** A)$i$3"
    by (simp add: dotv_def matrix_matrix_mult_def A3)
  have n12: "(1::3) \<noteq> 2"
  proof
    assume e: "(1::3) = 2"
    have "(vector [0, 1, 2::nat]::nat^3)$(1::3) = (vector [0, 1, 2::nat]::nat^3)$(2::3)"
      by (rule arg_cong[where f = "\<lambda>k. (vector [0, 1, 2::nat]::nat^3)$k", OF e])
    then show False by (simp add: vector_3)
  qed
  have n13: "(1::3) \<noteq> 3"
  proof
    assume e: "(1::3) = 3"
    have "(vector [0, 1, 2::nat]::nat^3)$(1::3) = (vector [0, 1, 2::nat]::nat^3)$(3::3)"
      by (rule arg_cong[where f = "\<lambda>k. (vector [0, 1, 2::nat]::nat^3)$k", OF e])
    then show False by (simp add: vector_3)
  qed
  have n23: "(2::3) \<noteq> 3"
  proof
    assume e: "(2::3) = 3"
    have "(vector [0, 1, 2::nat]::nat^3)$(2::3) = (vector [0, 1, 2::nat]::nat^3)$(3::3)"
      by (rule arg_cong[where f = "\<lambda>k. (vector [0, 1, 2::nat]::nat^3)$k", OF e])
    then show False by (simp add: vector_3)
  qed
  have n21: "(2::3) \<noteq> 1" using n12 by (rule not_sym)
  have n31: "(3::3) \<noteq> 1" using n13 by (rule not_sym)
  have n32: "(3::3) \<noteq> 2" using n23 by (rule not_sym)
  show ?thesis
    apply (rule exI[of _ "B$1"], rule exI[of _ "B$2"], rule exI[of _ "B$3"])
    by (simp add: g1 g2 g3 B mat_def n12 n13 n23 n21 n31 n32)
qed

lemma expand_vec:
  fixes u1 u2 u3 d1 d2 d3 K :: "'a::comm_ring_1^'n"
  assumes h11: "dotv d1 u1 = 1" and h12: "dotv d1 u2 = 0" and h13: "dotv d1 u3 = 0"
    and h21: "dotv d2 u1 = 0" and h22: "dotv d2 u2 = 1" and h23: "dotv d2 u3 = 0"
    and h31: "dotv d3 u1 = 0" and h32: "dotv d3 u2 = 0" and h33: "dotv d3 u3 = 1"
    and hyp: "\<forall>x. dotv (x - dotv x u1 *s d1 - dotv x u2 *s d2 - dotv x u3 *s d3) K = 0"
  shows "K = dotv K d1 *s u1 + dotv K d2 *s u2 + dotv K d3 *s u3"
proof -
  have c1: "dotv d1 K = dotv K d1" by (rule dotv_comm)
  have c2: "dotv d2 K = dotv K d2" by (rule dotv_comm)
  have c3: "dotv d3 K = dotv K d3" by (rule dotv_comm)
  have z: "\<forall>x. dotv x (K - (dotv K d1 *s u1 + dotv K d2 *s u2 + dotv K d3 *s u3)) = 0"
  proof
    fix x
    have e: "dotv (x - dotv x u1 *s d1 - dotv x u2 *s d2 - dotv x u3 *s d3) K = 0" using hyp by blast
    have "dotv x (K - (dotv K d1 *s u1 + dotv K d2 *s u2 + dotv K d3 *s u3))
        = dotv (x - dotv x u1 *s d1 - dotv x u2 *s d2 - dotv x u3 *s d3) K"
      by (simp only: dotv_diff_l dotv_diff_r dotv_add_r dotv_smul_l dotv_smul_r c1 c2 c3; simp add: algebra_simps)
    then show "dotv x (K - (dotv K d1 *s u1 + dotv K d2 *s u2 + dotv K d3 *s u3)) = 0" using e by simp
  qed
  have "K - (dotv K d1 *s u1 + dotv K d2 *s u2 + dotv K d3 *s u3) = 0" by (rule dotv_zero_iff[OF z])
  then show ?thesis by (rule iffD1[OF right_minus_eq])
qed

theorem five_gives_K:
  fixes K12 K23 K31 u1 u2 u3 :: "'a::field^'n"
  assumes two: "(2::'a) \<noteq> 0"
    and ind: "\<forall>a b c. a *s u1 + b *s u2 + c *s u3 = 0 \<longrightarrow> a = 0 \<and> b = 0 \<and> c = 0"
    and five: "symp K12 u3 + symp K23 u1 + symp K31 u2 = 0"
  shows "\<exists>t1 t2 t3. K12 = t1 *s u2 - t2 *s u1 \<and> K23 = t2 *s u3 - t3 *s u2 \<and> K31 = t3 *s u1 - t1 *s u3"
proof -
  obtain d1 d2 d3 where h11: "dotv d1 u1 = 1" and h12: "dotv d1 u2 = 0" and h13: "dotv d1 u3 = 0"
    and h21: "dotv d2 u1 = 0" and h22: "dotv d2 u2 = 1" and h23: "dotv d2 u3 = 0"
    and h31: "dotv d3 u1 = 0" and h32: "dotv d3 u2 = 0" and h33: "dotv d3 u3 = 1"
    using dual3[OF ind] by blast
  have r11: "dotv u1 d1 = 1" using h11 by (metis dotv_comm)
  have r12: "dotv u2 d1 = 0" using h12 by (metis dotv_comm)
  have r13: "dotv u3 d1 = 0" using h13 by (metis dotv_comm)
  have r21: "dotv u1 d2 = 0" using h21 by (metis dotv_comm)
  have r22: "dotv u2 d2 = 1" using h22 by (metis dotv_comm)
  have r23: "dotv u3 d2 = 0" using h23 by (metis dotv_comm)
  have r31: "dotv u1 d3 = 0" using h31 by (metis dotv_comm)
  have r32: "dotv u2 d3 = 0" using h32 by (metis dotv_comm)
  have r33: "dotv u3 d3 = 1" using h33 by (metis dotv_comm)
  have cA1: "dotv d1 K12 = dotv K12 d1" by (rule dotv_comm)
  have cA2: "dotv d2 K12 = dotv K12 d2" by (rule dotv_comm)
  have cA3: "dotv d3 K12 = dotv K12 d3" by (rule dotv_comm)
  have cB1: "dotv d1 K23 = dotv K23 d1" by (rule dotv_comm)
  have cB2: "dotv d2 K23 = dotv K23 d2" by (rule dotv_comm)
  have cB3: "dotv d3 K23 = dotv K23 d3" by (rule dotv_comm)
  have cC1: "dotv d1 K31 = dotv K31 d1" by (rule dotv_comm)
  have cC2: "dotv d2 K31 = dotv K31 d2" by (rule dotv_comm)
  have cC3: "dotv d3 K31 = dotv K31 d3" by (rule dotv_comm)
  note facts = h11 h12 h13 h21 h22 h23 h31 h32 h33 r11 r12 r13 r21 r22 r23 r31 r32 r33
    cA1 cA2 cA3 cB1 cB2 cB3 cC1 cC2 cC3
  have E: "\<forall>x y. dotv x K12 * dotv u3 y + dotv x u3 * dotv K12 y + dotv x K23 * dotv u1 y
      + dotv x u1 * dotv K23 y + dotv x K31 * dotv u2 y + dotv x u2 * dotv K31 y = 0"
  proof (intro allI)
    fix x y
    have "dotv x ((symp K12 u3 + symp K23 u1 + symp K31 u2) *v y) = 0" by (simp add: five dotv_def)
    then show "dotv x K12 * dotv u3 y + dotv x u3 * dotv K12 y + dotv x K23 * dotv u1 y
      + dotv x u1 * dotv K23 y + dotv x K31 * dotv u2 y + dotv x u2 * dotv K31 y = 0"
      by (simp add: mv_add_l dotv_add_r symp_eval add.assoc)
  qed
  have exP: "\<exists>Pf::'a^'n \<Rightarrow> 'a^'n. \<forall>x. Pf x = x - dotv x u1 *s d1 - dotv x u2 *s d2 - dotv x u3 *s d3"
    by (rule exI[of _ "\<lambda>x. x - dotv x u1 *s d1 - dotv x u2 *s d2 - dotv x u3 *s d3"]) simp
  then obtain Pf :: "'a^'n \<Rightarrow> 'a^'n"
    where Pf0: "\<forall>x. Pf x = x - dotv x u1 *s d1 - dotv x u2 *s d2 - dotv x u3 *s d3" by blast
  have Pf: "\<And>x. Pf x = x - dotv x u1 *s d1 - dotv x u2 *s d2 - dotv x u3 *s d3" using Pf0 by blast
  have Pu1: "\<And>x. dotv (Pf x) u1 = 0"
    by (simp add: Pf dotv_diff_l dotv_smul_l h11 h21 h31)
  have Pu2: "\<And>x. dotv (Pf x) u2 = 0"
    by (simp add: Pf dotv_diff_l dotv_smul_l h12 h22 h32)
  have Pu3: "\<And>x. dotv (Pf x) u3 = 0"
    by (simp add: Pf dotv_diff_l dotv_smul_l h13 h23 h33)
  have P12: "\<And>x. dotv (Pf x) K12 = 0"
  proof -
    fix x
    have "dotv (Pf x) K12 * dotv u3 d3 + dotv (Pf x) u3 * dotv K12 d3 + dotv (Pf x) K23 * dotv u1 d3
      + dotv (Pf x) u1 * dotv K23 d3 + dotv (Pf x) K31 * dotv u2 d3 + dotv (Pf x) u2 * dotv K31 d3 = 0"
      by (rule E[rule_format, where x = "Pf x" and y = d3])
    then show "dotv (Pf x) K12 = 0" by (simp add: Pu1 Pu2 Pu3 r33 r31 r32)
  qed
  have P23: "\<And>x. dotv (Pf x) K23 = 0"
  proof -
    fix x
    have "dotv (Pf x) K12 * dotv u3 d1 + dotv (Pf x) u3 * dotv K12 d1 + dotv (Pf x) K23 * dotv u1 d1
      + dotv (Pf x) u1 * dotv K23 d1 + dotv (Pf x) K31 * dotv u2 d1 + dotv (Pf x) u2 * dotv K31 d1 = 0"
      by (rule E[rule_format, where x = "Pf x" and y = d1])
    then show "dotv (Pf x) K23 = 0" by (simp add: Pu1 Pu2 Pu3 r11 r12 r13)
  qed
  have P31: "\<And>x. dotv (Pf x) K31 = 0"
  proof -
    fix x
    have "dotv (Pf x) K12 * dotv u3 d2 + dotv (Pf x) u3 * dotv K12 d2 + dotv (Pf x) K23 * dotv u1 d2
      + dotv (Pf x) u1 * dotv K23 d2 + dotv (Pf x) K31 * dotv u2 d2 + dotv (Pf x) u2 * dotv K31 d2 = 0"
      by (rule E[rule_format, where x = "Pf x" and y = d2])
    then show "dotv (Pf x) K31 = 0" by (simp add: Pu1 Pu2 Pu3 r21 r22 r23)
  qed
  have e12: "K12 = dotv K12 d1 *s u1 + dotv K12 d2 *s u2 + dotv K12 d3 *s u3"
    by (rule expand_vec[OF h11 h12 h13 h21 h22 h23 h31 h32 h33]) (simp add: Pf[symmetric] P12)
  have e23: "K23 = dotv K23 d1 *s u1 + dotv K23 d2 *s u2 + dotv K23 d3 *s u3"
    by (rule expand_vec[OF h11 h12 h13 h21 h22 h23 h31 h32 h33]) (simp add: Pf[symmetric] P23)
  have e31: "K31 = dotv K31 d1 *s u1 + dotv K31 d2 *s u2 + dotv K31 d3 *s u3"
    by (rule expand_vec[OF h11 h12 h13 h21 h22 h23 h31 h32 h33]) (simp add: Pf[symmetric] P31)
  have z1: "dotv K12 d3 = 0"
  proof -
    have s: "dotv K12 d3 + dotv K12 d3 = 0"
      using E[rule_format, where x = d3 and y = d3] by (simp only: facts mult_1_right mult_1_left mult_zero_left mult_zero_right add_0_right add_0_left)
    have "(2::'a) * dotv K12 d3 = 0" using s by (simp only: mult_2)
    then show ?thesis using two by simp
  qed
  have z2: "dotv K23 d1 = 0"
  proof -
    have s: "dotv K23 d1 + dotv K23 d1 = 0"
      using E[rule_format, where x = d1 and y = d1] by (simp only: facts mult_1_right mult_1_left mult_zero_left mult_zero_right add_0_right add_0_left)
    have "(2::'a) * dotv K23 d1 = 0" using s by (simp only: mult_2)
    then show ?thesis using two by simp
  qed
  have z3: "dotv K31 d2 = 0"
  proof -
    have s: "dotv K31 d2 + dotv K31 d2 = 0"
      using E[rule_format, where x = d2 and y = d2] by (simp only: facts mult_1_right mult_1_left mult_zero_left mult_zero_right add_0_right add_0_left)
    have "(2::'a) * dotv K31 d2 = 0" using s by (simp only: mult_2)
    then show ?thesis using two by simp
  qed
  have s1: "dotv K12 d1 + dotv K23 d3 = 0"
    using E[rule_format, where x = d3 and y = d1] by (simp only: facts; simp add: add.commute)
  have s2: "dotv K23 d2 + dotv K31 d1 = 0"
    using E[rule_format, where x = d1 and y = d2] by (simp only: facts; simp add: add.commute)
  have s3: "dotv K31 d3 + dotv K12 d2 = 0"
    using E[rule_format, where x = d2 and y = d3] by (simp only: facts; simp add: add.commute)
  have q1: "dotv K12 d1 = - dotv K23 d3" using s1 by (rule iffD2[OF eq_neg_iff_add_eq_0])
  have q2: "dotv K23 d2 = - dotv K31 d1" using s2 by (rule iffD2[OF eq_neg_iff_add_eq_0])
  have q3: "dotv K31 d3 = - dotv K12 d2" using s3 by (rule iffD2[OF eq_neg_iff_add_eq_0])
  show ?thesis
  proof (rule exI[of _ "dotv K12 d2"], rule exI[of _ "dotv K23 d3"], rule exI[of _ "dotv K31 d1"], intro conjI)
    show "K12 = dotv K12 d2 *s u2 - dotv K23 d3 *s u1"
      by (subst e12) (simp add: q1 z1 vec_eq_iff algebra_simps)
    show "K23 = dotv K23 d3 *s u3 - dotv K31 d1 *s u2"
      by (subst e23) (simp add: q2 z2 vec_eq_iff algebra_simps)
    show "K31 = dotv K31 d1 *s u1 - dotv K12 d2 *s u3"
      by (subst e31) (simp add: q3 z3 vec_eq_iff algebra_simps)
  qed
qed

subsection \<open>Step 3: the bordered maps commute\<close>

theorem bordered_commute:
  fixes Ai Aj :: "'a::comm_ring_1^'n^'n" and ui uj :: "'a^'n" and ti tj :: 'a
  assumes si: "transpose Ai = Ai" and sj: "transpose Aj = Aj"
    and cij: "comm Ai Aj = outer uj ui - outer ui uj"
    and kij: "Ai *v uj - Aj *v ui = ti *s uj - tj *s ui"
  shows "bord Ai ui ti \<circ> bord Aj uj tj = bord Aj uj tj \<circ> bord Ai ui ti"
proof (rule ext)
  fix p :: "('a^'n) \<times> 'a"
  obtain x s where p: "p = (x, s)" by (cases p)
  have h1: "(Ai ** Aj) *v x = (dotv ui x *s uj - dotv uj x *s ui) + (Aj ** Ai) *v x"
  proof -
    have "(Ai ** Aj) *v x - (Aj ** Ai) *v x = comm Ai Aj *v x" by (simp add: comm_def mv_sub_l)
    also have "\<dots> = dotv ui x *s uj - dotv uj x *s ui" by (simp add: cij mv_sub_l outer_mv)
    finally show ?thesis by (rule iffD1[OF diff_eq_eq])
  qed
  have h2: "Ai *v uj = (ti *s uj - tj *s ui) + Aj *v ui" by (rule iffD1[OF diff_eq_eq kij])
  have F: "Ai *v (Aj *v x + s *s uj) + (dotv uj x + tj * s) *s ui
         = Aj *v (Ai *v x + s *s ui) + (dotv ui x + ti * s) *s uj"
    by (simp add: mv_add mv_smul matrix_vector_mul_assoc h1 h2 vec_eq_iff algebra_simps)
  have a1: "dotv ui (Aj *v x) = dotv (Aj *v ui) x" by (simp add: dotv_mv sj)
  have a2: "dotv uj (Ai *v x) = dotv (Ai *v uj) x" by (simp add: dotv_mv si)
  have a3: "dotv (Ai *v uj) x = dotv (Aj *v ui) x + (ti * dotv uj x - tj * dotv ui x)"
    by (simp add: h2 dotv_add_l dotv_diff_l dotv_smul_l)
  have a4: "dotv ui uj = dotv uj ui" by (rule dotv_comm)
  have S: "dotv ui (Aj *v x + s *s uj) + ti * (dotv uj x + tj * s)
         = dotv uj (Ai *v x + s *s ui) + tj * (dotv ui x + ti * s)"
    by (simp add: dotv_add_r dotv_smul_r a1 a2 a3 a4 algebra_simps)
  show "(bord Ai ui ti \<circ> bord Aj uj tj) p = (bord Aj uj tj \<circ> bord Ai ui ti) p"
    by (simp add: p bord_def comp_def F S)
qed

subsection \<open>Assembly: (4) and independence give commuting bordered maps\<close>

theorem nonsingular_slice_core:
  fixes A1 A2 A3 :: "'a::field^'n^'n" and u1 u2 u3 :: "'a^'n"
  assumes two: "(2::'a) \<noteq> 0"
    and s1: "transpose A1 = A1" and s2: "transpose A2 = A2" and s3: "transpose A3 = A3"
    and c12: "comm A1 A2 = outer u2 u1 - outer u1 u2"
    and c23: "comm A2 A3 = outer u3 u2 - outer u2 u3"
    and c31: "comm A3 A1 = outer u1 u3 - outer u3 u1"
    and ind: "\<forall>a b c. a *s u1 + b *s u2 + c *s u3 = 0 \<longrightarrow> a = 0 \<and> b = 0 \<and> c = 0"
  shows "\<exists>t1 t2 t3. bord A1 u1 t1 \<circ> bord A2 u2 t2 = bord A2 u2 t2 \<circ> bord A1 u1 t1
                  \<and> bord A2 u2 t2 \<circ> bord A3 u3 t3 = bord A3 u3 t3 \<circ> bord A2 u2 t2
                  \<and> bord A3 u3 t3 \<circ> bord A1 u1 t1 = bord A1 u1 t1 \<circ> bord A3 u3 t3"
proof -
  have J: "symp (A1 *v u2 - A2 *v u1) u3 + symp (A2 *v u3 - A3 *v u2) u1 + symp (A3 *v u1 - A1 *v u3) u2 = 0"
    by (rule jacobi_gives_5[OF s1 s2 s3 c12 c23 c31])
  obtain t1 t2 t3 where k12: "A1 *v u2 - A2 *v u1 = t1 *s u2 - t2 *s u1"
    and k23: "A2 *v u3 - A3 *v u2 = t2 *s u3 - t3 *s u2"
    and k31: "A3 *v u1 - A1 *v u3 = t3 *s u1 - t1 *s u3"
    using five_gives_K[OF two ind J] by blast
  have b12: "bord A1 u1 t1 \<circ> bord A2 u2 t2 = bord A2 u2 t2 \<circ> bord A1 u1 t1"
    by (rule bordered_commute[where Ai = A1 and Aj = A2 and ui = u1 and uj = u2 and ti = t1 and tj = t2,
        OF s1 s2 c12 k12])
  have b23: "bord A2 u2 t2 \<circ> bord A3 u3 t3 = bord A3 u3 t3 \<circ> bord A2 u2 t2"
    by (rule bordered_commute[where Ai = A2 and Aj = A3 and ui = u2 and uj = u3 and ti = t2 and tj = t3,
        OF s2 s3 c23 k23])
  have b31: "bord A3 u3 t3 \<circ> bord A1 u1 t1 = bord A1 u1 t1 \<circ> bord A3 u3 t3"
    by (rule bordered_commute[where Ai = A3 and Aj = A1 and ui = u3 and uj = u1 and ti = t3 and tj = t1,
        OF s3 s1 c31 k31])
  show ?thesis using b12 b23 b31 by blast
qed

end
