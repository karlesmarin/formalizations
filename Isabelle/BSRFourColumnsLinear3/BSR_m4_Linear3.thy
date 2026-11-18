(*  Title:      BSR_m4_Linear3.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Third batch of elementary pieces of the paper "Boundary inertia and sums of squares of biquadratic forms"
   (C. Marín, 2026, in preparation).

   (1) symmetric_4linear_polarization, symmetric_5linear_polarization: a fully symmetric 4- (5-) linear form over a
       field of characteristic 0 with vanishing diagonal is zero (Lemma "Invariant extension of an isotropic plane";
       R = <B_c p_d, B_e p_f> and U = <B_i B_j p_k, B_l p_m>).
   (2) positive_averaging: sum over pairs i<j of (h_i + h_j) = (n-1) sum h_i, its consequence, and the
       "as n >= 3 all diagonal terms vanish" step of Lemma "Positive annihilator".
   (3) rank_le_one_space_full: a set of n x k matrices closed under addition, all of whose 2 x 2 minors vanish, has a
       common image line or a common covector line (Lemma "Small tableaux", s = 3).
   (4) support_count_inequality: arithmetic of the upper bound in Lemma "Support bounds".
   Not formalized: the projective dimension theorem itself (needs algebraic geometry), the general k-linear
   polarization (only k = 4, 5 are done, by descent to the trilinear case), and everything involving inner products
   of the paper's spaces. *)
theory BSR_m4_Linear3
  imports Complex_Main
begin

section \<open>(1) Polarization of symmetric 4- and 5-linear forms\<close>

text \<open>The trilinear case (copied from session 241): B is additive in the first argument and symmetric under the
  adjacent transpositions, the target is a field of characteristic 0. Then the diagonal controls everything.\<close>

theorem symmetric_trilinear_polarization:
  fixes B :: "'v::ab_group_add \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'k::field_char_0"
  assumes add1: "\<And>x x' y z. B (x + x') y z = B x y z + B x' y z"
    and s12: "\<And>x y z. B x y z = B y x z"
    and s23: "\<And>x y z. B x y z = B x z y"
    and diag: "\<And>x. B x x x = 0"
  shows "B x y z = 0"
proof -
  have add2: "\<And>x y y' z. B x (y + y') z = B x y z + B x y' z" using add1 s12 by metis
  have add3: "\<And>x y z z'. B x y (z + z') = B x y z + B x y z'" using add2 s23 by metis
  have cube: "B (u+v) (u+v) (u+v) = B u u u + B v v v + 3 * B u u v + 3 * B u v v" for u v
  proof -
    have e1: "B u v u = B u u v" using s23 by metis
    have e2: "B v u u = B u u v" using s12 e1 by metis
    have e3: "B v u v = B u v v" using s12 by metis
    have e4: "B v v u = B u v v" using s23 e3 by metis
    show ?thesis by (simp add: add1 add2 add3 e1 e2 e3 e4 algebra_simps)
  qed
  have quad: "B (x+y) (x+y) z = B x x z + 2 * B x y z + B y y z"
    by (simp add: add1 add2 algebra_simps s12[of y x z])
  have lin: "B (x+y) z z = B x z z + B y z z" by (rule add1)
  have c1: "B (x+y+z) (x+y+z) (x+y+z) = B (x+y) (x+y) (x+y) + B z z z + 3 * B (x+y) (x+y) z + 3 * B (x+y) z z"
    by (rule cube)
  have c2: "B (x+z) (x+z) (x+z) = B x x x + B z z z + 3 * B x x z + 3 * B x z z" by (rule cube)
  have c3: "B (y+z) (y+z) (y+z) = B y y y + B z z z + 3 * B y y z + 3 * B y z z" by (rule cube)
  have hz: "B x x z + B x z z = 0"
  proof -
    have "3 * (B x x z + B x z z) = 0" using c2 diag[of "x+z"] diag[of x] diag[of z] by (simp add: algebra_simps)
    then have "(3::'k) = 0 \<or> (B x x z + B x z z) = 0" by (simp only: mult_eq_0_iff)
    then show ?thesis by simp
  qed
  have hy: "B y y z + B y z z = 0"
  proof -
    have "3 * (B y y z + B y z z) = 0" using c3 diag[of "y+z"] diag[of y] diag[of z] by (simp add: algebra_simps)
    then have "(3::'k) = 0 \<or> (B y y z + B y z z) = 0" by (simp only: mult_eq_0_iff)
    then show ?thesis by simp
  qed
  have step: "B (x+y+z) (x+y+z) (x+y+z) = 0 + 0 + 3 * (B x x z + 2 * B x y z + B y y z) + 3 * (B x z z + B y z z)"
    by (simp only: c1 quad lin, simp only: diag)
  have rearr: "3 * (B x x z + 2 * B x y z + B y y z) + 3 * (B x z z + B y z z) =
      6 * B x y z + 3 * (B x x z + B x z z) + 3 * (B y y z + B y z z)" by (simp add: algebra_simps)
  have "6 * B x y z = 0"
    using step diag[of "x+y+z"] rearr hz hy by simp
  then show ?thesis by simp
qed

text \<open>Elimination steps: a vanishing combination of the expansion of the diagonal at x + t y for several integer t
  forces the coefficient of the "last-slot-cubed" term to vanish.\<close>

lemma num_cancel:
  fixes x :: "'k::field_char_0"
  assumes "(c::'k) \<noteq> 0" and "c * x = 0"
  shows "x = 0"
  using assms by simp

lemma solve_quad:
  fixes a b c :: "'k::field_char_0"
  assumes e1: "4*a + 6*b + 4*c = 0" and e2: "-4*a + 6*b - 4*c = 0" and e3: "8*a + 24*b + 32*c = 0"
  shows "c = 0"
proof -
  have h1: "12 * b = 0"
  proof -
    have "12 * b = (4*a + 6*b + 4*c) + (-4*a + 6*b - 4*c)" by algebra
    also have "\<dots> = 0" by (simp only: e1 e2 add_0_left)
    finally show ?thesis .
  qed
  have hb: "b = 0" by (rule num_cancel[OF _ h1]) simp
  have h2: "8 * (a + c) = 0"
  proof -
    have "8 * (a + c) = (4*a + 6*b + 4*c) - (-4*a + 6*b - 4*c)" by algebra
    also have "\<dots> = 0" by (simp only: e1 e2 diff_self)
    finally show ?thesis .
  qed
  have "24 * c = (8*a + 24*b + 32*c) - 8 * (a + c) - 24 * b" by algebra
  also have "\<dots> = 0 - 0 - 24 * b" by (simp only: e3 h2)
  also have "\<dots> = 0" by (simp add: hb)
  finally have "24 * c = 0" .
  show ?thesis by (rule num_cancel[OF _ \<open>24 * c = 0\<close>]) simp
qed

lemma solve_quint:
  fixes a b c d :: "'k::field_char_0"
  assumes e1: "5*a + 10*b + 10*c + 5*d = 0" and e2: "-5*a + 10*b - 10*c + 5*d = 0"
    and e3: "10*a + 40*b + 80*c + 80*d = 0" and e4: "-10*a + 40*b - 80*c + 80*d = 0"
  shows "d = 0"
proof -
  have h1: "10 * (2*b + d) = 0"
  proof -
    have "10 * (2*b + d) = (5*a + 10*b + 10*c + 5*d) + (-5*a + 10*b - 10*c + 5*d)" by algebra
    also have "\<dots> = 0" by (simp only: e1 e2 add_0_left)
    finally show ?thesis .
  qed
  have h1': "2*b + d = 0" by (rule num_cancel[OF _ h1]) simp
  have h2: "80 * (b + 2*d) = 0"
  proof -
    have "80 * (b + 2*d) = (10*a + 40*b + 80*c + 80*d) + (-10*a + 40*b - 80*c + 80*d)" by algebra
    also have "\<dots> = 0" by (simp only: e3 e4 add_0_left)
    finally show ?thesis .
  qed
  have h2': "b + 2*d = 0" by (rule num_cancel[OF _ h2]) simp
  have h3: "3 * b = 0"
  proof -
    have "3 * b = 2 * (2*b + d) - (b + 2*d)" by algebra
    also have "\<dots> = 2 * 0 - 0" by (simp only: h1' h2')
    also have "\<dots> = 0" by simp
    finally show ?thesis .
  qed
  have hb: "b = 0" by (rule num_cancel[OF _ h3]) simp
  have "d = (2*b + d) - 2 * b" by algebra
  also have "\<dots> = 0 - 2 * b" by (simp only: h1')
  also have "\<dots> = 0" by (simp add: hb)
  finally show ?thesis .
qed

theorem symmetric_4linear_polarization:
  fixes B :: "'v::ab_group_add \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'k::field_char_0"
  assumes add1: "\<And>x x' y z w. B (x + x') y z w = B x y z w + B x' y z w"
    and s12: "\<And>x y z w. B x y z w = B y x z w"
    and s23: "\<And>x y z w. B x y z w = B x z y w"
    and s34: "\<And>x y z w. B x y z w = B x y w z"
    and diag: "\<And>x. B x x x x = 0"
  shows "B x y z w = 0"
proof -
  have add2: "\<And>x y y' z w. B x (y + y') z w = B x y z w + B x y' z w" using add1 s12 by metis
  have add3: "\<And>x y z z' w. B x y (z + z') w = B x y z w + B x y z' w" using add2 s23 by metis
  have add4: "\<And>x y z w w'. B x y z (w + w') = B x y z w + B x y z w'" using add3 s34 by metis
  have B0: "\<And>y z w. B 0 y z w = 0" using add1[of 0 0] by simp
  have neg1: "\<And>x y z w. B (-x) y z w = - B x y z w"
  proof -
    fix x y z w
    have "B x y z w + B (-x) y z w = B (x + -x) y z w" by (rule add1[symmetric])
    also have "\<dots> = 0" by (simp add: B0)
    finally show "B (-x) y z w = - B x y z w" by (rule minus_unique[symmetric])
  qed
  have neg2: "\<And>x y z w. B x (-y) z w = - B x y z w" using neg1 s12 by metis
  have neg3: "\<And>x y z w. B x y (-z) w = - B x y z w" using neg2 s23 by metis
  have neg4: "\<And>x y z w. B x y z (-w) = - B x y z w" using neg3 s34 by metis
  note rules = add1 add2 add3 add4 neg1 neg2 neg3 neg4 s12 s23 s34
  have E: "\<And>x y. 4 * B x x x y + 6 * B x x y y + 4 * B x y y y = 0"
  proof -
    fix x y
    have "B (x+y) (x+y) (x+y) (x+y) =
      B x x x x + (4 * B x x x y + 6 * B x x y y + 4 * B x y y y) + B y y y y"
      by ((simp add: rules); algebra)
    then show "4 * B x x x y + 6 * B x x y y + 4 * B x y y y = 0"
      using diag[of "x+y"] diag[of x] diag[of y] by simp
  qed
  have c0: "\<And>x y. B x y y y = 0"
  proof -
    fix x y
    have e2: "-4 * B x x x y + 6 * B x x y y - 4 * B x y y y = 0"
    proof -
      have "4 * B x x x (-y) + 6 * B x x (-y) (-y) + 4 * B x (-y) (-y) (-y)
          = -4 * B x x x y + 6 * B x x y y - 4 * B x y y y"
        by ((simp add: rules); algebra)
      then show ?thesis using E[of x "-y"] by simp
    qed
    have e3: "8 * B x x x y + 24 * B x x y y + 32 * B x y y y = 0"
    proof -
      have "4 * B x x x (y+y) + 6 * B x x (y+y) (y+y) + 4 * B x (y+y) (y+y) (y+y)
          = 8 * B x x x y + 24 * B x x y y + 32 * B x y y y"
        by ((simp add: rules); algebra)
      then show ?thesis using E[of x "y+y"] by simp
    qed
    show "B x y y y = 0" by (rule solve_quad[OF E[of x y] e2 e3])
  qed
  have "\<And>x. \<forall>y z w. B x y z w = 0"
  proof (intro allI)
    fix x y z w
    show "B x y z w = 0"
      by (rule symmetric_trilinear_polarization[of "\<lambda>y z w. B x y z w" y z w])
         (use add2 s23 s34 c0 in \<open>auto\<close>)
  qed
  then show ?thesis by blast
qed

theorem symmetric_5linear_polarization:
  fixes B :: "'v::ab_group_add \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'k::field_char_0"
  assumes add1: "\<And>x x' y z w v. B (x + x') y z w v = B x y z w v + B x' y z w v"
    and s12: "\<And>x y z w v. B x y z w v = B y x z w v"
    and s23: "\<And>x y z w v. B x y z w v = B x z y w v"
    and s34: "\<And>x y z w v. B x y z w v = B x y w z v"
    and s45: "\<And>x y z w v. B x y z w v = B x y z v w"
    and diag: "\<And>x. B x x x x x = 0"
  shows "B x y z w v = 0"
proof -
  have add2: "\<And>x y y' z w v. B x (y + y') z w v = B x y z w v + B x y' z w v" using add1 s12 by metis
  have add3: "\<And>x y z z' w v. B x y (z + z') w v = B x y z w v + B x y z' w v" using add2 s23 by metis
  have add4: "\<And>x y z w w' v. B x y z (w + w') v = B x y z w v + B x y z w' v" using add3 s34 by metis
  have add5: "\<And>x y z w v v'. B x y z w (v + v') = B x y z w v + B x y z w v'" using add4 s45 by metis
  have B0: "\<And>y z w v. B 0 y z w v = 0" using add1[of 0 0] by simp
  have neg1: "\<And>x y z w v. B (-x) y z w v = - B x y z w v"
  proof -
    fix x y z w v
    have "B x y z w v + B (-x) y z w v = B (x + -x) y z w v" by (rule add1[symmetric])
    also have "\<dots> = 0" by (simp add: B0)
    finally show "B (-x) y z w v = - B x y z w v" by (rule minus_unique[symmetric])
  qed
  have neg2: "\<And>x y z w v. B x (-y) z w v = - B x y z w v" using neg1 s12 by metis
  have neg3: "\<And>x y z w v. B x y (-z) w v = - B x y z w v" using neg2 s23 by metis
  have neg4: "\<And>x y z w v. B x y z (-w) v = - B x y z w v" using neg3 s34 by metis
  have neg5: "\<And>x y z w v. B x y z w (-v) = - B x y z w v" using neg4 s45 by metis
  note rules = add1 add2 add3 add4 add5 neg1 neg2 neg3 neg4 neg5 s12 s23 s34 s45
  have E: "\<And>x y. 5 * B x x x x y + 10 * B x x x y y + 10 * B x x y y y + 5 * B x y y y y = 0"
  proof -
    fix x y
    have "B (x+y) (x+y) (x+y) (x+y) (x+y) =
      B x x x x x + (5 * B x x x x y + 10 * B x x x y y + 10 * B x x y y y + 5 * B x y y y y) + B y y y y y"
      by ((simp add: rules); algebra)
    then show "5 * B x x x x y + 10 * B x x x y y + 10 * B x x y y y + 5 * B x y y y y = 0"
      using diag[of "x+y"] diag[of x] diag[of y] by simp
  qed
  have d0: "\<And>x y. B x y y y y = 0"
  proof -
    fix x y
    have e2: "-5 * B x x x x y + 10 * B x x x y y - 10 * B x x y y y + 5 * B x y y y y = 0"
    proof -
      have "5 * B x x x x (-y) + 10 * B x x x (-y) (-y) + 10 * B x x (-y) (-y) (-y) + 5 * B x (-y) (-y) (-y) (-y)
          = -5 * B x x x x y + 10 * B x x x y y - 10 * B x x y y y + 5 * B x y y y y"
        by ((simp add: rules); algebra)
      then show ?thesis using E[of x "-y"] by simp
    qed
    have e3gen: "\<And>y. 10 * B x x x x y + 40 * B x x x y y + 80 * B x x y y y + 80 * B x y y y y = 0"
    proof -
      fix y
      have "5 * B x x x x (y+y) + 10 * B x x x (y+y) (y+y) + 10 * B x x (y+y) (y+y) (y+y)
            + 5 * B x (y+y) (y+y) (y+y) (y+y)
          = 10 * B x x x x y + 40 * B x x x y y + 80 * B x x y y y + 80 * B x y y y y"
        by ((simp add: rules); algebra)
      then show "10 * B x x x x y + 40 * B x x x y y + 80 * B x x y y y + 80 * B x y y y y = 0"
        using E[of x "y+y"] by simp
    qed
    have e3: "10 * B x x x x y + 40 * B x x x y y + 80 * B x x y y y + 80 * B x y y y y = 0" by (rule e3gen)
    have e4: "-10 * B x x x x y + 40 * B x x x y y - 80 * B x x y y y + 80 * B x y y y y = 0"
    proof -
      have "10 * B x x x x (-y) + 40 * B x x x (-y) (-y) + 80 * B x x (-y) (-y) (-y)
            + 80 * B x (-y) (-y) (-y) (-y)
          = -10 * B x x x x y + 40 * B x x x y y - 80 * B x x y y y + 80 * B x y y y y"
        by ((simp add: rules); algebra)
      then show ?thesis using e3gen[of "-y"] by simp
    qed
    show "B x y y y y = 0" by (rule solve_quint[OF E[of x y] e2 e3 e4])
  qed
  have "\<And>x. \<forall>y z w v. B x y z w v = 0"
  proof (intro allI)
    fix x y z w v
    show "B x y z w v = 0"
      by (rule symmetric_4linear_polarization[of "\<lambda>y z w v. B x y z w v" y z w v])
         (use add2 s23 s34 s45 d0 in \<open>auto\<close>)
  qed
  then show ?thesis by blast
qed

section \<open>(2) Positive averaging (Lemma positive)\<close>

text \<open>For the numbers h_i = H_ii(a,a): the sum over the pairs i < j of (h_i + h_j) is (n-1) times the total.\<close>

lemma pair_sum_identity:
  fixes h :: "nat \<Rightarrow> real"
  shows "(\<Sum>j<n. \<Sum>i<j. h i + h j) = (real n - 1) * (\<Sum>i<n. h i)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "(\<Sum>j<Suc n. \<Sum>i<j. h i + h j) = (\<Sum>j<n. \<Sum>i<j. h i + h j) + (\<Sum>i<n. h i + h n)" by simp
  also have "\<dots> = (real n - 1) * (\<Sum>i<n. h i) + ((\<Sum>i<n. h i) + real n * h n)"
    using Suc by (simp add: sum.distrib)
  also have "\<dots> = (real (Suc n) - 1) * (\<Sum>i<Suc n. h i)" by (simp add: algebra_simps)
  finally show ?case .
qed

theorem positive_averaging_nonneg:
  fixes h :: "nat \<Rightarrow> real"
  assumes n2: "2 \<le> n" and pairs: "\<And>i j. i < j \<Longrightarrow> j < n \<Longrightarrow> 0 \<le> h i + h j"
  shows "0 \<le> (\<Sum>i<n. h i)"
proof -
  have "0 \<le> (\<Sum>j<n. \<Sum>i<j. h i + h j)"
    by (intro sum_nonneg) (use pairs in auto)
  then have "0 \<le> (real n - 1) * (\<Sum>i<n. h i)" by (simp only: pair_sum_identity)
  moreover have "0 < real n - 1" using n2 by simp
  ultimately show ?thesis by (simp add: zero_le_mult_iff)
qed

text \<open>The step "as n >= 3, all diagonal terms also vanish": if h_i + h_j = 0 for all i different from j (from the
  pairings of equal wedges), then every h_i is zero (characteristic different from 2).\<close>

theorem diagonal_terms_vanish:
  fixes h :: "nat \<Rightarrow> 'k::field_char_0"
  assumes n3: "3 \<le> n" and pairs: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> i \<noteq> j \<Longrightarrow> h i + h j = 0" and i: "i < n"
  shows "h i = 0"
proof -
  obtain j k where jk: "j < n" "k < n" "j \<noteq> i" "k \<noteq> i" "j \<noteq> k"
  proof (cases "i = 0")
    case True
    then show ?thesis using n3 that[of 1 2] by simp
  next
    case f0: False
    show ?thesis
    proof (cases "i = 1")
      case True
      then show ?thesis using n3 that[of 0 2] by simp
    next
      case f1: False
      then show ?thesis using n3 f0 that[of 0 1] by simp
    qed
  qed
  have a: "h i + h j = 0" using pairs i jk by (metis)
  have b: "h i + h k = 0" using pairs i jk by (metis)
  have c: "h j + h k = 0" using pairs jk by (metis)
  have "2 * h i = (h i + h j) + (h i + h k) - (h j + h k)" by algebra
  then have "2 * h i = 0" using a b c by simp
  then show ?thesis by simp
qed

section \<open>(3) Linear spaces of matrices of rank at most one (Lemma small-tableaux, s = 3)\<close>

text \<open>A matrix is a function M i l (indices i < n, l < k) with values in a field. All 2 x 2 minors vanishing means
  rank at most one. Only closure under addition is used (scalar closure is not needed).\<close>

definition minors_zero :: "(nat \<Rightarrow> nat \<Rightarrow> 'a::comm_ring) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "minors_zero M n k = (\<forall>i<n. \<forall>j<n. \<forall>l<k. \<forall>m<k. M i l * M j m = M i m * M j l)"

text \<open>dep N x y: the vectors x, y (indices below N) are linearly dependent in the sense of vanishing 2 x 2 minors.\<close>

definition dep :: "nat \<Rightarrow> (nat \<Rightarrow> 'a::comm_ring) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool" where
  "dep N x y = (\<forall>i<N. \<forall>j<N. x i * y j = x j * y i)"

lemma dep_sym: "dep N x y \<Longrightarrow> dep N y x"
  unfolding dep_def by (metis mult.commute)

lemma dep_trans:
  fixes x y z :: "nat \<Rightarrow> 'a::field"
  assumes jj: "jj < N" "z jj \<noteq> 0" and xz: "dep N x z" and yz: "dep N y z"
  shows "dep N x y"
  unfolding dep_def
proof (intro allI impI)
  fix i j assume ij: "i < N" "j < N"
  have h1: "x i * z jj = x jj * z i" using xz ij jj unfolding dep_def by blast
  have h2: "x j * z jj = x jj * z j" using xz ij jj unfolding dep_def by blast
  have h3: "y i * z jj = y jj * z i" using yz ij jj unfolding dep_def by blast
  have h4: "y j * z jj = y jj * z j" using yz ij jj unfolding dep_def by blast
  have "(x i * y j) * (z jj * z jj) = (x i * z jj) * (y j * z jj)" by algebra
  also have "\<dots> = (x jj * z i) * (y jj * z j)" using h1 h4 by simp
  also have "\<dots> = (x jj * z j) * (y jj * z i)" by algebra
  also have "\<dots> = (x j * z jj) * (y i * z jj)" using h2 h3 by simp
  also have "\<dots> = (x j * y i) * (z jj * z jj)" by algebra
  finally have "(x i * y j) * (z jj * z jj) = (x j * y i) * (z jj * z jj)" .
  moreover have "z jj * z jj \<noteq> 0" using jj by simp
  ultimately show "x i * y j = x j * y i" by simp
qed

lemma minor_sum_rank_one:
  fixes u v :: "nat \<Rightarrow> 'a::comm_ring"
  shows "(u i * a l + v i * b l) * (u j * a m + v j * b m) - (u i * a m + v i * b m) * (u j * a l + v j * b l)
       = (u i * v j - u j * v i) * (a l * b m - a m * b l)"
  by (simp add: algebra_simps)

text \<open>Two rank-one members with independent image lines and independent covector lines give a rank-two sum.\<close>

lemma two_rank_one_contra:
  fixes M N :: "nat \<Rightarrow> nat \<Rightarrow> 'a::field" and u v :: "nat \<Rightarrow> 'a" and a b :: "nat \<Rightarrow> 'a"
  assumes add: "\<And>A B. A \<in> S \<Longrightarrow> B \<in> S \<Longrightarrow> (\<lambda>i l. A i l + B i l) \<in> S"
    and mz: "\<And>A. A \<in> S \<Longrightarrow> minors_zero A n k"
    and MS: "M \<in> S" and NS: "N \<in> S"
    and rM: "\<And>i l. i < n \<Longrightarrow> l < k \<Longrightarrow> M i l = u i * a l"
    and rN: "\<And>i l. i < n \<Longrightarrow> l < k \<Longrightarrow> N i l = v i * b l"
    and indu: "\<not> dep n u v" and indb: "\<not> dep k a b"
  shows False
proof -
  obtain i j where ij: "i < n" "j < n" "u i * v j \<noteq> u j * v i" using indu unfolding dep_def by blast
  obtain l m where lm: "l < k" "m < k" "a l * b m \<noteq> a m * b l" using indb unfolding dep_def by blast
  have "(\<lambda>i l. M i l + N i l) \<in> S" by (rule add[OF MS NS])
  then have "minors_zero (\<lambda>i l. M i l + N i l) n k" by (rule mz)
  then have z: "(M i l + N i l) * (M j m + N j m) = (M i m + N i m) * (M j l + N j l)"
    using ij lm unfolding minors_zero_def by blast
  have z': "(u i * a l + v i * b l) * (u j * a m + v j * b m) = (u i * a m + v i * b m) * (u j * a l + v j * b l)"
    using z ij lm by (simp add: rM rN)
  have mm: "(u i * v j - u j * v i) * (a l * b m - a m * b l) = 0"
    using minor_sum_rank_one[of u i a l v b j m] z' by simp
  then show False using ij(3) lm(3) by simp
qed

lemma nonzero_decomp:
  fixes M :: "nat \<Rightarrow> nat \<Rightarrow> 'a::field"
  assumes mz: "minors_zero M n k" and i0: "i0 < n" and l0: "l0 < k" and nz: "M i0 l0 \<noteq> 0"
  shows "\<exists>u a. (\<forall>i<n. \<forall>l<k. M i l = u i * a l) \<and> u i0 \<noteq> 0 \<and> a l0 \<noteq> 0"
proof -
  have key: "\<forall>i<n. \<forall>l<k. M i l = M i l0 * (M i0 l / M i0 l0)"
  proof (intro allI impI)
    fix i l assume "i < n" "l < k"
    then have "M i l * M i0 l0 = M i l0 * M i0 l" using mz i0 l0 unfolding minors_zero_def by blast
    then show "M i l = M i l0 * (M i0 l / M i0 l0)" using nz by (simp add: field_simps)
  qed
  have nz2: "M i0 l0 / M i0 l0 \<noteq> 0" using nz by simp
  show ?thesis
    by (rule exI[of _ "\<lambda>i. M i l0"], rule exI[of _ "\<lambda>l. M i0 l / M i0 l0"], intro conjI key nz nz2)
qed

theorem rank_le_one_space_full:
  fixes S :: "(nat \<Rightarrow> nat \<Rightarrow> 'a::field) set"
  assumes n: "0 < n" and k: "0 < k"
    and add: "\<And>A B. A \<in> S \<Longrightarrow> B \<in> S \<Longrightarrow> (\<lambda>i l. A i l + B i l) \<in> S"
    and mz: "\<And>M. M \<in> S \<Longrightarrow> minors_zero M n k"
  shows "(\<exists>u. (\<exists>i<n. u i \<noteq> 0) \<and> (\<forall>M\<in>S. \<exists>\<phi>. \<forall>i<n. \<forall>l<k. M i l = u i * \<phi> l))
       \<or> (\<exists>a. (\<exists>l<k. a l \<noteq> 0) \<and> (\<forall>M\<in>S. \<exists>\<psi>. \<forall>i<n. \<forall>l<k. M i l = \<psi> i * a l))"
proof (cases "\<forall>M\<in>S. \<forall>i<n. \<forall>l<k. M i l = 0")
  case True
  show ?thesis
  proof (intro disjI1 exI[of _ "\<lambda>_. (1::'a)"] conjI)
    show "\<exists>i<n. (1::'a) \<noteq> 0" using n by auto
    show "\<forall>M\<in>S. \<exists>\<phi>. \<forall>i<n. \<forall>l<k. M i l = 1 * \<phi> l"
      by (intro ballI exI[of _ "\<lambda>_. 0"] allI impI) (use True in auto)
  qed
next
  case False
  then obtain M1 i0 l0 where M1: "M1 \<in> S" "i0 < n" "l0 < k" "M1 i0 l0 \<noteq> 0" by blast
  obtain u a where rM1: "\<And>i l. i < n \<Longrightarrow> l < k \<Longrightarrow> M1 i l = u i * a l" and u0: "u i0 \<noteq> 0" and a0: "a l0 \<noteq> 0"
    using nonzero_decomp[OF mz[OF M1(1)] M1(2-4)] by blast
  show ?thesis
  proof (cases "\<forall>M\<in>S. \<exists>\<phi>. \<forall>i<n. \<forall>l<k. M i l = u i * \<phi> l")
    case True
    note Hall = this
    show ?thesis
    proof (intro disjI1 exI[of _ u] conjI)
      show "\<exists>i<n. u i \<noteq> 0" using u0 M1(2) by auto
      show "\<forall>M\<in>S. \<exists>\<phi>. \<forall>i<n. \<forall>l<k. M i l = u i * \<phi> l" by (rule Hall)
    qed
  next
    case False
    then obtain P where PS: "P \<in> S" and Pn: "\<And>\<phi>. \<not> (\<forall>i<n. \<forall>l<k. P i l = u i * \<phi> l)" by blast
    have Pnz: "\<exists>i<n. \<exists>l<k. P i l \<noteq> 0"
    proof (rule ccontr)
      assume "\<not> (\<exists>i<n. \<exists>l<k. P i l \<noteq> 0)"
      then have "\<forall>i<n. \<forall>l<k. P i l = u i * (\<lambda>_. 0) l" by auto
      then show False using Pn[of "\<lambda>_. 0"] by blast
    qed
    then obtain j1 m1 where j1: "j1 < n" "m1 < k" "P j1 m1 \<noteq> 0" by blast
    obtain w c where rP: "\<And>i l. i < n \<Longrightarrow> l < k \<Longrightarrow> P i l = w i * c l" and w0: "w j1 \<noteq> 0" and c0: "c m1 \<noteq> 0"
      using nonzero_decomp[OF mz[OF PS] j1] by blast
    have indwu: "\<not> dep n w u"
    proof
      assume dwu: "dep n w u"
      have "\<forall>i<n. \<forall>l<k. P i l = u i * ((w i0 / u i0) * c l)"
      proof (intro allI impI)
        fix i l assume il: "i < n" "l < k"
        have "w i * u i0 = w i0 * u i" using dwu il M1(2) unfolding dep_def by blast
        then have "w i = u i * (w i0 / u i0)" using u0 by (simp add: field_simps)
        then show "P i l = u i * ((w i0 / u i0) * c l)" using rP il by simp
      qed
      then show False by (rule notE[OF Pn[of "\<lambda>l. (w i0 / u i0) * c l"]])
    qed
    have indu_w: "\<not> dep n u w" using indwu dep_sym by blast
    have dac: "dep k a c"
    proof (rule ccontr)
      assume "\<not> dep k a c"
      then show False using two_rank_one_contra[OF add mz M1(1) PS rM1 rP indu_w] by blast
    qed
    have main: "\<And>Q. Q \<in> S \<Longrightarrow> \<exists>\<psi>. \<forall>i<n. \<forall>l<k. Q i l = \<psi> i * a l"
    proof -
      fix Q assume QS: "Q \<in> S"
      show "\<exists>\<psi>. \<forall>i<n. \<forall>l<k. Q i l = \<psi> i * a l"
      proof (cases "\<forall>i<n. \<forall>l<k. Q i l = 0")
        case True
        then show ?thesis by (intro exI[of _ "\<lambda>_. 0"]) simp
      next
        case False
        then obtain i1 l1 where i1: "i1 < n" "l1 < k" "Q i1 l1 \<noteq> 0" by blast
        obtain z d where rQ: "\<And>i l. i < n \<Longrightarrow> l < k \<Longrightarrow> Q i l = z i * d l" and z0: "z i1 \<noteq> 0" and d0: "d l1 \<noteq> 0"
          using nonzero_decomp[OF mz[OF QS] i1] by blast
        have notboth: "\<not> dep n u z \<or> \<not> dep n w z"
        proof (rule ccontr)
          assume "\<not> (\<not> dep n u z \<or> \<not> dep n w z)"
          then have "dep n u z" "dep n w z" by simp_all
          then have "dep n u w" by (rule dep_trans[where jj=i1 and N=n and z=z and x=u and y=w, OF i1(1) z0])
          then show False using indu_w by blast
        qed
        have dad: "dep k a d"
        proof -
          from notboth show ?thesis
          proof
            assume nuz: "\<not> dep n u z"
            show ?thesis
            proof (rule ccontr)
              assume "\<not> dep k a d"
              then show False using two_rank_one_contra[OF add mz M1(1) QS rM1 rQ nuz] by blast
            qed
          next
            assume nwz: "\<not> dep n w z"
            have dcd: "dep k c d"
            proof (rule ccontr)
              assume "\<not> dep k c d"
              then show False using two_rank_one_contra[OF add mz PS QS rP rQ nwz] by blast
            qed
            show ?thesis by (rule dep_trans[where jj=m1 and N=k and z=c and x=a and y=d, OF j1(2) c0 dac dep_sym[OF dcd]])
          qed
        qed
        show ?thesis
        proof (intro exI[of _ "\<lambda>i. z i * d l0 / a l0"] allI impI)
          fix i l assume il: "i < n" "l < k"
          have "a l * d l0 = a l0 * d l" using dad il M1(3) unfolding dep_def by blast
          then have "d l = a l * d l0 / a l0" using a0 by (simp add: field_simps)
          then show "Q i l = z i * d l0 / a l0 * a l" using rQ il by simp
        qed
      qed
    qed
    show ?thesis
    proof (intro disjI2 exI[of _ a] conjI)
      show "\<exists>l<k. a l \<noteq> 0" using a0 M1(3) by auto
      show "\<forall>M\<in>S. \<exists>\<psi>. \<forall>i<n. \<forall>l<k. M i l = \<psi> i * a l" by (intro ballI main)
    qed
  qed
qed

section \<open>(4) The support count (Lemma supports)\<close>

text \<open>With a, b >= 1 the supports and r >= 1 the dimension: the projective image has dimension r - 1, the Segre
  variety has dimension a + b - 2 inside P^(ab-1). The projective dimension theorem says that a disjoint pair is
  impossible when (r-1) + (a+b-2) >= ab - 1; the arithmetic below turns the negation into r <= (a-1)(b-1).\<close>

theorem support_count_equivalence:
  fixes a b r :: nat
  assumes a: "1 \<le> a" and b: "1 \<le> b" and r: "1 \<le> r"
  shows "(r - 1) + (a + b - 2) < a * b - 1 \<longleftrightarrow> r \<le> (a - 1) * (b - 1)"
proof -
  obtain a' where a': "a = Suc a'" using a by (cases a) auto
  obtain b' where b': "b = Suc b'" using b by (cases b) auto
  obtain r' where r': "r = Suc r'" using r by (cases r) auto
  have e1: "a * b - 1 = a' * b' + a' + b'" using a' b' by (simp add: algebra_simps)
  have e2: "a + b - 2 = a' + b'" using a' b' by simp
  have e3: "(a - 1) * (b - 1) = a' * b'" using a' b' by simp
  have e4: "r - 1 = r'" using r' by simp
  show ?thesis unfolding e1 e2 e3 e4 r' by arith
qed

theorem support_count_inequality:
  fixes a b r :: nat
  assumes a: "1 \<le> a" and b: "1 \<le> b" and r: "1 \<le> r"
    and hyp: "a * b - 1 \<le> (r - 1) + (a + b - 2)"
  shows "(a - 1) * (b - 1) + 1 \<le> r"
proof -
  have "\<not> (r - 1) + (a + b - 2) < a * b - 1" using hyp by simp
  then have "\<not> r \<le> (a - 1) * (b - 1)" using support_count_equivalence[OF a b r] by simp
  then show ?thesis by simp
qed

corollary product_free_bound:
  fixes a b r :: nat
  assumes "1 \<le> a" "1 \<le> b" "1 \<le> r"
    and "\<not> (a * b - 1 \<le> (r - 1) + (a + b - 2))"
  shows "r \<le> (a - 1) * (b - 1)"
proof -
  have lt: "(r - 1) + (a + b - 2) < a * b - 1" using assms(4) by (rule not_le_imp_less)
  then show ?thesis using support_count_equivalence[OF assms(1-3)] by blast
qed

end
