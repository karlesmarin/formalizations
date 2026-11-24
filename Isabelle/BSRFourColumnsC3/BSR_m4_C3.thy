(*  Title:      BSR_m4_C3.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Computation C3 of the paper "Every m x 4 biquadratic sum of squares is a sum of 3m-1 squares (5 <= m <= 16)" (2026, in preparation),
    Theorem "Full-support rank-six exclusion" (label rank6), case (ii):
      flatness  A_i p_j + t_j p_i = A_j p_i + t_i p_j,  A_i symmetric,  P = span p_i totally isotropic,
      diagonal cubic  p_c^t (A_c - t_c I) p_c = 0  for all c
      ==>  B(i,j,k) = p_i^t (A_j - t_j I) p_k = 0,  and if P^perp = P then A_c P is contained in P.
    Statements written from the paper; proofs complete, with a negative control.
*)

theory BSR_m4_C3
  imports "HOL-Analysis.Finite_Cartesian_Product" "HOL-Analysis.Linear_Algebra" "HOL-Analysis.Cartesian_Space"
begin

text \<open>Bilinear dot product (no conjugation; the paper works over \<open>\<complex>\<close> with \<open>J = I\<close>).\<close>

definition dotv :: "'a::comm_ring_1^'n \<Rightarrow> 'a^'n \<Rightarrow> 'a" where
  "dotv v w = (\<Sum>k\<in>UNIV. v$k * w$k)"

text \<open>The objects linear in \<open>c \<in> B\<close>: \<open>p_c = \<Sum> c_i p_i\<close>, \<open>A_c = \<Sum> c_i A_i\<close>, \<open>t_c = \<Sum> c_i t_i\<close>.\<close>

definition msc :: "'a::comm_ring_1 \<Rightarrow> 'a^'n^'m \<Rightarrow> 'a^'n^'m" where
  "msc k M = (\<chi> i j. k * M $ i $ j)"

lemma msc_nth [simp]: "msc k M $ i $ j = k * M $ i $ j"
  by (simp add: msc_def)

definition pc :: "('b::finite \<Rightarrow> 'a::comm_ring_1^'n) \<Rightarrow> 'a^'b \<Rightarrow> 'a^'n" where
  "pc p c = (\<Sum>i\<in>UNIV. c$i *s p i)"

definition Ac :: "('b::finite \<Rightarrow> 'a::comm_ring_1^'n^'n) \<Rightarrow> 'a^'b \<Rightarrow> 'a^'n^'n" where
  "Ac A c = (\<Sum>i\<in>UNIV. msc (c$i) (A i))"

definition tc :: "('b::finite \<Rightarrow> 'a::comm_ring_1) \<Rightarrow> 'a^'b \<Rightarrow> 'a" where
  "tc t c = (\<Sum>i\<in>UNIV. c$i * t i)"

section \<open>Auxiliary lemmas\<close>

lemma vsum_nth: "(\<Sum>i\<in>S. f i :: 'a::comm_monoid_add^'n)$k = (\<Sum>i\<in>S. f i $ k)"
  by (induct S rule: infinite_finite_induct) simp_all

lemma dotv_comm: "dotv v w = dotv w v"
  unfolding dotv_def by (simp add: mult.commute)

lemma dotv_add_l: "dotv (v + v') w = dotv v w + dotv v' w"
  unfolding dotv_def by (simp add: algebra_simps sum.distrib)

lemma dotv_sum_gen: "dotv (\<Sum>i\<in>S. f i) w = (\<Sum>i\<in>S. dotv (f i) w)"
proof (induct S rule: infinite_finite_induct)
  case infinite
  then show ?case by (simp add: dotv_def)
next
  case empty
  show ?case by (simp add: dotv_def)
next
  case (insert x F)
  then show ?case by (simp add: dotv_add_l)
qed

lemma dotv_smul_l: "dotv (a *s v) w = a * dotv v w"
  by (simp add: dotv_def sum_distrib_left mult.assoc)

lemma dotv_sum_l:
  fixes u :: "'b::finite \<Rightarrow> 'a::comm_ring_1^'n::finite"
  shows "dotv (\<Sum>i\<in>UNIV. x i *s u i) w = (\<Sum>i\<in>UNIV. x i * dotv (u i) w)"
proof -
  have "dotv (\<Sum>i\<in>UNIV. x i *s u i) w = (\<Sum>k\<in>UNIV. \<Sum>i\<in>UNIV. x i * (u i $ k * w $ k))"
    unfolding dotv_def by (simp add: vsum_nth sum_distrib_left sum_distrib_right mult_ac)
  also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>k\<in>UNIV. x i * (u i $ k * w $ k))" by (rule sum.swap)
  also have "\<dots> = (\<Sum>i\<in>UNIV. x i * dotv (u i) w)"
    unfolding dotv_def by (simp add: sum_distrib_left mult.assoc)
  finally show ?thesis .
qed

lemma mv_sum_r:
  fixes M :: "'a::comm_ring_1^'n::finite^'m::finite" and q :: "'b::finite \<Rightarrow> 'a^'n"
  shows "M *v (\<Sum>k\<in>UNIV. z k *s q k) = (\<Sum>k\<in>UNIV. z k *s (M *v q k))"
proof (rule iffD2[OF vec_eq_iff], rule allI)
  fix a
  have "(M *v (\<Sum>k\<in>UNIV. z k *s q k)) $ a = (\<Sum>l\<in>UNIV. \<Sum>k\<in>UNIV. M $ a $ l * (z k * q k $ l))"
    by (simp add: matrix_vector_mult_def vsum_nth sum_distrib_left)
  also have "\<dots> = (\<Sum>k\<in>UNIV. \<Sum>l\<in>UNIV. M $ a $ l * (z k * q k $ l))" by (rule sum.swap)
  also have "\<dots> = (\<Sum>k\<in>UNIV. (z k *s (M *v q k)) $ a)"
    by (simp add: matrix_vector_mult_def sum_distrib_left algebra_simps)
  also have "\<dots> = (\<Sum>k\<in>UNIV. z k *s (M *v q k)) $ a" by (simp add: vsum_nth)
  finally show "(M *v (\<Sum>k\<in>UNIV. z k *s q k)) $ a = (\<Sum>k\<in>UNIV. z k *s (M *v q k)) $ a" .
qed

lemma mv_sum_l:
  fixes M :: "'b::finite \<Rightarrow> 'a::comm_ring_1^'n::finite^'m::finite" and w :: "'a^'n"
  shows "(\<Sum>j\<in>UNIV. msc (y j) (M j)) *v w = (\<Sum>j\<in>UNIV. y j *s (M j *v w))"
proof (rule iffD2[OF vec_eq_iff], rule allI)
  fix a
  have "((\<Sum>j\<in>UNIV. msc (y j) (M j)) *v w) $ a = (\<Sum>l\<in>UNIV. \<Sum>j\<in>UNIV. y j * M j $ a $ l * w $ l)"
    by (simp add: matrix_vector_mult_def vsum_nth sum_distrib_right)
  also have "\<dots> = (\<Sum>j\<in>UNIV. \<Sum>l\<in>UNIV. y j * M j $ a $ l * w $ l)" by (rule sum.swap)
  also have "\<dots> = (\<Sum>j\<in>UNIV. (y j *s (M j *v w)) $ a)"
    by (simp add: matrix_vector_mult_def sum_distrib_left algebra_simps)
  also have "\<dots> = (\<Sum>j\<in>UNIV. y j *s (M j *v w)) $ a" by (simp add: vsum_nth)
  finally show "((\<Sum>j\<in>UNIV. msc (y j) (M j)) *v w) $ a = (\<Sum>j\<in>UNIV. y j *s (M j *v w)) $ a" .
qed

lemma My_eq:
  fixes A :: "'b::finite \<Rightarrow> 'a::comm_ring_1^'n::finite^'n" and t :: "'b \<Rightarrow> 'a"
  shows "Ac A y - msc (tc t y) (mat 1) = (\<Sum>j\<in>UNIV. msc (y$j) (A j - msc (t j) (mat 1)))"
proof (rule iffD2[OF vec_eq_iff], rule allI)
  fix a
  show "(Ac A y - msc (tc t y) (mat 1)) $ a = (\<Sum>j\<in>UNIV. msc (y$j) (A j - msc (t j) (mat 1))) $ a"
  proof (rule iffD2[OF vec_eq_iff], rule allI)
    fix b
    show "(Ac A y - msc (tc t y) (mat 1)) $ a $ b = (\<Sum>j\<in>UNIV. msc (y$j) (A j - msc (t j) (mat 1))) $ a $ b"
      by (simp add: Ac_def tc_def vsum_nth sum_subtractf sum_distrib_right algebra_simps mat_def)
  qed
qed

lemma mv_expand:
  fixes p :: "'b::finite \<Rightarrow> 'a::comm_ring_1^'n::finite" and A :: "'b \<Rightarrow> 'a^'n^'n"
  shows "(Ac A y - msc (tc t y) (mat 1)) *v pc p z
     = (\<Sum>j\<in>UNIV. \<Sum>k\<in>UNIV. (y$j * z$k) *s ((A j - msc (t j) (mat 1)) *v p k))"
proof -
  have "(Ac A y - msc (tc t y) (mat 1)) *v pc p z
      = (\<Sum>j\<in>UNIV. y$j *s ((A j - msc (t j) (mat 1)) *v (\<Sum>k\<in>UNIV. z$k *s p k)))"
    unfolding My_eq pc_def by (rule mv_sum_l)
  also have "\<dots> = (\<Sum>j\<in>UNIV. y$j *s (\<Sum>k\<in>UNIV. z$k *s ((A j - msc (t j) (mat 1)) *v p k)))"
    by (simp only: mv_sum_r)
  also have "\<dots> = (\<Sum>j\<in>UNIV. \<Sum>k\<in>UNIV. (y$j * z$k) *s ((A j - msc (t j) (mat 1)) *v p k))"
    by (simp add: vec_eq_iff vsum_nth sum_distrib_left mult.assoc)
  finally show ?thesis .
qed

lemma Mv:
  fixes A :: "'a::comm_ring_1^'n::finite^'n"
  shows "(A - msc t (mat 1)) *v p = A *v p - t *s p"
proof -
  have "msc t (mat 1) *v p = t *s p"
  proof (rule iffD2[OF vec_eq_iff], rule allI)
    fix i
    have "\<And>j. t * mat 1 $ i $ j * p $ j = (if j = i then t * p $ i else 0)"
      by (cases "j = i") (auto simp: mat_def eq_commute)
    then show "(msc t (mat 1) *v p) $ i = (t *s p) $ i" by (simp add: matrix_vector_mult_def sum.delta)
  qed
  then show ?thesis by (simp add: matrix_vector_mult_diff_rdistrib)
qed

lemma pc_add: "pc p (x + x') = pc p x + pc p x'"
  by (simp add: pc_def vec_eq_iff vsum_nth algebra_simps sum.distrib)

lemma axis1: "axis i (1::'a::comm_ring_1) $ x = (if x = i then 1 else 0)"
  by (simp add: axis_def)

lemma msc_one [simp]: "msc 1 M = M" by (simp add: msc_def vec_eq_iff)

lemma msc_zero [simp]: "msc 0 M = 0" by (simp add: msc_def vec_eq_iff)

lemma pc_axis: "pc p (axis i 1) = p i"
proof -
  have "\<And>x. axis i 1 $ x *s p x = (if x = i then p i else 0)"
    by (cases "x = i") (simp_all add: axis1)
  then show ?thesis unfolding pc_def by (simp add: sum.delta)
qed

lemma Ac_axis: "Ac A (axis i 1) = A i"
proof -
  have "\<And>x. msc (axis i 1 $ x) (A x) = (if x = i then A i else 0)"
    by (cases "x = i") (simp_all add: axis1)
  then show ?thesis unfolding Ac_def by (simp add: sum.delta)
qed

lemma tc_axis: "tc t (axis i 1) = t i"
proof -
  have "\<And>x. axis i 1 $ x * t x = (if x = i then t i else 0)"
    by (cases "x = i") (simp_all add: axis1)
  then show ?thesis unfolding tc_def by (simp add: sum.delta)
qed

lemma mv_swap:
  fixes N :: "'a::comm_ring_1^'n::finite^'n"
  assumes sy: "\<And>k l. N $ k $ l = N $ l $ k"
  shows "dotv u (N *v w) = dotv w (N *v u)"
proof -
  have "dotv u (N *v w) = (\<Sum>k\<in>UNIV. \<Sum>l\<in>UNIV. u $ k * (N $ k $ l * w $ l))"
    by (simp add: dotv_def matrix_vector_mult_def sum_distrib_left)
  also have "\<dots> = (\<Sum>l\<in>UNIV. \<Sum>k\<in>UNIV. u $ k * (N $ k $ l * w $ l))" by (rule sum.swap)
  also have "\<dots> = dotv w (N *v u)"
    by (simp add: dotv_def matrix_vector_mult_def sum_distrib_left sy[of _ "_"] algebra_simps)
  finally show ?thesis .
qed

lemma My_sym:
  fixes A :: "'b::finite \<Rightarrow> 'a::comm_ring_1^'n::finite^'n" and t :: "'b \<Rightarrow> 'a"
  assumes sym: "\<And>i. transpose (A i) = A i"
  shows "(Ac A y - msc (tc t y) (mat 1)) $ k $ l = (Ac A y - msc (tc t y) (mat 1)) $ l $ k"
proof -
  have s: "A i $ k $ l = A i $ l $ k" for i
    using arg_cong[OF sym[of i], of "\<lambda>M. M $ l $ k"] by (simp add: transpose_def)
  show ?thesis by (simp add: Ac_def tc_def vsum_nth s mat_def eq_commute)
qed

text \<open>The polarization of a fully symmetric trilinear form with zero diagonal (copy of
  \<open>symmetric_trilinear_polarization\<close> of session 241).\<close>

theorem sym_trilinear_pol:
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

theorem c3_tensor_vanishes:
  fixes p :: "'b::finite \<Rightarrow> 'a::field_char_0^'n" and A :: "'b \<Rightarrow> 'a^'n^'n" and t :: "'b \<Rightarrow> 'a"
  assumes sym: "\<And>i. transpose (A i) = A i"
    and flat: "\<And>i j. A i *v p j + t j *s p i = A j *v p i + t i *s p j"
    and iso: "\<And>i j. dotv (p i) (p j) = 0"
    and cubic: "\<And>c. dotv (pc p c) ((Ac A c - msc (tc t c) (mat 1)) *v pc p c) = 0"
  shows "dotv (p i) ((A j - msc (t j) (mat 1)) *v p k) = 0"
proof -
  define Bf where "Bf x y z = dotv (pc p x) ((Ac A y - msc (tc t y) (mat 1)) *v pc p z)" for x y z
  have flat': "\<And>j k. (A j - msc (t j) (mat 1)) *v p k = (A k - msc (t k) (mat 1)) *v p j"
  proof -
    fix j k
    have "A j *v p k - t j *s p k = A k *v p j - t k *s p j"
      using flat[of j k] by (simp add: algebra_simps eq_diff_eq add_diff_eq diff_eq_eq)
    then show "(A j - msc (t j) (mat 1)) *v p k = (A k - msc (t k) (mat 1)) *v p j" by (simp add: Mv)
  qed
  have s13: "\<And>x y z. Bf x y z = Bf z y x"
    unfolding Bf_def by (rule mv_swap[OF My_sym[OF sym]])
  have swapyz: "\<And>y z. (Ac A y - msc (tc t y) (mat 1)) *v pc p z = (Ac A z - msc (tc t z) (mat 1)) *v pc p y"
  proof -
    fix y z
    have "(Ac A y - msc (tc t y) (mat 1)) *v pc p z
        = (\<Sum>j\<in>UNIV. \<Sum>k\<in>UNIV. (y$j * z$k) *s ((A k - msc (t k) (mat 1)) *v p j))"
      by (simp only: mv_expand flat')
    also have "\<dots> = (\<Sum>k\<in>UNIV. \<Sum>j\<in>UNIV. (y$j * z$k) *s ((A k - msc (t k) (mat 1)) *v p j))"
      by (rule sum.swap)
    also have "\<dots> = (Ac A z - msc (tc t z) (mat 1)) *v pc p y"
      by (simp only: mv_expand mult.commute)
    finally show "(Ac A y - msc (tc t y) (mat 1)) *v pc p z = (Ac A z - msc (tc t z) (mat 1)) *v pc p y" .
  qed
  have s23: "\<And>x y z. Bf x y z = Bf x z y" unfolding Bf_def by (simp only: swapyz)
  have s12: "\<And>x y z. Bf x y z = Bf y x z" using s13 s23 by metis
  have add1: "\<And>x x' y z. Bf (x + x') y z = Bf x y z + Bf x' y z"
    unfolding Bf_def by (simp add: pc_add dotv_add_l)
  have dg: "\<And>x. Bf x x x = 0" unfolding Bf_def by (rule cubic)
  have z0: "\<And>x y z. Bf x y z = 0"
    by (rule sym_trilinear_pol[OF add1 s12 s23 dg])
  have "Bf (axis i 1) (axis j 1) (axis k 1) = dotv (p i) ((A j - msc (t j) (mat 1)) *v p k)"
    by (simp add: Bf_def pc_axis Ac_axis tc_axis)
  then show ?thesis using z0[of "axis i 1" "axis j 1" "axis k 1"] by simp
qed

theorem c3_inclusion:
  fixes p :: "'b::finite \<Rightarrow> 'a::field_char_0^'n" and A :: "'b \<Rightarrow> 'a^'n^'n" and t :: "'b \<Rightarrow> 'a"
  assumes sym: "\<And>i. transpose (A i) = A i"
    and flat: "\<And>i j. A i *v p j + t j *s p i = A j *v p i + t i *s p j"
    and iso: "\<And>i j. dotv (p i) (p j) = 0"
    and cubic: "\<And>c. dotv (pc p c) ((Ac A c - msc (tc t c) (mat 1)) *v pc p c) = 0"
    and maxiso: "\<And>v. (\<forall>i. dotv v (p i) = 0) \<Longrightarrow> \<exists>l. v = (\<Sum>i\<in>UNIV. l i *s p i)"
  shows "\<exists>\<nu>. Ac A c *v (\<Sum>i\<in>UNIV. \<mu> i *s p i) = (\<Sum>i\<in>UNIV. \<nu> i *s p i)"
proof -
  note T = c3_tensor_vanishes[OF sym flat iso cubic]
  define q where "q = (\<Sum>i\<in>UNIV. \<mu> i *s p i)"
  define w where "w = (Ac A c - msc (tc t c) (mat 1)) *v q"
  define mv where "mv = (\<chi> i. \<mu> i)"
  have pcq: "pc p mv = q" unfolding pc_def mv_def q_def by simp
  have w_eq: "w = (\<Sum>j\<in>UNIV. \<Sum>k\<in>UNIV. (c$j * \<mu> k) *s ((A j - msc (t j) (mat 1)) *v p k))"
    unfolding w_def pcq[symmetric] using mv_expand[where A = A and t = t and y = c and p = p and z = mv] by (simp add: mv_def)
  have wp: "\<And>i. dotv w (p i) = 0"
  proof -
    fix i
    have "dotv w (p i) = (\<Sum>j\<in>UNIV. \<Sum>k\<in>UNIV. (c$j * \<mu> k) * dotv ((A j - msc (t j) (mat 1)) *v p k) (p i))"
      by (simp add: w_eq dotv_sum_gen dotv_smul_l)
    also have "\<dots> = 0" by (simp add: dotv_comm[of _ "p i"] T)
    finally show "dotv w (p i) = 0" .
  qed
  obtain lam where l: "w = (\<Sum>i\<in>UNIV. lam i *s p i)" using maxiso[of w] wp by blast
  have "Ac A c *v q = w + tc t c *s q"
    unfolding w_def by (simp add: Mv)
  also have "\<dots> = (\<Sum>i\<in>UNIV. (lam i + tc t c * \<mu> i) *s p i)"
    by (simp add: l q_def sum.distrib algebra_simps vec_eq_iff vsum_nth sum_distrib_left)
  finally have "Ac A c *v q = (\<Sum>i\<in>UNIV. (lam i + tc t c * \<mu> i) *s p i)" .
  then show ?thesis unfolding q_def by (rule exI[where x = "\<lambda>i. lam i + tc t c * \<mu> i"])
qed

end
