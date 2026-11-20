(*  Title:      Lengths_One_Core.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Rational sums-of-squares lengths of biquadratic forms: the algebraic core of the proof of Theorem "one"
   (one interior eigenvalue) of the paper "Rational sums-of-squares lengths of biquadratic forms and orthogonal
   dilations" (Carles Marín, in preparation), Section "One interior eigenvalue".

   Let S be a real skew-symmetric matrix (transpose S = - S) and d > 0, and put Delta = d I + S S, which is
   d I - S^T S. Matrices are HOL-Analysis matrices real^'n^'n; the complex statements use complex^'n^'n.
   Proved without any assumption:
   (1) Delta is symmetric, commutes with S, and x . (Delta x) = d |x|^2 - |S x|^2.
   (2) The kernel and the range of Delta are S-stable, and every vector of the kernel is orthogonal to every
       vector of the range.
   (3) For iota with iota * iota = - d (for instance iota = i sqrt d), the plain transpose (not the conjugate
       transpose) satisfies transpose (iota I + S) (iota I + S) = - Delta and (iota I - S) (iota I + S) = - Delta;
       hence iota I + S is injective on the range of Delta, over the complex numbers.
   (4) Parity, inside the locale one_eigenvalue_planes. The ONLY assumption not proved is the named assumption
       "planes": the kernel of Delta is an orthogonal sum of finitely many 2-dimensional S-stable subspaces (the
       extraction of the theorem on rational isometries by planes, which is not formalized here). Then the
       dimension of the kernel is even, and the dimension of the range is congruent to the dimension of the
       whole space modulo 2. The space V of the paper is modelled as the whole space real^'n, S and Delta being
       the restrictions to V; its dimension m is CARD('n).
*)
theory Lengths_One_Core
  imports "HOL-Analysis.Analysis"
begin

section \<open>Definitions\<close>

definition skew_mat :: "real^'n::finite^'n \<Rightarrow> bool" where
  "skew_mat S \<longleftrightarrow> transpose S = - S"

definition delta_mat :: "real \<Rightarrow> real^'n::finite^'n \<Rightarrow> real^'n^'n" where
  "delta_mat d S = mat d + S ** S"

definition ker_set :: "real \<Rightarrow> real^'n::finite^'n \<Rightarrow> (real^'n) set" where
  "ker_set d S = {x. delta_mat d S *v x = 0}"

definition ran_set :: "real \<Rightarrow> real^'n::finite^'n \<Rightarrow> (real^'n) set" where
  "ran_set d S = range (\<lambda>x. delta_mat d S *v x)"

section \<open>Matrix helper lemmas\<close>

lemma mif_left: "(if P then a else 0) * b = (if P then a * b else (0::'a::comm_ring_1))"
  by simp

lemma mif_right: "b * (if P then a else 0) = (if P then b * a else (0::'a::comm_ring_1))"
  by simp

lemma mat_mult_left:
  fixes A :: "'a::comm_ring_1^'n::finite^'n"
  shows "mat c ** A = (\<chi> i j. c * A $ i $ j)"
  by (simp add: matrix_matrix_mult_def mat_def vec_eq_iff mif_left sum.delta')

lemma mat_mult_right:
  fixes A :: "'a::comm_ring_1^'n::finite^'n"
  shows "A ** mat c = (\<chi> i j. A $ i $ j * c)"
  by (simp add: matrix_matrix_mult_def mat_def vec_eq_iff mif_right sum.delta)

lemma madd_right:
  fixes A B C :: "'a::comm_ring_1^'n::finite^'n"
  shows "(A + B) ** C = A ** C + B ** C"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum.distrib distrib_right)

lemma mvadd_right:
  fixes A B :: "'a::comm_ring_1^'n::finite^'n"
  shows "(A + B) *v x = A *v x + B *v x"
  by (simp add: matrix_vector_mult_def vec_eq_iff sum.distrib distrib_right)

lemma transpose_plus:
  "transpose (A + B) = transpose A + transpose B"
  by (simp add: transpose_def vec_eq_iff)

lemma mat_commute:
  fixes A :: "'a::comm_ring_1^'n::finite^'n"
  shows "A ** mat c = mat c ** A"
  by (simp add: mat_mult_left mat_mult_right mult.commute)

lemma mat_mult_mat:
  "(mat a :: 'a::comm_ring_1^'n::finite^'n) ** mat b = mat (a * b)"
  unfolding mat_mult_left by (simp add: vec_eq_iff mat_def)

lemma mat_uminus: "(mat (- c) :: 'a::comm_ring_1^'n::finite^'n) = - mat c"
  by (simp add: vec_eq_iff mat_def)

lemma mat_vec_scale:
  fixes x :: "'a::comm_ring_1^'n::finite"
  shows "mat c *v x = c *s x"
  by (simp add: vec_eq_iff matrix_vector_mult_def mat_def mif_left sum.delta')

lemma mneg_left:
  fixes A B :: "'a::comm_ring_1^'n::finite^'n"
  shows "(- A) ** B = - (A ** B)"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum_negf)

lemma mneg_right:
  fixes A B :: "'a::comm_ring_1^'n::finite^'n"
  shows "A ** (- B) = - (A ** B)"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum_negf)

lemma mneg_vec:
  fixes A :: "'a::comm_ring_1^'n::finite^'n"
  shows "(- A) *v y = - (A *v y)"
  by (simp add: matrix_vector_mult_def vec_eq_iff sum_negf)

lemma transpose_mat_gen: "transpose (mat c :: 'a::zero^'n::finite^'n) = mat c"
  by (simp add: transpose_def mat_def vec_eq_iff)

lemma tvec:
  fixes A :: "'a::comm_ring_1^'n::finite^'n"
  shows "x v* transpose A = A *v x"
  by (simp add: vector_matrix_mult_def matrix_vector_mult_def transpose_def vec_eq_iff mult.commute)

lemma skew_entry:
  assumes "skew_mat S"
  shows "S $ j $ i = - (S $ i $ j)"
proof -
  have "(transpose S) $ i $ j = (- S) $ i $ j" using assms by (simp add: skew_mat_def)
  then show ?thesis by (simp add: transpose_def)
qed

section \<open>(1) Delta is symmetric, commutes with S, and its quadratic form\<close>

lemma skew_square_symmetric:
  assumes "skew_mat S"
  shows "transpose (S ** S) = S ** S"
proof -
  have "transpose (S ** S) = transpose S ** transpose S" by (simp add: matrix_transpose_mul)
  also have "\<dots> = (- S) ** (- S)" using assms by (simp add: skew_mat_def)
  also have "\<dots> = S ** S" by (simp add: mneg_left mneg_right)
  finally show ?thesis .
qed

theorem delta_symmetric:
  assumes "skew_mat S"
  shows "transpose (delta_mat d S) = delta_mat d S"
proof -
  have "transpose (mat d :: real^'n^'n) = mat d" by (simp add: transpose_def mat_def vec_eq_iff)
  then show ?thesis using skew_square_symmetric [OF assms]
    by (simp add: delta_mat_def transpose_plus)
qed

theorem delta_commutes: "S ** delta_mat d S = delta_mat d S ** S"
  by (simp add: delta_mat_def matrix_add_ldistrib madd_right matrix_mul_assoc mat_commute)

lemma delta_vec: "delta_mat d S *v x = d *s x + S *v (S *v x)"
  by (simp add: delta_mat_def mvadd_right mat_vec_scale matrix_vector_mul_assoc)

lemma vecmat_neg:
  fixes A :: "'a::comm_ring_1^'n::finite^'n"
  shows "x v* (- A) = - (x v* A)"
  by (simp add: vector_matrix_mult_def vec_eq_iff sum_negf)

lemma vecmat_skew:
  assumes "skew_mat S"
  shows "x v* S = - (S *v x)"
proof -
  have "S = - transpose S" using assms by (simp add: skew_mat_def)
  then have "x v* S = x v* (- transpose S)" by simp
  also have "\<dots> = - (x v* transpose S)" by (rule vecmat_neg)
  also have "\<dots> = - (S *v x)" by (simp add: tvec)
  finally show ?thesis .
qed

lemma dot_skew:
  assumes "skew_mat S"
  shows "x \<bullet> (S *v y) = - ((S *v x) \<bullet> y)"
proof -
  have "x \<bullet> (S *v y) = (x v* S) \<bullet> y" by (simp add: dot_lmul_matrix)
  also have "\<dots> = - ((S *v x) \<bullet> y)" using vecmat_skew [OF assms] by simp
  finally show ?thesis .
qed

theorem delta_quadratic_form:
  assumes "skew_mat S"
  shows "x \<bullet> (delta_mat d S *v x) = d * (x \<bullet> x) - (S *v x) \<bullet> (S *v x)"
  by (simp add: delta_vec inner_add_right dot_skew [OF assms] scalar_mult_eq_scaleR)

section \<open>(2) Kernel and range are S-stable and orthogonal\<close>

theorem kernel_stable:
  assumes "x \<in> ker_set d S"
  shows "S *v x \<in> ker_set d S"
proof -
  have "delta_mat d S *v (S *v x) = (delta_mat d S ** S) *v x" by (simp add: matrix_vector_mul_assoc)
  also have "\<dots> = (S ** delta_mat d S) *v x" by (simp add: delta_commutes)
  also have "\<dots> = S *v (delta_mat d S *v x)" by (simp add: matrix_vector_mul_assoc)
  also have "\<dots> = 0" using assms by (simp add: ker_set_def)
  finally show ?thesis by (simp add: ker_set_def)
qed

theorem range_stable:
  assumes "y \<in> ran_set d S"
  shows "S *v y \<in> ran_set d S"
proof -
  from assms obtain z where z: "y = delta_mat d S *v z" by (auto simp: ran_set_def)
  have "S *v y = (S ** delta_mat d S) *v z" by (simp add: z matrix_vector_mul_assoc)
  also have "\<dots> = (delta_mat d S ** S) *v z" by (simp add: delta_commutes)
  also have "\<dots> = delta_mat d S *v (S *v z)" by (simp add: matrix_vector_mul_assoc)
  finally show ?thesis by (auto simp: ran_set_def)
qed

theorem kernel_orthogonal_range:
  assumes "skew_mat S" and "x \<in> ker_set d S" and "y \<in> ran_set d S"
  shows "x \<bullet> y = 0"
proof -
  from assms(3) obtain z where z: "y = delta_mat d S *v z" by (auto simp: ran_set_def)
  have "x v* delta_mat d S = x v* transpose (delta_mat d S)" by (simp add: delta_symmetric [OF assms(1)])
  also have "\<dots> = delta_mat d S *v x" by (simp add: tvec)
  finally have "x v* delta_mat d S = 0" using assms(2) by (simp add: ker_set_def)
  then show ?thesis by (simp add: z dot_lmul_matrix [symmetric])
qed

section \<open>(3) The complex factorisation of Delta\<close>

definition cplx :: "real^'n::finite^'n \<Rightarrow> complex^'n^'n" where
  "cplx A = (\<chi> i j. complex_of_real (A $ i $ j))"

lemma cplx_mult: "cplx (A ** B) = cplx A ** cplx B"
  by (simp add: cplx_def matrix_matrix_mult_def vec_eq_iff)

lemma cplx_add: "cplx (A + B) = cplx A + cplx B"
  by (simp add: cplx_def vec_eq_iff)

lemma cplx_mat: "cplx (mat c) = mat (complex_of_real c)"
  by (simp add: cplx_def mat_def vec_eq_iff)

lemma cplx_transpose: "transpose (cplx A) = cplx (transpose A)"
  by (simp add: cplx_def transpose_def vec_eq_iff)

lemma cplx_uminus: "cplx (- A) = - cplx A"
  by (simp add: cplx_def vec_eq_iff)

lemma cplx_delta: "cplx (delta_mat d S) = mat (complex_of_real d) + cplx S ** cplx S"
  by (simp add: delta_mat_def cplx_add cplx_mat cplx_mult)

lemma cplx_skew:
  assumes "skew_mat S"
  shows "transpose (cplx S) = - cplx S"
  using assms by (simp add: cplx_transpose skew_mat_def cplx_uminus)

theorem factor_difference:
  assumes "skew_mat S" and "\<iota> * \<iota> = - complex_of_real d"
  shows "(mat \<iota> - cplx S) ** (mat \<iota> + cplx S) = - cplx (delta_mat d S)"
proof -
  have c: "mat \<iota> ** cplx S = cplx S ** mat \<iota>" by (rule mat_commute [symmetric])
  have "(mat \<iota> - cplx S) ** (mat \<iota> + cplx S) = (mat \<iota> + (- cplx S)) ** (mat \<iota> + cplx S)"
    by simp
  also have "\<dots> = (mat \<iota> ** mat \<iota> + (- cplx S) ** mat \<iota>) + (mat \<iota> ** cplx S + (- cplx S) ** cplx S)"
    by (simp only: matrix_add_ldistrib madd_right)
  also have "\<dots> = mat \<iota> ** mat \<iota> - cplx S ** cplx S" by (simp add: mneg_left c algebra_simps)
  also have "\<dots> = mat (- complex_of_real d) - cplx S ** cplx S"
    using assms(2) by (simp add: mat_mult_mat)
  also have "\<dots> = - cplx (delta_mat d S)" by (simp add: cplx_delta mat_uminus)
  finally show ?thesis .
qed

theorem factor_transpose:
  assumes "skew_mat S" and "\<iota> * \<iota> = - complex_of_real d"
  shows "transpose (mat \<iota> + cplx S) ** (mat \<iota> + cplx S) = - cplx (delta_mat d S)"
proof -
  have "transpose (mat \<iota> + cplx S) = mat \<iota> - cplx S"
    using cplx_skew [OF assms(1)] by (simp add: transpose_plus transpose_mat_gen)
  then show ?thesis using factor_difference [OF assms] by simp
qed

lemma real_symmetric_injective:
  fixes M :: "real^'n::finite^'n"
  assumes "transpose M = M" and "M *v (M *v a) = 0"
  shows "M *v a = 0"
proof -
  have "M *v a = a v* transpose M" by (simp add: tvec)
  then have "(M *v a) \<bullet> (M *v a) = (a v* M) \<bullet> (M *v a)" using assms(1) by simp
  also have "\<dots> = a \<bullet> (M *v (M *v a))" by (simp add: dot_lmul_matrix)
  also have "\<dots> = 0" using assms(2) by simp
  finally show ?thesis by simp
qed

lemma cplx_vec_re:
  "Re ((cplx M *v z) $ i) = (M *v (\<chi> k. Re (z $ k))) $ i"
  by (simp add: cplx_def matrix_vector_mult_def)

lemma cplx_vec_im:
  "Im ((cplx M *v z) $ i) = (M *v (\<chi> k. Im (z $ k))) $ i"
  by (simp add: cplx_def matrix_vector_mult_def)

lemma complex_symmetric_injective:
  fixes M :: "real^'n::finite^'n"
  assumes "transpose M = M" and "cplx M *v (cplx M *v z) = 0"
  shows "cplx M *v z = 0"
proof -
  define y where "y = cplx M *v z"
  define a where "a = (\<chi> k. Re (z $ k))"
  define b where "b = (\<chi> k. Im (z $ k))"
  have y0: "cplx M *v y = 0" using assms(2) by (simp add: y_def)
  have ya: "(\<chi> k. Re (y $ k)) = M *v a" by (simp add: vec_eq_iff y_def a_def cplx_vec_re)
  have yb: "(\<chi> k. Im (y $ k)) = M *v b" by (simp add: vec_eq_iff y_def b_def cplx_vec_im)
  have "M *v (M *v a) = 0"
  proof (rule vec_eq_iff [THEN iffD2], rule allI)
    fix i
    have "(M *v (M *v a)) $ i = (M *v (\<chi> k. Re (y $ k))) $ i" by (simp add: ya)
    also have "\<dots> = Re ((cplx M *v y) $ i)" by (simp add: cplx_vec_re)
    also have "\<dots> = 0" using y0 by simp
    finally show "(M *v (M *v a)) $ i = (0::real^'n) $ i" by simp
  qed
  then have a0: "M *v a = 0" by (rule real_symmetric_injective [OF assms(1)])
  have "M *v (M *v b) = 0"
  proof (rule vec_eq_iff [THEN iffD2], rule allI)
    fix i
    have "(M *v (M *v b)) $ i = (M *v (\<chi> k. Im (y $ k))) $ i" by (simp add: yb)
    also have "\<dots> = Im ((cplx M *v y) $ i)" by (simp add: cplx_vec_im)
    also have "\<dots> = 0" using y0 by simp
    finally show "(M *v (M *v b)) $ i = (0::real^'n) $ i" by simp
  qed
  then have b0: "M *v b = 0" by (rule real_symmetric_injective [OF assms(1)])
  have "\<And>k. Re (y $ k) = 0" using ya a0 by (metis vec_lambda_beta zero_index)
  moreover have "\<And>k. Im (y $ k) = 0" using yb b0 by (metis vec_lambda_beta zero_index)
  ultimately show ?thesis by (simp add: y_def [symmetric] vec_eq_iff complex_eq_iff)
qed

theorem inverse_on_range:
  assumes "skew_mat S" and "\<iota> * \<iota> = - complex_of_real d"
    and "y \<in> range (\<lambda>z. cplx (delta_mat d S) *v z)"
    and "(mat \<iota> + cplx S) *v y = 0"
  shows "y = 0"
proof -
  from assms(3) obtain z where z: "y = cplx (delta_mat d S) *v z" by auto
  have "(- cplx (delta_mat d S)) *v y = ((mat \<iota> - cplx S) ** (mat \<iota> + cplx S)) *v y"
    by (simp add: factor_difference [OF assms(1,2)])
  also have "\<dots> = (mat \<iota> - cplx S) *v ((mat \<iota> + cplx S) *v y)" by (simp add: matrix_vector_mul_assoc)
  also have "\<dots> = 0" using assms(4) by simp
  finally have "cplx (delta_mat d S) *v y = 0" by (simp add: mneg_vec)
  then have "cplx (delta_mat d S) *v (cplx (delta_mat d S) *v z) = 0" by (simp add: z)
  then show ?thesis using complex_symmetric_injective [OF delta_symmetric [OF assms(1)]] z by simp
qed


section \<open>(4) Parity under the named assumption "planes"\<close>

lemma dim_orth_family:
  fixes A :: "(real^'n::finite) set set"
  assumes "finite A" and "\<forall>P\<in>A. subspace P"
    and "\<forall>P\<in>A. \<forall>Q\<in>A. P \<noteq> Q \<longrightarrow> (\<forall>x\<in>P. \<forall>y\<in>Q. x \<bullet> y = 0)"
  shows "dim (span (\<Union>A)) = (\<Sum>P\<in>A. dim P)"
  using assms
proof (induction A rule: finite_induct)
  case empty
  show ?case using dim_span [of "{}::(real^'n) set"] by simp
next
  case (insert P A)
  have sP: "subspace P" using insert.prems by simp
  have rest: "\<forall>Q\<in>A. subspace Q" using insert.prems by simp
  have orthA: "\<forall>P\<in>A. \<forall>Q\<in>A. P \<noteq> Q \<longrightarrow> (\<forall>x\<in>P. \<forall>y\<in>Q. x \<bullet> y = 0)"
    using insert.prems by blast
  have IH: "dim (span (\<Union>A)) = (\<Sum>Q\<in>A. dim Q)" by (rule insert.IH [OF rest orthA])
  have sT: "subspace (span (\<Union>A))" by (rule subspace_span)
  have inter: "P \<inter> span (\<Union>A) = {0}"
  proof (rule set_eqI, rule iffI)
    fix x assume x: "x \<in> P \<inter> span (\<Union>A)"
    have ortho: "\<And>y. y \<in> \<Union>A \<Longrightarrow> orthogonal x y"
    proof -
      fix y assume "y \<in> \<Union>A"
      then obtain Q where Q: "Q \<in> A" "y \<in> Q" by blast
      have "P \<noteq> Q" using Q(1) insert.hyps(2) by blast
      then show "orthogonal x y" using insert.prems Q x by (auto simp: orthogonal_def)
    qed
    have "orthogonal x x"
    proof (rule orthogonal_to_span)
      show "x \<in> span (\<Union>A)" using x by blast
    next
      fix y assume "y \<in> \<Union>A"
      then show "orthogonal x y" by (rule ortho)
    qed
    then have "x = 0" by (simp add: orthogonal_def)
    then show "x \<in> {0}" by simp
  next
    fix x assume "x \<in> ({0}::(real^'n) set)"
    then show "x \<in> P \<inter> span (\<Union>A)" using sP sT by (simp add: subspace_0)
  qed
  have z: "dim ({0}::(real^'n) set) = 0" using dim_span [of "{}::(real^'n) set"] by simp
  have U: "span (\<Union>(insert P A)) = {x + y |x y. x \<in> P \<and> y \<in> span (\<Union>A)}"
  proof -
    have e: "span P = P" using sP by (simp add: span_eq_iff)
    show ?thesis by (simp add: span_Un e)
  qed
  have "dim {x + y |x y. x \<in> P \<and> y \<in> span (\<Union>A)} + dim (P \<inter> span (\<Union>A))
        = dim P + dim (span (\<Union>A))"
    by (rule dim_sums_Int [OF sP sT])
  then have "dim (span (\<Union>(insert P A))) = dim P + dim (span (\<Union>A))"
    using U inter z by simp
  then show ?case using IH insert.hyps by simp
qed

lemma rank_nullity_mat:
  fixes M :: "real^'n::finite^'n"
  shows "dim (range (\<lambda>x. M *v x)) + dim {x. M *v x = 0} = CARD('n)"
proof -
  define f where "f = (\<lambda>x::real^'n. M *v x)"
  have lin: "linear f" by (simp add: f_def)
  define K where "K = {x. f x = 0}"
  define W where "W = {y::real^'n. \<forall>x\<in>K. orthogonal x y}"
  have sK: "subspace K" unfolding K_def by (rule linear_subspace_kernel [OF lin])
  have sW: "subspace W" unfolding W_def by (rule subspace_orthogonal_to_vectors)
  have dimW: "dim W + dim K = CARD('n)"
    using dim_subspace_orthogonal_to_vectors [OF sK subspace_UNIV subset_UNIV] by (simp add: W_def)
  have inj: "inj_on f (span W)"
  proof (rule inj_onI)
    fix a b assume a: "a \<in> span W" and b: "b \<in> span W" and e: "f a = f b"
    have sp: "span W = W" using sW by (simp add: span_eq_iff)
    have "a - b \<in> W" using a b sp sW by (simp add: subspace_diff)
    moreover have "a - b \<in> K" using e lin by (simp add: K_def linear_diff)
    ultimately have "orthogonal (a - b) (a - b)" by (simp add: W_def)
    then show "a = b" by (simp add: orthogonal_def)
  qed
  have img: "range f = f ` W"
  proof (rule set_eqI, rule iffI)
    fix u assume "u \<in> range f"
    then obtain v where v: "u = f v" by auto
    obtain y z where y: "y \<in> span K" and z: "\<And>w. w \<in> span K \<Longrightarrow> orthogonal z w" and vyz: "v = y + z"
      using orthogonal_subspace_decomp_exists [where S = K and x = v] by blast
    have spK: "span K = K" using sK by (simp add: span_eq_iff)
    have yK: "y \<in> K" using y spK by simp
    have zW: "z \<in> W" using z spK by (auto simp: W_def orthogonal_commute)
    have "f v = f z" using vyz yK lin by (simp add: K_def linear_add)
    then show "u \<in> f ` W" using v zW by blast
  next
    fix u assume "u \<in> f ` W"
    then show "u \<in> range f" by blast
  qed
  have "dim (f ` W) = dim W" by (rule dim_image_eq [OF lin inj])
  then show ?thesis using img dimW by (simp add: f_def K_def)
qed

locale one_eigenvalue_planes =
  fixes S :: "real^'n::finite^'n" and d :: real
  assumes skew: "skew_mat S" and d_pos: "0 < d"
    and planes: "\<exists>A. finite A \<and> (\<forall>P\<in>A. subspace P \<and> dim P = 2 \<and> (\<forall>x\<in>P. S *v x \<in> P))
        \<and> (\<forall>P\<in>A. \<forall>Q\<in>A. P \<noteq> Q \<longrightarrow> (\<forall>x\<in>P. \<forall>y\<in>Q. x \<bullet> y = 0))
        \<and> ker_set d S = span (\<Union>A)"
begin

theorem kernel_dim_even: "even (dim (ker_set d S))"
proof -
  from planes show ?thesis
  proof (elim exE conjE)
    fix A
    assume A1: "finite A"
      and A2: "\<forall>P\<in>A. subspace P \<and> dim P = 2 \<and> (\<forall>x\<in>P. S *v x \<in> P)"
      and A3: "\<forall>P\<in>A. \<forall>Q\<in>A. P \<noteq> Q \<longrightarrow> (\<forall>x\<in>P. \<forall>y\<in>Q. x \<bullet> y = 0)"
      and A4: "ker_set d S = span (\<Union>A)"
    have A5: "\<forall>P\<in>A. subspace P" using A2 by blast
    have "dim (span (\<Union>A)) = (\<Sum>P\<in>A. dim P)" by (rule dim_orth_family [OF A1 A5 A3])
    also have "\<dots> = (\<Sum>P\<in>A. 2)" by (rule sum.cong [OF refl]) (use A2 in blast)
    also have "\<dots> = 2 * card A" by simp
    finally show ?thesis using A4 by simp
  qed
qed

theorem rank_plus_nullity: "dim (ran_set d S) + dim (ker_set d S) = CARD('n)"
  by (simp add: ker_set_def ran_set_def rank_nullity_mat)

theorem range_dim_parity: "dim (ran_set d S) mod 2 = CARD('n) mod 2"
proof -
  obtain k where k: "dim (ker_set d S) = 2 * k" using kernel_dim_even by (auto elim: evenE)
  have arith: "\<And>a k n::nat. a + 2 * k = n \<Longrightarrow> a mod 2 = n mod 2" by presburger
  show ?thesis using rank_plus_nullity k by (intro arith) simp
qed

end

end
