(*  Title:      Prop_Ten_Upper.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Rational sums-of-squares lengths of biquadratic forms: the UPPER BOUND of Proposition "ten" (prop:ten, Prop. 4.5)
   of the paper "Rational sums-of-squares lengths of biquadratic forms and orthogonal dilations" (Carles Marín, in
   preparation). Upper bound only; the lower bound is not formalized here (it uses Milnor's exact sequence and
   Springer's theorem, and is left to a later locale).

   Statement. H is the 10 x 10 rational symmetric matrix that is 3/4 on E1 = <e1,e2,e3,e4>, 57/64 on
   E2 = <e5, e6, 3 e7 + e8 + e9, -e7 + 3 e8 + e10>, and 1 on the complement. The defect of a rational matrix T is
   I - T^T T; T is a contraction when the defect is positive semidefinite. d_Q(H) is the minimum, over rational
   contractions T whose symmetric part (T + T^T)/2 is H, of the rank of the defect. This theory proves d_Q(H) <= 6,
   by an explicit T: H plus the skew blocks of upper entry 7/16 on the pairs (e1,e5) and (e2,e6).

   Matrices are Jordan_Normal_Form matrices rat mat (AFP), written with mat_of_rows_list. The exact rational
   identities on the 10 x 10 data are checked by evaluation (eval). The positive semidefiniteness of
   C^T diag(d) C with d_i > 0 is a general lemma (psd_of_factor), not an evaluation. The rank is the rank of
   Jordan_Normal_Form (dimension of the span of the columns): rank <= 6 because the defect is C^T (diag(d) C) with C
   of 6 rows (rank of a product is at most the rank of the left factor, which has 6 columns); rank >= 6 because
   the principal 6 x 6 minor on the rows and columns 0,1,2,3,6,7 (the Schur index) is diagonal with positive
   entries, so its determinant is nonzero (rank_gt_minor).
*)
theory Prop_Ten_Upper
  imports
    "Jordan_Normal_Form.Matrix"
    "Jordan_Normal_Form.Matrix_IArray_Impl"
    "Jordan_Normal_Form.Determinant_Impl"
    "Jordan_Normal_Form.DL_Rank_Submatrix"
    "Jordan_Normal_Form.DL_Submatrix"
    "Jordan_Normal_Form.Determinant"
    "BenOr_Kozen_Reif.More_Matrix"
begin

section \<open>Data of the certificate\<close>

definition H0 :: "rat mat" where
  "H0 = mat_of_rows_list 10 [[3/4, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 3/4, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 3/4, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 3/4, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 57/64, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 57/64, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 317/352, 0, -21/704, 7/704],
    [0, 0, 0, 0, 0, 0, 0, 317/352, -7/704, -21/704],
    [0, 0, 0, 0, 0, 0, -21/704, -7/704, 697/704, 0],
    [0, 0, 0, 0, 0, 0, 7/704, -21/704, 0, 697/704]]"

definition T0 :: "rat mat" where
  "T0 = mat_of_rows_list 10 [[3/4, 0, 0, 0, 7/16, 0, 0, 0, 0, 0],
    [0, 3/4, 0, 0, 0, 7/16, 0, 0, 0, 0],
    [0, 0, 3/4, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 3/4, 0, 0, 0, 0, 0, 0],
    [-7/16, 0, 0, 0, 57/64, 0, 0, 0, 0, 0],
    [0, -7/16, 0, 0, 0, 57/64, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 317/352, 0, -21/704, 7/704],
    [0, 0, 0, 0, 0, 0, 0, 317/352, -7/704, -21/704],
    [0, 0, 0, 0, 0, 0, -21/704, -7/704, 697/704, 0],
    [0, 0, 0, 0, 0, 0, 7/704, -21/704, 0, 697/704]]"

definition Delta :: "rat mat" where
  "Delta = mat_of_rows_list 10 [[63/256, 0, 0, 0, 63/1024, 0, 0, 0, 0, 0],
    [0, 63/256, 0, 0, 0, 63/1024, 0, 0, 0, 0],
    [0, 0, 7/16, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 7/16, 0, 0, 0, 0, 0, 0],
    [63/1024, 0, 0, 0, 63/4096, 0, 0, 0, 0, 0],
    [0, 63/1024, 0, 0, 0, 63/4096, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 385/2048, 0, 231/4096, -77/4096],
    [0, 0, 0, 0, 0, 0, 0, 385/2048, 77/4096, 231/4096],
    [0, 0, 0, 0, 0, 0, 231/4096, 77/4096, 77/4096, 0],
    [0, 0, 0, 0, 0, 0, -77/4096, 231/4096, 0, 77/4096]]"

definition C0 :: "rat mat" where
  "C0 = mat_of_rows_list 10 [[1, 0, 0, 0, 1/4, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 1/4, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 3/10, -1/10],
    [0, 0, 0, 0, 0, 0, 0, 1, 1/10, 3/10]]"

definition dd :: "rat list" where
  "dd = [63/256, 63/256, 7/16, 7/16, 385/2048, 385/2048]"

definition dmat :: "rat list \<Rightarrow> rat mat" where
  "dmat d = mat (length d) (length d) (\<lambda>(i,j). if i = j then d ! i else 0)"

definition sym_part :: "rat mat \<Rightarrow> rat mat" where
  "sym_part M = (1/2) \<cdot>\<^sub>m (M + M\<^sup>T)"

definition defect :: "rat mat \<Rightarrow> rat mat" where
  "defect M = 1\<^sub>m (dim_col M) - M\<^sup>T * M"

section \<open>The exact identities on the data\<close>

lemma H0_carrier: "H0 \<in> carrier_mat 10 10"
  unfolding H0_def mat_of_rows_list_def by auto

lemma T0_carrier: "T0 \<in> carrier_mat 10 10"
  unfolding T0_def mat_of_rows_list_def by auto

lemma Delta_carrier: "Delta \<in> carrier_mat 10 10"
  unfolding Delta_def mat_of_rows_list_def by auto

lemma C0_carrier: "C0 \<in> carrier_mat 6 10"
  unfolding C0_def mat_of_rows_list_def by auto

lemma dd_length: "length dd = 6"
  unfolding dd_def by simp

lemma dd_pos: "\<forall>i<6. 0 < dd ! i"
proof (intro allI impI)
  fix i :: nat assume "i < 6"
  hence "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5" by arith
  thus "0 < dd ! i" by (auto simp: dd_def)
qed

lemma sym_T0_eq_H0: "sym_part T0 = H0"
  unfolding sym_part_def T0_def H0_def by eval

lemma Delta_eq_defect: "Delta = 1\<^sub>m 10 - T0\<^sup>T * T0"
  unfolding Delta_def T0_def by eval

lemma Delta_factor: "Delta = C0\<^sup>T * (dmat dd * C0)"
  unfolding Delta_def C0_def dd_def dmat_def by eval

section \<open>Positive semidefiniteness of C^T diag(d) C, in general\<close>

definition psd :: "nat \<Rightarrow> rat mat \<Rightarrow> bool" where
  "psd n A \<longleftrightarrow> (\<forall>x\<in>carrier_vec n. 0 \<le> x \<bullet> (A *\<^sub>v x))"

lemma transpose_scalar_prod:
  fixes Q :: "rat mat"
  assumes "Q \<in> carrier_mat k n" "x \<in> carrier_vec n" "y \<in> carrier_vec k"
  shows "x \<bullet> (Q\<^sup>T *\<^sub>v y) = (Q *\<^sub>v x) \<bullet> y"
proof -
  have "Q\<^sup>T *\<^sub>v y = vec n (\<lambda>j. y \<bullet> col Q j)"
  proof (rule eq_vecI)
    fix i assume i: "i < dim_vec (vec n (\<lambda>j. y \<bullet> col Q j))"
    hence i': "i < n" by simp
    have ci: "col Q i \<in> carrier_vec k" using assms(1) i' by auto
    have "(Q\<^sup>T *\<^sub>v y) $ i = row Q\<^sup>T i \<bullet> y" using assms i' by simp
    also have "row Q\<^sup>T i = col Q i" using assms(1) i' by simp
    also have "col Q i \<bullet> y = y \<bullet> col Q i" by (rule comm_scalar_prod[OF ci assms(3)])
    finally show "(Q\<^sup>T *\<^sub>v y) $ i = vec n (\<lambda>j. y \<bullet> col Q j) $ i" using i' by simp
  next
    show "dim_vec (Q\<^sup>T *\<^sub>v y) = dim_vec (vec n (\<lambda>j. y \<bullet> col Q j))" using assms by simp
  qed
  hence "x \<bullet> (Q\<^sup>T *\<^sub>v y) = vec n (\<lambda>j. y \<bullet> col Q j) \<bullet> x"
    using assms by (subst comm_scalar_prod[of _ n]) auto
  also have "\<dots> = y \<bullet> vec k (\<lambda>i. row Q i \<bullet> x)"
    using assoc_scalar_prod[of y k Q n x] assms by auto
  also have "vec k (\<lambda>i. row Q i \<bullet> x) = Q *\<^sub>v x"
    unfolding mult_mat_vec_def using assms by auto
  finally show ?thesis
    using assms by (subst comm_scalar_prod[of _ k]) auto
qed

lemma dmat_mult_vec:
  assumes "length d = k" "z \<in> carrier_vec k" "i < k"
  shows "(dmat d *\<^sub>v z) $ i = d ! i * z $ i"
proof -
  have "(dmat d *\<^sub>v z) $ i = row (dmat d) i \<bullet> z"
    using assms by (simp add: dmat_def)
  also have "\<dots> = (\<Sum>j\<in>{0..<k}. row (dmat d) i $ j * z $ j)"
    using assms by (simp add: scalar_prod_def dmat_def)
  also have "\<dots> = (\<Sum>j\<in>{0..<k}. (if i = j then d ! i else 0) * z $ j)"
    using assms by (intro sum.cong) (auto simp: dmat_def)
  also have "\<dots> = (\<Sum>j\<in>{0..<k}. if i = j then d ! i * z $ i else 0)"
    by (intro sum.cong) auto
  also have "\<dots> = d ! i * z $ i"
    using assms by (simp add: sum.delta')
  finally show ?thesis .
qed

lemma psd_form:
  fixes Q :: "rat mat" and d :: "rat list"
  assumes "Q \<in> carrier_mat k n" "x \<in> carrier_vec n" "length d = k"
  shows "x \<bullet> ((Q\<^sup>T * (dmat d * Q)) *\<^sub>v x) = (\<Sum>i\<in>{0..<k}. d ! i * ((Q *\<^sub>v x) $ i)\<^sup>2)"
proof -
  have dm: "dmat d \<in> carrier_mat k k" using assms(3) by (simp add: dmat_def)
  have Cx: "Q *\<^sub>v x \<in> carrier_vec k" using assms by auto
  have DCx: "dmat d *\<^sub>v (Q *\<^sub>v x) \<in> carrier_vec k" using dm Cx by auto
  have Qt: "Q\<^sup>T \<in> carrier_mat n k" using assms(1) by simp
  have DQ: "dmat d * Q \<in> carrier_mat k n" using dm assms(1) by simp
  have e1: "(Q\<^sup>T * (dmat d * Q)) *\<^sub>v x = Q\<^sup>T *\<^sub>v ((dmat d * Q) *\<^sub>v x)"
    by (rule assoc_mult_mat_vec[OF Qt DQ assms(2)])
  have e2: "(dmat d * Q) *\<^sub>v x = dmat d *\<^sub>v (Q *\<^sub>v x)"
    by (rule assoc_mult_mat_vec[OF dm assms(1) assms(2)])
  have "(Q\<^sup>T * (dmat d * Q)) *\<^sub>v x = Q\<^sup>T *\<^sub>v (dmat d *\<^sub>v (Q *\<^sub>v x))"
    using e1 e2 by simp
  hence "x \<bullet> ((Q\<^sup>T * (dmat d * Q)) *\<^sub>v x) = x \<bullet> (Q\<^sup>T *\<^sub>v (dmat d *\<^sub>v (Q *\<^sub>v x)))" by simp
  also have "\<dots> = (Q *\<^sub>v x) \<bullet> (dmat d *\<^sub>v (Q *\<^sub>v x))"
    using transpose_scalar_prod[OF assms(1,2) DCx] .
  also have "\<dots> = (\<Sum>i\<in>{0..<k}. (Q *\<^sub>v x) $ i * (dmat d *\<^sub>v (Q *\<^sub>v x)) $ i)"
    by (simp only: scalar_prod_def carrier_vecD[OF DCx])
  also have "\<dots> = (\<Sum>i\<in>{0..<k}. d ! i * ((Q *\<^sub>v x) $ i)\<^sup>2)"
    using dmat_mult_vec[OF assms(3) Cx] by (intro sum.cong) (auto simp: power2_eq_square)
  finally show ?thesis .
qed

lemma psd_of_factor:
  fixes Q :: "rat mat" and d :: "rat list"
  assumes "Q \<in> carrier_mat k n" "length d = k" "\<forall>i<k. 0 < d ! i"
  shows "psd n (Q\<^sup>T * (dmat d * Q))"
  unfolding psd_def
proof (intro ballI)
  fix x :: "rat vec" assume x: "x \<in> carrier_vec n"
  show "0 \<le> x \<bullet> ((Q\<^sup>T * (dmat d * Q)) *\<^sub>v x)"
    unfolding psd_form[OF assms(1) x assms(2)]
    using assms(3) by (intro sum_nonneg) auto
qed

lemma Delta_psd: "psd 10 Delta"
  unfolding Delta_factor using psd_of_factor[OF C0_carrier dd_length dd_pos] .

section \<open>The rank of the defect is 6\<close>

abbreviation rk :: "nat \<Rightarrow> rat mat \<Rightarrow> nat" where
  "rk n A \<equiv> vec_space.rank n A"

lemma dmat_carrier: "length d = k \<Longrightarrow> dmat d \<in> carrier_mat k k"
  by (simp add: dmat_def)

lemma rank_Delta_le_6: "rk 10 Delta \<le> 6"
proof -
  have Ct: "C0\<^sup>T \<in> carrier_mat 10 6" using C0_carrier by simp
  have B: "dmat dd * C0 \<in> carrier_mat 6 10"
    using dmat_carrier[OF dd_length] C0_carrier by auto
  have "rk 10 (C0\<^sup>T * (dmat dd * C0)) \<le> rk 10 (C0\<^sup>T)"
    using vec_space.rank_mat_mul_right[OF Ct B] .
  also have "\<dots> \<le> 6" using vec_space.rank_le_nc[OF Ct] .
  finally show ?thesis unfolding Delta_factor .
qed

definition I6 :: "nat set" where "I6 = {0, 1, 2, 3, 6, 7}"

definition Dsub :: "rat mat" where
  "Dsub = mat_of_rows_list 6 [[63/256, 0, 0, 0, 0, 0],
    [0, 63/256, 0, 0, 0, 0],
    [0, 0, 7/16, 0, 0, 0],
    [0, 0, 0, 7/16, 0, 0],
    [0, 0, 0, 0, 385/2048, 0],
    [0, 0, 0, 0, 0, 385/2048]]"

lemma least_I6: "(LEAST a. a \<in> I6) = 0"
  by (simp add: I6_def Least_equality)

lemma pick_I6_step:
  assumes "pick I6 n = m" "k = n + 1" "m' \<in> I6" "m < m'" "\<forall>a\<in>I6. m < a \<longrightarrow> m' \<le> a"
  shows "pick I6 k = m'"
proof -
  have "pick I6 k = (LEAST a. a \<in> I6 \<and> pick I6 n < a)" using assms(2) by simp
  also have "\<dots> = m'" using assms by (intro Least_equality) auto
  finally show ?thesis .
qed

lemma pick_I6:
  "pick I6 0 = 0" "pick I6 1 = 1" "pick I6 2 = 2" "pick I6 3 = 3" "pick I6 4 = 6" "pick I6 5 = 7"
proof -
  have p0: "pick I6 0 = 0" by (simp add: I6_def Least_equality)
  have p1: "pick I6 1 = 1" by (rule pick_I6_step[OF p0]) (simp_all add: I6_def)
  have p2: "pick I6 2 = 2" by (rule pick_I6_step[OF p1]) (simp_all add: I6_def)
  have p3: "pick I6 3 = 3" by (rule pick_I6_step[OF p2]) (simp_all add: I6_def)
  have p4: "pick I6 4 = 6" by (rule pick_I6_step[OF p3]) (simp_all add: I6_def)
  have p5: "pick I6 5 = 7" by (rule pick_I6_step[OF p4]) (simp_all add: I6_def)
  show "pick I6 0 = 0" "pick I6 1 = 1" "pick I6 2 = 2" "pick I6 3 = 3" "pick I6 4 = 6" "pick I6 5 = 7"
    using p0 p1 p2 p3 p4 p5 by simp_all
qed

lemma dim_Delta: "dim_row Delta = 10" "dim_col Delta = 10"
  using Delta_carrier by auto

lemma dim_Dsub: "dim_row Dsub = 6" "dim_col Dsub = 6"
  unfolding Dsub_def by eval+

lemma card_I6: "card {i. i < 10 \<and> i \<in> I6} = 6"
proof -
  have "{i. i < 10 \<and> i \<in> I6} = I6" unfolding I6_def by auto
  thus ?thesis unfolding I6_def by simp
qed

lemma Delta_pick:
  fixes pk :: "nat \<Rightarrow> nat"
  assumes "pk 0 = 0" "pk 1 = 1" "pk 2 = 2" "pk 3 = 3" "pk 4 = 6" "pk 5 = 7" "i < 6" "j < 6"
  shows "Delta $$ (pk i, pk j) = Dsub $$ (i, j)"
proof -
  have iL: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5" using assms(7) by arith
  have jL: "j = 0 \<or> j = 1 \<or> j = 2 \<or> j = 3 \<or> j = 4 \<or> j = 5" using assms(8) by arith
  have p1: "pk (Suc 0) = 1" using assms(2) by simp
  from iL jL show ?thesis
    by (elim disjE) (auto simp add: assms(1-6) p1 Delta_def Dsub_def mat_of_rows_list_def)
qed

lemma minor_Delta: "submatrix Delta I6 I6 = Dsub"
proof (rule eq_matI)
  have c: "card {i. i < dim_row Delta \<and> i \<in> I6} = 6" using card_I6 dim_Delta by simp
  have c': "card {i. i < dim_col Delta \<and> i \<in> I6} = 6" using card_I6 dim_Delta by simp
  show "dim_row (submatrix Delta I6 I6) = dim_row Dsub"
    using c by (simp add: dim_submatrix dim_Dsub)
  show "dim_col (submatrix Delta I6 I6) = dim_col Dsub"
    using c' by (simp add: dim_submatrix dim_Dsub)
  fix i j assume ij: "i < dim_row Dsub" "j < dim_col Dsub"
  hence i6: "i < 6" and j6: "j < 6" by (simp_all add: dim_Dsub)
  have "submatrix Delta I6 I6 $$ (i, j) = Delta $$ (pick I6 i, pick I6 j)"
    using c c' i6 j6 by (simp add: submatrix_index)
  also have "\<dots> = Dsub $$ (i, j)"
    by (rule Delta_pick[OF pick_I6(1) pick_I6(2) pick_I6(3) pick_I6(4) pick_I6(5) pick_I6(6) i6 j6])
  finally show "submatrix Delta I6 I6 $$ (i, j) = Dsub $$ (i, j)" .
qed

lemma det_Dsub: "det Dsub \<noteq> 0"
  unfolding Dsub_def by eval

lemma rank_Delta_ge_6: "6 \<le> rk 10 Delta"
proof -
  have "det (submatrix Delta I6 I6) \<noteq> 0" using minor_Delta det_Dsub by simp
  from vec_space.rank_gt_minor[OF Delta_carrier this]
  have "card {j. j < 10 \<and> j \<in> I6} \<le> rk 10 Delta" .
  moreover have "card {j. j < 10 \<and> j \<in> I6} = 6" by (rule card_I6)
  ultimately show ?thesis by simp
qed

theorem rank_Delta: "rk 10 Delta = 6"
  using rank_Delta_le_6 rank_Delta_ge_6 by simp

section \<open>The upper bound d_Q(H) <= 6\<close>

text \<open>An n x n rational matrix T is a contraction when its defect I - T^T T is positive semidefinite.
  The set of defect ranks of the contractions whose symmetric part is M; d_Q(M) is its minimum (the paper's
  definition: minimum of the rank of I - T^T T over rational contractions T with (T + T^T)/2 = M).\<close>

definition contraction :: "nat \<Rightarrow> rat mat \<Rightarrow> bool" where
  "contraction n B \<longleftrightarrow> B \<in> carrier_mat n n \<and> psd n (1\<^sub>m n - B\<^sup>T * B)"

definition defect_ranks :: "nat \<Rightarrow> rat mat \<Rightarrow> nat set" where
  "defect_ranks n M = {rk n (1\<^sub>m n - B\<^sup>T * B) | B. contraction n B \<and> sym_part B = M}"

definition d_Q :: "nat \<Rightarrow> rat mat \<Rightarrow> nat" where
  "d_Q n M = Inf (defect_ranks n M)"

theorem T0_contraction: "contraction 10 T0"
  unfolding contraction_def using T0_carrier Delta_psd Delta_eq_defect by simp

theorem prop_ten_defect_exists:
  "\<exists>B. B \<in> carrier_mat 10 10 \<and> sym_part B = H0 \<and> psd 10 (1\<^sub>m 10 - B\<^sup>T * B)
       \<and> rk 10 (1\<^sub>m 10 - B\<^sup>T * B) \<le> 6"
  using T0_carrier sym_T0_eq_H0 Delta_psd rank_Delta_le_6 Delta_eq_defect by (intro exI[of _ T0]) simp

text \<open>The set of defect ranks is not empty (Inf of the empty set of naturals would be 0 and would make the
  bound below vacuous): it contains 6, attained by T0.\<close>

theorem prop_ten_defect_ranks_contain_6: "6 \<in> defect_ranks 10 H0"
proof -
  have "rk 10 (1\<^sub>m 10 - T0\<^sup>T * T0) \<in> defect_ranks 10 H0"
    unfolding defect_ranks_def using T0_contraction sym_T0_eq_H0 by blast
  thus ?thesis using rank_Delta Delta_eq_defect by simp
qed

theorem prop_ten_defect_le_6: "d_Q 10 H0 \<le> 6"
proof -
  have "rk 10 (1\<^sub>m 10 - T0\<^sup>T * T0) \<in> defect_ranks 10 H0"
    unfolding defect_ranks_def using T0_contraction sym_T0_eq_H0 by blast
  hence "d_Q 10 H0 \<le> rk 10 (1\<^sub>m 10 - T0\<^sup>T * T0)"
    unfolding d_Q_def by (rule wellorder_Inf_le1)
  also have "\<dots> = 6" using rank_Delta Delta_eq_defect by simp
  finally show ?thesis .
qed

end
