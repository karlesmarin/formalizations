(*  Title:      Prop_Forest_Upper.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Rational and integral sums-of-squares lengths of biquadratic forms: the UPPER BOUND of Proposition "forest"
   (prop:forest, Prop. 9.5) of the paper "Rational sums-of-squares lengths of biquadratic forms and orthogonal
   dilations" (Carles Marín, in preparation).  UPPER BOUND ONLY: for the forest Gamma = 4 P_6 (disjoint union) 3 P_5
   on 39 vertices we prove l_Z(Gamma) <= 46 (hence l_Q(Gamma) <= 46) by an explicit integral representation.
   The lower bound l_Q(Gamma) >= 46 (Springer's theorem and residues over Q(t)) is NOT formalized here.

   We use the matrix form of Proposition 2.1 of the paper: l(H) <= r iff there are A, B with r rows,
   A^T A = B^T B = I and A^T B + B^T A = 2H (the equivalence with sums of squares of bilinear forms is not
   formalized here).  Here the matrix called H below is 2H, the adjacency matrix of the graph.  Matrices are
   Jordan_Normal_Form matrices (int mat).

   Results.
     path_repr    : for every j, A_j = [I_j; 0] and B_j = shift (both integral, (j+1) x j) represent the adjacency
                    matrix of the path P_j with j + 1 rows (general proof, not by evaluation).
     block_sum    : representations add by blocks: (r1 + r2) rows for the direct sum.
     forest_repr  : any list of paths with sizes js is represented with sum (j + 1) rows.
     forest_upper : Gamma = 4 P_6 (+) 3 P_5 has an integral representation with 46 rows; so l_Z <= 46, l_Q <= 46.
     forest_eval  : the same, the identities for the concrete 39-column, 46-row matrices checked by evaluation.
*)
theory Prop_Forest_Upper
  imports
    "Jordan_Normal_Form.Matrix"
    "Jordan_Normal_Form.Matrix_IArray_Impl"
begin

section \<open>Representations and block sums\<close>

text \<open>@{text "repr H n r A B"}: H is n x n, A and B are r x n, A^T A = B^T B = I_n and A^T B + B^T A = H
  (so H is "2 H" in the notation of the paper).  Integral matrices.\<close>

definition repr :: "int mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int mat \<Rightarrow> int mat \<Rightarrow> bool" where
  "repr H n r A B \<longleftrightarrow> H \<in> carrier_mat n n \<and> A \<in> carrier_mat r n \<and> B \<in> carrier_mat r n
     \<and> transpose_mat A * A = 1\<^sub>m n \<and> transpose_mat B * B = 1\<^sub>m n
     \<and> transpose_mat A * B + transpose_mat B * A = H"

text \<open>Integral length at most r: an integral representation with r rows.  Rational length: the same
  over the rationals (matrices mapped with of_int; every integral representation is a rational one).\<close>

definition lenZ_le :: "nat \<Rightarrow> int mat \<Rightarrow> bool" where
  "lenZ_le r H \<longleftrightarrow> (\<exists>A B. repr H (dim_row H) r A B)"

definition lenQ_le :: "nat \<Rightarrow> int mat \<Rightarrow> bool" where
  "lenQ_le r H \<longleftrightarrow> (\<exists>A B::rat mat. H \<in> carrier_mat (dim_row H) (dim_row H)
     \<and> A \<in> carrier_mat r (dim_row H) \<and> B \<in> carrier_mat r (dim_row H)
     \<and> transpose_mat A * A = 1\<^sub>m (dim_row H) \<and> transpose_mat B * B = 1\<^sub>m (dim_row H)
     \<and> transpose_mat A * B + transpose_mat B * A = map_mat of_int H)"

definition bd :: "int mat \<Rightarrow> int mat \<Rightarrow> int mat" where
  "bd X Y = four_block_mat X (0\<^sub>m (dim_row X) (dim_col Y)) (0\<^sub>m (dim_row Y) (dim_col X)) Y"

lemma bd_eq:
  assumes "X \<in> carrier_mat a b" "Y \<in> carrier_mat c d"
  shows "bd X Y = four_block_mat X (0\<^sub>m a d) (0\<^sub>m c b) Y"
proof -
  have "dim_row X = a" "dim_col X = b" "dim_row Y = c" "dim_col Y = d"
    using assms by (simp_all only: carrier_matD)
  then show ?thesis unfolding bd_def by simp
qed

lemma bd_carrier:
  assumes "X \<in> carrier_mat a b" "Y \<in> carrier_mat c d"
  shows "bd X Y \<in> carrier_mat (a + c) (b + d)"
  unfolding bd_eq[OF assms] by (rule four_block_carrier_mat[OF assms])

lemma bd_transpose:
  assumes "X \<in> carrier_mat a b" "Y \<in> carrier_mat c d"
  shows "transpose_mat (bd X Y) = bd (transpose_mat X) (transpose_mat Y)"
proof -
  have tX: "transpose_mat X \<in> carrier_mat b a" and tY: "transpose_mat Y \<in> carrier_mat d c"
    using assms by (simp_all only: transpose_carrier_mat)
  have z1: "transpose_mat (0\<^sub>m a d :: int mat) = 0\<^sub>m d a" by (rule eq_matI) simp_all
  have z2: "transpose_mat (0\<^sub>m c b :: int mat) = 0\<^sub>m b c" by (rule eq_matI) simp_all
  have "transpose_mat (four_block_mat X (0\<^sub>m a d) (0\<^sub>m c b) Y)
      = four_block_mat (transpose_mat X) (transpose_mat (0\<^sub>m c b)) (transpose_mat (0\<^sub>m a d)) (transpose_mat Y)"
    by (rule transpose_four_block_mat[OF assms(1) zero_carrier_mat zero_carrier_mat assms(2)])
  then show ?thesis
    by (simp only: bd_eq[OF assms(1) assms(2)] bd_eq[OF tX tY] z1 z2)
qed

lemma bd_mult:
  assumes "X1 \<in> carrier_mat a b" "X2 \<in> carrier_mat c d" "Y1 \<in> carrier_mat b e" "Y2 \<in> carrier_mat d f"
  shows "bd X1 X2 * bd Y1 Y2 = bd (X1 * Y1) (X2 * Y2)"
proof -
  have m1: "X1 * Y1 \<in> carrier_mat a e" using assms(1,3) by (rule mult_carrier_mat)
  have m2: "X2 * Y2 \<in> carrier_mat c f" using assms(2,4) by (rule mult_carrier_mat)
  have z: "0\<^sub>m a d * 0\<^sub>m d e = (0\<^sub>m a e :: int mat)" "X1 * 0\<^sub>m b f = (0\<^sub>m a f :: int mat)"
    "0\<^sub>m a d * Y2 = (0\<^sub>m a f :: int mat)" "0\<^sub>m c b * Y1 = (0\<^sub>m c e :: int mat)"
    "X2 * 0\<^sub>m d e = (0\<^sub>m c e :: int mat)" "0\<^sub>m c b * 0\<^sub>m b f = (0\<^sub>m c f :: int mat)"
    by (rule left_mult_zero_mat[OF zero_carrier_mat] right_mult_zero_mat[OF assms(1)]
        left_mult_zero_mat[OF assms(4)] left_mult_zero_mat[OF assms(3)]
        right_mult_zero_mat[OF assms(2)] left_mult_zero_mat[OF zero_carrier_mat])+
  have "four_block_mat X1 (0\<^sub>m a d) (0\<^sub>m c b) X2 * four_block_mat Y1 (0\<^sub>m b f) (0\<^sub>m d e) Y2
      = four_block_mat (X1 * Y1 + 0\<^sub>m a d * 0\<^sub>m d e) (X1 * 0\<^sub>m b f + 0\<^sub>m a d * Y2)
          (0\<^sub>m c b * Y1 + X2 * 0\<^sub>m d e) (0\<^sub>m c b * 0\<^sub>m b f + X2 * Y2)"
    by (rule mult_four_block_mat[OF assms(1) zero_carrier_mat zero_carrier_mat assms(2)
        assms(3) zero_carrier_mat zero_carrier_mat assms(4)])
  also have "\<dots> = four_block_mat (X1 * Y1) (0\<^sub>m a f) (0\<^sub>m c e) (X2 * Y2)"
    by (simp only: z right_add_zero_mat[OF m1] left_add_zero_mat[OF m2]
        left_add_zero_mat[OF zero_carrier_mat] right_add_zero_mat[OF zero_carrier_mat])
  finally show ?thesis
    by (simp only: bd_eq[OF assms(1) assms(2)] bd_eq[OF assms(3) assms(4)] bd_eq[OF m1 m2])
qed

lemma bd_add:
  assumes "X1 \<in> carrier_mat a b" "X2 \<in> carrier_mat c d" "Y1 \<in> carrier_mat a b" "Y2 \<in> carrier_mat c d"
  shows "bd X1 X2 + bd Y1 Y2 = bd (X1 + Y1) (X2 + Y2)"
proof -
  have s1: "X1 + Y1 \<in> carrier_mat a b" using assms(3) by (rule add_carrier_mat)
  have s2: "X2 + Y2 \<in> carrier_mat c d" using assms(4) by (rule add_carrier_mat)
  have "four_block_mat X1 (0\<^sub>m a d) (0\<^sub>m c b) X2 + four_block_mat Y1 (0\<^sub>m a d) (0\<^sub>m c b) Y2
      = four_block_mat (X1 + Y1) (0\<^sub>m a d + 0\<^sub>m a d) (0\<^sub>m c b + 0\<^sub>m c b) (X2 + Y2)"
    by (rule add_four_block_mat[OF assms(1) zero_carrier_mat zero_carrier_mat assms(2)
        assms(3) zero_carrier_mat zero_carrier_mat assms(4)])
  also have "\<dots> = four_block_mat (X1 + Y1) (0\<^sub>m a d) (0\<^sub>m c b) (X2 + Y2)"
    by (simp only: right_add_zero_mat[OF zero_carrier_mat])
  finally show ?thesis
    by (simp only: bd_eq[OF assms(1) assms(2)] bd_eq[OF assms(3) assms(4)] bd_eq[OF s1 s2])
qed

lemma bd_one: "bd (1\<^sub>m a) (1\<^sub>m c) = 1\<^sub>m (a + c)"
  unfolding bd_def by simp

theorem block_sum:
  assumes "repr H1 n1 r1 A1 B1" "repr H2 n2 r2 A2 B2"
  shows "repr (bd H1 H2) (n1 + n2) (r1 + r2) (bd A1 A2) (bd B1 B2)"
proof -
  from assms have c: "H1 \<in> carrier_mat n1 n1" "A1 \<in> carrier_mat r1 n1" "B1 \<in> carrier_mat r1 n1"
    "H2 \<in> carrier_mat n2 n2" "A2 \<in> carrier_mat r2 n2" "B2 \<in> carrier_mat r2 n2"
    and i: "transpose_mat A1 * A1 = 1\<^sub>m n1" "transpose_mat B1 * B1 = 1\<^sub>m n1"
    "transpose_mat A2 * A2 = 1\<^sub>m n2" "transpose_mat B2 * B2 = 1\<^sub>m n2"
    and s: "transpose_mat A1 * B1 + transpose_mat B1 * A1 = H1"
    "transpose_mat A2 * B2 + transpose_mat B2 * A2 = H2"
    unfolding repr_def by auto
  have tA1: "transpose_mat A1 \<in> carrier_mat n1 r1" and tB1: "transpose_mat B1 \<in> carrier_mat n1 r1"
    and tA2: "transpose_mat A2 \<in> carrier_mat n2 r2" and tB2: "transpose_mat B2 \<in> carrier_mat n2 r2"
    using c by auto
  have p1: "transpose_mat A1 * B1 \<in> carrier_mat n1 n1" "transpose_mat B1 * A1 \<in> carrier_mat n1 n1"
    using tA1 tB1 c by auto
  have p2: "transpose_mat A2 * B2 \<in> carrier_mat n2 n2" "transpose_mat B2 * A2 \<in> carrier_mat n2 n2"
    using tA2 tB2 c by auto
  have ta: "transpose_mat (bd A1 A2) = bd (transpose_mat A1) (transpose_mat A2)"
    by (rule bd_transpose[OF c(2) c(5)])
  have tb: "transpose_mat (bd B1 B2) = bd (transpose_mat B1) (transpose_mat B2)"
    by (rule bd_transpose[OF c(3) c(6)])
  show ?thesis unfolding repr_def
  proof (intro conjI)
    show "bd H1 H2 \<in> carrier_mat (n1 + n2) (n1 + n2)" by (rule bd_carrier[OF c(1) c(4)])
    show "bd A1 A2 \<in> carrier_mat (r1 + r2) (n1 + n2)" by (rule bd_carrier[OF c(2) c(5)])
    show "bd B1 B2 \<in> carrier_mat (r1 + r2) (n1 + n2)" by (rule bd_carrier[OF c(3) c(6)])
    show "transpose_mat (bd A1 A2) * bd A1 A2 = 1\<^sub>m (n1 + n2)"
      by (simp only: ta bd_mult[OF tA1 tA2 c(2) c(5)] i bd_one)
    show "transpose_mat (bd B1 B2) * bd B1 B2 = 1\<^sub>m (n1 + n2)"
      by (simp only: tb bd_mult[OF tB1 tB2 c(3) c(6)] i bd_one)
    show "transpose_mat (bd A1 A2) * bd B1 B2 + transpose_mat (bd B1 B2) * bd A1 A2 = bd H1 H2"
      by (simp only: ta tb bd_mult[OF tA1 tA2 c(3) c(6)] bd_mult[OF tB1 tB2 c(2) c(5)]
          bd_add[OF p1(1) p2(1) p1(2) p2(2)] s)
  qed
qed

section \<open>The path P_j\<close>

definition adjP :: "nat \<Rightarrow> int mat" where
  "adjP j = mat j j (\<lambda>(i, k). if i = Suc k \<or> k = Suc i then 1 else 0)"

definition PA :: "nat \<Rightarrow> int mat" where
  "PA j = mat (Suc j) j (\<lambda>(i, k). if i = k then 1 else 0)"

definition PB :: "nat \<Rightarrow> int mat" where
  "PB j = mat (Suc j) j (\<lambda>(i, k). if i = Suc k then 1 else 0)"

lemma sum_ind1: "(\<Sum>i<(n::nat). if i = (b::nat) then (1::int) else 0) = (if b < n then 1 else 0)"
  by (induction n) auto

lemma sum_ind2:
  "(\<Sum>i\<in>{0..<(n::nat)}. (if i = (a::nat) then (1::int) else 0) * (if i = (b::nat) then 1 else 0))
    = (if a < n \<and> a = b then 1 else 0)"
proof (cases "a = b")
  case True
  have "(\<Sum>i\<in>{0..<n}. (if i = a then (1::int) else 0) * (if i = b then 1 else 0))
      = (\<Sum>i\<in>{0..<n}. if i = b then (1::int) else 0)"
    using True by (intro sum.cong) simp_all
  also have "\<dots> = (\<Sum>i<n. if i = b then (1::int) else 0)" by (simp only: lessThan_atLeast0)
  also have "\<dots> = (if b < n then 1 else 0)" by (rule sum_ind1)
  finally show ?thesis using True by simp
next
  case False
  have "(\<Sum>i\<in>{0..<n}. (if i = a then (1::int) else 0) * (if i = b then 1 else 0))
      = (\<Sum>i\<in>{0..<n}. (0::int))"
    using False by (intro sum.cong) auto
  then show ?thesis using False by simp
qed

theorem path_repr: "repr (adjP j) j (Suc j) (PA j) (PB j)"
  unfolding repr_def
proof (intro conjI)
  show "adjP j \<in> carrier_mat j j" "PA j \<in> carrier_mat (Suc j) j" "PB j \<in> carrier_mat (Suc j) j"
    unfolding adjP_def PA_def PB_def by auto
  show "transpose_mat (PA j) * PA j = 1\<^sub>m j"
  proof (rule eq_matI)
    fix a b assume "a < dim_row (1\<^sub>m j)" "b < dim_col (1\<^sub>m j)"
    then have ab: "a < j" "b < j" by auto
    have "(\<Sum>i\<in>{0..<Suc j}. PA j $$ (i, a) * PA j $$ (i, b))
        = (\<Sum>i\<in>{0..<Suc j}. (if i = a then (1::int) else 0) * (if i = b then 1 else 0))"
      by (rule sum.cong[OF refl]) (simp add: PA_def ab)
    also have "\<dots> = (if a = b then 1 else 0)" using ab by (simp add: sum_ind2)
    finally show "(transpose_mat (PA j) * PA j) $$ (a, b) = 1\<^sub>m j $$ (a, b)"
      using ab by (simp add: times_mat_def scalar_prod_def PA_def)
  qed (auto simp: PA_def)
  show "transpose_mat (PB j) * PB j = 1\<^sub>m j"
  proof (rule eq_matI)
    fix a b assume "a < dim_row (1\<^sub>m j)" "b < dim_col (1\<^sub>m j)"
    then have ab: "a < j" "b < j" by auto
    have "(\<Sum>i\<in>{0..<Suc j}. PB j $$ (i, a) * PB j $$ (i, b))
        = (\<Sum>i\<in>{0..<Suc j}. (if i = Suc a then (1::int) else 0) * (if i = Suc b then 1 else 0))"
      by (rule sum.cong[OF refl]) (simp add: PB_def ab)
    also have "\<dots> = (if a = b then 1 else 0)" using ab by (simp add: sum_ind2)
    finally show "(transpose_mat (PB j) * PB j) $$ (a, b) = 1\<^sub>m j $$ (a, b)"
      using ab by (simp add: times_mat_def scalar_prod_def PB_def)
  qed (auto simp: PB_def)
  show "transpose_mat (PA j) * PB j + transpose_mat (PB j) * PA j = adjP j"
  proof (rule eq_matI)
    fix a b assume "a < dim_row (adjP j)" "b < dim_col (adjP j)"
    then have ab: "a < j" "b < j" by (auto simp: adjP_def)
    have s1: "(\<Sum>i\<in>{0..<Suc j}. PA j $$ (i, a) * PB j $$ (i, b))
        = (\<Sum>i\<in>{0..<Suc j}. (if i = a then (1::int) else 0) * (if i = Suc b then 1 else 0))"
      by (rule sum.cong[OF refl]) (simp add: PA_def PB_def ab)
    have s2: "(\<Sum>i\<in>{0..<Suc j}. PB j $$ (i, a) * PA j $$ (i, b))
        = (\<Sum>i\<in>{0..<Suc j}. (if i = Suc a then (1::int) else 0) * (if i = b then 1 else 0))"
      by (rule sum.cong[OF refl]) (simp add: PA_def PB_def ab)
    have "(\<Sum>i\<in>{0..<Suc j}. (if i = a then (1::int) else 0) * (if i = Suc b then 1 else 0))
        = (if a = Suc b then 1 else 0)" using ab by (simp add: sum_ind2)
    moreover have "(\<Sum>i\<in>{0..<Suc j}. (if i = Suc a then (1::int) else 0) * (if i = b then 1 else 0))
        = (if Suc a = b then 1 else 0)" using ab by (simp add: sum_ind2)
    ultimately show "(transpose_mat (PA j) * PB j + transpose_mat (PB j) * PA j) $$ (a, b) = adjP j $$ (a, b)"
      using ab s1 s2 by (auto simp: times_mat_def scalar_prod_def PA_def PB_def adjP_def)
  qed (auto simp: adjP_def PA_def PB_def)
qed

section \<open>The forest\<close>

text \<open>A list of path sizes js; the forest is the direct sum of the paths P_j, j in js (an empty list gives
  the 0 x 0 matrix).\<close>

fun forestH :: "nat list \<Rightarrow> int mat" where
  "forestH [] = 0\<^sub>m 0 0"
| "forestH (j # js) = bd (adjP j) (forestH js)"

fun forestA :: "nat list \<Rightarrow> int mat" where
  "forestA [] = 0\<^sub>m 0 0"
| "forestA (j # js) = bd (PA j) (forestA js)"

fun forestB :: "nat list \<Rightarrow> int mat" where
  "forestB [] = 0\<^sub>m 0 0"
| "forestB (j # js) = bd (PB j) (forestB js)"

theorem forest_repr: "repr (forestH js) (sum_list js) (sum_list (map Suc js)) (forestA js) (forestB js)"
proof (induction js)
  case Nil
  have z: "(0\<^sub>m 0 0 :: int mat) = 1\<^sub>m 0" by (rule eq_matI) simp_all
  have z2: "(1\<^sub>m 0 + 1\<^sub>m 0 :: int mat) = 1\<^sub>m 0" by (rule eq_matI) simp_all
  show ?case unfolding repr_def using z z2 by simp
next
  case (Cons j js)
  from block_sum[OF path_repr[of j] Cons.IH] show ?case by simp
qed

definition Gamma :: "nat list" where "Gamma = [6, 6, 6, 6, 5, 5, 5]"

lemma Gamma_vertices: "sum_list Gamma = 39" by (simp add: Gamma_def)
lemma Gamma_rows: "sum_list (map Suc Gamma) = 46" by (simp add: Gamma_def)

theorem forest_upper_repr: "repr (forestH Gamma) 39 46 (forestA Gamma) (forestB Gamma)"
  using forest_repr[of Gamma] Gamma_vertices Gamma_rows by simp

theorem forest_upper_Z: "lenZ_le 46 (forestH Gamma)"
proof -
  have "dim_row (forestH Gamma) = 39"
    using forest_upper_repr unfolding repr_def by auto
  then show ?thesis unfolding lenZ_le_def using forest_upper_repr by auto
qed

theorem forest_upper_Q: "lenQ_le 46 (forestH Gamma)"
proof -
  have d: "dim_row (forestH Gamma) = 39"
    using forest_upper_repr unfolding repr_def by auto
  from forest_upper_repr
  have c: "forestH Gamma \<in> carrier_mat 39 39" "forestA Gamma \<in> carrier_mat 46 39"
    "forestB Gamma \<in> carrier_mat 46 39"
    and i: "transpose_mat (forestA Gamma) * forestA Gamma = 1\<^sub>m 39"
    "transpose_mat (forestB Gamma) * forestB Gamma = 1\<^sub>m 39"
    and s: "transpose_mat (forestA Gamma) * forestB Gamma + transpose_mat (forestB Gamma) * forestA Gamma
       = forestH Gamma"
    unfolding repr_def by auto
  let ?m = "map_mat (of_int :: int \<Rightarrow> rat)"
  have mm: "\<And>(X::int mat) (Y::int mat) a b c. X \<in> carrier_mat a b \<Longrightarrow> Y \<in> carrier_mat b c
      \<Longrightarrow> ?m (X * Y) = ?m X * ?m Y"
  proof -
    fix X Y :: "int mat" and a b c :: nat
    assume "X \<in> carrier_mat a b" "Y \<in> carrier_mat b c"
    then show "?m (X * Y) = ?m X * ?m Y"
      by (intro eq_matI) (auto simp: times_mat_def scalar_prod_def map_mat_def)
  qed
  have tr: "\<And>(X::int mat). transpose_mat (?m X) = ?m (transpose_mat X)" by (rule eq_matI) auto
  have cd: "dim_col (forestA Gamma) = 39" "dim_col (forestB Gamma) = 39"
    using c(2,3) by (simp_all only: carrier_matD)
  have m1: "?m (1\<^sub>m 39) = (1\<^sub>m 39 :: rat mat)" by (rule eq_matI) simp_all
  have tA: "transpose_mat (forestA Gamma) \<in> carrier_mat 39 46" using c(2) by simp
  have tB: "transpose_mat (forestB Gamma) \<in> carrier_mat 39 46" using c(3) by simp
  have eAA: "?m (transpose_mat (forestA Gamma) * forestA Gamma)
      = ?m (transpose_mat (forestA Gamma)) * ?m (forestA Gamma)"
    by (rule mm[OF tA c(2)])
  have eBB: "?m (transpose_mat (forestB Gamma) * forestB Gamma)
      = ?m (transpose_mat (forestB Gamma)) * ?m (forestB Gamma)"
    by (rule mm[OF tB c(3)])
  have eAB: "?m (transpose_mat (forestA Gamma) * forestB Gamma)
      = ?m (transpose_mat (forestA Gamma)) * ?m (forestB Gamma)"
    by (rule mm[OF tA c(3)])
  have eBA: "?m (transpose_mat (forestB Gamma) * forestA Gamma)
      = ?m (transpose_mat (forestB Gamma)) * ?m (forestA Gamma)"
    by (rule mm[OF tB c(2)])
  have a1: "transpose_mat (?m (forestA Gamma)) * ?m (forestA Gamma) = 1\<^sub>m 39"
    using eAA i(1) m1 tr by metis
  have b1: "transpose_mat (?m (forestB Gamma)) * ?m (forestB Gamma) = 1\<^sub>m 39"
    using eBB i(2) m1 tr by metis
  have pA: "transpose_mat (forestA Gamma) * forestB Gamma \<in> carrier_mat 39 39"
    using tA c(3) by (rule mult_carrier_mat)
  have pB: "transpose_mat (forestB Gamma) * forestA Gamma \<in> carrier_mat 39 39"
    using tB c(2) by (rule mult_carrier_mat)
  have madd: "?m (transpose_mat (forestA Gamma) * forestB Gamma + transpose_mat (forestB Gamma) * forestA Gamma)
      = ?m (transpose_mat (forestA Gamma) * forestB Gamma) + ?m (transpose_mat (forestB Gamma) * forestA Gamma)"
    using pA pB cd by (intro eq_matI) (simp_all add: map_mat_def carrier_matD)
  have s1: "transpose_mat (?m (forestA Gamma)) * ?m (forestB Gamma)
      + transpose_mat (?m (forestB Gamma)) * ?m (forestA Gamma) = ?m (forestH Gamma)"
  proof -
    have "transpose_mat (?m (forestA Gamma)) * ?m (forestB Gamma)
        + transpose_mat (?m (forestB Gamma)) * ?m (forestA Gamma)
        = ?m (transpose_mat (forestA Gamma)) * ?m (forestB Gamma)
        + ?m (transpose_mat (forestB Gamma)) * ?m (forestA Gamma)" by (simp only: tr)
    also have "\<dots> = ?m (transpose_mat (forestA Gamma) * forestB Gamma)
        + ?m (transpose_mat (forestB Gamma) * forestA Gamma)" by (simp only: eAB eBA)
    also have "\<dots> = ?m (transpose_mat (forestA Gamma) * forestB Gamma
        + transpose_mat (forestB Gamma) * forestA Gamma)" by (rule madd[symmetric])
    also have "\<dots> = ?m (forestH Gamma)" by (simp only: s)
    finally show ?thesis .
  qed
  have cA: "?m (forestA Gamma) \<in> carrier_mat 46 39" using c(2) by (simp only: map_carrier_mat)
  have cB: "?m (forestB Gamma) \<in> carrier_mat 46 39" using c(3) by (simp only: map_carrier_mat)
  show ?thesis unfolding lenQ_le_def d
    using c(1) cA cB a1 b1 s1
    by blast
qed

section \<open>Direct check of the concrete 39 x 46 matrices by evaluation\<close>

lemma forest_eval:
  "transpose_mat (forestA Gamma) * forestA Gamma = 1\<^sub>m 39
   \<and> transpose_mat (forestB Gamma) * forestB Gamma = 1\<^sub>m 39
   \<and> transpose_mat (forestA Gamma) * forestB Gamma + transpose_mat (forestB Gamma) * forestA Gamma
       = forestH Gamma"
  by eval

end
