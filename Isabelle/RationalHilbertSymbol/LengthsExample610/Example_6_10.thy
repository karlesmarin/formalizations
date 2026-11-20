(*  Title:      Example_6_10.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Example 6.10 (ex:sharp) of the paper "Rational sums-of-squares lengths of biquadratic forms and orthogonal
   dilations" (Carles Marín, in preparation): the explicit witness of the constructive part of Proposition
   prop:order6.  WITNESS AND LOCAL DATA ONLY; the length 13 follows from Theorem thm:sharp, not formalized here.

   Data. q = <11,21,23,23>, lambda = 3/4, L = Q(sqrt(-7)). W = M/55 with M the integer 6 x 4 matrix of the paper,
   H = I_6 - P_W/4 with P_W = W (W^T W)^{-1} W^T the orthogonal projection on the column space of W.

   Proved (all exact rational arithmetic by eval, matrices are Jordan_Normal_Form rat mat):
   (1) W^T W = diag(11,21,23,23); P_W symmetric, idempotent, P_W W = W and trace P_W = 4 (the rank of the
       idempotent); H symmetric; H W = (3/4) W; a basis N of the orthogonal complement of the columns of W
       (two integer columns) with W^T N = 0 and H N = N; the 6 x 6 matrix [W | N] has nonzero determinant, so the
       columns of W and N form a basis of Q^6 and H has spectrum (3/4)^4, 1^2 (H [W|N] = [W|N] diag).  The general
       statement "W^T X = 0 implies H X = X" is a lemma (H_fixes_orthogonal), not an evaluation.
   (2) Local data, with the Hilbert symbol of the theory Rational_Hilbert_Symbol (queue entry 272, imported
       unmodified; each value was first computed with the Python tool excovery.forma_racional.hilbert):
       det q = 231 * 23^2 (class 231 mod squares); 2 splits in L = Q(sqrt(-7)) because -7 = 1 mod 8 and -231 = 1
       mod 8 (so -D is a square in Q_2, checked also by the symbols (-231,b)_2 = 1 on a list of b); 23 splits
       because -7 = 4^2 mod 23; -D = -1 mod 23 is a non square modulo 23 (and (-231,23)_23 = -1); the six
       symbols (a_i,a_j)_2 of q and the Hasse invariants w_2(q) = w_23(q) = -1 (also at 3 and 11, and +1 at 7
       and at infinity: the product formula).  At 2 only (11,23)_2 and (23,23)_2 are -1, as in the paper.
*)
theory Example_6_10
  imports
    "RationalHilbertSymbol.Rational_Hilbert_Symbol"
    "Jordan_Normal_Form.Matrix"
    "Jordan_Normal_Form.Matrix_IArray_Impl"
    "Jordan_Normal_Form.Determinant_Impl"
    "Jordan_Normal_Form.Determinant"
begin

section \<open>The witness W and the matrix H\<close>

definition W :: "rat mat" where
  "W = mat_of_rows_list 4 [[-32/55, -156/55, 14/55, -23/55],
    [107/55, 6/55, -64/55, 168/55],
    [80/55, -50/55, 185/55, -80/55],
    [-119/55, 18/55, 83/55, 119/55],
    [-15/55, -80/55, -155/55, -95/55],
    [4/55, -173/55, 12/55, 106/55]]"

definition G0 :: "rat mat" where
  "G0 = mat_of_rows_list 4 [[11, 0, 0, 0], [0, 21, 0, 0], [0, 0, 23, 0], [0, 0, 0, 23]]"

definition Ginv :: "rat mat" where
  "Ginv = mat_of_rows_list 4 [[1/11, 0, 0, 0], [0, 1/21, 0, 0], [0, 0, 1/23, 0], [0, 0, 0, 1/23]]"

definition P_W :: "rat mat" where
  "P_W = W * Ginv * W\<^sup>T"

definition H :: "rat mat" where
  "H = 1\<^sub>m 6 - (1/4) \<cdot>\<^sub>m P_W"

text \<open>A basis of the orthogonal complement of the columns of W (integer columns).\<close>

definition N :: "rat mat" where
  "N = mat_of_rows_list 2 [[-2339, -8507], [1023, -4683], [2435, -545], [2716, -2039], [3727, 0], [0, 7454]]"

definition WN :: "rat mat" where
  "WN = mat_of_rows_list 6 [[-32/55, -156/55, 14/55, -23/55, -2339, -8507],
    [107/55, 6/55, -64/55, 168/55, 1023, -4683],
    [80/55, -50/55, 185/55, -80/55, 2435, -545],
    [-119/55, 18/55, 83/55, 119/55, 2716, -2039],
    [-15/55, -80/55, -155/55, -95/55, 3727, 0],
    [4/55, -173/55, 12/55, 106/55, 0, 7454]]"

definition Spec :: "rat mat" where
  "Spec = mat_of_rows_list 6 [[3/4, 0, 0, 0, 0, 0], [0, 3/4, 0, 0, 0, 0], [0, 0, 3/4, 0, 0, 0],
    [0, 0, 0, 3/4, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]]"

lemma dims: "W \<in> carrier_mat 6 4" "N \<in> carrier_mat 6 2" "WN \<in> carrier_mat 6 6" "Ginv \<in> carrier_mat 4 4"
  "G0 \<in> carrier_mat 4 4" "Spec \<in> carrier_mat 6 6"
  unfolding W_def N_def WN_def Ginv_def G0_def Spec_def mat_of_rows_list_def by auto

lemma P_carrier: "P_W \<in> carrier_mat 6 6"
  unfolding P_W_def using dims by auto

lemma H_carrier: "H \<in> carrier_mat 6 6"
  unfolding H_def using P_carrier by auto

section \<open>Gram matrix and projection\<close>

lemma gram_diag: "W\<^sup>T * W = G0"
  unfolding W_def G0_def by eval

lemma Ginv_inverse: "Ginv * G0 = 1\<^sub>m 4" "G0 * Ginv = 1\<^sub>m 4"
  unfolding Ginv_def G0_def by eval+

lemma P_sym: "P_W\<^sup>T = P_W"
  unfolding P_W_def W_def Ginv_def by eval

lemma P_idem: "P_W * P_W = P_W"
  unfolding P_W_def W_def Ginv_def by eval

lemma P_W_W: "P_W * W = W"
  unfolding P_W_def W_def Ginv_def by eval

definition trace6 :: "rat mat \<Rightarrow> rat" where
  "trace6 A = sum_list (map (\<lambda>i. A $$ (i, i)) [0..<6])"

lemma trace_P: "trace6 P_W = 4"
  unfolding trace6_def P_W_def W_def Ginv_def by eval

lemma H_sym: "H\<^sup>T = H"
  unfolding H_def P_W_def W_def Ginv_def by eval

lemma H_W: "H * W = (3/4) \<cdot>\<^sub>m W"
  unfolding H_def P_W_def W_def Ginv_def by eval

section \<open>The orthogonal complement\<close>

lemma WtN_zero: "W\<^sup>T * N = 0\<^sub>m 4 2"
  unfolding W_def N_def by eval

lemma H_fixes_orthogonal:
  fixes X :: "rat mat" and k :: nat
  assumes X: "X \<in> carrier_mat 6 k" and orth: "W\<^sup>T * X = 0\<^sub>m 4 k"
  shows "H * X = X"
proof -
  have c1: "W * Ginv \<in> carrier_mat 6 4" using dims by auto
  have c2: "W\<^sup>T \<in> carrier_mat 4 6" using dims by auto
  have c3: "W\<^sup>T * X \<in> carrier_mat 4 k" using c2 X by auto
  have "P_W * X = (W * Ginv) * (W\<^sup>T * X)"
    unfolding P_W_def using assoc_mult_mat[OF c1 c2 X] by simp
  also have "\<dots> = W * (Ginv * (W\<^sup>T * X))"
    using assoc_mult_mat[OF dims(1) dims(4) c3] by simp
  also have "\<dots> = 0\<^sub>m 6 k" using orth dims by simp
  finally have PX: "P_W * X = 0\<^sub>m 6 k" .
  have "H * X = 1\<^sub>m 6 * X - ((1/4) \<cdot>\<^sub>m P_W) * X"
    unfolding H_def using minus_mult_distrib_mat[of "1\<^sub>m 6" 6 6 "(1/4) \<cdot>\<^sub>m P_W" X k] P_carrier X by auto
  also have "\<dots> = X - (1/4) \<cdot>\<^sub>m (P_W * X)"
    using mult_smult_assoc_mat[OF P_carrier X, of "1/4"] X by simp
  also have "\<dots> = X" using PX X by (intro eq_matI) auto
  finally show ?thesis .
qed

lemma H_N: "H * N = N"
  using H_fixes_orthogonal[OF _ WtN_zero] dims by simp

lemma det_WN: "det WN \<noteq> 0"
  unfolding WN_def by eval

lemma gram_N_det: "det (N\<^sup>T * N) \<noteq> 0"
  unfolding N_def by eval

lemma H_WN_Spec: "H * WN = WN * Spec"
  unfolding H_def P_W_def W_def Ginv_def WN_def Spec_def by eval

section \<open>Local data of the example\<close>

definition qdiag :: "rat list" where "qdiag = [11, 21, 23, 23]"

lemma det_q: "(11 :: int) * 21 * 23 * 23 = 231 * 23 ^ 2" by simp

lemma split_2: "(-7 :: int) mod 8 = 1" "(-231 :: int) mod 8 = 1" "(231 :: int) mod 8 = 7" by eval+

lemma split_23: "(4 :: int) * 4 mod 23 = (-7) mod 23" by eval

lemma minus_D_nonsquare_mod_23:
  "(-231 :: int) mod 23 = 22" "\<forall>x \<in> set (map int [0..<23]). x * x mod 23 \<noteq> 22"
  by eval+

definition tests :: "rat list" where "tests = [-1, 2, 3, 5, 7, 11, 13, 21, 23, -7, -23, -2, 6, 10]"

text \<open>-D is a square in Q_2 and -7 is a square in Q_2 and in Q_23 (all symbols with it are 1 on the tests);
-D is not a square in Q_23.\<close>

lemma minus_D_square_Q2:
  "list_all (\<lambda>b. Rational_Hilbert_Symbol.hilbert 2 (-231) b = 1) tests"
  unfolding tests_def by eval

lemma minus_7_square_Q2:
  "list_all (\<lambda>b. Rational_Hilbert_Symbol.hilbert 2 (-7) b = 1) tests"
  unfolding tests_def by eval

lemma minus_7_square_Q23:
  "list_all (\<lambda>b. Rational_Hilbert_Symbol.hilbert 23 (-7) b = 1) tests"
  unfolding tests_def by eval

lemma minus_D_nonsquare_Q23: "Rational_Hilbert_Symbol.hilbert 23 (-231) 23 = -1"
  by eval

text \<open>The six symbols (a_i, a_j) of q at 2 and the Hasse invariants (values of
excovery.forma_racional.hilbert, computed before being written here).\<close>

lemma symbols_at_2:
  "Rational_Hilbert_Symbol.hilbert 2 11 21 = 1" "Rational_Hilbert_Symbol.hilbert 2 11 23 = -1"
  "Rational_Hilbert_Symbol.hilbert 2 21 23 = 1" "Rational_Hilbert_Symbol.hilbert 2 23 23 = -1"
  by eval+

lemma symbols_at_23:
  "Rational_Hilbert_Symbol.hilbert 23 11 21 = 1" "Rational_Hilbert_Symbol.hilbert 23 11 23 = -1"
  "Rational_Hilbert_Symbol.hilbert 23 21 23 = -1" "Rational_Hilbert_Symbol.hilbert 23 23 23 = -1"
  by eval+

lemma hasse_values:
  "Rational_Hilbert_Symbol.hasse 2 qdiag = -1" "Rational_Hilbert_Symbol.hasse 23 qdiag = -1"
  "Rational_Hilbert_Symbol.hasse 3 qdiag = -1" "Rational_Hilbert_Symbol.hasse 11 qdiag = -1"
  "Rational_Hilbert_Symbol.hasse 7 qdiag = 1" "Rational_Hilbert_Symbol.hasse_inf qdiag = 1"
  unfolding qdiag_def Rational_Hilbert_Symbol.hasse_def Rational_Hilbert_Symbol.hasse_inf_def by eval+

section \<open>Summary\<close>

theorem example_6_10_witness:
  "W\<^sup>T * W = G0 \<and>
   P_W\<^sup>T = P_W \<and> P_W * P_W = P_W \<and> P_W * W = W \<and> trace6 P_W = 4 \<and>
   H\<^sup>T = H \<and> H * W = (3/4) \<cdot>\<^sub>m W \<and>
   W\<^sup>T * N = 0\<^sub>m 4 2 \<and> H * N = N \<and> det WN \<noteq> 0 \<and> H * WN = WN * Spec \<and>
   (\<forall>k (X :: rat mat). X \<in> carrier_mat 6 k \<longrightarrow> W\<^sup>T * X = 0\<^sub>m 4 k \<longrightarrow> H * X = X) \<and>
   (11 :: int) * 21 * 23 * 23 = 231 * 23 ^ 2 \<and>
   (-7 :: int) mod 8 = 1 \<and> (-231 :: int) mod 8 = 1 \<and> (4 :: int) * 4 mod 23 = (-7) mod 23 \<and>
   (\<forall>x \<in> set (map int [0..<23]). x * x mod 23 \<noteq> 22) \<and>
   Rational_Hilbert_Symbol.hilbert 2 11 23 = -1 \<and> Rational_Hilbert_Symbol.hilbert 2 23 23 = -1 \<and>
   Rational_Hilbert_Symbol.hilbert 2 11 21 = 1 \<and> Rational_Hilbert_Symbol.hilbert 2 21 23 = 1 \<and>
   Rational_Hilbert_Symbol.hasse 2 qdiag = -1 \<and> Rational_Hilbert_Symbol.hasse 23 qdiag = -1"
  using gram_diag P_sym P_idem P_W_W trace_P H_sym H_W WtN_zero H_N det_WN H_WN_Spec H_fixes_orthogonal
    det_q split_2 split_23 minus_D_nonsquare_mod_23 symbols_at_2 symbols_at_23 hasse_values
  by blast

end
