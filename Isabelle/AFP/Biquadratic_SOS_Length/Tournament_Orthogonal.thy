theory Tournament_Orthogonal
  imports "HOL-Analysis.Analysis"
begin

text \<open>Bailey--Craigen construction (arXiv:1810.08961, Theorem 4.2). Let \<open>S\<close> be a real
skew-symmetric \<open>n \<times> n\<close> matrix with \<open>S J = J S = 0\<close> and \<open>S S\<^sup>T = n I - J\<close> (the skew
part of a doubly regular tournament), and \<open>a\<^sup>2 = n - 2\<close>. Then \<open>N = J - I + a S\<close> satisfies
\<open>N N\<^sup>T = N\<^sup>T N = (n-1)\<^sup>2 I\<close>, so \<open>N/(n-1)\<close> is orthogonal with symmetric part
\<open>(J - I)/(n-1)\<close>.\<close>

section \<open>Matrix algebra\<close>

definition Jmat :: "real^'n^'n" where
  "Jmat = (\<chi> i j. 1)"

definition tourn_N :: "real^'n^'n \<Rightarrow> real \<Rightarrow> real^'n^'n" where
  "tourn_N S a = Jmat - mat 1 + a *\<^sub>R S"

lemma mm_add_left: "(A + B) ** C = A ** C + B ** C"
  for A B :: "real^'n^'m" and C :: "real^'k^'n"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum.distrib algebra_simps)

lemma mm_add_right: "A ** (B + C) = A ** B + A ** C"
  for A :: "real^'n^'m" and B C :: "real^'k^'n"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum.distrib algebra_simps)

lemma mm_diff_left: "(A - B) ** C = A ** C - B ** C"
  for A B :: "real^'n^'m" and C :: "real^'k^'n"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum_subtractf algebra_simps)

lemma mm_diff_right: "A ** (B - C) = A ** B - A ** C"
  for A :: "real^'n^'m" and B C :: "real^'k^'n"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum_subtractf algebra_simps)

lemma mm_scale_left: "(c *\<^sub>R A) ** C = c *\<^sub>R (A ** C)"
  for A :: "real^'n^'m" and C :: "real^'k^'n"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum_distrib_left algebra_simps)

lemma mm_scale_right: "A ** (c *\<^sub>R C) = c *\<^sub>R (A ** C)"
  for A :: "real^'n^'m" and C :: "real^'k^'n"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum_distrib_left algebra_simps)

lemma mm_uminus_right: "A ** (- C) = - (A ** C)"
  for A :: "real^'n^'m" and C :: "real^'k^'n"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum_negf)

lemma tr_add: "transpose (A + B) = transpose A + transpose B"
  by (simp add: transpose_def vec_eq_iff)

lemma tr_diff: "transpose (A - B) = transpose A - transpose B"
  by (simp add: transpose_def vec_eq_iff)

lemma tr_scale: "transpose (c *\<^sub>R A) = c *\<^sub>R transpose A"
  by (simp add: transpose_def vec_eq_iff)

lemma tr_J: "transpose (Jmat :: real^'n^'n) = Jmat"
  by (simp add: transpose_def Jmat_def vec_eq_iff)

lemma J_J: "(Jmat :: real^'n::finite^'n) ** Jmat = real CARD('n) *\<^sub>R Jmat"
  by (simp add: matrix_matrix_mult_def Jmat_def vec_eq_iff)

section \<open>Generic expansions\<close>

lemma expand1:
  fixes K S :: "real^'n::finite^'n"
  shows "(K + a *\<^sub>R S) ** (K - a *\<^sub>R S)
    = K ** K - a *\<^sub>R (K ** S) + a *\<^sub>R (S ** K) - (a * a) *\<^sub>R (S ** S)"
  by ((simp add: mm_add_left mm_add_right mm_diff_right mm_scale_left mm_scale_right
        scaleR_scaleR algebra_simps; fail)
    | (simp add: mm_add_left mm_add_right mm_diff_right mm_scale_left mm_scale_right
        scaleR_scaleR add_ac diff_conv_add_uminus; fail))

lemma expand2:
  fixes K S :: "real^'n::finite^'n"
  shows "(K - a *\<^sub>R S) ** (K + a *\<^sub>R S)
    = K ** K + a *\<^sub>R (K ** S) - a *\<^sub>R (S ** K) - (a * a) *\<^sub>R (S ** S)"
  by ((simp add: mm_add_left mm_add_right mm_diff_left mm_scale_left mm_scale_right
        scaleR_scaleR algebra_simps; fail)
    | (simp add: mm_add_left mm_add_right mm_diff_left mm_scale_left mm_scale_right
        scaleR_scaleR add_ac diff_conv_add_uminus; fail))

lemma lin1:
  fixes P Q S :: "real^'n^'n"
  shows "((c - 2) *\<^sub>R P + Q) - a *\<^sub>R (- S) + a *\<^sub>R (- S) - (c - 2) *\<^sub>R (P - c *\<^sub>R Q)
    = ((c - 1)\<^sup>2) *\<^sub>R Q"
  apply (rule iffD2[OF vec_eq_iff], rule allI, rule iffD2[OF vec_eq_iff], rule allI)
  apply (simp add: power2_eq_square)
  apply (algebra)?
  done

lemma lin2:
  fixes P Q S :: "real^'n^'n"
  shows "((c - 2) *\<^sub>R P + Q) + a *\<^sub>R (- S) - a *\<^sub>R (- S) - (c - 2) *\<^sub>R (P - c *\<^sub>R Q)
    = ((c - 1)\<^sup>2) *\<^sub>R Q"
  apply (rule iffD2[OF vec_eq_iff], rule allI, rule iffD2[OF vec_eq_iff], rule allI)
  apply (simp add: power2_eq_square)
  apply (algebra)?
  done

lemma half_sum:
  fixes K S :: "real^'n^'n"
  shows "(1 / 2) *\<^sub>R (c *\<^sub>R (K + a *\<^sub>R S) + c *\<^sub>R (K - a *\<^sub>R S)) = c *\<^sub>R K"
  apply (rule iffD2[OF vec_eq_iff], rule allI, rule iffD2[OF vec_eq_iff], rule allI)
  apply (simp add: algebra_simps)
  apply (algebra)?
  done

section \<open>The skew part\<close>

locale skew_part =
  fixes S :: "real^'n::finite^'n::finite" and a n :: real and K :: "real^'n^'n"
  assumes n_eq: "n = real CARD('n)"
    and K_def: "K = Jmat - mat 1"
    and skew: "transpose S = - S"
    and SJ: "S ** Jmat = 0"
    and JS: "Jmat ** S = 0"
    and SSt: "S ** transpose S = n *\<^sub>R mat 1 - Jmat"
    and a2: "a\<^sup>2 = n - 2"
begin

abbreviation "N \<equiv> tourn_N S a"

lemma KK: "K ** K = (n - 2) *\<^sub>R Jmat + mat 1"
proof -
  have "K ** K = Jmat ** Jmat - Jmat ** mat 1 - mat 1 ** Jmat + mat 1 ** mat 1"
    by (simp add: K_def mm_diff_left mm_diff_right)
  also have "\<dots> = n *\<^sub>R Jmat - Jmat - Jmat + mat 1"
    by (simp add: J_J n_eq matrix_mul_rid matrix_mul_lid)
  also have "\<dots> = (n - 2) *\<^sub>R Jmat + mat 1"
    by (simp add: scaleR_left_diff_distrib scaleR_2 algebra_simps)
  finally show ?thesis .
qed

lemma KS: "K ** S = - S"
  by (simp add: K_def mm_diff_left JS matrix_mul_lid)

lemma SK: "S ** K = - S"
  by (simp add: K_def mm_diff_right SJ matrix_mul_rid)

lemma SS: "S ** S = Jmat - n *\<^sub>R mat 1"
proof -
  have "- (S ** S) = n *\<^sub>R mat 1 - Jmat"
    using SSt skew by (simp add: mm_uminus_right)
  hence "S ** S = - (n *\<^sub>R mat 1 - Jmat)" by (metis minus_minus)
  thus ?thesis by simp
qed

lemma N_eq: "N = K + a *\<^sub>R S"
  by (simp add: K_def tourn_N_def)

lemma trN: "transpose N = K - a *\<^sub>R S"
  by (simp add: K_def tourn_N_def tr_add tr_diff tr_scale tr_J skew)

lemma aa: "a * a = n - 2"
  using a2 by (simp add: power2_eq_square)

lemma NNt_expand:
  "N ** transpose N = K ** K - a *\<^sub>R (K ** S) + a *\<^sub>R (S ** K) - (a * a) *\<^sub>R (S ** S)"
  unfolding trN by (simp only: N_eq expand1)

lemma NtN_expand:
  "transpose N ** N = K ** K + a *\<^sub>R (K ** S) - a *\<^sub>R (S ** K) - (a * a) *\<^sub>R (S ** S)"
  unfolding trN by (simp only: N_eq expand2)

theorem N_Nt: "N ** transpose N = ((n - 1)\<^sup>2) *\<^sub>R mat 1"
proof -
  have "N ** transpose N = ((n - 2) *\<^sub>R Jmat + mat 1) - a *\<^sub>R (- S) + a *\<^sub>R (- S)
      - (n - 2) *\<^sub>R (Jmat - n *\<^sub>R mat 1)"
    by (simp add: NNt_expand KK KS SK SS aa)
  also have "\<dots> = ((n - 1)\<^sup>2) *\<^sub>R mat 1"
    by (rule lin1)
  finally show ?thesis .
qed

theorem Nt_N: "transpose N ** N = ((n - 1)\<^sup>2) *\<^sub>R mat 1"
proof -
  have "transpose N ** N = ((n - 2) *\<^sub>R Jmat + mat 1) + a *\<^sub>R (- S) - a *\<^sub>R (- S)
      - (n - 2) *\<^sub>R (Jmat - n *\<^sub>R mat 1)"
    by (simp add: NtN_expand KK KS SK SS aa)
  also have "\<dots> = ((n - 1)\<^sup>2) *\<^sub>R mat 1"
    by (rule lin2)
  finally show ?thesis .
qed

theorem orthogonal_T:
  assumes n2: "2 \<le> CARD('n)"
  defines "T \<equiv> (1 / (n - 1)) *\<^sub>R N"
  shows "orthogonal_matrix T"
proof -
  have h: "of_nat 2 \<le> (of_nat CARD('n) :: real)" using n2 by (rule of_nat_mono)
  have n1': "n \<ge> 2" using h by (simp add: n_eq)
  hence n1: "n - 1 \<noteq> 0" by simp
  have key: "(1 / (n - 1))\<^sup>2 * (n - 1)\<^sup>2 = 1" using n1 by (simp add: power_divide)
  have "T ** transpose T = ((1 / (n - 1))\<^sup>2 * (n - 1)\<^sup>2) *\<^sub>R mat 1"
    by (simp add: T_def tr_scale mm_scale_left mm_scale_right N_Nt power2_eq_square
        mult.assoc)
  hence a: "T ** transpose T = mat 1" using key by simp
  have "transpose T ** T = ((1 / (n - 1))\<^sup>2 * (n - 1)\<^sup>2) *\<^sub>R mat 1"
    by (simp add: T_def tr_scale mm_scale_left mm_scale_right Nt_N power2_eq_square
        mult.assoc)
  hence b: "transpose T ** T = mat 1" using key by simp
  show ?thesis using a b by (simp add: orthogonal_matrix_def)
qed

theorem sym_part_T:
  defines "T \<equiv> (1 / (n - 1)) *\<^sub>R N"
  shows "(1 / 2) *\<^sub>R (T + transpose T) = (1 / (n - 1)) *\<^sub>R (Jmat - mat 1)"
proof -
  have t1: "transpose T = (1 / (n - 1)) *\<^sub>R (K - a *\<^sub>R S)"
    unfolding T_def by (simp only: tr_scale trN)
  have "(1 / 2) *\<^sub>R (T + transpose T)
      = (1 / 2) *\<^sub>R ((1 / (n - 1)) *\<^sub>R (K + a *\<^sub>R S) + (1 / (n - 1)) *\<^sub>R (K - a *\<^sub>R S))"
    unfolding t1 by (simp only: T_def N_eq)
  also have "\<dots> = (1 / (n - 1)) *\<^sub>R K" by (rule half_sum)
  finally show ?thesis by (simp add: K_def)
qed

end

section \<open>Statement with the dimension \<open>CARD('n)\<close>\<close>

theorem bailey_craigen:
  fixes S :: "real^'n::finite^'n" and a :: real
  assumes skew: "transpose S = - S" and SJ: "S ** Jmat = 0" and JS: "Jmat ** S = 0"
    and SSt: "S ** transpose S = real CARD('n) *\<^sub>R mat 1 - Jmat"
    and a2: "a\<^sup>2 = real CARD('n) - 2" and n2: "2 \<le> CARD('n)"
  defines "N \<equiv> Jmat - mat 1 + a *\<^sub>R S"
    and "T \<equiv> (1 / (real CARD('n) - 1)) *\<^sub>R (Jmat - mat 1 + a *\<^sub>R S)"
  shows "N ** transpose N = (real CARD('n) - 1)\<^sup>2 *\<^sub>R mat 1"
    and "transpose N ** N = (real CARD('n) - 1)\<^sup>2 *\<^sub>R mat 1"
    and "orthogonal_matrix T"
    and "(1 / 2) *\<^sub>R (T + transpose T) = (1 / (real CARD('n) - 1)) *\<^sub>R (Jmat - mat 1)"
proof -
  interpret skew_part S a "real CARD('n)" "Jmat - mat 1"
    using skew SJ JS SSt a2 by unfold_locales simp_all
  have NN: "N = tourn_N S a" by (simp add: N_def tourn_N_def)
  show "N ** transpose N = (real CARD('n) - 1)\<^sup>2 *\<^sub>R mat 1" unfolding NN by (rule N_Nt)
  show "transpose N ** N = (real CARD('n) - 1)\<^sup>2 *\<^sub>R mat 1" unfolding NN by (rule Nt_N)
  have TT: "T = (1 / (real CARD('n) - 1)) *\<^sub>R tourn_N S a" by (simp add: T_def tourn_N_def)
  show "orthogonal_matrix T" unfolding TT by (rule orthogonal_T[OF n2])
  show "(1 / 2) *\<^sub>R (T + transpose T) = (1 / (real CARD('n) - 1)) *\<^sub>R (Jmat - mat 1)"
    unfolding TT by (rule sym_part_T)
qed

end
