(*  Title:      Zero_NN_Criterion.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín
    License:    BSD

    Zero-NN-projection criterion: a linear-algebra lemma used in the study of biquadratic sums of squares.
    In coordinates: D is indexed by a finite type 'n, the indices are split into W (the 13-plane, after an adapted
    change of basis P on K), C = the rest of K, and N; Sym^2 is modelled by symmetric matrices, and the image of a
    relation M in Sym^2(D/W) by Q M = (P^T M P) with the W rows and columns set to zero.
    If every M in J has zero N x N block and P is the identity on the N coordinates, then
        2 * dim (Q ` J) <= c (c + 1) + 2 c q,     c = card C, q = card N,
    i.e. r_D(W) <= C(c+1,2) + c q, and with the identity dim ker beta = Delta - r_D + r_K, r_K >= 0 (a hypothesis
    here), 2 dim ker beta >= 2 Delta - c (c + 1) - 2 c q.
    Necessity: without the zero N x N block the bound fails (zero_NN_needed).
    NOT formalized: the identity (1) (hypothesis), and the passage from the intrinsic statement (a 13-plane W of K,
    D/W = C_W + N) to the adapted coordinates.
*)
theory Zero_NN_Criterion
  imports "HOL-Analysis.Analysis"
begin

section \<open>Symmetric generators\<close>

definition Esym :: "'n set \<Rightarrow> real^'n^'n" where
  "Esym A = (\<chi> a b. if {a, b} = A then 1 else 0)"

definition sym_supp :: "'n set \<Rightarrow> 'n set \<Rightarrow> (real^'n^'n) set" where
  "sym_supp U N = {M. transpose M = M \<and> (\<forall>a b. (a \<notin> U \<or> b \<notin> U) \<longrightarrow> M$a$b = 0)
                      \<and> (\<forall>a\<in>N. \<forall>b\<in>N. M$a$b = 0)}"

definition s12 :: "'n set \<Rightarrow> 'n set set" where
  "s12 X = {A. A \<subseteq> X \<and> (card A = 1 \<or> card A = 2)}"

definition gens_idx :: "'n set \<Rightarrow> 'n set \<Rightarrow> 'n set set" where
  "gens_idx U N = {A. A \<subseteq> U \<and> (card A = 1 \<or> card A = 2) \<and> \<not> A \<subseteq> N}"

definition Fm :: "'n \<Rightarrow> 'n \<Rightarrow> real^'n^'n" where
  "Fm i j = (\<chi> a b. if a = i \<and> b = j then 1 else 0)"

lemma Fm_pair: "Fm i j + Fm j i = (if i = j then 2 *\<^sub>R Esym {i} else Esym {i, j})"
  by (auto simp: vec_eq_iff Fm_def Esym_def doubleton_eq_iff)

lemma times_delta: "x * (if P then 1 else 0) = (if P then x else (0::real))"
  by simp

lemma delta_times: "(if P then 1 else 0) * x = (if P then x else (0::real))"
  by simp

lemma double_delta:
  fixes g :: "'n::finite \<Rightarrow> 'n \<Rightarrow> real"
  shows "(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. g i j * (if a = i \<and> b = j then 1 else 0)) = g a b"
proof -
  have inner: "(\<Sum>j\<in>UNIV. g i j * (if a = i \<and> b = j then 1 else 0)) = (if a = i then g i b else 0)" for i
    by (cases "a = i") (simp_all add: times_delta sum.delta')
  show ?thesis by (simp add: inner sum.delta')
qed

lemma expand_sym:
  fixes M :: "real^'n^'n"
  assumes "transpose M = M"
  shows "M = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (M$i$j / 2) *\<^sub>R (Fm i j + Fm j i))"
proof -
  have sym: "M$j$i = M$i$j" for i j
    using assms by (metis transpose_def vec_lambda_beta)
  have c1: "(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (M$i$j / 2) * (if a = i \<and> b = j then 1 else 0)) = M$a$b / 2" for a b
    by (rule double_delta)
  have c2: "(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (M$i$j / 2) * (if a = j \<and> b = i then 1 else 0)) = M$b$a / 2" for a b
  proof -
    have e: "(a = j \<and> b = i) = (b = i \<and> a = j)" for i j by blast
    show ?thesis unfolding e by (rule double_delta)
  qed
  show ?thesis
  proof (subst vec_eq_iff, intro allI, subst vec_eq_iff, intro allI)
    fix a b
    have "(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (M$i$j / 2) *\<^sub>R (Fm i j + Fm j i)) $ a $ b
        = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (M$i$j / 2) * (if a = i \<and> b = j then 1 else 0))
          + (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (M$i$j / 2) * (if a = j \<and> b = i then 1 else 0))"
      by (simp add: sum_component Fm_def distrib_left sum.distrib)
    also have "\<dots> = M$a$b" unfolding c1 c2 sym[of a b] by simp
    finally show "M $ a $ b = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (M$i$j / 2) *\<^sub>R (Fm i j + Fm j i)) $ a $ b"
      by simp
  qed
qed

lemma sym_supp_span:
  fixes M :: "real^'n^'n"
  assumes "M \<in> sym_supp U N"
  shows "M \<in> span (Esym ` gens_idx U N)"
proof -
  have tM: "transpose M = M" and out: "\<And>a b. a \<notin> U \<or> b \<notin> U \<Longrightarrow> M$a$b = 0"
    and nn: "\<And>a b. a \<in> N \<Longrightarrow> b \<in> N \<Longrightarrow> M$a$b = 0"
    using assms by (auto simp: sym_supp_def)
  have trm: "(M$i$j / 2) *\<^sub>R (Fm i j + Fm j i) \<in> span (Esym ` gens_idx U N)" for i j
  proof (cases "M$i$j = 0")
    case True then show ?thesis by (simp add: span_zero)
  next
    case False
    then have iU: "i \<in> U" and jU: "j \<in> U" and nN: "\<not> (i \<in> N \<and> j \<in> N)"
      using out nn by blast+
    show ?thesis
    proof (cases "i = j")
      case True
      have "{i} \<in> gens_idx U N" using iU nN True by (auto simp: gens_idx_def)
      then have "Esym {i} \<in> span (Esym ` gens_idx U N)" by (intro span_base imageI)
      then show ?thesis using True by (simp add: Fm_pair span_mul)
    next
      case False
      have "{i, j} \<in> gens_idx U N" using iU jU nN False by (auto simp: gens_idx_def)
      then have "Esym {i, j} \<in> span (Esym ` gens_idx U N)" by (intro span_base imageI)
      then show ?thesis using False by (simp add: Fm_pair span_mul)
    qed
  qed
  have "(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (M$i$j / 2) *\<^sub>R (Fm i j + Fm j i)) \<in> span (Esym ` gens_idx U N)"
    by (intro span_sum trm)
  then show ?thesis using expand_sym[OF tM] by simp
qed

section \<open>Counting the generators\<close>

lemma finite_s12: "finite X \<Longrightarrow> finite (s12 X)"
  by (rule finite_subset[of _ "Pow X"]) (auto simp: s12_def)

lemma card_s12:
  assumes "finite X"
  shows "2 * card (s12 X) = card X * (card X + 1)"
proof -
  have u: "s12 X = {A. A \<subseteq> X \<and> card A = 1} \<union> {A. A \<subseteq> X \<and> card A = 2}"
    by (auto simp: s12_def)
  have f1: "finite {A. A \<subseteq> X \<and> card A = 1}" and f2: "finite {A. A \<subseteq> X \<and> card A = 2}"
    using assms by (auto intro: finite_subset[of _ "Pow X"])
  have "card (s12 X) = (card X choose 1) + (card X choose 2)"
    unfolding u using assms f1 f2 by (subst card_Un_disjoint) (auto simp: n_subsets)
  moreover have "2 * (card X choose 2) = card X * (card X - 1)"
  proof -
    have ev: "2 dvd card X * (card X - 1)" by (cases "card X") auto
    show ?thesis using ev by (metis choose_two dvd_mult_div_cancel)
  qed
  ultimately show ?thesis
    by (cases "card X") (auto simp: algebra_simps)
qed

lemma gens_idx_eq: "gens_idx U N = s12 U - s12 N"
  by (auto simp: gens_idx_def s12_def)

lemma card_gens_idx:
  assumes "finite U" "N \<subseteq> U"
  shows "2 * card (gens_idx U N) = card (U - N) * (card (U - N) + 1) + 2 * card (U - N) * card N"
proof -
  have fN: "finite N" using assms finite_subset by blast
  have sub: "s12 N \<subseteq> s12 U" using assms by (auto simp: s12_def)
  have "card (s12 U) = card (gens_idx U N) + card (s12 N)"
    unfolding gens_idx_eq using sub finite_s12[OF assms(1)] finite_subset[OF sub]
    by (simp add: card_Diff_subset card_mono)
  moreover have "card U = card (U - N) + card N"
    using assms fN by (simp add: card_Diff_subset card_mono)
  ultimately have "2 * card (gens_idx U N) + card N * (card N + 1)
                   = (card (U - N) + card N) * (card (U - N) + card N + 1)"
    using card_s12[OF assms(1)] card_s12[OF fN] by simp
  then show ?thesis by (simp add: algebra_simps)
qed

lemma dim_sym_supp:
  assumes "finite U" "N \<subseteq> U" "V \<subseteq> sym_supp U N"
  shows "2 * dim V \<le> card (U - N) * (card (U - N) + 1) + 2 * card (U - N) * card N"
proof -
  have fg: "finite (gens_idx U N)"
    by (rule finite_subset[of _ "Pow U"]) (use assms(1) in \<open>auto simp: gens_idx_def\<close>)
  have "V \<subseteq> span (Esym ` gens_idx U N)" using assms(3) sym_supp_span by blast
  then have "dim V \<le> card (Esym ` gens_idx U N)"
    using fg by (intro dim_le_card) auto
  also have "\<dots> \<le> card (gens_idx U N)" using fg by (rule card_image_le)
  finally show ?thesis using card_gens_idx[OF assms(1,2)] by linarith
qed

section \<open>The quotient by W keeps the zero N x N block\<close>

definition Qmap :: "'n set \<Rightarrow> real^'n^'n \<Rightarrow> real^'n^'n \<Rightarrow> real^'n^'n" where
  "Qmap Wi P M = (\<chi> a b. if a \<in> Wi \<or> b \<in> Wi then 0 else (transpose P ** M ** P) $ a $ b)"

lemma congruence_NN:
  fixes P M :: "real^'n^'n"
  assumes PN: "\<And>a b. a \<in> N \<or> b \<in> N \<Longrightarrow> P$a$b = (if a = b then 1 else 0)"
    and "a \<in> N" "b \<in> N"
  shows "(transpose P ** M ** P) $ a $ b = M $ a $ b"
proof -
  have pa: "P$i$a = (if i = a then 1 else 0)" for i using PN assms(2) by auto
  have pb: "P$k$b = (if k = b then 1 else 0)" for k using PN assms(3) by auto
  have "(transpose P ** M ** P) $ a $ b = (\<Sum>k\<in>UNIV. (\<Sum>i\<in>UNIV. P$i$a * M$i$k) * P$k$b)"
    by (simp add: matrix_matrix_mult_def transpose_def)
  also have "\<dots> = M $ a $ b"
    by (simp add: pa pb times_delta delta_times sum.delta)
  finally show ?thesis .
qed

lemma Qmap_in_sym_supp:
  fixes P M :: "real^'n^'n"
  assumes PN: "\<And>a b. a \<in> N \<or> b \<in> N \<Longrightarrow> P$a$b = (if a = b then 1 else 0)"
    and NW: "N \<inter> Wi = {}" and tM: "transpose M = M" and nn: "\<forall>a\<in>N. \<forall>b\<in>N. M$a$b = 0"
  shows "Qmap Wi P M \<in> sym_supp (- Wi) N"
proof -
  define S where "S = transpose P ** M ** P"
  have tS: "transpose S = S"
    using tM by (simp add: S_def matrix_transpose_mul matrix_mul_assoc)
  then have s: "S $ b $ a = S $ a $ b" for a b
    by (metis transpose_def vec_lambda_beta)
  have Q: "Qmap Wi P M = (\<chi> a b. if a \<in> Wi \<or> b \<in> Wi then 0 else S $ a $ b)"
    unfolding Qmap_def S_def by (rule refl)
  have "transpose (Qmap Wi P M) $ a $ b = Qmap Wi P M $ a $ b" for a b
    unfolding Q transpose_def using s[of a b] by auto
  then have "transpose (Qmap Wi P M) = Qmap Wi P M"
    by (simp add: vec_eq_iff)
  moreover have "(a \<notin> - Wi \<or> b \<notin> - Wi) \<longrightarrow> Qmap Wi P M $ a $ b = 0" for a b
    by (auto simp: Qmap_def)
  moreover have "Qmap Wi P M $ a $ b = 0" if "a \<in> N" "b \<in> N" for a b
    using that NW nn congruence_NN[OF PN] by (auto simp: Qmap_def)
  ultimately show ?thesis by (auto simp: sym_supp_def)
qed

section \<open>The criterion\<close>

theorem zero_NN_rank_bound:
  fixes J :: "(real^'n^'n) set" and P :: "real^'n^'n"
  assumes symJ: "\<forall>M\<in>J. transpose M = M"
    and nnJ: "\<forall>M\<in>J. \<forall>a\<in>N. \<forall>b\<in>N. M$a$b = 0"
    and PN: "\<And>a b. a \<in> N \<or> b \<in> N \<Longrightarrow> P$a$b = (if a = b then 1 else 0)"
    and NW: "N \<inter> Wi = {}"
  shows "2 * dim (Qmap Wi P ` J) \<le> card (- Wi - N) * (card (- Wi - N) + 1) + 2 * card (- Wi - N) * card N"
proof (rule dim_sym_supp)
  show "finite (- Wi)" by simp
  show "N \<subseteq> - Wi" using NW by blast
  show "Qmap Wi P ` J \<subseteq> sym_supp (- Wi) N"
  proof (rule subsetI)
    fix y assume "y \<in> Qmap Wi P ` J"
    then obtain M where MJ: "M \<in> J" and y: "y = Qmap Wi P M" by blast
    show "y \<in> sym_supp (- Wi) N"
      unfolding y using Qmap_in_sym_supp[OF PN NW] symJ nnJ MJ by simp
  qed
qed

text \<open>With the identity (1), dim ker beta = Delta - r_D + r_K and r_K >= 0, as hypotheses.\<close>

corollary zero_NN_kernel_bound:
  fixes J :: "(real^'n^'n) set" and P :: "real^'n^'n" and kb Delta rK :: int
  assumes symJ: "\<forall>M\<in>J. transpose M = M"
    and nnJ: "\<forall>M\<in>J. \<forall>a\<in>N. \<forall>b\<in>N. M$a$b = 0"
    and PN: "\<And>a b. a \<in> N \<or> b \<in> N \<Longrightarrow> P$a$b = (if a = b then 1 else 0)"
    and NW: "N \<inter> Wi = {}"
    and id1: "kb = Delta - int (dim (Qmap Wi P ` J)) + rK" and rK: "rK \<ge> 0"
    and c: "c = int (card (- Wi - N))" and q: "q = int (card N)"
  shows "2 * kb \<ge> 2 * Delta - c * (c + 1) - 2 * c * q"
proof -
  have "2 * dim (Qmap Wi P ` J) \<le> card (- Wi - N) * (card (- Wi - N) + 1) + 2 * card (- Wi - N) * card N"
    by (rule zero_NN_rank_bound[OF symJ nnJ PN NW])
  then have "int (2 * dim (Qmap Wi P ` J))
             \<le> int (card (- Wi - N) * (card (- Wi - N) + 1) + 2 * card (- Wi - N) * card N)"
    by (simp only: of_nat_le_iff)
  then have "2 * int (dim (Qmap Wi P ` J)) \<le> c * (c + 1) + 2 * c * q"
    by (simp add: c q algebra_simps)
  then show ?thesis using id1 rK by linarith
qed

section \<open>The zero N x N block is needed\<close>

lemma dim_mat1: "dim {mat 1 :: real^2^2} = 1"
proof -
  have "mat 1 \<noteq> (0 :: real^2^2)" by (simp add: vec_eq_iff mat_def)
  then show ?thesis by (simp add: dim_insert)
qed

lemma zero_NN_needed:
  "\<not> (2 * dim (Qmap {} (mat 1) ` {mat 1 :: real^2^2})
        \<le> card (- {} - (UNIV :: 2 set)) * (card (- {} - (UNIV :: 2 set)) + 1)
          + 2 * card (- {} - (UNIV :: 2 set)) * card (UNIV :: 2 set))"
proof -
  have "Qmap {} (mat 1) (mat 1 :: real^2^2) = mat 1"
    by (simp add: Qmap_def vec_eq_iff transpose_mat matrix_mul_lid)
  then show ?thesis using dim_mat1 by simp
qed

end
