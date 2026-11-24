(*  Title:      Rows_Columns_Kernel.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín
    License:    BSD

    Kernel of a connected rows-columns multiplier (a Hankel multiplier family of biquadratic forms).
    Index sets 'a (rows, a = CARD('a)) and 'b (columns, b = CARD('b)); X ranges over real^('a x 'b) (a x b matrices,
    flattened), C :: 'a => 'b => real.  Am C sends X to the vector of weighted row sums sum_j C i j X(i,j) and column
    sums sum_i C i j X(i,j) (indices Inl i, Inr j); its transpose sends u to the matrix C i j (u(Inl i) + u(Inr j)),
    i.e. Z u with columns R_i, S_j.  H = Z diag(w) Z^T is Hmat C w = transpose (Am C) ** diag w ** Am C.
    If the bipartite graph of the nonzero entries of C is connected:
      kernel_Z:     Z u = 0  iff  u is a multiple of v = (1,...,1,-1,...,-1);
      rank_Z:       rank Z = a + b - 1;
      kernel_H_eq7: H X = 0  iff  for one lambda, w_i (row sum i) = lambda and w_(a+j) (column sum j) = -lambda  (7);
      dim_kernel_H: if all w_t are nonzero and sum_t 1/w_t = 0, then dim ker H = a b - a - b + 2  (8).
    NOT formalized: the embedding into R^5 (x) R^4 with the factor-radical part (9), and that every Hankel multiplier
    of rank a + b - 2 has this form (completeness, an open point).
*)
theory Rows_Columns_Kernel
  imports "HOL-Analysis.Analysis"
begin

declare transpose_matrix_vector [simp del]

section \<open>Sums over sum and product index types\<close>

lemma sum_Plus_UNIV:
  fixes f :: "'a::finite + 'b::finite \<Rightarrow> real"
  shows "(\<Sum>k\<in>UNIV. f k) = (\<Sum>i\<in>UNIV. f (Inl i)) + (\<Sum>j\<in>UNIV. f (Inr j))"
proof -
  have "(\<Sum>k\<in>UNIV. f k) = (\<Sum>k\<in>UNIV <+> UNIV. f k)" by simp
  also have "\<dots> = (\<Sum>i\<in>UNIV. f (Inl i)) + (\<Sum>j\<in>UNIV. f (Inr j))"
    by (subst sum.Plus) (simp_all add: o_def)
  finally show ?thesis .
qed

lemma sum_prod_UNIV:
  fixes f :: "'a::finite \<times> 'b::finite \<Rightarrow> real"
  shows "(\<Sum>p\<in>UNIV. f p) = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. f (i, j))"
  by (subst sum.cartesian_product) simp

lemma times_delta: "x * (if P then 1 else 0) = (if P then x else (0::real))"
  by simp

lemma delta_times: "(if P then y else 0) * x = (if P then y * x else (0::real))"
  by simp

section \<open>The rows-columns map\<close>

definition Am :: "('a::finite \<Rightarrow> 'b::finite \<Rightarrow> real) \<Rightarrow> real^('a \<times> 'b)^('a + 'b)" where
  "Am C = (\<chi> k p. case k of Inl i' \<Rightarrow> (if i' = fst p then C (fst p) (snd p) else 0)
                          | Inr j' \<Rightarrow> (if j' = snd p then C (fst p) (snd p) else 0))"

definition vv :: "real^('a::finite + 'b::finite)" where
  "vv = (\<chi> k. case k of Inl _ \<Rightarrow> 1 | Inr _ \<Rightarrow> -1)"

definition adj :: "('a \<Rightarrow> 'b \<Rightarrow> real) \<Rightarrow> 'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool" where
  "adj C x y \<longleftrightarrow> (\<exists>i j. C i j \<noteq> 0 \<and> ((x = Inl i \<and> y = Inr j) \<or> (x = Inr j \<and> y = Inl i)))"

definition connected_supp :: "('a \<Rightarrow> 'b \<Rightarrow> real) \<Rightarrow> bool" where
  "connected_supp C \<longleftrightarrow> (\<forall>x y. (adj C)\<^sup>*\<^sup>* x y)"

lemma Zm_entry: "(transpose (Am C) *v u) $ (i, j) = C i j * (u $ Inl i + u $ Inr j)"
proof -
  have "(transpose (Am C) *v u) $ (i, j) = (\<Sum>k\<in>UNIV. Am C $ k $ (i, j) * u $ k)"
    by (simp add: matrix_vector_mult_def transpose_def)
  also have "\<dots> = (\<Sum>i'\<in>UNIV. Am C $ Inl i' $ (i, j) * u $ Inl i')
                  + (\<Sum>j'\<in>UNIV. Am C $ Inr j' $ (i, j) * u $ Inr j')"
    by (rule sum_Plus_UNIV)
  also have "\<dots> = C i j * u $ Inl i + C i j * u $ Inr j"
    by (simp add: Am_def delta_times sum.delta)
  finally show ?thesis by (simp add: distrib_left)
qed

lemma Zt_row: "(Am C *v X) $ Inl i = (\<Sum>j\<in>UNIV. C i j * X $ (i, j))"
proof -
  have "(Am C *v X) $ Inl i = (\<Sum>p\<in>UNIV. Am C $ Inl i $ p * X $ p)"
    by (simp add: matrix_vector_mult_def)
  also have "\<dots> = (\<Sum>i'\<in>UNIV. \<Sum>j\<in>UNIV. Am C $ Inl i $ (i', j) * X $ (i', j))"
    by (rule sum_prod_UNIV)
  also have "\<dots> = (\<Sum>j\<in>UNIV. \<Sum>i'\<in>UNIV. Am C $ Inl i $ (i', j) * X $ (i', j))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>j\<in>UNIV. C i j * X $ (i, j))"
    by (simp add: Am_def delta_times sum.delta')
  finally show ?thesis .
qed

lemma Zt_col: "(Am C *v X) $ Inr j = (\<Sum>i\<in>UNIV. C i j * X $ (i, j))"
proof -
  have "(Am C *v X) $ Inr j = (\<Sum>p\<in>UNIV. Am C $ Inr j $ p * X $ p)"
    by (simp add: matrix_vector_mult_def)
  also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j'\<in>UNIV. Am C $ Inr j $ (i, j') * X $ (i, j'))"
    by (rule sum_prod_UNIV)
  also have "\<dots> = (\<Sum>i\<in>UNIV. C i j * X $ (i, j))"
    by (simp add: Am_def delta_times sum.delta')
  finally show ?thesis .
qed

lemma Zm_scaled_vv: "transpose (Am C) *v (c *\<^sub>R vv) = 0"
  by (simp add: vec_eq_iff Zm_entry vv_def split_paired_All)

lemma vv_nonzero: "(vv :: real^('a::finite + 'b::finite)) \<noteq> 0"
proof
  assume h: "(vv :: real^('a + 'b)) = 0"
  have "(vv :: real^('a + 'b)) $ Inl (undefined :: 'a) = (0::real)" by (simp add: h)
  then show False by (simp add: vv_def)
qed

section \<open>Kernel and rank of Z\<close>

theorem kernel_Z:
  fixes C :: "'a::finite \<Rightarrow> 'b::finite \<Rightarrow> real"
  assumes conn: "connected_supp C"
  shows "transpose (Am C) *v u = 0 \<longleftrightarrow> (\<exists>c. u = c *\<^sub>R vv)"
proof
  assume z: "transpose (Am C) *v u = 0"
  define g where "g k = (case k of Inl i \<Rightarrow> u $ k | Inr j \<Rightarrow> - u $ k)" for k :: "'a + 'b"
  have e: "u $ Inl i = - u $ Inr j" if "C i j \<noteq> 0" for i j
  proof -
    have "C i j * (u $ Inl i + u $ Inr j) = 0"
      using z Zm_entry[of C u i j] by (metis zero_index)
    then have "u $ Inl i + u $ Inr j = 0" using that by simp
    then show ?thesis by linarith
  qed
  have step: "g x = g y" if "adj C x y" for x y
    using that e by (auto simp: adj_def g_def)
  have path: "g x = g y" if "(adj C)\<^sup>*\<^sup>* x y" for x y
    using that by (induct rule: rtranclp_induct) (auto dest: step)
  define c where "c = g (undefined :: 'a + 'b)"
  have gk: "g k = c" for k
    using path conn unfolding connected_supp_def c_def by metis
  have "u $ k = (c *\<^sub>R vv) $ k" for k
  proof (cases k)
    case (Inl i) with gk[of k] show ?thesis by (simp add: g_def vv_def)
  next
    case (Inr j) with gk[of k] show ?thesis by (simp add: g_def vv_def)
  qed
  then show "\<exists>c. u = c *\<^sub>R vv" by (auto simp: vec_eq_iff)
next
  assume "\<exists>c. u = c *\<^sub>R vv"
  then show "transpose (Am C) *v u = 0" using Zm_scaled_vv by blast
qed

lemma dim_line: "dim (range (\<lambda>c::real. c *\<^sub>R (vv :: real^('a::finite + 'b::finite)))) = 1"
proof (rule antisym)
  have nz: "(vv :: real^('a + 'b)) \<noteq> 0" by (rule vv_nonzero)
  have "range (\<lambda>c::real. c *\<^sub>R (vv :: real^('a + 'b))) \<subseteq> span {vv}"
    by (auto intro: span_mul span_base)
  then have "dim (range (\<lambda>c::real. c *\<^sub>R (vv :: real^('a + 'b)))) \<le> dim (span {vv :: real^('a + 'b)})"
    by (rule dim_subset)
  then show "dim (range (\<lambda>c::real. c *\<^sub>R (vv :: real^('a + 'b)))) \<le> 1"
    using nz by simp
  have "{vv :: real^('a + 'b)} \<subseteq> range (\<lambda>c::real. c *\<^sub>R vv)"
    by (auto intro: range_eqI[of _ _ 1])
  then have "dim {vv :: real^('a + 'b)} \<le> dim (range (\<lambda>c::real. c *\<^sub>R (vv :: real^('a + 'b))))"
    by (rule dim_subset)
  then show "1 \<le> dim (range (\<lambda>c::real. c *\<^sub>R (vv :: real^('a + 'b))))"
    using nz by simp
qed

lemma orth_range_Zt:
  "{u \<in> UNIV. \<forall>x \<in> range (\<lambda>X. Am C *v X). orthogonal x u} = {u. transpose (Am C) *v u = 0}"
proof (intro set_eqI iffI)
  fix u assume "u \<in> {u \<in> UNIV. \<forall>x \<in> range (\<lambda>X. Am C *v X). orthogonal x u}"
  then have "(Am C *v (transpose (Am C) *v u)) \<bullet> u = 0" by (auto simp: orthogonal_def)
  then have "(transpose (Am C) *v u) \<bullet> (transpose (Am C) *v u) = 0" by (simp add: transpose_mv_inner)
  then show "u \<in> {u. transpose (Am C) *v u = 0}" by simp
next
  fix u assume "u \<in> {u. transpose (Am C) *v u = 0}"
  then show "u \<in> {u \<in> UNIV. \<forall>x \<in> range (\<lambda>X. Am C *v X). orthogonal x u}"
    by (auto simp: orthogonal_def transpose_mv_inner)
qed

lemma orth_range_Zm:
  "{X \<in> UNIV. \<forall>Y \<in> range (\<lambda>u. transpose (Am C) *v u). orthogonal Y X} = {X. Am C *v X = 0}"
proof (intro set_eqI iffI)
  fix X assume "X \<in> {X \<in> UNIV. \<forall>Y \<in> range (\<lambda>u. transpose (Am C) *v u). orthogonal Y X}"
  then have "(transpose (Am C) *v (Am C *v X)) \<bullet> X = 0" by (auto simp: orthogonal_def)
  then have "(Am C *v X) \<bullet> (Am C *v X) = 0" by (simp add: transpose_mv_inner inner_commute)
  then show "X \<in> {X. Am C *v X = 0}" by simp
next
  fix X assume "X \<in> {X. Am C *v X = 0}"
  then have h: "Am C *v X = 0" by simp
  have "orthogonal (transpose (Am C) *v u) X" for u
  proof -
    have "(transpose (Am C) *v u) \<bullet> X = X \<bullet> (transpose (Am C) *v u)" by (rule inner_commute)
    also have "\<dots> = (Am C *v X) \<bullet> u" by (rule transpose_mv_inner[symmetric])
    also have "\<dots> = 0" by (simp add: h)
    finally show ?thesis by (simp add: orthogonal_def)
  qed
  then show "X \<in> {X \<in> UNIV. \<forall>Y \<in> range (\<lambda>u. transpose (Am C) *v u). orthogonal Y X}"
    by auto
qed

lemma card_UNIV_Plus: "CARD('a::finite + 'b::finite) = CARD('a) + CARD('b)"
  by (subst UNIV_Plus_UNIV[symmetric]) (simp add: card_Plus del: UNIV_Plus_UNIV)

lemma subspace_range_mv: "subspace (range (\<lambda>x. (M :: real^'n^'m) *v x))"
  by (rule linear_subspace_image[OF matrix_vector_mul_linear subspace_UNIV])

theorem rank_Z:
  fixes C :: "'a::finite \<Rightarrow> 'b::finite \<Rightarrow> real"
  assumes conn: "connected_supp C"
  shows "rank (Am C) + 1 = CARD('a) + CARD('b)"
proof -
  have "dim {u \<in> UNIV. \<forall>x \<in> range (\<lambda>X. Am C *v X). orthogonal x u} + dim (range (\<lambda>X. Am C *v X))
        = dim (UNIV :: (real^('a + 'b)) set)"
    by (rule dim_subspace_orthogonal_to_vectors[OF subspace_range_mv subspace_UNIV subset_UNIV])
  then have d: "dim {u. transpose (Am C) *v u = 0} + rank (Am C) = dim (UNIV :: (real^('a + 'b)) set)"
    by (simp only: orth_range_Zt rank_dim_range)
  have "{u. transpose (Am C) *v u = 0} = range (\<lambda>c::real. c *\<^sub>R (vv :: real^('a + 'b)))"
    using kernel_Z[OF conn] by auto
  then have "dim {u. transpose (Am C) *v u = 0} = 1" by (simp add: dim_line)
  moreover have "dim (UNIV :: (real^('a + 'b)) set) = CARD('a) + CARD('b)"
    by (simp add: card_UNIV_Plus)
  ultimately show ?thesis using d by linarith
qed

section \<open>The kernel of H\<close>

definition diagw :: "real^'k \<Rightarrow> real^'k^'k" where
  "diagw w = (\<chi> k l. if k = l then w $ k else 0)"

definition Hmat :: "('a::finite \<Rightarrow> 'b::finite \<Rightarrow> real) \<Rightarrow> real^('a + 'b) \<Rightarrow> real^('a \<times> 'b)^('a \<times> 'b)" where
  "Hmat C w = transpose (Am C) ** diagw w ** Am C"

lemma diagw_mv: "(diagw w *v z) $ k = w $ k * z $ k"
  by (simp add: diagw_def matrix_vector_mult_def delta_times sum.delta)

lemma Hmat_mv: "Hmat C w *v X = transpose (Am C) *v (diagw w *v (Am C *v X))"
  by (simp add: Hmat_def matrix_vector_mul_assoc matrix_mul_assoc)

theorem kernel_H_scaled:
  assumes conn: "connected_supp C"
  shows "Hmat C w *v X = 0 \<longleftrightarrow> (\<exists>c. \<forall>k. w $ k * (Am C *v X) $ k = c * vv $ k)"
  unfolding Hmat_mv kernel_Z[OF conn] by (simp add: vec_eq_iff diagw_mv)

theorem kernel_H_eq7:
  assumes conn: "connected_supp C"
  shows "Hmat C w *v X = 0 \<longleftrightarrow>
         (\<exists>c. (\<forall>i. w $ Inl i * (\<Sum>j\<in>UNIV. C i j * X $ (i, j)) = c)
            \<and> (\<forall>j. w $ Inr j * (\<Sum>i\<in>UNIV. C i j * X $ (i, j)) = - c))"
proof -
  have "(\<forall>k. w $ k * (Am C *v X) $ k = c * vv $ k) \<longleftrightarrow>
        (\<forall>i. w $ Inl i * (\<Sum>j\<in>UNIV. C i j * X $ (i, j)) = c)
        \<and> (\<forall>j. w $ Inr j * (\<Sum>i\<in>UNIV. C i j * X $ (i, j)) = - c)" for c
  proof
    assume h: "\<forall>k. w $ k * (Am C *v X) $ k = c * vv $ k"
    show "(\<forall>i. w $ Inl i * (\<Sum>j\<in>UNIV. C i j * X $ (i, j)) = c)
          \<and> (\<forall>j. w $ Inr j * (\<Sum>i\<in>UNIV. C i j * X $ (i, j)) = - c)"
      using h[rule_format, of "Inl _"] h[rule_format, of "Inr _"] by (simp add: Zt_row Zt_col vv_def)
  next
    assume h: "(\<forall>i. w $ Inl i * (\<Sum>j\<in>UNIV. C i j * X $ (i, j)) = c)
               \<and> (\<forall>j. w $ Inr j * (\<Sum>i\<in>UNIV. C i j * X $ (i, j)) = - c)"
    show "\<forall>k. w $ k * (Am C *v X) $ k = c * vv $ k"
    proof
      fix k show "w $ k * (Am C *v X) $ k = c * vv $ k"
        using h by (cases k) (simp_all add: Zt_row Zt_col vv_def)
    qed
  qed
  then show ?thesis unfolding kernel_H_scaled[OF conn] by simp
qed

theorem dim_kernel_H:
  fixes C :: "'a::finite \<Rightarrow> 'b::finite \<Rightarrow> real" and w :: "real^('a + 'b)"
  assumes conn: "connected_supp C"
    and wnz: "\<And>k. w $ k \<noteq> 0"
    and recip: "(\<Sum>k\<in>UNIV. 1 / w $ k) = 0"
  shows "dim {X. Hmat C w *v X = 0} + CARD('a) + CARD('b) = CARD('a) * CARD('b) + 2"
proof -
  define A where "A = Am C"
  define u0 where "u0 = (\<chi> k. (vv :: real^('a + 'b)) $ k / w $ k)"
  define K0 where "K0 = {X. A *v X = 0}"
  define W where "W = {u. orthogonal (vv :: real^('a + 'b)) u}"
  \<comment> \<open>dim ker Z^T + rank Z = a b\<close>
  have dK0: "dim K0 + rank A = CARD('a) * CARD('b)"
  proof -
    have "dim {X \<in> UNIV. \<forall>Y \<in> range (\<lambda>u. transpose A *v u). orthogonal Y X}
          + dim (range (\<lambda>u. transpose A *v u)) = dim (UNIV :: (real^('a \<times> 'b)) set)"
      by (rule dim_subspace_orthogonal_to_vectors[OF subspace_range_mv subspace_UNIV subset_UNIV])
    then show ?thesis
      unfolding A_def K0_def orth_range_Zm
      by (simp add: rank_dim_range[symmetric] rank_transpose)
  qed
  have rA: "rank A + 1 = CARD('a) + CARD('b)" unfolding A_def by (rule rank_Z[OF conn])
  \<comment> \<open>range Z^T = v-perp\<close>
  have subW: "subspace W" unfolding W_def by (rule subspace_orthogonal_to_vector)
  have dW: "dim W + 1 = CARD('a) + CARD('b)"
  proof -
    have "dim {y \<in> UNIV. \<forall>x \<in> span {vv :: real^('a + 'b)}. orthogonal x y} + dim (span {vv :: real^('a + 'b)})
          = dim (UNIV :: (real^('a + 'b)) set)"
      by (rule dim_subspace_orthogonal_to_vectors[OF subspace_span subspace_UNIV subset_UNIV])
    moreover have "{y \<in> UNIV. \<forall>x \<in> span {vv :: real^('a + 'b)}. orthogonal x y} = W"
    proof (intro set_eqI iffI)
      fix y assume "y \<in> {y \<in> UNIV. \<forall>x \<in> span {vv :: real^('a + 'b)}. orthogonal x y}"
      then show "y \<in> W" by (auto simp: W_def intro: span_base)
    next
      fix y assume y: "y \<in> W"
      have "orthogonal y x" if "x \<in> span {vv :: real^('a + 'b)}" for x
        by (rule orthogonal_to_span[OF that]) (use y in \<open>auto simp: W_def orthogonal_commute\<close>)
      then show "y \<in> {y \<in> UNIV. \<forall>x \<in> span {vv :: real^('a + 'b)}. orthogonal x y}" by (auto simp: orthogonal_commute)
    qed
    moreover have "(vv :: real^('a + 'b)) \<noteq> 0" by (rule vv_nonzero)
    ultimately show ?thesis by simp
  qed
  have rangeW: "range (\<lambda>X. A *v X) = W"
  proof (rule subspace_dim_equal)
    show "subspace (range (\<lambda>X. A *v X))" by (rule subspace_range_mv)
    show "subspace W" by (rule subW)
    show "range (\<lambda>X. A *v X) \<subseteq> W"
    proof
      fix u assume "u \<in> range (\<lambda>X. A *v X)"
      then obtain X where u: "u = A *v X" by blast
      have "vv \<bullet> (A *v X) = (transpose A *v vv) \<bullet> X"
        by (metis inner_commute transpose_mv_inner)
      also have "\<dots> = 0" using Zm_scaled_vv[of C 1] by (simp add: A_def)
      finally show "u \<in> W" by (simp add: W_def orthogonal_def u)
    qed
    show "dim W \<le> dim (range (\<lambda>X. A *v X))"
      using dW rA by (simp add: rank_dim_range)
  qed
  \<comment> \<open>u0 lies in v-perp, so u0 = A X0\<close>
  have "vv \<bullet> u0 = (\<Sum>k\<in>UNIV. 1 / w $ k)"
    unfolding inner_vec_def u0_def
    by (rule sum.cong) (auto simp: vv_def split: sum.splits)
  then have "u0 \<in> W" using recip by (simp add: W_def orthogonal_def)
  then obtain X0 where X0: "A *v X0 = u0" using rangeW by (metis rangeE)
  have u0nz: "u0 \<noteq> 0"
  proof
    assume "u0 = 0"
    then have "u0 $ Inl (undefined :: 'a) = 0" by simp
    then show False using wnz[of "Inl undefined"] by (simp add: u0_def vv_def)
  qed
  \<comment> \<open>ker H = span (insert X0 K0)\<close>
  have kerH: "{X. Hmat C w *v X = 0} = {X. \<exists>c. A *v X = c *\<^sub>R u0}"
  proof (intro set_eqI iffI)
    fix X assume "X \<in> {X. Hmat C w *v X = 0}"
    then obtain c where h: "\<forall>k. w $ k * (A *v X) $ k = c * vv $ k"
      using kernel_H_scaled[OF conn] by (auto simp: A_def)
    have "(A *v X) $ k = (c *\<^sub>R u0) $ k" for k
      using h[rule_format, of k] wnz[of k] by (simp add: u0_def field_simps)
    then show "X \<in> {X. \<exists>c. A *v X = c *\<^sub>R u0}" by (auto simp: vec_eq_iff)
  next
    fix X assume "X \<in> {X. \<exists>c. A *v X = c *\<^sub>R u0}"
    then obtain c where h: "A *v X = c *\<^sub>R u0" by blast
    have "\<forall>k. w $ k * (A *v X) $ k = c * vv $ k"
      using wnz by (simp add: h u0_def)
    then show "X \<in> {X. Hmat C w *v X = 0}"
      using kernel_H_scaled[OF conn] by (auto simp: A_def)
  qed
  have subK0: "subspace K0" unfolding K0_def
    by (rule linear_subspace_kernel[OF matrix_vector_mul_linear])
  have sK0: "span K0 = K0" using subK0 by (simp add: span_eq_iff)
  have X0K0: "X0 \<notin> span K0"
    unfolding sK0 using u0nz X0 by (simp add: K0_def)
  have eq: "{X. \<exists>c. A *v X = c *\<^sub>R u0} = span (insert X0 K0)"
  proof (intro set_eqI iffI)
    fix X assume "X \<in> {X. \<exists>c. A *v X = c *\<^sub>R u0}"
    then obtain c where h: "A *v X = c *\<^sub>R u0" by blast
    have "X - c *\<^sub>R X0 \<in> K0"
      using h X0 by (simp add: K0_def matrix_vector_mult_diff_distrib matrix_vector_mult_scaleR)
    then have "X - c *\<^sub>R X0 \<in> span (insert X0 K0)" by (auto intro: span_base)
    moreover have "c *\<^sub>R X0 \<in> span (insert X0 K0)" by (auto intro: span_mul span_base)
    ultimately have "(X - c *\<^sub>R X0) + c *\<^sub>R X0 \<in> span (insert X0 K0)" by (rule span_add)
    then show "X \<in> span (insert X0 K0)" by simp
  next
    fix X assume "X \<in> span (insert X0 K0)"
    moreover have "subspace {X. \<exists>c. A *v X = c *\<^sub>R u0}"
      unfolding subspace_def
    proof (intro conjI ballI allI)
      show "0 \<in> {X. \<exists>c. A *v X = c *\<^sub>R u0}" by (auto intro: exI[of _ 0])
    next
      fix x y assume "x \<in> {X. \<exists>c. A *v X = c *\<^sub>R u0}" "y \<in> {X. \<exists>c. A *v X = c *\<^sub>R u0}"
      then obtain c d where "A *v x = c *\<^sub>R u0" "A *v y = d *\<^sub>R u0" by blast
      then have "A *v (x + y) = (c + d) *\<^sub>R u0"
        by (simp add: matrix_vector_right_distrib scaleR_add_left)
      then show "x + y \<in> {X. \<exists>c. A *v X = c *\<^sub>R u0}" by blast
    next
      fix r :: real and x assume "x \<in> {X. \<exists>c. A *v X = c *\<^sub>R u0}"
      then obtain c where "A *v x = c *\<^sub>R u0" by blast
      then have "A *v (r *\<^sub>R x) = (r * c) *\<^sub>R u0" by (simp add: matrix_vector_mult_scaleR)
      then show "r *\<^sub>R x \<in> {X. \<exists>c. A *v X = c *\<^sub>R u0}" by blast
    qed
    moreover have "insert X0 K0 \<subseteq> {X. \<exists>c. A *v X = c *\<^sub>R u0}"
      using X0 by (auto simp: K0_def intro: exI[of _ 1] exI[of _ 0])
    ultimately show "X \<in> {X. \<exists>c. A *v X = c *\<^sub>R u0}"
      using span_minimal by blast
  qed
  have "dim {X. Hmat C w *v X = 0} = dim K0 + 1"
    unfolding kerH eq dim_span using X0K0 by (simp add: dim_insert)
  then show ?thesis using dK0 rA by linarith
qed

section \<open>Without connectedness the description fails\<close>

text \<open>Two rows, two columns, C = identity: the graph has two components and Z kills (1,0,-1,0) too.\<close>

lemma disconnected_kernel_bigger:
  "transpose (Am (\<lambda>i j. if i = j then 1 else 0 :: real) :: real^(2 \<times> 2)^(2 + 2))
     *v (\<chi> k. case k of Inl i \<Rightarrow> (if i = 1 then 1 else 0) | Inr j \<Rightarrow> (if j = 1 then -1 else 0)) = 0
   \<and> \<not> (\<exists>c. (\<chi> k. case k of Inl i \<Rightarrow> (if i = (1::2) then 1 else 0) | Inr j \<Rightarrow> (if j = (1::2) then -1 else (0::real)))
           = c *\<^sub>R (vv :: real^(2 + 2)))"
proof
  show "transpose (Am (\<lambda>i j. if i = j then 1 else 0 :: real) :: real^(2 \<times> 2)^(2 + 2))
     *v (\<chi> k. case k of Inl i \<Rightarrow> (if i = 1 then 1 else 0) | Inr j \<Rightarrow> (if j = 1 then -1 else 0)) = 0"
    by (simp add: vec_eq_iff Zm_entry split_paired_All)
  show "\<not> (\<exists>c. (\<chi> k. case k of Inl i \<Rightarrow> (if i = (1::2) then 1 else 0) | Inr j \<Rightarrow> (if j = (1::2) then -1 else (0::real)))
           = c *\<^sub>R (vv :: real^(2 + 2)))"
  proof
    assume "\<exists>c. (\<chi> k. case k of Inl i \<Rightarrow> (if i = (1::2) then 1 else 0) | Inr j \<Rightarrow> (if j = (1::2) then -1 else (0::real)))
           = c *\<^sub>R (vv :: real^(2 + 2))"
    then obtain c where h: "(\<chi> k. case k of Inl i \<Rightarrow> (if i = (1::2) then 1 else 0) | Inr j \<Rightarrow> (if j = (1::2) then -1 else (0::real)))
           = c *\<^sub>R (vv :: real^(2 + 2))" by blast
    have "(1::real) = c" using arg_cong[OF h, of "\<lambda>x. x $ Inl 1"] by (simp add: vv_def)
    moreover have "(0::real) = c" using arg_cong[OF h, of "\<lambda>x. x $ Inl 2"] by (simp add: vv_def)
    ultimately show False by simp
  qed
qed

end
