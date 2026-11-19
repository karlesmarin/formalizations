(*  Title:      Real_Jump_Locale.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Rational sums-of-squares lengths of biquadratic forms: Theorem "real", part (2), and Corollary "jump" of the paper
   "Rational sums-of-squares lengths of biquadratic forms and orthogonal dilations" (Carles Marín, in preparation),
   Section "Real length" and Section "A global criterion".

   PARTIAL formalization. Everything is proved from the axioms of HOL-Analysis except ONE named assumption: the
   locale witt_over_Q assumes Witt cancellation over Q (extension of a rational matrix with orthonormal columns to a
   rational orthogonal matrix, Lam, Introduction to Quadratic Forms over Fields, Ch. I). Nothing else is assumed.
   The facts proved here include the spectral lemma (an invariant subspace of a symmetric matrix contains an
   eigenvector, by maximizing the Rayleigh quotient) and the parity of the eigenspaces of the symmetric part of an
   orthogonal matrix. Proposition "iso" is NOT re-proved (it is Huckel_SOS.represents_iff); lengths are expressed by
   its item (2), the matrix equations, and by its last sentence (an orthogonal T with sym T = H).
*)
theory Real_Jump_Locale
  imports "HOL-Analysis.Analysis"
begin

section \<open>Definitions and elementary identities\<close>

definition tr :: "real^'n^'m \<Rightarrow> real^'m^'n" where
  "tr M = transpose M"   \<comment> \<open>opaque to the simplifier, which rewrites transpose A *v x\<close>

definition sympart :: "real^'n^'n \<Rightarrow> real^'n^'n" where
  "sympart Q = (1/2) *\<^sub>R (Q + tr Q)"

definition skewpart :: "real^'n^'n \<Rightarrow> real^'n^'n" where
  "skewpart Q = (1/2) *\<^sub>R (Q - tr Q)"

definition orth_mat :: "real^'n^'n \<Rightarrow> bool" where
  "orth_mat Q \<longleftrightarrow> tr Q ** Q = mat 1"

lemma sympart_entry: "sympart Q $ i $ j = (Q $ i $ j + Q $ j $ i) / 2"
  by (simp add: sympart_def tr_def transpose_def)

lemma adjoint_dot: "(A *v y) \<bullet> w = y \<bullet> (tr A *v w)"
  for A :: "real^'n^'m"
  unfolding tr_def by (metis dot_lmul_matrix vector_transpose_matrix)

lemma orth_left: "orth_mat Q \<Longrightarrow> tr Q *v (Q *v x) = x"
  by (simp add: orth_mat_def matrix_vector_mul_assoc)

lemma orth_right_mat: "orth_mat Q \<Longrightarrow> Q ** tr Q = mat 1"
  using matrix_left_right_inverse[of "tr Q" Q] by (simp add: orth_mat_def)

lemma orth_right: "orth_mat Q \<Longrightarrow> Q *v (tr Q *v x) = x"
  by (simp add: orth_right_mat matrix_vector_mul_assoc)

lemma tr_tr: "tr (tr Q) = Q"
  by (simp add: tr_def)

lemma orth_transpose: "orth_mat Q \<Longrightarrow> orth_mat (tr Q)"
  by (simp add: orth_mat_def tr_tr orth_right_mat)

lemma orth_inner: "orth_mat Q \<Longrightarrow> (Q *v x) \<bullet> (Q *v y) = x \<bullet> y"
  by (simp add: adjoint_dot orth_left)

lemma sympart_vec: "sympart Q *v x = (1/2) *\<^sub>R (Q *v x + tr Q *v x)"
  by (simp add: sympart_def scaleR_matrix_vector_assoc[symmetric] matrix_vector_mult_add_rdistrib)

lemma skewpart_vec: "skewpart Q *v x = (1/2) *\<^sub>R (Q *v x - tr Q *v x)"
  by (simp add: skewpart_def scaleR_matrix_vector_assoc[symmetric] matrix_vector_mult_diff_rdistrib)

lemma Q_split: "Q *v x = sympart Q *v x + skewpart Q *v x"
proof -
  have h: "(1/2) *\<^sub>R (u + v) + (1/2) *\<^sub>R (u - v) = u" for u v :: "real^'n"
    by (simp add: vec_eq_iff field_simps)
  show ?thesis by (simp add: sympart_vec skewpart_vec h)
qed

lemma sym_self: "(sympart Q *v x) \<bullet> y = x \<bullet> (sympart Q *v y)"
  by (simp add: sympart_vec adjoint_dot tr_tr inner_add_left inner_add_right algebra_simps)

lemma skew_self: "(skewpart Q *v x) \<bullet> y = - (x \<bullet> (skewpart Q *v y))"
  by (simp add: skewpart_vec adjoint_dot tr_tr inner_diff_left inner_diff_right algebra_simps)

lemma skew_zero: "y \<bullet> (skewpart Q *v y) = 0"
proof -
  have "(skewpart Q *v y) \<bullet> y = - (y \<bullet> (skewpart Q *v y))" by (rule skew_self)
  moreover have "(skewpart Q *v y) \<bullet> y = y \<bullet> (skewpart Q *v y)" by (rule inner_commute)
  ultimately show ?thesis by linarith
qed

lemma sym_skew_commute:
  assumes "orth_mat Q"
  shows "sympart Q *v (skewpart Q *v x) = skewpart Q *v (sympart Q *v x)"
  by (simp add: sympart_vec skewpart_vec matrix_vector_right_distrib matrix_vector_mult_diff_distrib
      matrix_vector_mult_scaleR orth_left[OF assms] orth_right[OF assms] algebra_simps)

lemma skew_square:
  assumes "orth_mat Q"
  shows "skewpart Q *v (skewpart Q *v x) = sympart Q *v (sympart Q *v x) - x"
  by (simp add: sympart_vec skewpart_vec matrix_vector_right_distrib matrix_vector_mult_diff_distrib
      matrix_vector_mult_scaleR orth_left[OF assms] orth_right[OF assms] algebra_simps)
     (simp add: vec_eq_iff)

section \<open>Parity of an invariant subspace carrying a complex structure\<close>

lemma even_dim_skew:
  fixes A :: "real^'n^'n" and k :: real
  assumes k: "k > 0"
    and skew: "\<And>x y. (A *v x) \<bullet> y = - (x \<bullet> (A *v y))"
  shows "\<And>G. subspace G \<Longrightarrow> (\<forall>x\<in>G. A *v x \<in> G) \<Longrightarrow>
      (\<forall>x\<in>G. A *v (A *v x) = - k *\<^sub>R x) \<Longrightarrow> even (dim G)"
proof -
  have main: "\<And>G. dim G = d \<Longrightarrow> subspace G \<Longrightarrow> (\<forall>x\<in>G. A *v x \<in> G) \<Longrightarrow>
      (\<forall>x\<in>G. A *v (A *v x) = - k *\<^sub>R x) \<Longrightarrow> even d" for d
  proof (induction d rule: less_induct)
    case (less d)
    note dG = less.prems(1) and sub = less.prems(2) and inv = less.prems(3) and sq = less.prems(4)
    show ?case
    proof (cases "G \<subseteq> {0}")
      case True
      hence "dim G = 0" by simp
      thus ?thesis using dG by simp
    next
      case False
      then obtain v where vG: "v \<in> G" and v0: "v \<noteq> 0" by auto
      define w where "w = A *v v"
      have wG: "w \<in> G" using inv vG w_def by simp
      have vw: "v \<bullet> w = 0"
      proof -
        have "(A *v v) \<bullet> v = - (v \<bullet> (A *v v))" by (rule skew)
        thus ?thesis by (simp add: w_def inner_commute)
      qed
      have ww: "w \<bullet> w = k * (v \<bullet> v)"
      proof -
        have "(A *v v) \<bullet> (A *v v) = - (v \<bullet> (A *v (A *v v)))" by (rule skew)
        also have "\<dots> = k * (v \<bullet> v)" using sq vG by simp
        finally show ?thesis by (simp add: w_def)
      qed
      have vv: "v \<bullet> v > 0" using v0 by simp
      have w0: "w \<noteq> 0" using ww k vv by auto
      define G' where "G' = {x \<in> G. x \<bullet> v = 0 \<and> x \<bullet> w = 0}"
      have subG': "subspace G'"
        using sub by (auto simp: G'_def subspace_def inner_add_left)
      have invG': "\<forall>x\<in>G'. A *v x \<in> G'"
      proof
        fix x assume xG': "x \<in> G'"
        hence xG: "x \<in> G" and xv: "x \<bullet> v = 0" and xw: "x \<bullet> w = 0" by (auto simp: G'_def)
        have "(A *v x) \<bullet> v = - (x \<bullet> (A *v v))" by (rule skew)
        hence 1: "(A *v x) \<bullet> v = 0" using xw by (simp add: w_def)
        have "(A *v x) \<bullet> w = - (x \<bullet> (A *v w))" by (rule skew)
        also have "A *v w = - k *\<^sub>R v" using sq vG by (simp add: w_def)
        finally have 2: "(A *v x) \<bullet> w = 0" using xv by simp
        show "A *v x \<in> G'" using 1 2 inv xG by (auto simp: G'_def)
      qed
      have sqG': "\<forall>x\<in>G'. A *v (A *v x) = - k *\<^sub>R x" using sq by (auto simp: G'_def)
      have span_eq: "span (span {v, w} \<union> G') = G"
      proof (rule subset_antisym)
        show "span (span {v, w} \<union> G') \<subseteq> G"
          apply (rule span_minimal[OF _ sub])
          using vG wG sub by (auto simp: G'_def span_minimal)
      next
        show "G \<subseteq> span (span {v, w} \<union> G')"
        proof
          fix x assume xG: "x \<in> G"
          define a where "a = (x \<bullet> v) / (v \<bullet> v)"
          define b where "b = (x \<bullet> w) / (w \<bullet> w)"
          define x' where "x' = x - a *\<^sub>R v - b *\<^sub>R w"
          have ww0: "w \<bullet> w \<noteq> 0" using w0 by simp
          have x'G: "x' \<in> G"
            using xG vG wG sub unfolding x'_def
            by (simp add: subspace_diff subspace_mul)
          have x'v: "x' \<bullet> v = 0"
            using vw vv by (simp add: x'_def a_def inner_diff_left inner_commute[of w v])
          have x'w: "x' \<bullet> w = 0"
            using vw ww0 by (simp add: x'_def b_def inner_diff_left inner_commute[of v w])
          have "x' \<in> G'" using x'G x'v x'w by (simp add: G'_def)
          moreover have "a *\<^sub>R v + b *\<^sub>R w \<in> span {v, w}"
            by (intro span_add span_mul span_base) auto
          ultimately have "x = (a *\<^sub>R v + b *\<^sub>R w) + x'" by (simp add: x'_def)
          moreover have "(a *\<^sub>R v + b *\<^sub>R w) \<in> span (span {v, w} \<union> G')"
            using \<open>a *\<^sub>R v + b *\<^sub>R w \<in> span {v, w}\<close> span_base by blast
          moreover have "x' \<in> span (span {v, w} \<union> G')"
            using \<open>x' \<in> G'\<close> span_base by blast
          ultimately show "x \<in> span (span {v, w} \<union> G')"
            by (metis span_add)
        qed
      qed
      have orthPG': "\<And>x y. x \<in> span {v, w} \<Longrightarrow> y \<in> G' \<Longrightarrow> x \<bullet> y = 0"
      proof -
        fix x y assume xs: "x \<in> span {v, w}" and yG': "y \<in> G'"
        have ov: "orthogonal y v" and ow: "orthogonal y w" using yG' by (auto simp: G'_def orthogonal_def)
        have "orthogonal y x" by (rule orthogonal_to_span[OF xs]) (auto simp: ov ow)
        thus "x \<bullet> y = 0" by (simp add: orthogonal_def inner_commute)
      qed
      have dimP: "dim (span {v, w}) = 2"
      proof -
        have ne: "v \<noteq> w"
        proof
          assume "v = w"
          hence "v \<bullet> v = 0" using vw by simp
          thus False using vv by simp
        qed
        have "pairwise orthogonal {v, w}"
          using vw by (auto simp: pairwise_def orthogonal_def inner_commute)
        moreover have "0 \<notin> {v, w}" using v0 w0 by simp
        ultimately have ind: "independent {v, w}" by (rule pairwise_orthogonal_independent)
        have "dim {v, w} = card {v, w}" by (rule dim_eq_card_independent[OF ind])
        thus ?thesis using ne by simp
      qed
      have "dim G = dim (span (span {v, w} \<union> G'))" using span_eq by simp
      also have "\<dots> = dim (span {v, w} \<union> G')" by simp
      also have "\<dots> = dim (span {v, w}) + dim G'"
        by (rule dim_orthogonal_sum) (use orthPG' in blast)
      finally have dsum: "dim G = 2 + dim G'" using dimP by simp
      have lt: "dim G' < d" using dsum dG by simp
      have "even (dim G')" using less.IH[OF lt _ subG' invG' sqG'] by blast
      thus ?thesis using dsum dG by simp
    qed
  qed
  fix G assume "subspace G" "\<forall>x\<in>G. A *v x \<in> G" "\<forall>x\<in>G. A *v (A *v x) = - k *\<^sub>R x"
  thus "even (dim G)" using main[of G "dim G"] by blast
qed

section \<open>The eigenspaces of the symmetric part of an orthogonal matrix are even for |lambda| < 1\<close>

definition eigsp :: "real^'n^'n \<Rightarrow> real \<Rightarrow> (real^'n) set" where
  "eigsp S l = {x. S *v x = l *\<^sub>R x}"

lemma subspace_eigsp: "subspace (eigsp S l)"
  by (auto simp: subspace_def eigsp_def matrix_vector_right_distrib matrix_vector_mult_scaleR algebra_simps)

theorem even_dim_interior_eigenspace:
  assumes Q: "orth_mat Q" and l: "l\<^sup>2 < 1"
  shows "even (dim (eigsp (sympart Q) l))"
proof (rule even_dim_skew[of "1 - l\<^sup>2" "skewpart Q" "eigsp (sympart Q) l"])
  show "0 < 1 - l\<^sup>2" using l by simp
  show "\<And>x y. (skewpart Q *v x) \<bullet> y = - (x \<bullet> (skewpart Q *v y))" by (rule skew_self)
  show "subspace (eigsp (sympart Q) l)" by (rule subspace_eigsp)
  show "\<forall>x\<in>eigsp (sympart Q) l. skewpart Q *v x \<in> eigsp (sympart Q) l"
    by (simp add: eigsp_def sym_skew_commute[OF Q] matrix_vector_mult_scaleR)
  show "\<forall>x\<in>eigsp (sympart Q) l. skewpart Q *v (skewpart Q *v x) = - (1 - l\<^sup>2) *\<^sub>R x"
  proof
    fix x assume "x \<in> eigsp (sympart Q) l"
    hence "sympart Q *v x = l *\<^sub>R x" by (simp add: eigsp_def)
    hence "sympart Q *v (sympart Q *v x) = l\<^sup>2 *\<^sub>R x"
      by (simp add: matrix_vector_mult_scaleR power2_eq_square)
    thus "skewpart Q *v (skewpart Q *v x) = - (1 - l\<^sup>2) *\<^sub>R x"
      by (simp add: skew_square[OF Q] algebra_simps scaleR_diff_left)
  qed
qed


section \<open>An invariant subspace of a symmetric matrix contains an eigenvector\<close>

lemma eigvec_in_invariant:
  fixes H :: "real^'a::finite^'a"
  assumes symH: "\<And>x y. (H *v x) \<bullet> y = x \<bullet> (H *v y)"
    and sub: "subspace U" and inv: "\<forall>x\<in>U. H *v x \<in> U" and ne: "\<exists>x\<in>U. x \<noteq> 0"
  shows "\<exists>v\<in>U. v \<noteq> 0 \<and> (\<exists>mu. H *v v = mu *\<^sub>R v)"
proof -
  define Sp where "Sp = U \<inter> sphere 0 1"
  have compSp: "compact Sp"
    unfolding Sp_def using closed_subspace[OF sub] compact_sphere by (rule closed_Int_compact)
  have normSp: "x \<in> Sp \<longleftrightarrow> x \<in> U \<and> norm x = 1" for x by (simp add: Sp_def)
  obtain x1 where x1U: "x1 \<in> U" and x10: "x1 \<noteq> 0" using ne by auto
  have "(1 / norm x1) *\<^sub>R x1 \<in> Sp"
    using x1U x10 sub by (simp add: normSp subspace_scale)
  hence Spne: "Sp \<noteq> {}" by auto
  have cont: "continuous_on Sp (\<lambda>x. x \<bullet> (H *v x))"
    by (intro continuous_intros linear_continuous_on matrix_vector_mul_linear)
  obtain x0 where x0Sp: "x0 \<in> Sp" and x0max: "\<forall>y\<in>Sp. y \<bullet> (H *v y) \<le> x0 \<bullet> (H *v x0)"
    using continuous_attains_sup[OF compSp Spne cont] by blast
  define mu where "mu = x0 \<bullet> (H *v x0)"
  have x0U: "x0 \<in> U" and x0n: "norm x0 = 1" using x0Sp by (auto simp: normSp)
  have x00: "x0 \<bullet> x0 = 1" using x0n using power2_norm_eq_inner[of x0] by simp
  have bound: "x \<bullet> (H *v x) \<le> mu * (x \<bullet> x)" if xU: "x \<in> U" for x
  proof (cases "x = 0")
    case True thus ?thesis by simp
  next
    case False
    define r where "r = norm x"
    have rpos: "r > 0" using False by (simp add: r_def)
    define y where "y = (1 / r) *\<^sub>R x"
    have ySp: "y \<in> Sp" using xU sub rpos by (simp add: normSp subspace_scale r_def y_def)
    have yle: "y \<bullet> (H *v y) \<le> mu" using x0max ySp unfolding mu_def by blast
    have hs: "H *v y = (1 / r) *\<^sub>R (H *v x)" unfolding y_def by (rule matrix_vector_mult_scaleR)
    have yx: "y \<bullet> (H *v x) = (1 / r) * (x \<bullet> (H *v x))" by (simp only: y_def inner_scaleR_left)
    have "y \<bullet> (H *v y) = (1 / r) * (y \<bullet> (H *v x))" by (simp only: hs inner_scaleR_right)
    also have "\<dots> = (1 / r)\<^sup>2 * (x \<bullet> (H *v x))" by (simp only: yx power2_eq_square mult.assoc)
    finally have "(1 / r)\<^sup>2 * (x \<bullet> (H *v x)) \<le> mu" using yle by simp
    hence "x \<bullet> (H *v x) \<le> mu * r\<^sup>2" using rpos by (simp add: field_simps power2_eq_square)
    thus ?thesis by (simp add: r_def power2_norm_eq_inner)
  qed
  define B where "B x y = mu * (x \<bullet> y) - x \<bullet> (H *v y)" for x y :: "real^'a"
  have Bpos: "B x x \<ge> 0" if "x \<in> U" for x using bound[OF that] by (simp add: B_def)
  have B00: "B x0 x0 = 0" using x00 by (simp add: B_def mu_def)
  have Bzero: "B x0 y = 0" if yU: "y \<in> U" for y
  proof (rule ccontr)
    assume bne: "B x0 y \<noteq> 0"
    define beta where "beta = B x0 y"
    define q where "q = B y y"
    have qpos: "q \<ge> 0" using Bpos[OF yU] by (simp add: q_def)
    have sw: "y \<bullet> (H *v x0) = x0 \<bullet> (H *v y)"
      using symH[of y x0] by (simp add: inner_commute)
    have expand: "B (x0 + t *\<^sub>R y) (x0 + t *\<^sub>R y) = 2 * t * beta + t\<^sup>2 * q" for t
    proof -
      have e1: "(x0 + t *\<^sub>R y) \<bullet> (x0 + t *\<^sub>R y) = x0 \<bullet> x0 + 2 * t * (x0 \<bullet> y) + t\<^sup>2 * (y \<bullet> y)"
        by (simp add: inner_add_left inner_add_right inner_commute[of y x0] power2_eq_square algebra_simps)
      have e2: "(x0 + t *\<^sub>R y) \<bullet> (H *v (x0 + t *\<^sub>R y)) =
          x0 \<bullet> (H *v x0) + 2 * t * (x0 \<bullet> (H *v y)) + t\<^sup>2 * (y \<bullet> (H *v y))"
        by (simp add: matrix_vector_right_distrib matrix_vector_mult_scaleR inner_add_left inner_add_right
            sw power2_eq_square algebra_simps)
      show ?thesis
        unfolding B_def beta_def q_def using e1 e2 B00[unfolded B_def] by (simp add: algebra_simps)
    qed
    have nonneg: "0 \<le> 2 * t * beta + t\<^sup>2 * q" for t
      using Bpos[of "x0 + t *\<^sub>R y"] expand[of t] sub x0U yU
      by (simp add: subspace_add subspace_scale)
    define t where "t = - beta / (q + 1)"
    have q1: "q + 1 > 0" using qpos by simp
    have qne: "q + 1 \<noteq> 0" using q1 by simp
    have h1: "t * (q + 1) = - beta" unfolding t_def using qne by simp
    have "(q + 1)\<^sup>2 * (2 * t * beta + t\<^sup>2 * q) = 2 * beta * (t * (q + 1)) * (q + 1) + q * (t * (q + 1))\<^sup>2"
      by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> = - beta\<^sup>2 * (q + 2)"
      by (simp only: h1) (simp add: power2_eq_square algebra_simps)
    finally have "(q + 1)\<^sup>2 * (2 * t * beta + t\<^sup>2 * q) = - beta\<^sup>2 * (q + 2)" .
    moreover have "- beta\<^sup>2 * (q + 2) < 0" using bne beta_def qpos by (simp add: mult_pos_pos)
    moreover have "(q + 1)\<^sup>2 * (2 * t * beta + t\<^sup>2 * q) \<ge> 0" using nonneg[of t] by simp
    ultimately show False by linarith
  qed
  define z where "z = H *v x0 - mu *\<^sub>R x0"
  have zU: "z \<in> U" using inv x0U sub unfolding z_def by (simp add: subspace_diff subspace_scale)
  have zy: "z \<bullet> y = 0" if yU: "y \<in> U" for y
  proof -
    have e1: "z \<bullet> y = (H *v x0) \<bullet> y - mu * (x0 \<bullet> y)" by (simp add: z_def inner_diff_left)
    have e2: "(H *v x0) \<bullet> y = x0 \<bullet> (H *v y)" by (rule symH)
    have e3: "B x0 y = 0" by (rule Bzero[OF yU])
    show ?thesis using e1 e2 e3 unfolding B_def by linarith
  qed
  have "z \<bullet> z = 0" by (rule zy[OF zU])
  hence "z = 0" by simp
  hence "H *v x0 = mu *\<^sub>R x0" by (simp add: z_def)
  moreover have "x0 \<noteq> 0" using x0n by auto
  ultimately show ?thesis using x0U by blast
qed

lemma spectral_vanish:
  fixes H :: "real^'a::finite^'a" and b :: "real^'a"
  assumes symH: "\<And>x y. (H *v x) \<bullet> y = x \<bullet> (H *v y)"
    and eig: "\<And>v mu. H *v v = mu *\<^sub>R v \<Longrightarrow> b \<bullet> v = 0"
  shows "b = 0"
proof -
  define U where "U = {x::real^'a. \<forall>v mu. H *v v = mu *\<^sub>R v \<longrightarrow> x \<bullet> v = 0}"
  have sub: "subspace U" by (auto simp: U_def subspace_def inner_add_left)
  have inv: "\<forall>x\<in>U. H *v x \<in> U"
  proof
    fix x assume xU: "x \<in> U"
    show "H *v x \<in> U"
      unfolding U_def
    proof (intro CollectI allI impI)
      fix v mu assume hv: "H *v v = mu *\<^sub>R v"
      have "(H *v x) \<bullet> v = x \<bullet> (H *v v)" by (rule symH)
      also have "\<dots> = mu * (x \<bullet> v)" using hv by simp
      also have "\<dots> = 0" using xU hv by (auto simp: U_def)
      finally show "(H *v x) \<bullet> v = 0" .
    qed
  qed
  have bU: "b \<in> U" using eig by (auto simp: U_def inner_commute)
  have allz: "\<forall>x\<in>U. x = 0"
  proof (rule ccontr)
    assume "\<not> (\<forall>x\<in>U. x = 0)"
    hence "\<exists>x\<in>U. x \<noteq> 0" by auto
    from eigvec_in_invariant[OF symH sub inv this]
    obtain v mu where vU: "v \<in> U" and v0: "v \<noteq> 0" and hv: "H *v v = mu *\<^sub>R v" by auto
    have "v \<bullet> v = 0" using vU hv by (auto simp: U_def)
    thus False using v0 by simp
  qed
  thus ?thesis using bU by blast
qed

section \<open>Equality case: an isometry with a unit Rayleigh quotient\<close>

lemma eq_case:
  assumes P: "orth_mat P" and l: "l\<^sup>2 = 1" and q: "y \<bullet> (sympart P *v y) = l * (y \<bullet> y)"
  shows "P *v y = l *\<^sub>R y" and "tr P *v y = l *\<^sub>R y"
proof -
  have ysk: "y \<bullet> (skewpart P *v y) = 0" by (rule skew_zero)
  have yPy: "y \<bullet> (P *v y) = l * (y \<bullet> y)" using q ysk Q_split[of P y] by (simp add: inner_add_right)
  have nPy: "(P *v y) \<bullet> (P *v y) = y \<bullet> y" using orth_inner[OF P] by simp
  have "(P *v y - l *\<^sub>R y) \<bullet> (P *v y - l *\<^sub>R y) = 0"
    using nPy yPy l by (simp add: inner_diff_left inner_diff_right inner_commute power2_eq_square algebra_simps)
  thus "P *v y = l *\<^sub>R y" by simp
  have Pt: "orth_mat (tr P)" by (rule orth_transpose[OF P])
  have yPty: "y \<bullet> (tr P *v y) = l * (y \<bullet> y)"
    using yPy by (metis adjoint_dot inner_commute)
  have nPty: "(tr P *v y) \<bullet> (tr P *v y) = y \<bullet> y" using orth_inner[OF Pt] by simp
  have "(tr P *v y - l *\<^sub>R y) \<bullet> (tr P *v y - l *\<^sub>R y) = 0"
    using nPty yPty l by (simp add: inner_diff_left inner_diff_right inner_commute power2_eq_square algebra_simps)
  thus "tr P *v y = l *\<^sub>R y" by simp
qed


section \<open>The bordered setting: matrices of size n+1, indexed by 'a option\<close>

definition emb :: "real^'a::finite \<Rightarrow> real^('a option)" where
  "emb v = (\<chi> i. case i of None \<Rightarrow> 0 | Some j \<Rightarrow> v $ j)"

definition tailv :: "real^('a::finite option) \<Rightarrow> real^'a" where
  "tailv x = (\<chi> j. x $ Some j)"

definition axisN :: "real^('a::finite option)" where
  "axisN = (\<chi> i. case i of None \<Rightarrow> 1 | Some j \<Rightarrow> 0)"

definition hmat :: "real^('a::finite option)^('a option) \<Rightarrow> real^'a^'a" where
  "hmat S = (\<chi> i j. S $ Some i $ Some j)"

definition bvec :: "real^('a::finite option)^('a option) \<Rightarrow> real^'a" where
  "bvec S = (\<chi> i. S $ Some i $ None)"

definition cc :: "real^('a::finite option)^('a option) \<Rightarrow> real" where
  "cc S = S $ None $ None"

lemma sum_option: "(\<Sum>i\<in>UNIV. f i) = f None + (\<Sum>j\<in>UNIV. f (Some j))"
  for f :: "'a::finite option \<Rightarrow> 'b::comm_monoid_add"
proof -
  have "(\<Sum>i\<in>UNIV. f i) = (\<Sum>i\<in>insert None (range Some). f i)" by (simp add: UNIV_option_conv)
  also have "\<dots> = f None + (\<Sum>i\<in>range Some. f i)" by (rule sum.insert) auto
  also have "(\<Sum>i\<in>range Some. f i) = (\<Sum>j\<in>UNIV. f (Some j))"
    using sum.reindex[of Some UNIV f] by (simp add: o_def)
  finally show ?thesis .
qed

lemma all_option: "(\<forall>i::'a option. P i) \<longleftrightarrow> P None \<and> (\<forall>j. P (Some j))"
  by (metis option.exhaust)

lemma emb_None [simp]: "emb v $ None = 0" by (simp add: emb_def)
lemma emb_Some [simp]: "emb v $ Some j = v $ j" by (simp add: emb_def)
lemma tailv_Some [simp]: "tailv x $ j = x $ Some j" by (simp add: tailv_def)
lemma tailv_emb [simp]: "tailv (emb v) = v" by (simp add: vec_eq_iff)
lemma axisN_None [simp]: "axisN $ None = 1" by (simp add: axisN_def)
lemma axisN_Some [simp]: "axisN $ Some j = 0" by (simp add: axisN_def)
lemma tailv_axisN [simp]: "tailv axisN = 0" by (simp add: vec_eq_iff)

lemma x_decomp: "x = emb (tailv x) + (x $ None) *\<^sub>R axisN"
  by (auto simp: vec_eq_iff all_option)

lemma inner_emb: "emb u \<bullet> y = u \<bullet> tailv y"
  by (simp add: inner_vec_def sum_option)

lemma inner_emb_emb: "emb u \<bullet> emb v = u \<bullet> v"
  by (simp add: inner_emb)

lemma inner_axisN: "axisN \<bullet> y = y $ None"
  by (simp add: inner_vec_def sum_option)

lemma linear_emb: "linear emb"
  by (auto simp: linear_iff vec_eq_iff all_option)

lemma inj_emb: "inj emb"
  by (rule injI) (metis tailv_emb)

lemma emb_scaleR: "emb (a *\<^sub>R v) = a *\<^sub>R emb v" by (auto simp: vec_eq_iff all_option)

lemma emb_add: "emb (a + b) = emb a + emb b" by (auto simp: vec_eq_iff all_option)

lemma emb_zero: "emb 0 = 0" by (auto simp: vec_eq_iff all_option)

lemma subspace_emb: assumes "subspace E" shows "subspace (emb ` E)"
proof -
  have z: "0 \<in> emb ` E" using assms subspace_0 emb_zero by (metis image_eqI)
  have a: "\<forall>x y. x \<in> emb ` E \<longrightarrow> y \<in> emb ` E \<longrightarrow> x + y \<in> emb ` E"
  proof (intro allI impI)
    fix x y assume xi: "x \<in> emb ` E" and yi: "y \<in> emb ` E"
    from xi obtain a where a1: "a \<in> E" and a2: "x = emb a" by blast
    from yi obtain b where b1: "b \<in> E" and b2: "y = emb b" by blast
    have "a + b \<in> E" using assms a1 b1 by (simp add: subspace_add)
    thus "x + y \<in> emb ` E" using a2 b2 by (auto simp: emb_add intro: image_eqI[of _ _ "a + b"])
  qed
  have m: "\<forall>c x. x \<in> emb ` E \<longrightarrow> c *\<^sub>R x \<in> emb ` E"
  proof (intro allI impI)
    fix c x assume xi: "x \<in> emb ` E"
    from xi obtain a where a1: "a \<in> E" and a2: "x = emb a" by blast
    have "c *\<^sub>R a \<in> E" using assms a1 by (simp add: subspace_scale)
    thus "c *\<^sub>R x \<in> emb ` E" using a2 by (auto simp: emb_scaleR intro: image_eqI[of _ _ "c *\<^sub>R a"])
  qed
  show ?thesis using z a m by (simp add: subspace_def)
qed

lemma inj_on_emb: "inj_on emb S" using inj_emb by (rule inj_on_subset) simp

locale bordered =
  fixes Q :: "real^('a::finite option)^('a option)"
  assumes orthQ: "orth_mat Q"
begin

abbreviation S where "S \<equiv> sympart Q"
abbreviation Hm where "Hm \<equiv> hmat S"
abbreviation bv where "bv \<equiv> bvec S"
abbreviation cm where "cm \<equiv> cc S"
abbreviation Eh :: "real \<Rightarrow> (real^'a) set" where "Eh l \<equiv> eigsp Hm l"

lemma symS: "S $ i $ j = S $ j $ i" by (simp add: sympart_entry add.commute)

lemma Hm_sym: "(Hm *v x) \<bullet> y = x \<bullet> (Hm *v y)"
proof -
  have "tr Hm = Hm" by (simp add: tr_def hmat_def vec_eq_iff transpose_def symS)
  thus ?thesis using adjoint_dot[of Hm x y] by simp
qed

lemma row_Some: "(S *v x) $ Some i = (Hm *v tailv x) $ i + bv $ i * x $ None"
  by (simp add: matrix_vector_mult_def sum_option hmat_def bvec_def algebra_simps)

lemma NS_b: "S $ None $ Some j = bv $ j"
  by (simp add: bvec_def) (rule symS)

lemma row_None: "(S *v x) $ None = bv \<bullet> tailv x + cm * x $ None"
  by (simp add: matrix_vector_mult_def sum_option cc_def inner_vec_def NS_b algebra_simps)

lemma Fchar:
  "x \<in> eigsp S l \<longleftrightarrow>
    (Hm *v tailv x + (x $ None) *\<^sub>R bv = l *\<^sub>R tailv x) \<and> (bv \<bullet> tailv x + cm * x $ None = l * x $ None)"
  by (auto simp: eigsp_def vec_eq_iff all_option row_Some row_None algebra_simps)

lemma emb_F: assumes "v \<in> Eh l" and "bv \<bullet> v = 0" shows "emb v \<in> eigsp S l"
  by (rule iffD2[OF Fchar]) (use assms in \<open>simp add: eigsp_def\<close>)

lemma F_t0:
  assumes "x \<in> eigsp S l" and "x $ None = 0"
  shows "x = emb (tailv x)" and "tailv x \<in> Eh l" and "bv \<bullet> tailv x = 0"
proof -
  show "x = emb (tailv x)" using x_decomp[of x] assms(2) by simp
  have h: "(Hm *v tailv x + (x $ None) *\<^sub>R bv = l *\<^sub>R tailv x) \<and>
      (bv \<bullet> tailv x + cm * x $ None = l * x $ None)" using assms(1) by (rule iffD1[OF Fchar])
  show "tailv x \<in> Eh l" using h assms(2) by (simp add: eigsp_def)
  show "bv \<bullet> tailv x = 0" using h assms(2) by simp
qed

lemma even_F: assumes "l\<^sup>2 < 1" shows "even (dim (eigsp S l))"
  by (rule even_dim_interior_eigenspace[OF orthQ assms])

text \<open>Part 1 of the conclusion: b is orthogonal to the eigenspace.\<close>
theorem b_orth_Eh:
  assumes l: "l\<^sup>2 < 1" and ev: "even (dim (Eh l))"
  shows "\<forall>v\<in>Eh l. bv \<bullet> v = 0"
proof (rule ccontr)
  assume "\<not> (\<forall>v\<in>Eh l. bv \<bullet> v = 0)"
  then obtain v0 where v0E: "v0 \<in> Eh l" and v0b: "bv \<bullet> v0 \<noteq> 0" by auto
  define G where "G = {v \<in> Eh l. bv \<bullet> v = 0}"
  have subE: "subspace (Eh l)" by (rule subspace_eigsp)
  have subG: "subspace G" using subE by (auto simp: G_def subspace_def inner_add_right)
  have F_eq: "eigsp S l = emb ` G"
  proof (rule subset_antisym)
    show "eigsp S l \<subseteq> emb ` G"
    proof
      fix x assume xF: "x \<in> eigsp S l"
      have t0: "x $ None = 0"
      proof (rule ccontr)
        assume tn: "x $ None \<noteq> 0"
        have r1: "Hm *v tailv x + (x $ None) *\<^sub>R bv = l *\<^sub>R tailv x" using xF by (simp add: Fchar)
        have "(Hm *v tailv x) \<bullet> v0 = tailv x \<bullet> (Hm *v v0)" by (rule Hm_sym)
        also have "\<dots> = l * (tailv x \<bullet> v0)" using v0E by (simp add: eigsp_def)
        finally have h1: "(Hm *v tailv x) \<bullet> v0 = l * (tailv x \<bullet> v0)" .
        have "(Hm *v tailv x + (x $ None) *\<^sub>R bv) \<bullet> v0 = (l *\<^sub>R tailv x) \<bullet> v0" using r1 by simp
        hence "(Hm *v tailv x) \<bullet> v0 + (x $ None) * (bv \<bullet> v0) = l * (tailv x \<bullet> v0)"
          by (simp add: inner_add_left)
        hence "(x $ None) * (bv \<bullet> v0) = 0" using h1 by simp
        thus False using tn v0b by simp
      qed
      show "x \<in> emb ` G" using F_t0[OF xF t0] by (auto simp: G_def intro!: image_eqI[of _ _ "tailv x"])
    qed
  next
    show "emb ` G \<subseteq> eigsp S l" using emb_F by (auto simp: G_def)
  qed
  have dimF: "dim (eigsp S l) = dim G"
    unfolding F_eq by (rule dim_image_eq[OF linear_emb]) (rule inj_on_emb)
  have E_span: "Eh l = span (insert v0 G)"
  proof (rule subset_antisym)
    show "Eh l \<subseteq> span (insert v0 G)"
    proof
      fix v assume vE: "v \<in> Eh l"
      define a where "a = (bv \<bullet> v) / (bv \<bullet> v0)"
      have "v - a *\<^sub>R v0 \<in> G"
        using vE v0E subE v0b by (simp add: G_def a_def subspace_diff subspace_scale inner_diff_right)
      hence "v - a *\<^sub>R v0 \<in> span (insert v0 G)" by (intro span_base) auto
      moreover have "a *\<^sub>R v0 \<in> span (insert v0 G)" by (intro span_mul span_base) auto
      ultimately have "(v - a *\<^sub>R v0) + a *\<^sub>R v0 \<in> span (insert v0 G)" by (rule span_add)
      thus "v \<in> span (insert v0 G)" by simp
    qed
  next
    show "span (insert v0 G) \<subseteq> Eh l"
      by (rule span_minimal) (use v0E subE in \<open>auto simp: G_def\<close>)
  qed
  have v0nG: "v0 \<notin> span G"
  proof
    assume "v0 \<in> span G"
    moreover have "span G = G" by (rule iffD2[OF span_eq_iff subG])
    ultimately have "v0 \<in> G" by simp
    thus False using v0b by (simp add: G_def)
  qed
  have "dim (Eh l) = dim G + 1"
  proof -
    have "dim (Eh l) = dim (insert v0 G)" using E_span by (metis dim_span)
    also have "\<dots> = dim G + 1" using v0nG by (simp add: dim_insert)
    finally show ?thesis .
  qed
  hence "odd (dim G)" using ev by simp
  moreover have "even (dim G)" using even_F[OF l] dimF by simp
  ultimately show False by simp
qed

text \<open>If b is orthogonal to the eigenspace and some eigenvector of S has nonzero last coordinate,
the eigenspace of S is exactly one dimension larger.\<close>
lemma F_succ:
  assumes bperp: "\<forall>v\<in>Eh l. bv \<bullet> v = 0" and xF: "x \<in> eigsp S l" and xn: "x $ None \<noteq> 0"
  shows "dim (eigsp S l) = dim (Eh l) + 1"
proof -
  have subF: "subspace (eigsp S l)" by (rule subspace_eigsp)
  have sub_emb: "subspace (emb ` Eh l)"
    by (rule subspace_emb[OF subspace_eigsp])
  have F_span: "eigsp S l = span (insert x (emb ` Eh l))"
  proof (rule subset_antisym)
    show "eigsp S l \<subseteq> span (insert x (emb ` Eh l))"
    proof
      fix z assume zF: "z \<in> eigsp S l"
      define a where "a = (z $ None) / (x $ None)"
      have z'F: "z - a *\<^sub>R x \<in> eigsp S l"
        using zF xF subF by (simp add: subspace_diff subspace_scale)
      have z'0: "(z - a *\<^sub>R x) $ None = 0" using xn by (simp add: a_def)
      have "z - a *\<^sub>R x \<in> emb ` Eh l"
        using F_t0[OF z'F z'0] by (auto intro!: image_eqI[of _ _ "tailv (z - a *\<^sub>R x)"])
      hence "z - a *\<^sub>R x \<in> span (insert x (emb ` Eh l))" by (intro span_base) auto
      moreover have "a *\<^sub>R x \<in> span (insert x (emb ` Eh l))" by (intro span_mul span_base) auto
      ultimately have "(z - a *\<^sub>R x) + a *\<^sub>R x \<in> span (insert x (emb ` Eh l))" by (rule span_add)
      thus "z \<in> span (insert x (emb ` Eh l))" by simp
    qed
  next
    show "span (insert x (emb ` Eh l)) \<subseteq> eigsp S l"
      by (rule span_minimal) (use xF subF bperp emb_F in \<open>auto\<close>)
  qed
  have xnot: "x \<notin> span (emb ` Eh l)"
  proof
    assume "x \<in> span (emb ` Eh l)"
    moreover have "span (emb ` Eh l) = emb ` Eh l" by (rule iffD2[OF span_eq_iff sub_emb])
    ultimately have "x \<in> emb ` Eh l" by simp
    then obtain v where "x = emb v" by blast
    thus False using xn by simp
  qed
  have "dim (eigsp S l) = dim (insert x (emb ` Eh l))" using F_span by (metis dim_span)
  also have "\<dots> = dim (emb ` Eh l) + 1" using xnot by (simp add: dim_insert)
  also have "dim (emb ` Eh l) = dim (Eh l)"
    by (rule dim_image_eq[OF linear_emb]) (rule inj_on_emb)
  finally show ?thesis .
qed

theorem F_eq_emb:
  assumes l: "l\<^sup>2 < 1" and ev: "even (dim (Eh l))"
  shows "eigsp S l = emb ` Eh l"
proof -
  have bperp: "\<forall>v\<in>Eh l. bv \<bullet> v = 0" by (rule b_orth_Eh[OF l ev])
  show ?thesis
  proof (rule subset_antisym)
    show "eigsp S l \<subseteq> emb ` Eh l"
    proof
      fix x assume xF: "x \<in> eigsp S l"
      show "x \<in> emb ` Eh l"
      proof (cases "x $ None = 0")
        case True
        thus ?thesis using F_t0[OF xF True] by (auto intro!: image_eqI[of _ _ "tailv x"])
      next
        case False
        from F_succ[OF bperp xF False] have "dim (eigsp S l) = dim (Eh l) + 1" .
        hence "odd (dim (eigsp S l))" using ev by simp
        thus ?thesis using even_F[OF l] by simp
      qed
    qed
  next
    show "emb ` Eh l \<subseteq> eigsp S l" using emb_F bperp by auto
  qed
qed

text \<open>Theorem real (2): b is orthogonal to E_l and Q maps E_l into itself.\<close>
theorem real_part2:
  assumes l: "l\<^sup>2 < 1" and ev: "even (dim (Eh l))" and v: "v \<in> Eh l"
  shows "bv \<bullet> v = 0" and "\<exists>w\<in>Eh l. Q *v emb v = emb w"
proof -
  show "bv \<bullet> v = 0" using b_orth_Eh[OF l ev] v by blast
  have bperp: "bv \<bullet> v = 0" by fact
  have vF: "emb v \<in> eigsp S l" by (rule emb_F[OF v bperp])
  have "skewpart Q *v emb v \<in> eigsp S l"
    using vF by (simp add: eigsp_def sym_skew_commute[OF orthQ] matrix_vector_mult_scaleR)
  hence "skewpart Q *v emb v \<in> emb ` Eh l" using F_eq_emb[OF l ev] by simp
  then obtain u where uE: "u \<in> Eh l" and u: "skewpart Q *v emb v = emb u" by auto
  have "Q *v emb v = l *\<^sub>R emb v + emb u"
    using Q_split[of Q "emb v"] vF u by (simp add: eigsp_def)
  hence "Q *v emb v = emb (l *\<^sub>R v + u)" by (simp add: emb_scaleR emb_add)
  moreover have "l *\<^sub>R v + u \<in> Eh l"
    using v uE subspace_eigsp[of Hm l] by (simp add: subspace_add subspace_scale)
  ultimately show "\<exists>w\<in>Eh l. Q *v emb v = emb w" by blast
qed

end



section \<open>Corollary jump: the corner block of Q is orthogonal\<close>

lemma rayleigh_bound:
  assumes P: "orth_mat P" and y0: "y \<noteq> 0" and q: "y \<bullet> (sympart P *v y) = l * (y \<bullet> y)"
  shows "l\<^sup>2 \<le> 1"
proof -
  have ysk: "y \<bullet> (skewpart P *v y) = 0" by (rule skew_zero)
  have yPy: "y \<bullet> (P *v y) = l * (y \<bullet> y)" using q ysk Q_split[of P y] by (simp add: inner_add_right)
  have nPy: "(P *v y) \<bullet> (P *v y) = y \<bullet> y" using orth_inner[OF P] by simp
  have cs: "(y \<bullet> (P *v y))\<^sup>2 \<le> (y \<bullet> y) * ((P *v y) \<bullet> (P *v y))" by (rule Cauchy_Schwarz_ineq)
  have yy: "y \<bullet> y > 0" using y0 by simp
  have "l\<^sup>2 * ((y \<bullet> y) * (y \<bullet> y)) \<le> (y \<bullet> y) * (y \<bullet> y)"
    using cs yPy nPy by (simp add: power2_eq_square algebra_simps)
  thus ?thesis using yy by (simp add: mult_le_cancel_right)
qed

context bordered
begin

lemma tailv_S_emb: "tailv (S *v emb v) = Hm *v v"
  by (simp add: vec_eq_iff row_Some)

lemma quad_emb: "emb v \<bullet> (S *v emb v) = v \<bullet> (Hm *v v)"
  by (simp add: inner_emb tailv_S_emb)

lemma None_S_emb: "(S *v emb v) $ None = bv \<bullet> v"
  by (simp add: row_None)

text \<open>Every eigenvector v of H (|l| < 1 needs the even multiplicity supplied by an orthogonal T0 with
symmetric part H) is orthogonal to b.\<close>
lemma b_orth_eigvec:
  fixes T0 :: "real^'a^'a"
  assumes T0: "orth_mat T0" and hH: "sympart T0 = Hm" and v: "v \<in> Eh l"
  shows "bv \<bullet> v = 0"
proof (cases "v = 0")
  case True thus ?thesis by simp
next
  case False
  have hv: "Hm *v v = l *\<^sub>R v" using v by (simp add: eigsp_def)
  have q: "emb v \<bullet> (S *v emb v) = l * (emb v \<bullet> emb v)" using quad_emb[of v] hv by (simp add: inner_emb)
  have emb0: "emb v \<noteq> 0"
  proof
    assume e0: "emb v = 0"
    have "tailv (emb v) = tailv (0::real^('a option))" by (rule arg_cong[OF e0])
    hence "v = 0" by (simp add: vec_eq_iff)
    thus False using False by simp
  qed
  have l1: "l\<^sup>2 \<le> 1" by (rule rayleigh_bound[OF orthQ emb0 q])
  show ?thesis
  proof (cases "l\<^sup>2 < 1")
    case True
    have "even (dim (eigsp (sympart T0) l))" by (rule even_dim_interior_eigenspace[OF T0 True])
    hence "even (dim (Eh l))" using hH by simp
    thus ?thesis using b_orth_Eh[OF True] v by blast
  next
    case False
    hence l2: "l\<^sup>2 = 1" using l1 by simp
    have "tr Q *v emb v = l *\<^sub>R emb v" and "Q *v emb v = l *\<^sub>R emb v"
      using eq_case[OF orthQ l2 q] by auto
    hence "S *v emb v = l *\<^sub>R emb v" by (simp add: sympart_vec vec_eq_iff)
    hence "(S *v emb v) $ None = 0" by simp
    thus ?thesis using None_S_emb by simp
  qed
qed

lemma b_zero:
  fixes T0 :: "real^'a^'a"
  assumes T0: "orth_mat T0" and hH: "sympart T0 = Hm"
  shows "bv = 0"
proof (rule spectral_vanish[OF Hm_sym])
  fix v mu assume "Hm *v v = mu *\<^sub>R v"
  thus "bv \<bullet> v = 0" using b_orth_eigvec[OF T0 hH, of v mu] by (simp add: eigsp_def)
qed

lemma axisN_eig:
  assumes "bv = 0"
  shows "S *v axisN = cm *\<^sub>R axisN"
  using assms by (auto simp: vec_eq_iff all_option row_Some row_None)

lemma c_unit:
  fixes T0 :: "real^'a^'a"
  assumes T0: "orth_mat T0" and hH: "sympart T0 = Hm" and b0: "bv = 0"
  shows "cm\<^sup>2 = 1"
proof -
  have eig: "S *v axisN = cm *\<^sub>R axisN" by (rule axisN_eig[OF b0])
  have q: "axisN \<bullet> (S *v axisN) = cm * (axisN \<bullet> (axisN :: real^('a option)))" using eig by simp
  have an0: "(axisN :: real^('a option)) \<noteq> 0"
  proof
    assume h: "axisN = (0::real^('a option))"
    have "(axisN :: real^('a option)) \<bullet> axisN = 1" by (simp add: inner_axisN)
    thus False using h by simp
  qed
  have c1: "cm\<^sup>2 \<le> 1" by (rule rayleigh_bound[OF orthQ an0 q])
  show ?thesis
  proof (rule ccontr)
    assume "cm\<^sup>2 \<noteq> 1"
    hence lt: "cm\<^sup>2 < 1" using c1 by simp
    have bperp: "\<forall>v\<in>Eh cm. bv \<bullet> v = 0" using b0 by simp
    have axF: "axisN \<in> eigsp S cm" using eig by (simp add: eigsp_def)
    have "dim (eigsp S cm) = dim (Eh cm) + 1" by (rule F_succ[OF bperp axF]) simp
    moreover have "even (dim (Eh cm))"
      using even_dim_interior_eigenspace[OF T0 lt] hH by simp
    moreover have "even (dim (eigsp S cm))" by (rule even_F[OF lt])
    ultimately show False by simp
  qed
qed

definition Tn :: "real^'a^'a" where "Tn = (\<chi> i j. Q $ Some i $ Some j)"

theorem jump_core:
  fixes T0 :: "real^'a^'a"
  assumes T0: "orth_mat T0" and hH: "sympart T0 = Hm"
  shows "orth_mat Tn" and "sympart Tn = Hm" and "\<And>i j. Tn $ i $ j = Q $ Some i $ Some j"
proof -
  have b0: "bv = 0" by (rule b_zero[OF T0 hH])
  have c2: "cm\<^sup>2 = 1" by (rule c_unit[OF T0 hH b0])
  have eig: "S *v axisN = cm *\<^sub>R axisN" by (rule axisN_eig[OF b0])
  have q: "axisN \<bullet> (S *v axisN) = cm * (axisN \<bullet> (axisN :: real^('a option)))" using eig by simp
  have Qe: "tr Q *v axisN = cm *\<^sub>R axisN" using eq_case[OF orthQ c2 q] by auto
  have Qpres: "(Q *v emb v) $ None = 0" for v
  proof -
    have "(Q *v emb v) $ None = axisN \<bullet> (Q *v emb v)" by (simp add: inner_axisN)
    also have "\<dots> = (tr Q *v axisN) \<bullet> emb v" using adjoint_dot[of "tr Q" axisN "emb v"] by (simp add: tr_tr)
    also have "\<dots> = cm * (axisN \<bullet> emb v)" by (simp add: Qe)
    finally have h: "(Q *v emb v) $ None = cm * (axisN \<bullet> emb v)" .
    show ?thesis by (simp only: h inner_axisN emb_None mult_zero_right)
  qed
  have Tentry: "\<And>i j. Tn $ i $ j = Q $ Some i $ Some j" by (simp add: Tn_def)
  have Tapp: "Q *v emb v = emb (Tn *v v)" for v
  proof -
    have "(Q *v emb v) $ None = emb (Tn *v v) $ None" by (simp add: Qpres)
    moreover have "\<And>j. (Q *v emb v) $ Some j = emb (Tn *v v) $ Some j"
      by (simp add: matrix_vector_mult_def sum_option Tn_def)
    ultimately show ?thesis by (simp add: vec_eq_iff all_option)
  qed
  have iso: "(Tn *v v) \<bullet> (Tn *v w) = v \<bullet> w" for v w
  proof -
    have "(Tn *v v) \<bullet> (Tn *v w) = emb (Tn *v v) \<bullet> emb (Tn *v w)" by (simp add: inner_emb_emb)
    also have "\<dots> = (Q *v emb v) \<bullet> (Q *v emb w)" by (simp add: Tapp)
    also have "\<dots> = emb v \<bullet> emb w" by (rule orth_inner[OF orthQ])
    finally show ?thesis by (simp add: inner_emb_emb)
  qed
  show "orth_mat Tn"
  proof -
    have "(tr Tn ** Tn) *v v = mat 1 *v v" for v
    proof -
      define z where "z = tr Tn *v (Tn *v v) - v"
      have "z \<bullet> w = 0" for w
        using adjoint_dot[of "tr Tn" "Tn *v v" w] iso[of v w]
        by (simp add: z_def inner_diff_left tr_tr)
      hence "z \<bullet> z = 0" by blast
      hence "z = 0" by simp
      thus ?thesis by (simp add: z_def matrix_vector_mul_assoc)
    qed
    hence "tr Tn ** Tn = mat 1" by (simp add: matrix_eq)
    thus ?thesis by (simp add: orth_mat_def)
  qed
  show "sympart Tn = Hm"
    by (simp add: vec_eq_iff sympart_entry hmat_def Tentry)
  show "\<And>i j. Tn $ i $ j = Q $ Some i $ Some j" by (rule Tentry)
qed

end

section \<open>Rational matrices, Witt cancellation as a named assumption, and Corollary jump\<close>

definition rational_mat :: "real^'n^'m \<Rightarrow> bool" where
  "rational_mat M \<longleftrightarrow> (\<forall>i j. M $ i $ j \<in> Rats)"

definition rep_mat :: "real^'n::finite^'r::finite \<Rightarrow> real^'n^'r \<Rightarrow> real^'n^'n \<Rightarrow> bool" where
  "rep_mat A B H \<longleftrightarrow> transpose A ** A = mat 1 \<and> transpose B ** B = mat 1 \<and>
     transpose A ** B + transpose B ** A = 2 *\<^sub>R H"

lemma sum_in_Rats: "finite A \<Longrightarrow> (\<forall>x\<in>A. f x \<in> Rats) \<Longrightarrow> sum f A \<in> Rats"
  by (induct rule: finite_induct) (auto simp: Rats_add)

lemma rational_mat_mult:
  fixes A :: "real^'n::finite^'m" and B :: "real^'k^'n"
  assumes "rational_mat A" and "rational_mat B"
  shows "rational_mat (A ** B)"
  using assms
  by (auto simp: rational_mat_def matrix_matrix_mult_def intro!: sum_in_Rats Rats_mult)

lemma rational_mat_transpose: "rational_mat M \<Longrightarrow> rational_mat (transpose M)"
  by (simp add: rational_mat_def transpose_def)

text \<open>Named assumption (the only unproved fact of this theory): Witt cancellation over Q. If the
columns of a rational (n+1) x n matrix M are orthonormal, then M extends, by one more rational column, to
a rational orthogonal matrix of size n+1. (The orthogonal complement of the column space is a rational line
L with I_(n+1) = I_n + L; by Witt cancellation L is isometric to the unit form, so it has a rational vector of
norm 1.  Lam, Introduction to Quadratic Forms over Fields, Chapter I, Witt cancellation theorem.)\<close>
locale witt_over_Q =
  fixes Wext :: "real^'a::finite^('a option) \<Rightarrow> real^('a option)^('a option)"
  assumes witt: "\<And>M. rational_mat M \<Longrightarrow> transpose M ** M = mat 1 \<Longrightarrow>
      rational_mat (Wext M) \<and> orth_mat (Wext M) \<and> (\<forall>i j. Wext M $ i $ Some j = M $ i $ j)"

lemma transpose_mult_entry: "(transpose A ** B) $ i $ j = (\<Sum>k\<in>UNIV. A $ k $ i * B $ k $ j)"
  for A :: "real^'n::finite^'r::finite" and B :: "real^'m^'r"
  by (simp add: matrix_matrix_mult_def transpose_def)

theorem (in witt_over_Q) cor_jump:
  fixes H :: "real^'a^'a"
  assumes real_n: "\<exists>T0. orth_mat T0 \<and> sympart T0 = H"
    and rat_n1: "\<exists>A B::real^'a^('a option). rational_mat A \<and> rational_mat B \<and> rep_mat A B H"
  shows "\<exists>T. rational_mat T \<and> orth_mat T \<and> sympart T = H"
proof -
  obtain T0 where T0: "orth_mat T0" and hT0: "sympart T0 = H" using real_n by blast
  obtain A B :: "real^'a^('a option)" where rA: "rational_mat A" and rB: "rational_mat B"
    and rep: "rep_mat A B H" using rat_n1 by blast
  have AA: "transpose A ** A = mat 1" and BB: "transpose B ** B = mat 1"
    and AB: "transpose A ** B + transpose B ** A = 2 *\<^sub>R H" using rep by (simp_all add: rep_mat_def)
  obtain P where rP: "rational_mat P" and oP: "orth_mat P" and PA: "\<And>i j. P $ i $ Some j = A $ i $ j"
    using witt[OF rA AA] by metis
  define Bp where "Bp = transpose P ** B"
  have rBp: "rational_mat Bp"
    unfolding Bp_def using rational_mat_mult[OF rational_mat_transpose[OF rP] rB] .
  have PPt: "P ** transpose P = mat 1" using orth_right_mat[OF oP] by (simp add: tr_def)
  have BpBp: "transpose Bp ** Bp = mat 1"
  proof -
    have "transpose Bp ** Bp = (transpose B ** P) ** (transpose P ** B)" by (simp add: Bp_def matrix_transpose_mul)
    also have "\<dots> = transpose B ** (P ** (transpose P ** B))" by (simp add: matrix_mul_assoc)
    also have "\<dots> = transpose B ** ((P ** transpose P) ** B)" by (simp add: matrix_mul_assoc)
    also have "\<dots> = mat 1" using PPt BB by (simp add: matrix_mul_lid)
    finally show ?thesis .
  qed
  obtain Q where rQ: "rational_mat Q" and oQ: "orth_mat Q" and QB: "\<And>i j. Q $ i $ Some j = Bp $ i $ j"
    using witt[OF rBp BpBp] by metis
  interpret bordered Q by unfold_locales (rule oQ)
  have X: "\<And>i j. Q $ Some i $ Some j = (\<Sum>k\<in>UNIV. A $ k $ i * B $ k $ j)"
  proof -
    fix i j
    have "Q $ Some i $ Some j = Bp $ Some i $ j" by (rule QB)
    also have "\<dots> = (\<Sum>k\<in>UNIV. P $ k $ Some i * B $ k $ j)" by (simp add: Bp_def matrix_matrix_mult_def transpose_def)
    also have "\<dots> = (\<Sum>k\<in>UNIV. A $ k $ i * B $ k $ j)" by (simp add: PA)
    finally show "Q $ Some i $ Some j = (\<Sum>k\<in>UNIV. A $ k $ i * B $ k $ j)" .
  qed
  have HH: "Hm = H"
  proof (rule vec_eq_iff[THEN iffD2, rule_format]; rule vec_eq_iff[THEN iffD2, rule_format])
    fix i j
    have "(transpose A ** B + transpose B ** A) $ i $ j = (2 *\<^sub>R H) $ i $ j" using AB by simp
    hence "(\<Sum>k\<in>UNIV. A $ k $ i * B $ k $ j) + (\<Sum>k\<in>UNIV. A $ k $ j * B $ k $ i) = 2 * H $ i $ j"
      by (simp add: transpose_mult_entry matrix_matrix_mult_def transpose_def mult.commute)
    thus "Hm $ i $ j = H $ i $ j"
      by (simp add: hmat_def sympart_entry X)
  qed
  obtain T where oT: "orth_mat T" and sT: "sympart T = Hm" and eT: "\<And>i j. T $ i $ j = Q $ Some i $ Some j"
    using jump_core[OF T0] hT0 HH by (metis)
  have "rational_mat T" using rQ eT by (simp add: rational_mat_def)
  thus ?thesis using oT sT HH by auto
qed

end
