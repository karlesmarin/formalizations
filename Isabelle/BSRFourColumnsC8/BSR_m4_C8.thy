(*  Title:      BSR_m4_C8.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Computation C8 of the paper "Every m x 4 biquadratic sum of squares is a sum of 3m-1 squares (5 <= m <= 16)" (2026, in preparation),
    Lemma "Positive annihilator" (label positive).
    (a) Single-wedge pairings.  T_i : A' -> E linear, J symmetric bilinear on E, H_ij(a,b) = J(T_i a, T_j b),
        Psi(z)_k = sum_j T_j z_kj on antisymmetric z.  If J^{(+)n} is nonnegative on im Psi then
        S(a,a) = sum_i H_ii(a,a) >= 0, and for n >= 3, S(a,a) = 0 forces H_ij(a,b) = 0 for all i, j, b
        (a lies in the first radical).
    (b) Inertia subtraction.  For J = diag(I_p, -I_q), a J-nonnegative subspace L that is J-orthogonal to a
        J-positive definite subspace M satisfies dim L + dim M <= p  (this is rk Psi <= np - a).
        The reduction of a nondegenerate form to diag(I_p, -I_q) (Sylvester) is not part of this theory.
    Statements written from the paper; proofs complete, with negative controls.
*)

theory BSR_m4_C8
  imports "HOL-Analysis.Analysis"
begin

subsection \<open>(a) Single-wedge pairings\<close>

definition Psi :: "('i::finite \<Rightarrow> 'v \<Rightarrow> 'e::real_vector) \<Rightarrow> ('i \<Rightarrow> 'i \<Rightarrow> 'v) \<Rightarrow> 'i \<Rightarrow> 'e" where
  "Psi T z = (\<lambda>k. \<Sum>j\<in>UNIV. T j (z k j))"

definition Qn :: "('e \<Rightarrow> 'e \<Rightarrow> real) \<Rightarrow> ('i::finite \<Rightarrow> 'e) \<Rightarrow> real" where
  "Qn J w = (\<Sum>k\<in>UNIV. J (w k) (w k))"

definition antisym :: "('i \<Rightarrow> 'i \<Rightarrow> 'v::real_vector) \<Rightarrow> bool" where
  "antisym z \<longleftrightarrow> (\<forall>i j. z i j = - z j i)"

lemma third_index:
  assumes n: "3 \<le> CARD('i::finite)"
  shows "\<exists>m::'i. m \<noteq> i \<and> m \<noteq> j"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have sub: "(UNIV::'i set) \<subseteq> {i, j}" by auto
  have "CARD('i) \<le> card {i, j}" by (rule card_mono[OF _ sub]) simp
  moreover have "card {i, j} \<le> 2" by (cases "i = j") simp_all
  ultimately show False using n by simp
qed

lemma zero_by_three:
  fixes x :: "'i::finite \<Rightarrow> real"
  assumes n: "3 \<le> CARD('i)" and pr: "\<And>p q. p \<noteq> q \<Longrightarrow> x p + x q = 0"
  shows "x i = 0"
proof -
  obtain j where j: "j \<noteq> i" using third_index[OF n, of i i] by blast
  obtain k where k: "k \<noteq> i" "k \<noteq> j" using third_index[OF n, of i j] by blast
  have "x i + x j = 0" using pr[of i j] j by simp
  moreover have "x i + x k = 0" using pr[of i k] k by simp
  moreover have "x j + x k = 0" using pr[of j k] k by simp
  ultimately show ?thesis by linarith
qed

locale wedge_setup =
  fixes T :: "'i::finite \<Rightarrow> 'v::real_vector \<Rightarrow> 'e::real_vector"
    and J :: "'e \<Rightarrow> 'e \<Rightarrow> real"
  assumes T_lin: "\<And>i. linear (T i)"
    and J_bil: "bilinear J"
    and J_sym: "\<And>x y. J x y = J y x"
    and nonneg: "\<And>z. antisym z \<Longrightarrow> Qn J (Psi T z) \<ge> 0"
begin

definition H :: "'i \<Rightarrow> 'i \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> real" where
  "H i j a b = J (T i a) (T j b)"

definition S :: "'v \<Rightarrow> 'v \<Rightarrow> real" where
  "S a b = (\<Sum>i\<in>UNIV. H i i a b)"

definition W :: "'i \<Rightarrow> 'i \<Rightarrow> 'v \<Rightarrow> 'i \<Rightarrow> 'i \<Rightarrow> 'v" where
  "W i j a = (\<lambda>k l. if k = i \<and> l = j then a else if k = j \<and> l = i then - a else 0)"

definition QB :: "('i \<Rightarrow> 'e) \<Rightarrow> ('i \<Rightarrow> 'e) \<Rightarrow> real" where
  "QB P P' = (\<Sum>k\<in>UNIV. J (P k) (P' k))"

lemma J_zl [simp]: "J 0 x = 0" using J_bil by (rule bilinear_lzero)
lemma J_zr [simp]: "J x 0 = 0" using J_bil by (rule bilinear_rzero)
lemma J_nl [simp]: "J (- x) y = - J x y" using J_bil by (rule bilinear_lneg)
lemma J_nr [simp]: "J x (- y) = - J x y" using J_bil by (rule bilinear_rneg)
lemma T_zero [simp]: "T i 0 = 0" using T_lin by (rule linear_0)
lemma T_neg [simp]: "T i (- a) = - T i a" using T_lin by (rule linear_neg)

lemma antisym_W: assumes "i \<noteq> j" shows "antisym (W i j a)"
  using assms unfolding antisym_def W_def by auto

lemma Psi_W:
  assumes ne: "i \<noteq> j"
  shows "Psi T (W i j a) m = (if m = i then T j a else if m = j then - T i a else 0)"
proof -
  show ?thesis
    using ne unfolding Psi_def W_def
    by (cases "m = i"; cases "m = j") (simp_all add: if_distrib cong: if_cong)
qed

lemma Qb1:
  assumes "i \<noteq> j" "i \<noteq> k" "j \<noteq> k"
  shows "QB (Psi T (W i j a)) (Psi T (W i k b)) = H j k a b"
proof -
  have "\<And>m. J (Psi T (W i j a) m) (Psi T (W i k b) m) = (if m = i then H j k a b else 0)"
    using assms by (auto simp: Psi_W H_def)
  then show ?thesis unfolding QB_def by simp
qed

lemma Qb2:
  assumes "i \<noteq> j"
  shows "QB (Psi T (W i j a)) (Psi T (W i j b)) = H j j a b + H i i a b"
proof -
  have "\<And>m. J (Psi T (W i j a) m) (Psi T (W i j b) m)
      = (if m = i then H j j a b else 0) + (if m = j then H i i a b else 0)"
    using assms by (auto simp: Psi_W H_def)
  then show ?thesis unfolding QB_def by (simp add: sum.distrib)
qed

lemma Qn_QB: "Qn J P = QB P P" unfolding Qn_def QB_def by simp

lemma Psi_lin: "Psi T (\<lambda>k l. w k l + s *\<^sub>R z' k l) = (\<lambda>m. Psi T w m + s *\<^sub>R Psi T z' m)"
proof
  fix m
  show "Psi T (\<lambda>k l. w k l + s *\<^sub>R z' k l) m = Psi T w m + s *\<^sub>R Psi T z' m"
    by (simp add: Psi_def linear_add[OF T_lin] linear_cmul[OF T_lin] sum.distrib scaleR_sum_right)
qed

lemma Qn_expand:
  "Qn J (\<lambda>k. P k + s *\<^sub>R P' k) = Qn J P + 2 * s * QB P P' + s^2 * Qn J P'"
proof -
  have "\<And>k. J (P k + s *\<^sub>R P' k) (P k + s *\<^sub>R P' k)
      = J (P k) (P k) + 2 * s * J (P k) (P' k) + s^2 * J (P' k) (P' k)"
  proof -
    fix k
    have e: "J (P k + s *\<^sub>R P' k) (P k + s *\<^sub>R P' k)
      = J (P k) (P k) + s * J (P k) (P' k) + (s * J (P' k) (P k) + s * (s * J (P' k) (P' k)))"
      by (simp add: bilinear_ladd[OF J_bil] bilinear_radd[OF J_bil] bilinear_lmul[OF J_bil]
          bilinear_rmul[OF J_bil] algebra_simps)
    have sy: "J (P' k) (P k) = J (P k) (P' k)" by (rule J_sym)
    show "J (P k + s *\<^sub>R P' k) (P k + s *\<^sub>R P' k)
      = J (P k) (P k) + 2 * s * J (P k) (P' k) + s^2 * J (P' k) (P' k)"
      unfolding e sy by (simp add: power2_eq_square algebra_simps ring_distribs)
  qed
  then show ?thesis
    unfolding Qn_def QB_def by (simp add: sum.distrib sum_distrib_left)
qed

lemma QB_null:
  assumes w: "antisym w" and z: "antisym z'" and w0: "Qn J (Psi T w) = 0"
  shows "QB (Psi T w) (Psi T z') = 0"
proof -
  define b where "b = QB (Psi T w) (Psi T z')"
  define q where "q = Qn J (Psi T z')"
  have q0: "q \<ge> 0" unfolding q_def by (rule nonneg[OF z])
  have key: "\<And>s. 0 \<le> 2 * s * b + s^2 * q"
  proof -
    fix s :: real
    have "antisym (\<lambda>k l. w k l + s *\<^sub>R z' k l)"
      unfolding antisym_def
    proof (intro allI)
      fix k l
      have a: "w k l = - w l k" and b: "z' k l = - z' l k" using w z unfolding antisym_def by blast+
      show "w k l + s *\<^sub>R z' k l = - (w l k + s *\<^sub>R z' l k)" by (simp add: a b)
    qed
    from nonneg[OF this] show "0 \<le> 2 * s * b + s^2 * q"
      by (simp add: Psi_lin Qn_expand w0 b_def q_def)
  qed
  define s where "s = - (b / (q + 1))"
  have sb: "b = - (s * (q + 1))" unfolding s_def using q0 by (simp add: field_simps)
  have "0 \<le> 2 * s * b + s^2 * q" by (rule key)
  also have "2 * s * b + s^2 * q = - (s^2 * (q + 2))" unfolding sb by (simp add: algebra_simps power2_eq_square)
  finally have "s^2 * (q + 2) \<le> 0" by simp
  moreover have "0 \<le> s^2 * (q + 2)" using q0 by simp
  ultimately have "s^2 * (q + 2) = 0" by simp
  then have "s = 0" using q0 by simp
  then show ?thesis using sb b_def by simp
qed

lemma pair_total:
  "(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (if i = j then 0 else H i i a a + H j j a a))
   = 2 * (real CARD('i) - 1) * S a a"
proof -
  have e: "\<And>i j. (if i = j then 0 else H i i a a + H j j a a)
      = (H i i a a + H j j a a) - (if i = j then H i i a a + H j j a a else 0)" by simp
  have A: "(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (H i i a a + H j j a a)) = 2 * real CARD('i) * S a a"
    by (simp add: S_def sum.distrib sum_constant sum_distrib_left algebra_simps)
  have B: "(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (if i = j then H i i a a + H j j a a else 0)) = 2 * S a a"
    by (simp add: S_def sum_distrib_left algebra_simps)
  show ?thesis by (simp only: e sum_subtractf A B) (simp add: algebra_simps)
qed

theorem wedge_pair_nonneg:
  assumes "i \<noteq> j"
  shows "H i i a a + H j j a a \<ge> 0"
proof -
  have "0 \<le> Qn J (Psi T (W i j a))" by (rule nonneg[OF antisym_W[OF assms]])
  also have "Qn J (Psi T (W i j a)) = H j j a a + H i i a a"
    by (simp add: Qn_QB Qb2[OF assms])
  finally show ?thesis by simp
qed

theorem S_nonneg:
  assumes "2 \<le> CARD('i)"
  shows "S a a \<ge> 0"
proof -
  have g: "\<And>i j. 0 \<le> (if i = j then 0 else H i i a a + H j j a a)"
    using wedge_pair_nonneg by auto
  have "0 \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (if i = j then 0 else H i i a a + H j j a a))"
    by (intro sum_nonneg g)
  then have pos: "0 \<le> 2 * (real CARD('i) - 1) * S a a" by (simp only: pair_total)
  moreover have "(2::real) \<le> real CARD('i)" using assms by simp
  ultimately have c: "0 < 2 * (real CARD('i) - 1)" by simp
  show ?thesis
  proof (rule ccontr)
    assume "\<not> S a a \<ge> 0"
    then have "S a a < 0" by simp
    from mult_pos_neg[OF c this] pos show False by simp
  qed
qed

theorem S_zero_radical:
  assumes n3: "3 \<le> CARD('i)" and S0: "S a a = 0"
  shows "H i j a b = 0"
proof -
  have g: "\<And>p q. 0 \<le> (if p = q then 0 else H p p a a + H q q a a)"
    using wedge_pair_nonneg by auto
  have tot: "(\<Sum>p\<in>UNIV. \<Sum>q\<in>UNIV. (if p = q then 0 else H p p a a + H q q a a)) = 0"
    by (simp only: pair_total S0 mult_zero_right)
  have inner: "\<And>p. (\<Sum>q\<in>UNIV. (if p = q then 0 else H p p a a + H q q a a)) = 0"
  proof -
    have "\<forall>p\<in>UNIV. (\<Sum>q\<in>UNIV. (if p = q then 0 else H p p a a + H q q a a)) = 0"
      using tot by (subst (asm) sum_nonneg_eq_0_iff) (auto intro: sum_nonneg g)
    then show "\<And>p. (\<Sum>q\<in>UNIV. (if p = q then 0 else H p p a a + H q q a a)) = 0" by simp
  qed
  have pairs: "\<And>p q. p \<noteq> q \<Longrightarrow> H p p a a + H q q a a = 0"
  proof -
    fix p q :: 'i
    assume pq: "p \<noteq> q"
    have nn: "\<And>q. q \<in> UNIV \<Longrightarrow> 0 \<le> (if p = q then 0 else H p p a a + H q q a a)" by (rule g)
    have "\<forall>q\<in>UNIV. (if p = q then 0 else H p p a a + H q q a a) = 0"
      using iffD1[OF sum_nonneg_eq_0_iff[OF finite nn] inner[of p]] .
    then have "(if p = q then 0 else H p p a a + H q q a a) = 0" by (rule bspec) simp
    then show "H p p a a + H q q a a = 0" using pq by simp
  qed
  have wn0: "\<And>p q. p \<noteq> q \<Longrightarrow> Qn J (Psi T (W p q a)) = 0"
    by (simp add: Qn_QB Qb2 pairs)
  have diag: "\<And>p q. p \<noteq> q \<Longrightarrow> H p p a b + H q q a b = 0"
  proof -
    fix p q :: 'i
    assume pq: "p \<noteq> q"
    have "QB (Psi T (W q p a)) (Psi T (W q p b)) = 0"
      by (rule QB_null[OF antisym_W[OF pq[symmetric]] antisym_W[OF pq[symmetric]] wn0[OF pq[symmetric]]])
    then show "H p p a b + H q q a b = 0" by (simp add: Qb2[OF pq[symmetric]])
  qed
  have dz: "\<And>p. H p p a b = 0"
    by (rule zero_by_three[where x = "\<lambda>p. H p p a b", OF n3 diag]) simp
  show ?thesis
  proof (cases "i = j")
    case True
    then show ?thesis using dz by simp
  next
    case False
    obtain m where m: "m \<noteq> i" "m \<noteq> j" using third_index[OF n3, of i j] by blast
    have "QB (Psi T (W m i a)) (Psi T (W m j b)) = 0"
      by (rule QB_null[OF antisym_W[OF m(1)] antisym_W[OF m(2)] wn0[OF m(1)]])
    then show ?thesis using Qb1[OF m(1) m(2) False] by simp
  qed
qed

end

subsection \<open>(b) Inertia subtraction for \<open>J = diag(I_p, -I_q)\<close>\<close>

definition Jd :: "((real^'p) \<times> (real^'q)) \<Rightarrow> ((real^'p) \<times> (real^'q)) \<Rightarrow> real" where
  "Jd u v = fst u \<bullet> fst v - snd u \<bullet> snd v"

theorem inertia_subtraction:
  fixes L M :: "((real^'p::finite) \<times> (real^'q::finite)) set"
  assumes "subspace L" and "subspace M"
    and Lnn: "\<And>l. l \<in> L \<Longrightarrow> Jd l l \<ge> 0"
    and Mpd: "\<And>m. m \<in> M \<Longrightarrow> m \<noteq> 0 \<Longrightarrow> Jd m m > 0"
    and orth: "\<And>l m. l \<in> L \<Longrightarrow> m \<in> M \<Longrightarrow> Jd l m = 0"
  shows "dim L + dim M \<le> CARD('p)"
proof -
  define V where "V = {l + m | l m. l \<in> L \<and> m \<in> M}"
  have sL: "subspace L" and sM: "subspace M" using assms by simp_all
  have sV: "subspace V" unfolding V_def by (rule subspace_sums[OF sL sM])
  have LM: "L \<inter> M = {0}"
  proof (rule set_eqI)
    fix x
    show "x \<in> L \<inter> M \<longleftrightarrow> x \<in> {0}"
    proof
      assume x: "x \<in> L \<inter> M"
      have "Jd x x = 0" using orth[of x x] x by simp
      moreover have "x \<noteq> 0 \<Longrightarrow> Jd x x > 0" using Mpd[of x] x by simp
      ultimately show "x \<in> {0}" by auto
    next
      assume "x \<in> {0}"
      then show "x \<in> L \<inter> M" using sL sM by (simp add: subspace_0)
    qed
  qed
  have dsum: "dim V + dim (L \<inter> M) = dim L + dim M"
    unfolding V_def by (rule dim_sums_Int[OF sL sM])
  have d0: "dim (L \<inter> M) = 0" unfolding LM by (metis dim_span span_empty dim_empty)
  have Vnn: "\<And>v. v \<in> V \<Longrightarrow> Jd v v \<ge> 0"
  proof -
    fix v assume "v \<in> V"
    then obtain l m where v: "v = l + m" and l: "l \<in> L" and m: "m \<in> M" unfolding V_def by blast
    have lm: "Jd l m = 0" using orth[OF l m] .
    have ml: "Jd m l = 0" using lm unfolding Jd_def by (simp add: inner_commute)
    have "Jd (l + m) (l + m) = Jd l l + Jd l m + Jd m l + Jd m m"
      by (simp add: Jd_def inner_add_left inner_add_right algebra_simps)
    moreover have "Jd l l \<ge> 0" using Lnn[OF l] .
    moreover have "Jd m m \<ge> 0" using Mpd[OF m] by (cases "m = 0") (simp_all add: Jd_def)
    ultimately show "Jd v v \<ge> 0" using lm ml v by simp
  qed
  have inj: "inj_on fst V"
  proof (subst linear_inj_on_iff_eq_0[OF linear_fst sV], intro ballI impI)
    fix v assume vV: "v \<in> V" and f0: "fst v = 0"
    have "0 \<le> Jd v v" using Vnn[OF vV] .
    then have "snd v \<bullet> snd v \<le> 0" using f0 unfolding Jd_def by simp
    then have "snd v = 0" using inner_ge_zero[of "snd v"] by simp
    then show "v = 0" using f0 by (simp add: prod_eq_iff)
  qed
  have "dim V = dim (fst ` V)" proof -
    have sp: "span V = V" using sV by (simp add: span_eq_iff)
    have "inj_on fst (span V)" unfolding sp by (rule inj)
    from dim_image_eq[OF linear_fst this] show ?thesis by (simp add: sp)
  qed
  also have "\<dots> \<le> DIM(real^'p)" by (rule dim_subset_UNIV)
  finally have "dim V \<le> CARD('p)" by simp
  then show ?thesis using dsum d0 by simp
qed

end
