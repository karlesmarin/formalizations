(*  Title:      Segre_Width3.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

theory Segre_Width3
  imports Main
begin

text \<open>
  Scope (Theorem 1 of the note on quadratic persistence of Segre varieties: \<open>qp(P^{m-1} \<times> P^2) = m\<close> for \<open>m \<ge> 2\<close>).

  Covered here:
  \<^item> the upper bound in coordinates: with \<open>b_i = (1, i, i^2)\<close>, a family of \<open>3\<times>3\<close>
    antisymmetric matrices \<open>D i j\<close> (\<open>D j i = - D i j\<close>) with \<open>D i j \<cdot> b_i = 0\<close> for all
    \<open>i \<noteq> j\<close> is zero (theorem \<open>segre_width3_upper\<close>); this is the argument of the note
    ("\<open>D_ij\<close> has \<open>b_i\<close> and \<open>b_j\<close> in its radical; a nonzero alternating form on a
    3-space has a one-dimensional radical");
  \<^item> the key lemma: an antisymmetric \<open>3\<times>3\<close> matrix killing two linearly independent vectors is
    zero (lemma \<open>antisym3_two_kernel_zero\<close>);
  \<^item> the arithmetic of the lower bound: \<open>d - g(m-1) = m - 1\<close> with \<open>d = 3 C(m,2)\<close> and
    \<open>g(s) = s c - C(s,2)\<close>, \<open>c = 2(m-1)\<close> (lemma \<open>segre_width3_count\<close>).

  Not covered (used as text): the identification of the space \<open>\<D>\<close> of quadrics vanishing on
  the Segre variety with \<open>\<Lambda>^2 A^* \<otimes> \<Lambda>^2 B^*\<close>, the translation "the point
  \<open>e_i \<otimes> b_i\<close> lies in the radical of \<open>D\<close> iff \<open>D_ij(b_i,\<cdot>) = 0\<close> for all \<open>j\<close>"
  (for an antisymmetric matrix \<open>D(b,\<cdot>) = 0\<close> iff \<open>D b = 0\<close>), the characterization of
  \<open>qp\<close> by radicals (BSSV Def. 3.1, Lemma 3.3), and BSSV Corollary 3.7 (\<open>d \<le> g(qp)\<close>),
  together with the monotonicity of \<open>g\<close> that turns the count into \<open>qp \<ge> m\<close>.

  Representation: vectors are functions \<open>nat \<Rightarrow> 'a\<close> and matrices \<open>nat \<Rightarrow> nat \<Rightarrow> 'a\<close>,
  read on the indices \<open>0,1,2\<close> only. The field is any \<open>'a::field_char_0\<close> (e.g. \<open>rat\<close>,
  \<open>real\<close>, \<open>complex\<close>); characteristic 0 is used twice: \<open>S i i = -S i i\<close> gives
  \<open>S i i = 0\<close>, and the numbers \<open>of_nat i\<close> are distinct.
\<close>

definition antisym3 :: "(nat \<Rightarrow> nat \<Rightarrow> 'a::field) \<Rightarrow> bool" where
  "antisym3 S \<longleftrightarrow> (\<forall>i<3. \<forall>j<3. S j i = - S i j)"

definition mulv3 :: "(nat \<Rightarrow> nat \<Rightarrow> 'a::field) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "mulv3 S u i = (\<Sum>j<3. S i j * u j)"

definition kills3 :: "(nat \<Rightarrow> nat \<Rightarrow> 'a::field) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool" where
  "kills3 S u \<longleftrightarrow> (\<forall>i<3. mulv3 S u i = 0)"

definition indep2 :: "(nat \<Rightarrow> 'a::field) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool" where
  "indep2 u v \<longleftrightarrow> (\<forall>a b. (\<forall>k<3. a * u k + b * v k = 0) \<longrightarrow> a = 0 \<and> b = 0)"

definition zero3 :: "(nat \<Rightarrow> nat \<Rightarrow> 'a::field) \<Rightarrow> bool" where
  "zero3 S \<longleftrightarrow> (\<forall>i<3. \<forall>j<3. S i j = 0)"

lemma lessThan3: "{..<3::nat} = {0,1,2}" by auto

lemma mulv3_expand: "mulv3 S u i = S i 0 * u 0 + S i 1 * u 1 + S i 2 * u 2"
  by (simp add: mulv3_def lessThan3 algebra_simps)

lemma less3_cases: "k < (3::nat) \<Longrightarrow> k = 0 \<or> k = 1 \<or> k = 2" by auto

lemma zero3_iff:
  "zero3 S \<longleftrightarrow> S 0 0 = 0 \<and> S 0 1 = 0 \<and> S 0 2 = 0 \<and> S 1 0 = 0 \<and> S 1 1 = 0 \<and> S 1 2 = 0
     \<and> S 2 0 = 0 \<and> S 2 1 = 0 \<and> S 2 2 = 0"
proof
  assume "zero3 S"
  then have Z: "\<And>i j. i < 3 \<Longrightarrow> j < 3 \<Longrightarrow> S i j = 0" unfolding zero3_def by blast
  show "S 0 0 = 0 \<and> S 0 1 = 0 \<and> S 0 2 = 0 \<and> S 1 0 = 0 \<and> S 1 1 = 0 \<and> S 1 2 = 0
     \<and> S 2 0 = 0 \<and> S 2 1 = 0 \<and> S 2 2 = 0"
    by (intro conjI; rule Z; simp)
next
  assume H: "S 0 0 = 0 \<and> S 0 1 = 0 \<and> S 0 2 = 0 \<and> S 1 0 = 0 \<and> S 1 1 = 0 \<and> S 1 2 = 0
     \<and> S 2 0 = 0 \<and> S 2 1 = 0 \<and> S 2 2 = 0"
  show "zero3 S" unfolding zero3_def
  proof (intro allI impI)
    fix i j :: nat assume "i < 3" "j < 3"
    then consider "i = 0" | "i = 1" | "i = 2" by (auto dest: less3_cases)
    then show "S i j = 0"
    proof cases
      case 1
      from \<open>j < 3\<close> consider "j = 0" | "j = 1" | "j = 2" by (auto dest: less3_cases)
      then show ?thesis using H 1 by cases simp_all
    next
      case 2
      from \<open>j < 3\<close> consider "j = 0" | "j = 1" | "j = 2" by (auto dest: less3_cases)
      then show ?thesis using H 2 by cases simp_all
    next
      case 3
      from \<open>j < 3\<close> consider "j = 0" | "j = 1" | "j = 2" by (auto dest: less3_cases)
      then show ?thesis using H 3 by cases simp_all
    qed
  qed
qed

lemma diag_zero:
  fixes x :: "'a::field_char_0"
  assumes "x = - x" shows "x = 0"
proof -
  have "x + x = 0" using assms by (metis add.right_inverse)
  then have "2 * x = 0" by (simp only: mult_2)
  then show "x = 0" by simp
qed

lemma neg_add0: "- a + b = 0 \<Longrightarrow> a = (b::'a::ab_group_add)"
proof -
  assume h: "- a + b = 0"
  have "- a = - b" using h by (simp add: eq_neg_iff_add_eq_0)
  then show "a = b" by simp
qed

lemma neg_diff0: "- a - b = 0 \<Longrightarrow> a = - (b::'a::ab_group_add)"
proof -
  assume h: "- a - b = 0"
  have "- (a + b) = 0" using h by (simp only: minus_add_distrib diff_conv_add_uminus)
  then have "a + b = 0" by (simp only: neg_equal_0_iff_equal)
  then show "a = - b" by (simp add: eq_neg_iff_add_eq_0)
qed

lemma add0: "a + b = 0 \<Longrightarrow> a = - (b::'a::ab_group_add)"
  by (simp add: eq_neg_iff_add_eq_0)

text \<open>Lemma 1: a \<open>3\<times>3\<close> antisymmetric matrix with two linearly independent vectors in its
  kernel is zero.\<close>

lemma antisym3_two_kernel_zero:
  fixes S :: "nat \<Rightarrow> nat \<Rightarrow> 'a::field_char_0"
  assumes A: "antisym3 S" and Ku: "kills3 S u" and Kv: "kills3 S v" and I: "indep2 u v"
  shows "zero3 S"
proof -
  define p where "p = S 0 1"
  define q where "q = S 0 2"
  define r where "r = S 1 2"
  have Aij: "\<And>i j. i < 3 \<Longrightarrow> j < 3 \<Longrightarrow> S j i = - S i j"
    using A unfolding antisym3_def by blast
  have d0: "S 0 0 = 0" by (rule diag_zero, rule Aij) simp_all
  have d1: "S 1 1 = 0" by (rule diag_zero, rule Aij) simp_all
  have d2: "S 2 2 = 0" by (rule diag_zero, rule Aij) simp_all
  have s10: "S 1 0 = - p" unfolding p_def by (rule Aij) simp_all
  have s20: "S 2 0 = - q" unfolding q_def by (rule Aij) simp_all
  have s21: "S 2 1 = - r" unfolding r_def by (rule Aij) simp_all
  have eqs: "p * w 1 + q * w 2 = 0" "- (p * w 0) + r * w 2 = 0" "- (q * w 0) - r * w 1 = 0"
    if "kills3 S w" for w
  proof -
    have K: "\<And>i. i < 3 \<Longrightarrow> mulv3 S w i = 0" using that unfolding kills3_def by blast
    have "mulv3 S w 0 = 0" by (rule K) simp
    then have e0: "S 0 0 * w 0 + S 0 1 * w 1 + S 0 2 * w 2 = 0" by (simp only: mulv3_expand)
    have "mulv3 S w 1 = 0" by (rule K) simp
    then have e1: "S 1 0 * w 0 + S 1 1 * w 1 + S 1 2 * w 2 = 0" by (simp only: mulv3_expand)
    have "mulv3 S w 2 = 0" by (rule K) simp
    then have e2: "S 2 0 * w 0 + S 2 1 * w 1 + S 2 2 * w 2 = 0" by (simp only: mulv3_expand)
    have f0: "0 * w 0 + p * w 1 + q * w 2 = 0"
      using e0 unfolding d0 p_def[symmetric] q_def[symmetric] .
    have f1: "(- p) * w 0 + 0 * w 1 + r * w 2 = 0"
      using e1 unfolding s10 d1 r_def[symmetric] .
    have f2: "(- q) * w 0 + (- r) * w 1 + 0 * w 2 = 0"
      using e2 unfolding s20 s21 d2 .
    show "p * w 1 + q * w 2 = 0" using f0 by simp
    show "- (p * w 0) + r * w 2 = 0" using f1 by simp
    show "- (q * w 0) - r * w 1 = 0" using f2 by (simp add: algebra_simps)
  qed
  note u' = eqs[OF Ku] and v' = eqs[OF Kv]
  have u: "p * u 1 = - (q * u 2)" "p * u 0 = r * u 2" "q * u 0 = - (r * u 1)"
    using add0[OF u'(1)] neg_add0[OF u'(2)] neg_diff0[OF u'(3)] by simp_all
  have v: "p * v 1 = - (q * v 2)" "p * v 0 = r * v 2" "q * v 0 = - (r * v 1)"
    using add0[OF v'(1)] neg_add0[OF v'(2)] neg_diff0[OF v'(3)] by simp_all
  have u0: "\<not> (\<forall>k<3. u k = 0)"
  proof
    assume z: "\<forall>k<3. u k = 0"
    have "\<forall>k<3. (1::'a) * u k + 0 * v k = 0" using z by simp
    then have "(1::'a) = 0 \<and> (0::'a) = 0"
      using I unfolding indep2_def by blast
    then show False by simp
  qed
  have p0: "p = 0"
  proof (rule ccontr)
    assume hp: "p \<noteq> 0"
    have c0: "p * (v 2 * u 0 + (- u 2) * v 0) = 0"
    proof -
      have "p * (v 2 * u 0 + (- u 2) * v 0) = v 2 * (p * u 0) - u 2 * (p * v 0)"
        by (simp add: algebra_simps)
      also have "\<dots> = v 2 * (r * u 2) - u 2 * (r * v 2)" by (simp only: u(2) v(2))
      finally show ?thesis by (simp add: algebra_simps)
    qed
    have c1: "p * (v 2 * u 1 + (- u 2) * v 1) = 0"
    proof -
      have "p * (v 2 * u 1 + (- u 2) * v 1) = v 2 * (p * u 1) - u 2 * (p * v 1)"
        by (simp add: algebra_simps)
      also have "\<dots> = v 2 * (- (q * u 2)) - u 2 * (- (q * v 2))" by (simp only: u(1) v(1))
      finally show ?thesis by (simp add: algebra_simps)
    qed
    have "\<forall>k<3. v 2 * u k + (- u 2) * v k = 0"
    proof (intro allI impI)
      fix k :: nat assume "k < 3"
      then consider "k = 0" | "k = 1" | "k = 2" by (auto dest: less3_cases)
      then show "v 2 * u k + (- u 2) * v k = 0"
      proof cases
        case 1 then show ?thesis using c0 hp by simp
      next
        case 2 then show ?thesis using c1 hp by simp
      next
        case 3 then show ?thesis by (simp add: algebra_simps)
      qed
    qed
    then have "v 2 = 0 \<and> - u 2 = 0" using I unfolding indep2_def by blast
    then have z2: "u 2 = 0" by simp
    have "p * u 0 = 0" "p * u 1 = 0" using u(1) u(2) z2 by simp_all
    then have "u 0 = 0" "u 1 = 0" using hp by simp_all
    with z2 u0 show False by (auto dest: less3_cases)
  qed
  have q0: "q = 0"
  proof (rule ccontr)
    assume hq: "q \<noteq> 0"
    have "q * u 2 = 0" "q * v 2 = 0" using u(1) v(1) p0 by simp_all
    then have uz2: "u 2 = 0" and vz2: "v 2 = 0" using hq by simp_all
    have c0: "q * (v 1 * u 0 + (- u 1) * v 0) = 0"
    proof -
      have "q * (v 1 * u 0 + (- u 1) * v 0) = v 1 * (q * u 0) - u 1 * (q * v 0)"
        by (simp add: algebra_simps)
      also have "\<dots> = v 1 * (- (r * u 1)) - u 1 * (- (r * v 1))" by (simp only: u(3) v(3))
      finally show ?thesis by (simp add: algebra_simps)
    qed
    have "\<forall>k<3. v 1 * u k + (- u 1) * v k = 0"
    proof (intro allI impI)
      fix k :: nat assume "k < 3"
      then consider "k = 0" | "k = 1" | "k = 2" by (auto dest: less3_cases)
      then show "v 1 * u k + (- u 1) * v k = 0"
      proof cases
        case 1 then show ?thesis using c0 hq by simp
      next
        case 2 then show ?thesis by (simp add: algebra_simps)
      next
        case 3 then show ?thesis using uz2 vz2 by simp
      qed
    qed
    then have "v 1 = 0 \<and> - u 1 = 0" using I unfolding indep2_def by blast
    then have z1: "u 1 = 0" by simp
    have "q * u 0 = 0" using u(3) z1 by simp
    then have "u 0 = 0" using hq by simp
    with z1 uz2 u0 show False by (auto dest: less3_cases)
  qed
  have r0: "r = 0"
  proof (rule ccontr)
    assume hr: "r \<noteq> 0"
    have "r * u 2 = 0" "r * v 2 = 0" "r * u 1 = 0" "r * v 1 = 0"
      using u(2) v(2) u(3) v(3) p0 q0 by simp_all
    then have uz2: "u 2 = 0" and vz2: "v 2 = 0" and uz1: "u 1 = 0" and vz1: "v 1 = 0"
      using hr by simp_all
    have "\<forall>k<3. v 0 * u k + (- u 0) * v k = 0"
    proof (intro allI impI)
      fix k :: nat assume "k < 3"
      then consider "k = 0" | "k = 1" | "k = 2" by (auto dest: less3_cases)
      then show "v 0 * u k + (- u 0) * v k = 0"
      proof cases
        case 1 then show ?thesis by (simp add: algebra_simps)
      next
        case 2 then show ?thesis using uz1 vz1 by simp
      next
        case 3 then show ?thesis using uz2 vz2 by simp
      qed
    qed
    then have "v 0 = 0 \<and> - u 0 = 0" using I unfolding indep2_def by blast
    then have "u 0 = 0" by simp
    with uz1 uz2 u0 show False by (auto dest: less3_cases)
  qed
  have s01: "S 0 1 = 0" and s02: "S 0 2 = 0" and s12: "S 1 2 = 0"
    using p0 q0 r0 unfolding p_def q_def r_def by simp_all
  have s10': "S 1 0 = 0" and s20': "S 2 0 = 0" and s21': "S 2 1 = 0"
    using s10 s20 s21 p0 q0 r0 by simp_all
  show ?thesis
    unfolding zero3_iff using d0 d1 d2 s01 s02 s12 s10' s20' s21' by blast
qed

text \<open>The vectors \<open>b_i = (1, i, i^2)\<close>; two of them with distinct indices are independent.\<close>

definition bvec :: "nat \<Rightarrow> nat \<Rightarrow> 'a::field_char_0" where
  "bvec i k = (if k = 0 then 1 else if k = 1 then of_nat i else if k = 2 then (of_nat i)^2 else 0)"

lemma bvec_indep:
  assumes "i \<noteq> j" shows "indep2 (bvec i :: nat \<Rightarrow> 'a::field_char_0) (bvec j)"
  unfolding indep2_def
proof (intro allI impI)
  fix a b :: 'a
  assume h: "\<forall>k<3. a * bvec i k + b * bvec j k = 0"
  have e0: "a + b = 0" using h[rule_format, of 0] by (simp add: bvec_def)
  have e1: "a * of_nat i + b * of_nat j = 0" using h[rule_format, of 1] by (simp add: bvec_def)
  have bb: "b = - a" using e0 by (simp add: eq_neg_iff_add_eq_0 add.commute)
  have "a * (of_nat i - of_nat j) = 0" using e1 bb by (simp add: algebra_simps)
  moreover have "(of_nat i :: 'a) - of_nat j \<noteq> 0" using assms by simp
  ultimately have "a = 0" by simp
  with bb show "a = 0 \<and> b = 0" by simp
qed

text \<open>Theorem (upper bound \<open>qp(P^{m-1} \<times> P^2) \<le> m\<close>, in coordinates). The hypothesis
  \<open>kills3 (D i j) (bvec i)\<close> for all \<open>j \<noteq> i\<close> is the condition that the point
  \<open>e_i \<otimes> b_i\<close> lies in the radical of \<open>D\<close>. No hypothesis \<open>m \<ge> 2\<close> is needed.\<close>

theorem segre_width3_upper:
  fixes D :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a::field_char_0"
  assumes anti: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> i \<noteq> j \<Longrightarrow> antisym3 (D i j)"
    and swap: "\<And>i j k l. i < m \<Longrightarrow> j < m \<Longrightarrow> i \<noteq> j \<Longrightarrow> D j i k l = - D i j k l"
    and rad: "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> i \<noteq> j \<Longrightarrow> kills3 (D i j) (bvec i)"
    and ij: "i < m" "j < m" "i \<noteq> j"
  shows "zero3 (D i j)"
proof (rule antisym3_two_kernel_zero[where u = "bvec i" and v = "bvec j"])
  show "antisym3 (D i j)" using anti ij by blast
  show "kills3 (D i j) (bvec i)" using rad ij by blast
  show "indep2 (bvec i :: nat \<Rightarrow> 'a) (bvec j)" using bvec_indep ij(3) by blast
  have kj: "kills3 (D j i) (bvec j)" using rad ij by auto
  show "kills3 (D i j) (bvec j)"
    unfolding kills3_def
  proof (intro allI impI)
    fix k :: nat assume k: "k < 3"
    have "mulv3 (D j i) (bvec j) k = 0" using kj k unfolding kills3_def by blast
    moreover have "mulv3 (D j i) (bvec j) k = - mulv3 (D i j) (bvec j) k"
      using swap[OF ij(1) ij(2) ij(3)] by (simp add: mulv3_def sum_negf[symmetric])
    ultimately show "mulv3 (D i j) (bvec j) k = 0" by simp
  qed
qed

text \<open>The count of the lower bound: \<open>d - g(m-1) = m - 1\<close>, with \<open>d = 3 C(m,2)\<close>,
  \<open>c = (m-1)(3-1)\<close> and \<open>g(s) = s c - C(s,2)\<close>, in \<open>nat\<close> (truncated subtraction; both
  subtractions are exact here, see \<open>segre_width3_count_aux\<close>).\<close>

lemma two_choose2: "2 * (n choose 2) = n * (n - 1)"
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc n)
  have "Suc n choose 2 = (n choose 1) + (n choose 2)"
    by (simp add: numeral_2_eq_2)
  then have "2 * (Suc n choose 2) = 2 * n + 2 * (n choose 2)" by simp
  also have "\<dots> = 2 * n + n * (n - 1)" using Suc.IH by simp
  also have "\<dots> = Suc n * (Suc n - 1)" by (cases n) (simp_all add: algebra_simps)
  finally show ?case .
qed

lemma segre_width3_count_aux:
  assumes "2 \<le> m"
  shows "((m - 1) choose 2) \<le> (m - 1) * (2 * (m - 1))"
    and "3 * (m choose 2) + ((m - 1) choose 2) = (m - 1) * (2 * (m - 1)) + (m - 1)"
proof -
  obtain n where m: "m = n + 2" using assms by (metis add.commute le_iff_add)
  define X where "X = m choose 2"
  define Y where "Y = (m - 1) choose 2"
  define Z where "Z = (n + 1) * (2 * (n + 1))"
  have mm: "m - 1 = n + 1" using m by simp
  have X0: "X = (n + 2) choose 2" by (simp only: X_def m)
  have Y0: "Y = (n + 1) choose 2" by (simp only: Y_def mm)
  have X: "2 * X = (n + 2) * (n + 1)" using two_choose2[where n = "n + 2"] unfolding X0 by simp
  have Y: "2 * Y = (n + 1) * n" using two_choose2[where n = "n + 1"] unfolding Y0 by simp
  have "n \<le> 4 * (n + 1)" by simp
  then have "(n + 1) * n \<le> (n + 1) * (4 * (n + 1))" by (rule mult_le_mono2)
  also have "\<dots> = 2 * Z" by (simp add: Z_def algebra_simps)
  finally have "2 * Y \<le> 2 * Z" using Y by simp
  then have YZ: "Y \<le> Z" by simp
  have "2 * (3 * X + Y) = 3 * (2 * X) + 2 * Y" by simp
  also have "\<dots> = 3 * ((n + 2) * (n + 1)) + (n + 1) * n" using X Y by simp
  also have "\<dots> = 2 * (Z + (n + 1))" by (simp add: Z_def algebra_simps)
  finally have key: "3 * X + Y = Z + (n + 1)" by simp
  show "((m - 1) choose 2) \<le> (m - 1) * (2 * (m - 1))"
    using YZ unfolding Y_def Z_def mm .
  show "3 * (m choose 2) + ((m - 1) choose 2) = (m - 1) * (2 * (m - 1)) + (m - 1)"
    using key unfolding X_def Y_def Z_def mm .
qed

text \<open>Corollary (the count): \<open>d - g(m-1) = m - 1\<close> for \<open>m \<ge> 2\<close>, in \<open>nat\<close>.\<close>

lemma segre_width3_count:
  assumes "2 \<le> m"
  shows "3 * (m choose 2) - ((m - 1) * (2 * (m - 1)) - ((m - 1) choose 2)) = m - 1"
proof -
  have lin: "c \<le> z \<Longrightarrow> x + c = z + k \<Longrightarrow> x - (z - c) = (k::nat)" for x c z k by arith
  show ?thesis by (rule lin[OF segre_width3_count_aux(1)[OF assms] segre_width3_count_aux(2)[OF assms]])
qed

text \<open>The same identity in \<open>int\<close>, where subtraction is exact.\<close>

lemma segre_width3_count_int:
  assumes "2 \<le> m"
  shows "3 * int (m choose 2) - (int (m - 1) * (2 * int (m - 1)) - int ((m - 1) choose 2)) = int m - 1"
proof -
  define X where "X = m choose 2"
  define Y where "Y = (m - 1) choose 2"
  define W where "W = int (m - 1) * (2 * int (m - 1))"
  have h: "3 * X + Y = (m - 1) * (2 * (m - 1)) + (m - 1)"
    using segre_width3_count_aux(2)[OF assms] unfolding X_def Y_def .
  have "int (3 * X + Y) = int ((m - 1) * (2 * (m - 1)) + (m - 1))" using h by (rule arg_cong)
  then have h': "3 * int X + int Y = W + int (m - 1)" unfolding W_def by simp
  have m1: "int (m - 1) = int m - 1" using assms by simp
  have "3 * int X - (W - int Y) = int m - 1" using h' m1 by linarith
  then show ?thesis unfolding X_def Y_def W_def .
qed

end
