(*  Title:      Caballero_Twonum.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Marín, paper II on Rodríguez Caballero's parenthesis problem (in preparation): Proposition twonum (i), (ii)
   (two numerations of one progression) and Proposition Os (a = 3), on top of Caballero_Setting (Lemma P).

   The two points are P_1(k) = ((k+1/2)/(a+1), 1/(a+1)) and P_2(k) = (k+1/2, b+1).  Their position multisets
   {i theta + j} are the radix numerations {i + (a+1) j}/(a+1) and {i (b+1) + j} of {0, ..., K-1}, K = (a+1)(b+1);
   with Lemma P both give Z = {min(K, N+k+1) : 0 <= N <= K-1}.
*)
theory Caballero_Twonum
  imports Caballero_Setting
begin

section \<open>The two radix numerations of 0..K-1\<close>

lemma radix_inj:
  fixes m :: int
  assumes "0 < m" "0 \<le> i" "i < m" "0 \<le> i'" "i' < m" "i + m * j = i' + m * j'"
  shows "i = i' \<and> j = j'"
proof -
  have "(i + m * j) mod m = i mod m" by simp
  moreover have "(i' + m * j') mod m = i' mod m" by simp
  ultimately have "i mod m = i' mod m" using assms(6) by simp
  then have ii: "i = i'" using assms by simp
  then have "m * j = m * j'" using assms(6) by simp
  then have "j = j'" using assms(1) by simp
  with ii show ?thesis by simp
qed

lemma radix_image:
  fixes m n :: int
  assumes "0 < m" "0 < n"
  shows "(\<lambda>p::int \<times> int. fst p + m * snd p) ` ({0..m - 1} \<times> {0..n - 1}) = {0..m * n - 1}"
proof (rule set_eqI)
  fix N :: int
  show "N \<in> (\<lambda>p::int \<times> int. fst p + m * snd p) ` ({0..m - 1} \<times> {0..n - 1}) \<longleftrightarrow> N \<in> {0..m * n - 1}"
  proof
    assume "N \<in> (\<lambda>p::int \<times> int. fst p + m * snd p) ` ({0..m - 1} \<times> {0..n - 1})"
    then obtain i j where ij: "N = i + m * j" "0 \<le> i" "i \<le> m - 1" "0 \<le> j" "j \<le> n - 1" by auto
    have "m * j \<le> m * (n - 1)" using ij(5) assms(1) by (intro mult_left_mono) auto
    then show "N \<in> {0..m * n - 1}" using ij by (auto simp: algebra_simps)
  next
    assume N: "N \<in> {0..m * n - 1}"
    have r: "N mod m + m * (N div m) = N" by simp
    have "0 \<le> N mod m" "N mod m \<le> m - 1" using assms(1) by simp_all
    moreover have "0 \<le> N div m" using N assms(1) by (simp add: pos_imp_zdiv_nonneg_iff)
    moreover have "N div m \<le> n - 1"
    proof -
      have "N < m * n" using N by simp
      have "m * (N div m) + N mod m = N" by simp
      moreover have "0 \<le> N mod m" using assms(1) by simp
      ultimately have "m * (N div m) < m * n" using \<open>N < m * n\<close> by linarith
      then have "N div m < n" using assms(1) by (simp only: mult_less_cancel_left_pos)
      then show ?thesis by simp
    qed
    ultimately show "N \<in> (\<lambda>p::int \<times> int. fst p + m * snd p) ` ({0..m - 1} \<times> {0..n - 1})"
      by (intro image_eqI[where x = "(N mod m, N div m)"]) (use r in auto)
  qed
qed

lemma radix_inj_on:
  fixes m :: int
  assumes "0 < m"
  shows "inj_on (\<lambda>p::int \<times> int. fst p + m * snd p) ({0..m - 1} \<times> {0..n - 1})"
proof (rule inj_onI)
  fix p p' :: "int \<times> int"
  assume "p \<in> {0..m - 1} \<times> {0..n - 1}" "p' \<in> {0..m - 1} \<times> {0..n - 1}" "fst p + m * snd p = fst p' + m * snd p'"
  then show "p = p'" using radix_inj[OF assms, of "fst p" "fst p'" "snd p" "snd p'"] by (cases p; cases p') auto
qed

text \<open>Numeration 1: theta = 1/(a+1), N = i + (a+1) j.\<close>
lemma Pms_radix1:
  assumes "0 \<le> a" "0 \<le> b"
  shows "Pms a b (1 / real_of_int (a + 1))
         = image_mset (\<lambda>N. real_of_int N * (1 / real_of_int (a + 1))) (mset_set {0..(a + 1) * (b + 1) - 1})"
proof -
  have "0 < a + 1" "0 < b + 1" using assms by simp_all
  have ne: "real_of_int a + 1 \<noteq> 0" using assms by linarith
  let ?phi = "\<lambda>p::int \<times> int. fst p + (a + 1) * snd p"
  have inj: "inj_on ?phi ({0..a + 1 - 1} \<times> {0..b + 1 - 1})" by (rule radix_inj_on) fact
  have img: "?phi ` ({0..a + 1 - 1} \<times> {0..b + 1 - 1}) = {0..(a + 1) * (b + 1) - 1}"
    by (rule radix_image) fact+
  have "image_mset ?phi (mset_set ({0..a + 1 - 1} \<times> {0..b + 1 - 1})) = mset_set {0..(a + 1) * (b + 1) - 1}"
    using image_mset_mset_set[OF inj] img by simp
  moreover have "{0..a + 1 - 1} = {0..a}" "{0..b + 1 - 1} = {0..b}" by simp_all
  ultimately have e: "image_mset ?phi (mset_set ({0..a} \<times> {0..b})) = mset_set {0..(a + 1) * (b + 1) - 1}" by simp
  have "Pms a b (1 / real_of_int (a + 1))
      = image_mset (\<lambda>N. real_of_int N * (1 / real_of_int (a + 1))) (image_mset ?phi (mset_set ({0..a} \<times> {0..b})))"
    unfolding Pms_def image_mset.compositionality o_def
    by (rule image_mset_cong) (use ne in \<open>auto simp: field_simps\<close>)
  then show ?thesis using e by simp
qed

text \<open>Numeration 2: theta = b+1, N = (b+1) i + j.\<close>
lemma Pms_radix2:
  assumes "0 \<le> a" "0 \<le> b"
  shows "Pms a b (real_of_int (b + 1))
         = image_mset (\<lambda>N. real_of_int N * 1) (mset_set {0..(a + 1) * (b + 1) - 1})"
proof -
  have "0 < a + 1" "0 < b + 1" using assms by simp_all
  let ?phi = "\<lambda>p::int \<times> int. snd p + (b + 1) * fst p"
  have inj: "inj_on ?phi ({0..a + 1 - 1} \<times> {0..b + 1 - 1})"
  proof (rule inj_onI)
    fix p p' :: "int \<times> int"
    assume "p \<in> {0..a + 1 - 1} \<times> {0..b + 1 - 1}" "p' \<in> {0..a + 1 - 1} \<times> {0..b + 1 - 1}"
      "?phi p = ?phi p'"
    then show "p = p'"
      using radix_inj[OF \<open>0 < b + 1\<close>, of "snd p" "snd p'" "fst p" "fst p'"] by (cases p; cases p') auto
  qed
  have img: "?phi ` ({0..a + 1 - 1} \<times> {0..b + 1 - 1}) = {0..(b + 1) * (a + 1) - 1}"
  proof -
    have "(\<lambda>p::int \<times> int. fst p + (b + 1) * snd p) ` ({0..b + 1 - 1} \<times> {0..a + 1 - 1}) = {0..(b + 1) * (a + 1) - 1}"
      by (rule radix_image) fact+
    moreover have "?phi ` ({0..a + 1 - 1} \<times> {0..b + 1 - 1})
        = (\<lambda>p::int \<times> int. fst p + (b + 1) * snd p) ` prod.swap ` ({0..a + 1 - 1} \<times> {0..b + 1 - 1})"
      by (simp add: image_image)
    moreover have "prod.swap ` ({0..a + 1 - 1} \<times> {0..b + 1 - 1}) = {0..b + 1 - 1} \<times> {0..a + 1 - 1}"
    proof (rule set_eqI)
      fix q :: "int \<times> int"
      show "q \<in> prod.swap ` ({0..a + 1 - 1} \<times> {0..b + 1 - 1}) \<longleftrightarrow> q \<in> {0..b + 1 - 1} \<times> {0..a + 1 - 1}"
        by (cases q) (auto simp: image_iff intro: bexI[where x = "(snd q, fst q)"])
    qed
    ultimately show ?thesis by simp
  qed
  have "image_mset ?phi (mset_set ({0..a + 1 - 1} \<times> {0..b + 1 - 1})) = mset_set {0..(b + 1) * (a + 1) - 1}"
    using image_mset_mset_set[OF inj] img by simp
  moreover have "{0..a + 1 - 1} = {0..a}" "{0..b + 1 - 1} = {0..b}" by simp_all
  moreover have "(b + 1) * (a + 1) = (a + 1) * (b + 1)" by simp
  ultimately have e: "image_mset ?phi (mset_set ({0..a} \<times> {0..b})) = mset_set {0..(a + 1) * (b + 1) - 1}" by simp
  have "Pms a b (real_of_int (b + 1))
      = image_mset (\<lambda>N. real_of_int N * 1) (image_mset ?phi (mset_set ({0..a} \<times> {0..b})))"
    unfolding Pms_def image_mset.compositionality o_def
    by (rule image_mset_cong) (auto simp: algebra_simps)
  then show ?thesis using e by simp
qed

section \<open>Z of a point whose positions are a radix numeration\<close>

lemma count_le:
  fixes K N0 k :: int
  assumes "0 \<le> N0" "0 \<le> k" "1 \<le> K"
  shows "int (card {N' \<in> {0..K - 1}. N' \<le> N0 + k}) = min K (N0 + k + 1)"
proof -
  have "{N' \<in> {0..K - 1}. N' \<le> N0 + k} = {0..min (K - 1) (N0 + k)}" by auto
  then show ?thesis using assms by simp
qed

text \<open>If the positions are {N u : 0 <= N <= K-1} (u > 0) and Lambda = (k + 1/2) u, then
  Z = {min(K, N + k + 1) : 0 <= N <= K-1}.\<close>
lemma Zms_radix:
  fixes u Lam th :: real
  assumes pos: "0 < u" and k: "0 \<le> k" and K: "1 \<le> K"
    and P: "Pms a b th = image_mset (\<lambda>N. real_of_int N * u) (mset_set {0..K - 1})"
    and Lam: "Lam = (real_of_int k + 1 / 2) * u"
    and noint: "\<And>h. -a \<le> h \<Longrightarrow> h \<le> a \<Longrightarrow> Lam + real_of_int h * th \<notin> \<int>"
  shows "Zms a b (cpt b Lam th) = image_mset (\<lambda>N. min K (N + k + 1)) (mset_set {0..K - 1})"
proof -
  have "Zms a b (cpt b Lam th)
      = image_mset (\<lambda>p0. int (size (filter_mset (\<lambda>p. p < p0 + Lam) (Pms a b th)))) (Pms a b th)"
    by (rule lem_P[OF noint])
  also have "\<dots> = image_mset (\<lambda>N0. int (card {N' \<in> {0..K - 1}. real_of_int N' * u < real_of_int N0 * u + Lam}))
                       (mset_set {0..K - 1})"
    by (simp add: P image_mset.compositionality o_def filter_mset_image_mset filter_mset_mset_set)
  also have "\<dots> = image_mset (\<lambda>N. min K (N + k + 1)) (mset_set {0..K - 1})"
  proof (rule image_mset_cong)
    fix N0 assume N0: "N0 \<in># mset_set {0..K - 1}"
    then have N0': "0 \<le> N0" by simp
    have "\<And>N'. real_of_int N' * u < real_of_int N0 * u + Lam \<longleftrightarrow> N' \<le> N0 + k"
    proof -
      fix N' :: int
      have eq: "real_of_int N0 * u + Lam = (real_of_int N0 + (real_of_int k + 1 / 2)) * u"
        unfolding Lam by (simp add: algebra_simps)
      have "real_of_int N' * u < real_of_int N0 * u + Lam \<longleftrightarrow> real_of_int N' < real_of_int N0 + (real_of_int k + 1 / 2)"
        by (simp only: eq mult_less_cancel_right_pos[OF pos])
      also have "\<dots> \<longleftrightarrow> N' \<le> N0 + k" by linarith
      finally show "real_of_int N' * u < real_of_int N0 * u + Lam \<longleftrightarrow> N' \<le> N0 + k" .
    qed
    then have "{N' \<in> {0..K - 1}. real_of_int N' * u < real_of_int N0 * u + Lam} = {N' \<in> {0..K - 1}. N' \<le> N0 + k}"
      by simp
    then show "int (card {N' \<in> {0..K - 1}. real_of_int N' * u < real_of_int N0 * u + Lam}) = min K (N0 + k + 1)"
      using count_le[OF N0' k K] by simp
  qed
  finally show ?thesis .
qed


section \<open>Proposition twonum (i) and (ii)\<close>

text \<open>P_1(k) = (Lambda_1, theta_1) = ((k+1/2)/(a+1), 1/(a+1)) and P_2(k) = (Lambda_2, theta_2) = (k+1/2, b+1).\<close>
definition L1 :: "int \<Rightarrow> int \<Rightarrow> real" where "L1 a k = (real_of_int k + 1 / 2) * (1 / real_of_int (a + 1))"
definition T1 :: "int \<Rightarrow> real" where "T1 a = 1 / real_of_int (a + 1)"
definition L2 :: "int \<Rightarrow> real" where "L2 k = real_of_int k + 1 / 2"
definition T2 :: "int \<Rightarrow> real" where "T2 b = real_of_int (b + 1)"

lemma aux_frac:
  fixes x y u :: real
  assumes "u \<noteq> 0"
  shows "(x + 1 / 2) * (1 / u) + y * (1 / u) = (2 * (x + y) + 1) / (2 * u)"
  using assms by (simp add: field_simps)

lemma L1_eq:
  assumes "0 \<le> a"
  shows "L1 a k + real_of_int h * T1 a = real_of_int (2 * (k + h) + 1) / real_of_int (2 * (a + 1))"
proof -
  have d: "real_of_int a + 1 \<noteq> 0" using assms by linarith
  show ?thesis unfolding L1_def T1_def using aux_frac[OF d, of "real_of_int k" "real_of_int h"] by simp
qed

lemma nonint1:
  assumes "0 \<le> a"
  shows "L1 a k + real_of_int h * T1 a \<notin> \<int>"
proof
  assume "L1 a k + real_of_int h * T1 a \<in> \<int>"
  then obtain n where n: "L1 a k + real_of_int h * T1 a = real_of_int n" unfolding Ints_def by auto
  have pos: "0 < real_of_int (2 * (a + 1))" using assms by simp
  have ne: "real_of_int (2 * (a + 1)) \<noteq> 0" using pos by simp
  from n have "real_of_int (2 * (k + h) + 1) / real_of_int (2 * (a + 1)) = real_of_int n"
    using L1_eq[OF assms] by simp
  then have "real_of_int (2 * (k + h) + 1) = real_of_int n * real_of_int (2 * (a + 1))"
    by (simp only: nonzero_divide_eq_eq[OF ne])
  then have "real_of_int (2 * (k + h) + 1) = real_of_int (n * (2 * (a + 1)))" by simp
  then have "2 * (k + h) + 1 = n * (2 * (a + 1))" by (simp only: of_int_eq_iff)
  then obtain m where "2 * (k + h) + 1 = 2 * m" by (metis mult.commute mult.left_commute)
  then show False by presburger
qed

lemma nonint2:
  shows "L2 k + real_of_int h * T2 b \<notin> \<int>"
proof
  assume "L2 k + real_of_int h * T2 b \<in> \<int>"
  then obtain n where n: "L2 k + real_of_int h * T2 b = real_of_int n" unfolding Ints_def by auto
  then have "real_of_int (2 * k + 1 + 2 * (h * (b + 1))) = real_of_int (2 * n)" unfolding L2_def T2_def by simp
  then have "2 * k + 1 + 2 * (h * (b + 1)) = 2 * n" by (simp only: of_int_eq_iff)
  then show False by presburger
qed

lemma twonum_Z1:
  assumes "0 \<le> a" "0 \<le> b" "0 \<le> k"
  shows "Zms a b (cpt b (L1 a k) (T1 a))
         = image_mset (\<lambda>N. min ((a + 1) * (b + 1)) (N + k + 1)) (mset_set {0..(a + 1) * (b + 1) - 1})"
proof (rule Zms_radix[where u = "1 / real_of_int (a + 1)"])
  show "0 < 1 / real_of_int (a + 1)" using assms by simp
  show "0 \<le> k" by fact
  show "1 \<le> (a + 1) * (b + 1)"
  proof -
    have "0 \<le> a * b" using assms by (intro mult_nonneg_nonneg) auto
    moreover have "(a + 1) * (b + 1) = a * b + a + b + 1" by (simp add: algebra_simps)
    ultimately show ?thesis using assms by linarith
  qed
  show "Pms a b (T1 a) = image_mset (\<lambda>N. real_of_int N * (1 / real_of_int (a + 1))) (mset_set {0..(a + 1) * (b + 1) - 1})"
    unfolding T1_def by (rule Pms_radix1[OF assms(1,2)])
  show "L1 a k = (real_of_int k + 1 / 2) * (1 / real_of_int (a + 1))" unfolding L1_def by simp
  show "\<And>h. -a \<le> h \<Longrightarrow> h \<le> a \<Longrightarrow> L1 a k + real_of_int h * T1 a \<notin> \<int>" using nonint1[OF assms(1)] by simp
qed

lemma twonum_Z2:
  assumes "0 \<le> a" "0 \<le> b" "0 \<le> k"
  shows "Zms a b (cpt b (L2 k) (T2 b))
         = image_mset (\<lambda>N. min ((a + 1) * (b + 1)) (N + k + 1)) (mset_set {0..(a + 1) * (b + 1) - 1})"
proof (rule Zms_radix[where u = 1])
  show "0 < (1::real)" by simp
  show "0 \<le> k" by fact
  show "1 \<le> (a + 1) * (b + 1)"
  proof -
    have "0 \<le> a * b" using assms by (intro mult_nonneg_nonneg) auto
    moreover have "(a + 1) * (b + 1) = a * b + a + b + 1" by (simp add: algebra_simps)
    ultimately show ?thesis using assms by linarith
  qed
  show "Pms a b (T2 b) = image_mset (\<lambda>N. real_of_int N * 1) (mset_set {0..(a + 1) * (b + 1) - 1})"
    unfolding T2_def by (rule Pms_radix2[OF assms(1,2)])
  show "L2 k = (real_of_int k + 1 / 2) * 1" unfolding L2_def by simp
  show "\<And>h. -a \<le> h \<Longrightarrow> h \<le> a \<Longrightarrow> L2 k + real_of_int h * T2 b \<notin> \<int>" using nonint2 by simp
qed

text \<open>Proposition twonum (i) (paper, lines 1253-1258): both points are in the open quadrant, off the lines
  Lambda + h theta in Z (|h| <= a), and Z(P_1(k)) = Z(P_2(k)) = {min(K, N+k+1) : 0 <= N <= K-1}.\<close>
theorem prop_twonum_i:
  assumes "2 \<le> a" "1 \<le> b" "0 \<le> k" "k \<le> (a + 1) * (b + 1) - 2"
  shows "0 < L1 a k \<and> 0 < T1 a \<and> 0 < L2 k \<and> 0 < T2 b"
    and "\<And>h. -a \<le> h \<Longrightarrow> h \<le> a \<Longrightarrow> L1 a k + real_of_int h * T1 a \<notin> \<int>"
    and "\<And>h. -a \<le> h \<Longrightarrow> h \<le> a \<Longrightarrow> L2 k + real_of_int h * T2 b \<notin> \<int>"
    and "Zms a b (cpt b (L1 a k) (T1 a)) = image_mset (\<lambda>N. min ((a + 1) * (b + 1)) (N + k + 1)) (mset_set {0..(a + 1) * (b + 1) - 1})"
    and "Zms a b (cpt b (L2 k) (T2 b)) = image_mset (\<lambda>N. min ((a + 1) * (b + 1)) (N + k + 1)) (mset_set {0..(a + 1) * (b + 1) - 1})"
proof -
  have a0: "0 \<le> a" and b0: "0 \<le> b" using assms by simp_all
  show "0 < L1 a k \<and> 0 < T1 a \<and> 0 < L2 k \<and> 0 < T2 b"
    using assms unfolding L1_def T1_def L2_def T2_def by (auto intro: mult_pos_pos)
  show "\<And>h. -a \<le> h \<Longrightarrow> h \<le> a \<Longrightarrow> L1 a k + real_of_int h * T1 a \<notin> \<int>" using nonint1[OF a0] by simp
  show "\<And>h. -a \<le> h \<Longrightarrow> h \<le> a \<Longrightarrow> L2 k + real_of_int h * T2 b \<notin> \<int>" using nonint2 by simp
  show "Zms a b (cpt b (L1 a k) (T1 a)) = image_mset (\<lambda>N. min ((a + 1) * (b + 1)) (N + k + 1)) (mset_set {0..(a + 1) * (b + 1) - 1})"
    by (rule twonum_Z1[OF a0 b0 assms(3)])
  show "Zms a b (cpt b (L2 k) (T2 b)) = image_mset (\<lambda>N. min ((a + 1) * (b + 1)) (N + k + 1)) (mset_set {0..(a + 1) * (b + 1) - 1})"
    by (rule twonum_Z2[OF a0 b0 assms(3)])
qed

text \<open>(ii): the two points are separated by a line of the arrangement: with x_1 = Lambda_1 - a theta_1 and
  x_2 = Lambda_2 - a theta_2 (the values of Lambda + h theta at h = -a) there is an integer rho in [-b, b] with
  x_2 < rho < x_1, so the line Lambda - a theta = rho separates P_1(k) from P_2(k) and they lie in distinct cells.
  As a consequence the coordinate c_{-a} of their vectors differs.  Together with (i): equal Z, different cells.\<close>
theorem prop_twonum_ii:
  assumes "2 \<le> a" "1 \<le> b" "0 \<le> k" "k \<le> (a + 1) * (b + 1) - 3"
  shows "\<exists>\<rho>. -b \<le> \<rho> \<and> \<rho> \<le> b \<and> L2 k + real_of_int (-a) * T2 b < real_of_int \<rho>
              \<and> real_of_int \<rho> < L1 a k + real_of_int (-a) * T1 a"
    and "cpt b (L1 a k) (T1 a) (-a) \<noteq> cpt b (L2 k) (T2 b) (-a)"
proof -
  have a0: "0 \<le> a" using assms by simp
  let ?m = "k - a * (b + 1)"
  let ?r = "max (-b) (?m + 1)"
  have pa: "0 \<le> a * ((a + 1) * (b + 1) - k - 3)" using assms by (intro mult_nonneg_nonneg) auto
  have pb: "0 \<le> a * (b - 1)" using assms by (intro mult_nonneg_nonneg) auto
  have x2: "L2 k + real_of_int (-a) * T2 b = real_of_int ?m + 1 / 2"
    unfolding L2_def T2_def by (simp add: algebra_simps)
  have gt: "\<And>r. real_of_int r < L1 a k + real_of_int (-a) * T1 a \<longleftrightarrow> 2 * (a + 1) * r < 2 * (k + -a) + 1"
  proof -
    fix r :: int
    have pos: "0 < real_of_int (2 * (a + 1))" using a0 by simp
    have "real_of_int r < L1 a k + real_of_int (-a) * T1 a
          \<longleftrightarrow> real_of_int r < real_of_int (2 * (k + -a) + 1) / real_of_int (2 * (a + 1))"
      using L1_eq[OF a0, of k "-a"] by simp
    also have "\<dots> \<longleftrightarrow> real_of_int r * real_of_int (2 * (a + 1)) < real_of_int (2 * (k + -a) + 1)"
      by (rule pos_less_divide_eq[OF pos])
    also have "\<dots> \<longleftrightarrow> real_of_int (r * (2 * (a + 1))) < real_of_int (2 * (k + -a) + 1)" by simp
    also have "\<dots> \<longleftrightarrow> r * (2 * (a + 1)) < 2 * (k + -a) + 1" by (simp only: of_int_less_iff)
    finally show "real_of_int r < L1 a k + real_of_int (-a) * T1 a \<longleftrightarrow> 2 * (a + 1) * r < 2 * (k + -a) + 1"
      by (simp add: mult.commute)
  qed
  have lt1: "2 * (a + 1) * (?m + 1) < 2 * (k + -a) + 1" using pa assms by (simp add: algebra_simps)
  have pb': "0 \<le> a * b - a" using pb by (simp add: algebra_simps)
  have lt2: "2 * (a + 1) * (-b) < 2 * (k + -a) + 1"
  proof -
    have e: "2 * (k + -a) + 1 - 2 * (a + 1) * (-b) = 2 * (a * b - a) + 2 * b + 2 * k + 1"
      by (simp add: algebra_simps)
    have "0 < 2 * (k + -a) + 1 - 2 * (a + 1) * (-b)" unfolding e using pb' assms(2,3) by arith
    then show ?thesis by simp
  qed
  have lt: "2 * (a + 1) * ?r < 2 * (k + -a) + 1" using lt1 lt2 by (simp add: max_def)
  have rb: "?r \<le> b"
  proof (rule ccontr)
    assume "\<not> ?r \<le> b"
    then have "b < ?m + 1" using assms by (simp add: max_def split: if_splits)
    then have "(a + 1) * (b + 1) \<le> (a + 1) * (?m + 1)" using a0 by (intro mult_left_mono) auto
    then show False using lt1 assms by (simp add: algebra_simps)
  qed
  have r1: "real_of_int ?r < L1 a k + real_of_int (-a) * T1 a" using lt gt by blast
  have r2: "L2 k + real_of_int (-a) * T2 b < real_of_int ?r"
  proof -
    have "?m + 1 \<le> ?r" by simp
    then have "real_of_int (?m + 1) \<le> real_of_int ?r" by (simp only: of_int_le_iff)
    then show ?thesis unfolding x2 by simp
  qed
  show "\<exists>\<rho>. -b \<le> \<rho> \<and> \<rho> \<le> b \<and> L2 k + real_of_int (-a) * T2 b < real_of_int \<rho>
              \<and> real_of_int \<rho> < L1 a k + real_of_int (-a) * T1 a"
    using r1 r2 rb by (intro exI[of _ ?r]) auto
  have fl1: "?r \<le> \<lfloor>L1 a k + real_of_int (-a) * T1 a\<rfloor>" using r1 by (simp add: le_floor_iff less_imp_le)
  have fl2: "\<lfloor>L2 k + real_of_int (-a) * T2 b\<rfloor> = ?m" unfolding x2 by (rule floor_unique) auto
  have "?r \<le> clipb b \<lfloor>L1 a k + real_of_int (-a) * T1 a\<rfloor>" using fl1 rb by (auto simp: clipb_def)
  moreover have "clipb b ?m < ?r" using assms by (auto simp: clipb_def max_def min_def)
  ultimately have lt: "clipb b ?m < clipb b \<lfloor>L1 a k + real_of_int (-a) * T1 a\<rfloor>" by (meson less_le_trans)
  have c1: "cpt b (L1 a k) (T1 a) (-a) = clipb b \<lfloor>L1 a k + real_of_int (-a) * T1 a\<rfloor>" by (simp only: cpt_def)
  have c2: "cpt b (L2 k) (T2 b) (-a) = clipb b ?m" by (simp only: cpt_def fl2)
  show "cpt b (L1 a k) (T1 a) (-a) \<noteq> cpt b (L2 k) (T2 b) (-a)" unfolding c1 c2 using lt by auto
qed

section \<open>Proposition Os (a = 3)\<close>

text \<open>O(s) = [s+1, 4b+3] + (s+1) delta_T, T = 4b+4 (paper, Section a=3, one-prime words).
  O_1(s) = (clip floor((s+h)/4))_h and O_2(s) = (clip(s + h(b+1)))_h.\<close>
definition Os_ms :: "int \<Rightarrow> int \<Rightarrow> int multiset" where
  "Os_ms b s = image_mset id (mset_set {s + 1..4 * b + 3}) + replicate_mset (nat (s + 1)) (4 * b + 4)"

definition O1 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where "O1 b s h = clipb b ((s + h) div 4)"
definition O2 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where "O2 b s h = clipb b (s + h * (b + 1))"

lemma min_count_O:
  fixes T s :: int
  assumes "0 \<le> s" "s \<le> T - 1"
  shows "image_mset (\<lambda>N. min T (N + s + 1)) (mset_set {0..T - 1})
         = image_mset id (mset_set {s + 1..T - 1}) + replicate_mset (nat (s + 1)) T"
proof -
  have split: "{0..T - 1} = {0..T - s - 2} \<union> {T - s - 1..T - 1}" using assms by auto
  have dis: "{0..T - s - 2} \<inter> {T - s - 1..T - 1} = {}" by auto
  have m1: "image_mset (\<lambda>N. min T (N + s + 1)) (mset_set {0..T - s - 2})
            = image_mset id (mset_set {s + 1..T - 1})"
  proof -
    have "image_mset (\<lambda>N. min T (N + s + 1)) (mset_set {0..T - s - 2})
          = image_mset (\<lambda>N. N + (s + 1)) (mset_set {0..T - s - 2})"
      by (rule image_mset_cong) (auto simp: min_def)
    also have "\<dots> = mset_set ((\<lambda>N. N + (s + 1)) ` {0..T - s - 2})"
      by (rule image_mset_mset_set) simp
    also have "(\<lambda>N. N + (s + 1)) ` {0..T - s - 2} = {s + 1..T - 1}"
      by (rule set_eqI) (auto intro: image_eqI[where x = "_ - (s + 1)"])
    finally show ?thesis by simp
  qed
  have m2: "image_mset (\<lambda>N. min T (N + s + 1)) (mset_set {T - s - 1..T - 1}) = replicate_mset (nat (s + 1)) T"
  proof -
    have "image_mset (\<lambda>N. min T (N + s + 1)) (mset_set {T - s - 1..T - 1})
          = image_mset (\<lambda>_. T) (mset_set {T - s - 1..T - 1})"
      by (rule image_mset_cong) (auto simp: min_def)
    also have "\<dots> = replicate_mset (size (mset_set {T - s - 1..T - 1})) T" by (rule image_mset_const_eq)
    also have "size (mset_set {T - s - 1..T - 1}) = nat (s + 1)" using assms by simp
    finally show ?thesis .
  qed
  have "image_mset (\<lambda>N. min T (N + s + 1)) (mset_set {0..T - 1})
        = image_mset (\<lambda>N. min T (N + s + 1)) (mset_set {0..T - s - 2})
          + image_mset (\<lambda>N. min T (N + s + 1)) (mset_set {T - s - 1..T - 1})"
    by (simp only: split mset_set_Union[OF finite_atLeastAtMost finite_atLeastAtMost dis] image_mset_union)
  then show ?thesis using m1 m2 by simp
qed

lemma floor_div4:
  fixes n :: int
  shows "\<lfloor>(real_of_int n + 1 / 2) * (1 / 4)\<rfloor> = n div 4"
proof (rule floor_unique)
  have b1: "4 * (n div 4) \<le> n" and b2: "n \<le> 4 * (n div 4) + 3" by presburger+
  have c1: "4 * real_of_int (n div 4) \<le> real_of_int n"
  proof -
    have "real_of_int (4 * (n div 4)) \<le> real_of_int n" by (simp only: of_int_le_iff b1)
    then show ?thesis by simp
  qed
  have c2: "real_of_int n \<le> 4 * real_of_int (n div 4) + 3"
  proof -
    have "real_of_int n \<le> real_of_int (4 * (n div 4) + 3)" by (simp only: of_int_le_iff b2)
    then show ?thesis by simp
  qed
  show "real_of_int (n div 4) \<le> (real_of_int n + 1 / 2) * (1 / 4)" using c1 by simp
  show "(real_of_int n + 1 / 2) * (1 / 4) < real_of_int (n div 4) + 1" using c2 by simp
qed

theorem prop_Os:
  assumes "1 \<le> b" "0 \<le> s" "s \<le> 4 * b + 3"
  shows "L1 3 s = real_of_int (2 * s + 1) / 8 \<and> T1 3 = 1 / 4 \<and> L2 s = real_of_int s + 1 / 2 \<and> T2 b = real_of_int (b + 1)"
    and "\<And>h. cpt b (L1 3 s) (T1 3) h = O1 b s h"
    and "\<And>h. cpt b (L2 s) (T2 b) h = O2 b s h"
    and "Zms 3 b (O1 b s) = Os_ms b s" and "Zms 3 b (O2 b s) = Os_ms b s"
    and "2 \<le> b \<Longrightarrow> (\<exists>h. -3 \<le> h \<and> h \<le> 3 \<and> O1 b s h \<noteq> O2 b s h) \<longleftrightarrow> s \<le> 4 * b + 1"
proof -
  have b0: "0 \<le> b" using assms by simp
  show "L1 3 s = real_of_int (2 * s + 1) / 8 \<and> T1 3 = 1 / 4 \<and> L2 s = real_of_int s + 1 / 2 \<and> T2 b = real_of_int (b + 1)"
    unfolding L1_def T1_def L2_def T2_def by simp
  have c1: "\<And>h. cpt b (L1 3 s) (T1 3) h = O1 b s h"
  proof -
    fix h :: int
    have "L1 3 s + real_of_int h * T1 3 = (real_of_int (s + h) + 1 / 2) * (1 / 4)"
      unfolding L1_def T1_def by (simp add: algebra_simps)
    then show "cpt b (L1 3 s) (T1 3) h = O1 b s h" unfolding cpt_def O1_def by (simp only: floor_div4)
  qed
  have c2: "\<And>h. cpt b (L2 s) (T2 b) h = O2 b s h"
  proof -
    fix h :: int
    have "L2 s + real_of_int h * T2 b = real_of_int (s + h * (b + 1)) + 1 / 2"
      unfolding L2_def T2_def by simp
    moreover have "\<lfloor>real_of_int (s + h * (b + 1)) + 1 / 2\<rfloor> = s + h * (b + 1)" by (rule floor_unique) auto
    ultimately show "cpt b (L2 s) (T2 b) h = O2 b s h" unfolding cpt_def O2_def by simp
  qed
  show "\<And>h. cpt b (L1 3 s) (T1 3) h = O1 b s h" by fact
  show "\<And>h. cpt b (L2 s) (T2 b) h = O2 b s h" by fact
  have e1: "cpt b (L1 3 s) (T1 3) = O1 b s" by (rule ext) (rule c1)
  have e2: "cpt b (L2 s) (T2 b) = O2 b s" by (rule ext) (rule c2)
  have K: "(3 + 1) * (b + 1) = 4 * b + 4" by simp
  have M: "image_mset (\<lambda>N. min (4 * b + 4) (N + s + 1)) (mset_set {0..4 * b + 4 - 1}) = Os_ms b s"
    unfolding Os_ms_def using min_count_O[of s "4 * b + 4"] assms by simp
  show "Zms 3 b (O1 b s) = Os_ms b s"
    using twonum_Z1[of 3 b s] b0 assms e1 M unfolding K by simp
  show "Zms 3 b (O2 b s) = Os_ms b s"
    using twonum_Z2[of 3 b s] b0 assms e2 M unfolding K by simp
  assume b2: "2 \<le> b"
  show "(\<exists>h. -3 \<le> h \<and> h \<le> 3 \<and> O1 b s h \<noteq> O2 b s h) \<longleftrightarrow> s \<le> 4 * b + 1"
  proof
    assume "s \<le> 4 * b + 1"
    then have "cpt b (L1 3 s) (T1 3) (-3) \<noteq> cpt b (L2 s) (T2 b) (-3)"
      using prop_twonum_ii(2)[of 3 b s] assms by simp
    then show "\<exists>h. -3 \<le> h \<and> h \<le> 3 \<and> O1 b s h \<noteq> O2 b s h"
      using c1 c2 by (intro exI[of _ "-3"]) simp
  next
    assume "\<exists>h. -3 \<le> h \<and> h \<le> 3 \<and> O1 b s h \<noteq> O2 b s h"
    then obtain h where h: "-3 \<le> h" "h \<le> 3" "O1 b s h \<noteq> O2 b s h" by blast
    show "s \<le> 4 * b + 1"
    proof (rule ccontr)
      assume "\<not> s \<le> 4 * b + 1"
      then have "s = 4 * b + 2 \<or> s = 4 * b + 3" using assms by arith
      moreover have "h = -3 \<or> h = -2 \<or> h = -1 \<or> h = 0 \<or> h = 1 \<or> h = 2 \<or> h = 3" using h by presburger
      ultimately show False using h(3) b2 unfolding O1_def O2_def clipb_def
        by (elim disjE) (auto simp: min_def max_def split: if_splits)
    qed
  qed
qed

end
