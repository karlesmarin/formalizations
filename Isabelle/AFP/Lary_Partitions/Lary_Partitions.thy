(*  Title:      Lary_Partitions.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

(* encaje: Theorem 3 of Coons, The Calkin-Wilf problems on l-ary partition functions (arXiv:2611.08109) *)
section \<open>Monotonicity of restricted l-ary partition functions\<close>

theory Lary_Partitions
  imports Main
begin

text \<open>
Let @{text "k, l \<ge> 2"} and let @{text "b(n)"} be the number of partitions of @{text n} into powers
of @{text l} in which each power is used at most @{text k} times.  Theorem 3 of Coons \cite{Coons2026}
states that @{text b} is monotone if and only if @{text l} divides @{text "k + 1"}, and that @{text b}
is never strictly monotone.

Inside the locale @{text lary}, the function @{text b} is first defined by the recurrence
@{text "b(0) = 1"} and, for @{text "n \<ge> 1"}, @{text "b(n) = \<Sum> b(j)"} over the @{text j} with
@{text "l * j \<le> n \<le> k + l * j"} (the possible values of the units digit are @{text "n - l * j"}).
Theorem 3 is proved for this function.  The last section defines the count @{text b_count} of digit
expansions directly and proves that it equals @{text b}, so the theorem holds for the count itself.
\<close>

locale lary =
  fixes k l :: nat
  assumes k2: "2 \<le> k" and l2: "2 \<le> l"
begin

lemma two_j: "2 * j \<le> l * j" by (rule mult_le_mono1[OF l2])

lemma ndvd: "\<not> l dvd x \<Longrightarrow> l * j \<noteq> x" by (metis dvd_triv_left)

function b :: "nat \<Rightarrow> nat" where
  "b n = (if n = 0 then 1 else (\<Sum>j \<in> {j. l * j \<le> n \<and> n \<le> k + l * j}. b j))"
  by pat_completeness auto
termination
proof (relation "measure id")
  show "wf (measure id)" by simp
next
  fix n j
  assume "n \<noteq> 0" "j \<in> {j. l * j \<le> n \<and> n \<le> k + l * j}"
  then have h: "l * j \<le> n" by simp
  have "2 * j \<le> l * j" by (rule two_j)
  with h \<open>n \<noteq> 0\<close> have "j < n" by arith
  then show "(j, n) \<in> measure id" by simp
qed

declare b.simps[simp del]

definition W :: "nat \<Rightarrow> nat set" where
  "W n = {j. l * j \<le> n \<and> n \<le> k + l * j}"

lemma memW: "j \<in> W n \<longleftrightarrow> l * j \<le> n \<and> n \<le> k + l * j"
  by (simp add: W_def)

lemma lpos: "0 < l" using l2 by simp

lemma finW: "finite (W n)"
proof (rule finite_subset[of _ "{..n}"])
  show "W n \<subseteq> {..n}"
  proof
    fix j assume "j \<in> W n"
    then have "l * j \<le> n" by (simp add: memW)
    moreover have "j \<le> l * j" using two_j[of j] by arith
    ultimately have "j \<le> n" by arith
    then show "j \<in> {..n}" by simp
  qed
qed simp

lemma b_0: "b 0 = 1" by (simp add: b.simps)

lemma b_rec: "n \<noteq> 0 \<Longrightarrow> b n = (\<Sum>j \<in> W n. b j)"
  by (simp add: b.simps[of n] W_def)

lemma W1: "W 1 = {0}"
proof (rule set_eqI)
  fix j
  show "j \<in> W 1 \<longleftrightarrow> j \<in> {0}"
  proof
    assume "j \<in> W 1"
    then have h: "l * j \<le> 1" by (simp add: memW)
    show "j \<in> {0}"
    proof (rule ccontr)
      assume "j \<notin> {0}"
      then have "1 \<le> j" by simp
      then have "l * 1 \<le> l * j" by (rule mult_le_mono2)
      with h l2 show False by simp
    qed
  next
    assume "j \<in> {0}"
    then show "j \<in> W 1" using k2 by (simp add: memW)
  qed
qed

lemma b_1: "b 1 = 1"
proof -
  have "b 1 = (\<Sum>j \<in> W 1. b j)" by (rule b_rec) simp
  also have "\<dots> = (\<Sum>j \<in> {0}. b j)" by (simp only: W1)
  also have "\<dots> = b 0" by simp
  also have "\<dots> = 1" by (rule b_0)
  finally show ?thesis .
qed

text \<open>Never strictly monotone: b(0) = b(1) = 1.\<close>
theorem not_strict_mono: "\<not> strict_mono b"
proof
  assume sm: "strict_mono b"
  have "b 0 < b 1" by (rule strict_monoD[OF sm]) simp
  with b_0 b_1 show False by linarith
qed

text \<open>If l does not divide k+1, then b(k) = b(k+1) + 1.\<close>
lemma drop_at_k:
  assumes nd: "\<not> l dvd k + 1"
  shows "b k = b (k + 1) + 1"
proof -
  have W1': "W (k + 1) = {j. 1 \<le> j \<and> l * j \<le> k}"
  proof (rule set_eqI)
    fix j
    have ne: "l * j \<noteq> k + 1" by (rule ndvd[OF nd])
    have p: "1 \<le> l * j \<longleftrightarrow> 1 \<le> j"
    proof (cases "j = 0")
      case True
      then show ?thesis by simp
    next
      case False
      then have "1 \<le> j" by simp
      moreover have "1 \<le> l * j" using two_j[of j] \<open>1 \<le> j\<close> by arith
      ultimately show ?thesis by simp
    qed
    show "j \<in> W (k + 1) \<longleftrightarrow> j \<in> {j. 1 \<le> j \<and> l * j \<le> k}"
      using ne p by (auto simp: memW)
  qed
  have W0: "W k = insert 0 (W (k + 1))"
  proof (rule set_eqI)
    fix j
    show "j \<in> W k \<longleftrightarrow> j \<in> insert 0 (W (k + 1))"
    proof (cases "j = 0")
      case True
      then show ?thesis by (simp add: memW)
    next
      case False
      have "j \<in> W k \<longleftrightarrow> l * j \<le> k" by (simp add: memW)
      moreover have "j \<in> W (k + 1) \<longleftrightarrow> l * j \<le> k"
      proof -
        have "j \<in> W (k + 1) \<longleftrightarrow> j \<in> {j. 1 \<le> j \<and> l * j \<le> k}" by (simp only: W1')
        also have "\<dots> \<longleftrightarrow> l * j \<le> k" using False by simp
        finally show ?thesis .
      qed
      ultimately show ?thesis using False by simp
    qed
  qed
  have "0 \<notin> W (k + 1)" by (simp only: W1') simp
  then have "b k = b 0 + (\<Sum>j \<in> W (k + 1). b j)"
    using b_rec[of k] k2 W0 finW by simp
  moreover have "b (k + 1) = (\<Sum>j \<in> W (k + 1). b j)" by (rule b_rec) simp
  ultimately show ?thesis by (simp add: b_0)
qed

theorem not_mono:
  assumes "\<not> l dvd k + 1"
  shows "\<not> mono b"
proof
  assume m: "mono b"
  have "b k \<le> b (k + 1)" by (rule monoD[OF m]) simp
  with drop_at_k[OF assms] show False by simp
qed

subsection \<open>The case l divides k+1\<close>

lemma mono_upto:
  assumes h: "\<forall>i<m. b i \<le> b (Suc i)" and xy: "x \<le> y" and ym: "y \<le> m"
  shows "b x \<le> b y"
  using xy ym
proof (induction y)
  case 0
  then show ?case by simp
next
  case (Suc y)
  show ?case
  proof (cases "x = Suc y")
    case True
    then show ?thesis by simp
  next
    case False
    with Suc.prems have "x \<le> y" by simp
    with Suc.IH Suc.prems have "b x \<le> b y" by simp
    moreover have "b y \<le> b (Suc y)" using h Suc.prems by simp
    ultimately show ?thesis by simp
  qed
qed

lemma charW:
  assumes nm: "n + 1 = l * m" and ka: "k + 1 = l * a"
  shows "W n = {j. j < m \<and> m \<le> a + j}" and "W (n + 1) = {j. j \<le> m \<and> m < a + j}"
proof -
  have d: "\<And>j. l * (a + j) = k + 1 + l * j" using ka by (simp add: algebra_simps)
  show "W n = {j. j < m \<and> m \<le> a + j}"
  proof (rule set_eqI)
    fix j
    have e1: "(l * j \<le> n) = (j < m)"
    proof -
      have "(l * j \<le> n) = (l * j < l * m)" using nm by arith
      also have "\<dots> = (j < m)" using lpos by simp
      finally show ?thesis .
    qed
    have e2: "(n \<le> k + l * j) = (m \<le> a + j)"
    proof -
      have "(n \<le> k + l * j) = (l * m \<le> l * (a + j))" using nm d[of j] by arith
      also have "\<dots> = (m \<le> a + j)" using lpos by simp
      finally show ?thesis .
    qed
    show "j \<in> W n \<longleftrightarrow> j \<in> {j. j < m \<and> m \<le> a + j}" using e1 e2 by (simp add: memW)
  qed
  show "W (n + 1) = {j. j \<le> m \<and> m < a + j}"
  proof (rule set_eqI)
    fix j
    have e1: "(l * j \<le> n + 1) = (j \<le> m)"
    proof -
      have "(l * j \<le> n + 1) = (l * j \<le> l * m)" using nm by simp
      also have "\<dots> = (j \<le> m)" using lpos by simp
      finally show ?thesis .
    qed
    have e2: "(n + 1 \<le> k + l * j) = (m < a + j)"
    proof -
      have "(n + 1 \<le> k + l * j) = (l * m < l * (a + j))" using nm d[of j] by arith
      also have "\<dots> = (m < a + j)" using lpos by simp
      finally show ?thesis .
    qed
    show "j \<in> W (n + 1) \<longleftrightarrow> j \<in> {j. j \<le> m \<and> m < a + j}" using e1 e2 by (simp add: memW)
  qed
qed

lemma step:
  assumes ka: "k + 1 = l * a" and ih: "\<forall>i<n. b i \<le> b (Suc i)"
  shows "b n \<le> b (Suc n)"
proof (cases "n = 0")
  case True
  have e: "b (Suc 0) = 1" by (metis One_nat_def b_1)
  with True b_0 show ?thesis by simp
next
  case n0: False
  show ?thesis
  proof (cases "l dvd n + 1")
    case False
    have "W n = W (n + 1)"
    proof (rule set_eqI)
      fix j
      have d: "l * (a + j) = k + 1 + l * j" using ka by (simp add: algebra_simps)
      have ne1: "l * j \<noteq> n + 1" by (rule ndvd[OF False])
      have ne2: "k + l * j \<noteq> n"
      proof
        assume "k + l * j = n"
        then have "n + 1 = l * (a + j)" using d by simp
        then have "l dvd n + 1" by simp
        with False show False by simp
      qed
      show "j \<in> W n \<longleftrightarrow> j \<in> W (n + 1)" using ne1 ne2 by (auto simp: memW)
    qed
    then show ?thesis by (simp add: b_rec n0)
  next
    case True
    then obtain m where nm: "n + 1 = l * m" by auto
    have m1: "1 \<le> m" using nm by (cases m) auto
    have a1: "1 \<le> a" using ka by (cases a) auto
    have "2 * m \<le> l * m" by (rule two_j)
    with m1 nm have mn: "m \<le> n" by arith
    have ih': "\<forall>i<m. b i \<le> b (Suc i)" using ih mn by simp
    have fin: "\<And>P. finite {j. j < m \<and> P j}"
      by (rule finite_subset[of _ "{..m}"]) auto
    have Wn: "W n = {j. j < m \<and> m \<le> a + j}" and Wn1: "W (n + 1) = {j. j \<le> m \<and> m < a + j}"
      using charW[OF nm ka] by simp_all
    show ?thesis
    proof (cases "m < a")
      case True
      have "{j. j \<le> m \<and> m < a + j} = insert m {j. j < m \<and> m \<le> a + j}"
        using True by auto
      moreover have "m \<notin> {j. j < m \<and> m \<le> a + j}" by simp
      ultimately have "b (n + 1) = b m + b n"
        using b_rec[of "n + 1"] b_rec[of n] n0 Wn Wn1 fin by simp
      then show ?thesis by simp
    next
      case False
      define C where "C = {j. j < m \<and> m < a + j}"
      have A: "{j. j < m \<and> m \<le> a + j} = insert (m - a) C"
        unfolding C_def using False m1 a1 by auto
      have B: "{j. j \<le> m \<and> m < a + j} = insert m C"
        unfolding C_def using a1 by auto
      have fC: "finite C" unfolding C_def by (rule fin)
      have nA: "m - a \<notin> C"
      proof
        assume "m - a \<in> C"
        then have "m < a + (m - a)" unfolding C_def by simp
        with False show False by arith
      qed
      have nB: "m \<notin> C" unfolding C_def by simp
      have bm: "b (m - a) \<le> b m" using mono_upto[OF ih'] by simp
      have "b n = b (m - a) + (\<Sum>j \<in> C. b j)"
        using b_rec[of n] n0 Wn A fC nA by simp
      moreover have "b (n + 1) = b m + (\<Sum>j \<in> C. b j)"
        using b_rec[of "n + 1"] Wn1 B fC nB by simp
      ultimately show ?thesis using bm by simp
    qed
  qed
qed

theorem mono_if_dvd:
  assumes "l dvd k + 1"
  shows "mono b"
proof -
  from assms obtain a where ka: "k + 1 = l * a" by auto
  have "\<forall>n. b n \<le> b (Suc n)"
  proof
    fix n
    show "b n \<le> b (Suc n)"
      by (induction n rule: less_induct) (use step[OF ka] in blast)
  qed
  then show ?thesis by (simp add: mono_iff_le_Suc)
qed

text \<open>Theorem 3 of \cite{Coons2026}: @{text b} is monotone iff @{text l} divides @{text "k + 1"},
  and it is never strictly monotone.\<close>
theorem coons_theorem_3:
  "mono b \<longleftrightarrow> l dvd k + 1"
  "\<not> strict_mono b"
  using mono_if_dvd not_mono not_strict_mono by auto

subsection \<open>Fidelity: the recurrence counts digit expansions\<close>

text \<open>
A partition of @{text n} into powers of @{text l}, each used at most @{text k} times, is given by its
list of multiplicities @{text d} (the multiplicity of @{text "l ^ i"} at position @{text i}): every entry
is at most @{text k}, the list has no trailing zero, and its value
@{term "horner_sum (\<lambda>x. x) l d"} @{text "= \<Sum> d ! i * l ^ i"} is @{text n}.
\<close>

definition S :: "nat \<Rightarrow> nat list set" where
  "S n = {d. set d \<subseteq> {..k} \<and> (d = [] \<or> last d \<noteq> 0) \<and> horner_sum (\<lambda>x. x) l d = n}"

definition b_count :: "nat \<Rightarrow> nat" where
  "b_count n = card (S n)"

lemma S_horner_sum: "d \<in> S n \<Longrightarrow> (\<Sum>i < length d. d ! i * l ^ i) = n"
  by (simp add: S_def horner_sum_eq_sum atLeast0LessThan)

abbreviation dval :: "nat list \<Rightarrow> nat" where
  "dval d \<equiv> horner_sum (\<lambda>x. x) l d"

lemma dval_Nil: "dval [] = 0" by simp

lemma dval_Cons: "dval (a # d) = a + l * dval d" by simp

lemma dval0: "dval d = 0 \<Longrightarrow> \<forall>x \<in> set d. x = 0"
proof (induction d)
  case Nil
  then show ?case by simp
next
  case (Cons a d)
  then have h: "a + l * dval d = 0" by (simp add: dval_Cons)
  then have "a = 0" by simp
  moreover have "dval d = 0" using h lpos by simp
  ultimately show ?case using Cons.IH by simp
qed

lemma S0: "S 0 = {[]}"
proof (rule set_eqI)
  fix d
  show "d \<in> S 0 \<longleftrightarrow> d \<in> {[]}"
  proof
    assume h: "d \<in> S 0"
    show "d \<in> {[]}"
    proof (rule ccontr)
      assume "d \<notin> {[]}"
      then have ne: "d \<noteq> []" by simp
      from h have "dval d = 0" and "last d \<noteq> 0" using ne by (auto simp: S_def)
      then have z: "\<forall>x \<in> set d. x = 0" using dval0 by simp
      have "last d \<in> set d" by (rule last_in_set[OF ne])
      with z \<open>last d \<noteq> 0\<close> show False by simp
    qed
  next
    assume "d \<in> {[]}"
    then show "d \<in> S 0" by (simp add: S_def dval_Nil)
  qed
qed

lemma S_decomp:
  assumes n0: "n \<noteq> 0"
  shows "S n = (\<Union>j \<in> W n. (#) (n - l * j) ` S j)"
proof (rule set_eqI)
  fix d
  show "d \<in> S n \<longleftrightarrow> d \<in> (\<Union>j \<in> W n. (#) (n - l * j) ` S j)"
  proof
    assume h: "d \<in> S n"
    then have hs: "set d \<subseteq> {..k}" and hl: "d = [] \<or> last d \<noteq> 0" and hv: "dval d = n"
      by (simp_all add: S_def)
    have dne: "d \<noteq> []" using hv n0 by (auto simp: dval_Nil)
    then obtain a d' where d: "d = a # d'" by (cases d) auto
    define j where "j = dval d'"
    have an: "n = a + l * j" using hv d by (simp add: dval_Cons j_def)
    have ak: "a \<le> k" using hs d by simp
    have jW: "j \<in> W n" using an ak by (simp add: memW)
    have d'S: "d' \<in> S j"
    proof -
      have "set d' \<subseteq> {..k}" using hs d by simp
      moreover have "d' = [] \<or> last d' \<noteq> 0" using hl d by (cases d') auto
      ultimately show ?thesis by (simp add: S_def j_def)
    qed
    have "a = n - l * j" using an by simp
    then show "d \<in> (\<Union>j \<in> W n. (#) (n - l * j) ` S j)" using jW d'S d by auto
  next
    assume "d \<in> (\<Union>j \<in> W n. (#) (n - l * j) ` S j)"
    then obtain j d' where jW: "j \<in> W n" and d'S: "d' \<in> S j" and d: "d = (n - l * j) # d'" by auto
    have hs': "set d' \<subseteq> {..k}" and hl': "d' = [] \<or> last d' \<noteq> 0" and hv': "dval d' = j"
      using d'S by (simp_all add: S_def)
    have b1: "l * j \<le> n" and b2: "n \<le> k + l * j" using jW by (simp_all add: memW)
    have "set d \<subseteq> {..k}" using hs' b2 d by auto
    moreover have "d = [] \<or> last d \<noteq> 0"
    proof (cases "d' = []")
      case True
      then have "j = 0" using hv' by (simp add: dval_Nil)
      with True d n0 show ?thesis by simp
    next
      case False
      then show ?thesis using hl' d by simp
    qed
    moreover have "dval d = n" using d hv' b1 by (simp add: dval_Cons)
    ultimately show "d \<in> S n" by (simp add: S_def)
  qed
qed

lemma S_finite_card: "finite (S n) \<and> card (S n) = b n"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n = 0")
    case True
    then show ?thesis by (simp add: S0 b_0)
  next
    case n0: False
    have lt: "\<And>j. j \<in> W n \<Longrightarrow> j < n"
    proof -
      fix j assume "j \<in> W n"
      then have "l * j \<le> n" by (simp add: memW)
      with two_j[of j] n0 show "j < n" by arith
    qed
    have fin: "\<And>j. j \<in> W n \<Longrightarrow> finite (S j)" using less lt by blast
    have cd: "\<And>j. j \<in> W n \<Longrightarrow> card (S j) = b j" using less lt by blast
    show ?thesis
    proof
      show "finite (S n)" using S_decomp[OF n0] finW fin by auto
      have disj: "\<forall>i \<in> W n. \<forall>j \<in> W n. i \<noteq> j \<longrightarrow>
          ((#) (n - l * i) ` S i) \<inter> ((#) (n - l * j) ` S j) = {}"
      proof (intro ballI impI)
        fix i j assume "i \<in> W n" "j \<in> W n" "i \<noteq> j"
        show "((#) (n - l * i) ` S i) \<inter> ((#) (n - l * j) ` S j) = {}"
        proof (rule equals0I)
          fix x assume "x \<in> ((#) (n - l * i) ` S i) \<inter> ((#) (n - l * j) ` S j)"
          then obtain d1 d2 where "d1 \<in> S i" "d2 \<in> S j" "x = (n - l * i) # d1" "x = (n - l * j) # d2"
            by auto
          then have "d1 = d2" by simp
          with \<open>d1 \<in> S i\<close> \<open>d2 \<in> S j\<close> have "i = j" by (simp add: S_def)
          with \<open>i \<noteq> j\<close> show False by simp
        qed
      qed
      have "card (S n) = card (\<Union>j \<in> W n. (#) (n - l * j) ` S j)" using S_decomp[OF n0] by simp
      also have "\<dots> = (\<Sum>j \<in> W n. card ((#) (n - l * j) ` S j))"
        by (rule card_UN_disjoint) (use finW fin disj in auto)
      also have "\<dots> = (\<Sum>j \<in> W n. card (S j))"
        by (rule sum.cong) (auto simp: card_image inj_on_def)
      also have "\<dots> = (\<Sum>j \<in> W n. b j)" using cd by simp
      also have "\<dots> = b n" using b_rec[OF n0] by simp
      finally show "card (S n) = b n" .
    qed
  qed
qed

text \<open>The recurrence equals the digit count.\<close>
theorem b_count_eq_b: "b_count n = b n"
  using S_finite_card by (simp add: b_count_def)

corollary coons_theorem_3_count:
  "mono b_count \<longleftrightarrow> l dvd k + 1"
  "\<not> strict_mono b_count"
proof -
  have "b_count = b" by (rule ext) (rule b_count_eq_b)
  then show "mono b_count \<longleftrightarrow> l dvd k + 1" and "\<not> strict_mono b_count"
    using coons_theorem_3 by simp_all
qed

end

end
