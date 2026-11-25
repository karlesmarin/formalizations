(*  Title:      Caballero_KR.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín
*)

section \<open>Kassel--Reutenauer coefficients: the run structure of \<open>a\<^sub>{n,i}\<close>\<close>

theory Caballero_KR
  imports Main
begin

text \<open>
  This is a reformulation of results of Rodríguez Caballero (J. Number Theory, 2018), who linked the
  Kassel--Reutenauer polynomials \<open>P\<^sub>n(q)\<close> with the Erdős--Nicolas function; it is \<^emph>\<open>not\<close> a result of ours.

  Definition copied from the note (Section ``A reformulation through the Kassel--Reutenauer
  polynomials''): from \<open>P\<^sub>n(q)/q\<^sup>n\<^sup>-\<^sup>1 = \<Sum> (-1)\<^sup>k\<^sup>-\<^sup>1 [[-(m'-k-1)/2, (m'-k-1)/2]]\<close> over the pairs
  \<open>1 \<le> k < m'\<close>, \<open>k m' = 2n\<close>, \<open>k \<not>\<equiv> m' (mod 2)\<close>, coefficients of \<open>q\<^sup>i\<close> give
  \<open>a\<^sub>{n,i} = \<Sum>\<^sub>j \<epsilon>\<^sub>j [d\<^sub>j \<ge> 2i+1]\<close>, where \<open>k\<^sub>1 < \<dots> < k\<^sub>K\<close> are the smaller members of the pairs,
  \<open>d\<^sub>j = 2n/k\<^sub>j - k\<^sub>j\<close> and \<open>\<epsilon>\<^sub>j = (-1)\<^sup>k\<^sub>j\<^sup>-\<^sup>1\<close>. We start from that coefficient formula.

  Proved: the \<open>d\<^sub>j\<close> are odd and satisfy \<open>d\<^sub>j \<ge> d\<^sub>j\<^sub>+\<^sub>1 + 2\<close>; \<open>a\<^sub>{n,i} = h\<^sub>{J(i)}\<close> with \<open>h\<^sub>j\<close> the partial
  sums of the \<open>\<epsilon>\<close>; \<open>J(0) = K\<close>, \<open>J(i) \<ge> 1\<close> for \<open>i \<le> n-1\<close>; \<open>J\<close> is antitone; every value \<open>j \<in> [1,K]\<close>
  is attained at some \<open>i \<le> n-1\<close> (the runs are nonempty).

  \<^bold>\<open>Not proved here:\<close> (a) that the \<open>\<epsilon>\<^sub>j\<close> are the first \<open>K\<close> letters of the Dyck word of \<open>n\<close> of the
  companion session 290 (so that \<open>h\<^sub>j\<close> are its heights); (b) palindromy of \<open>P\<^sub>n\<close> and the symmetry of the
  height sequence, which give the second half of the coefficients; (c) the Kassel--Reutenauer identity
  itself, which is taken from the source and not rederived.
\<close>

subsection \<open>Definitions\<close>

definition pairsK :: "nat \<Rightarrow> nat set" where
  "pairsK n = {k. 0 < k \<and> k dvd 2 * n \<and> k * k < 2 * n \<and> odd k \<noteq> odd (2 * n div k)}"

definition dd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "dd n k = 2 * n div k - k"

definition eps :: "nat \<Rightarrow> int" where
  "eps k = (if odd k then 1 else -1)"

definition ks :: "nat \<Rightarrow> nat list" where
  "ks n = sorted_list_of_set (pairsK n)"

definition acoef :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "acoef n i = sum_list (map (\<lambda>k. if 2 * i + 1 \<le> dd n k then eps k else 0) (ks n))"

definition hh :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "hh n j = sum_list (map eps (take j (ks n)))"

definition JJ :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "JJ n i = length (filter (\<lambda>k. 2 * i + 1 \<le> dd n k) (ks n))"

lemma finite_pairsK: "finite (pairsK n)"
proof (rule finite_subset[of _ "{..<2 * n}"])
  show "pairsK n \<subseteq> {..<2 * n}"
  proof
    fix k assume k: "k \<in> pairsK n"
    hence kk: "k * k < 2 * n" by (simp add: pairsK_def)
    have "k \<le> k * k" by (rule le_square)
    hence "k < 2 * n" using kk by linarith
    thus "k \<in> {..<2 * n}" by simp
  qed
qed simp

subsection \<open>The \<open>d\<^sub>j\<close> are odd and spaced by at least 2\<close>

lemma pair_cofactor:
  assumes "k \<in> pairsK n"
  shows "k * (2 * n div k) = 2 * n" and "k < 2 * n div k"
proof -
  from assms have dv: "k dvd 2 * n" and kk: "k * k < 2 * n" and k0: "0 < k"
    by (simp_all add: pairsK_def)
  show e: "k * (2 * n div k) = 2 * n" using dv by simp
  show "k < 2 * n div k"
  proof (rule ccontr)
    assume "\<not> k < 2 * n div k"
    hence "2 * n div k \<le> k" by simp
    hence "k * (2 * n div k) \<le> k * k" by (rule mult_left_mono) simp
    with e kk show False by simp
  qed
qed

lemma dd_odd:
  assumes "n > 0" "k \<in> pairsK n"
  shows "odd (dd n k)"
proof -
  let ?m = "2 * n div k"
  have lt: "k < ?m" by (rule pair_cofactor(2)[OF assms(2)])
  have par: "odd k \<noteq> odd ?m" using assms(2) by (simp add: pairsK_def)
  obtain e where e: "?m = k + e" using lt by (metis less_imp_add_positive add.commute)
  have "dd n k = e" by (simp add: dd_def e)
  moreover have "odd e"
  proof (rule ccontr)
    assume "\<not> odd e"
    hence "even e" by simp
    hence "odd (k + e) = odd k" by simp
    show False using par \<open>odd (k + e) = odd k\<close> e by metis
  qed
  ultimately show ?thesis by simp
qed

lemma dd_gap:
  assumes "n > 0" "k \<in> pairsK n" "k' \<in> pairsK n" "k < k'"
  shows "dd n k' + 2 \<le> dd n k"
proof -
  let ?m = "2 * n div k" and ?m' = "2 * n div k'"
  have e1: "k * ?m = 2 * n" and l1: "k < ?m" using pair_cofactor[OF assms(2)] by blast+
  have e2: "k' * ?m' = 2 * n" and l2: "k' < ?m'" using pair_cofactor[OF assms(3)] by blast+
  have mm: "?m' < ?m"
  proof (rule ccontr)
    assume "\<not> ?m' < ?m"
    hence "?m \<le> ?m'" by simp
    hence "k * ?m \<le> k * ?m'" by (rule mult_left_mono) simp
    moreover have "k * ?m' < k' * ?m'" using assms(4) l2 by (intro mult_strict_right_mono) auto
    ultimately show False using e1 e2 by simp
  qed
  have gt: "dd n k' < dd n k" using mm assms(4) l1 l2 by (simp add: dd_def)
  have o1: "odd (dd n k)" and o2: "odd (dd n k')" using dd_odd[OF assms(1)] assms(2,3) by blast+
  from o1 o2 gt show ?thesis by (auto elim!: oddE; arith)
qed

lemma ks_props:
  assumes "n > 0"
  shows "distinct (ks n)" and "set (ks n) = pairsK n"
    and "sorted_wrt (\<lambda>a b. dd n b + 2 \<le> dd n a) (ks n)"
proof -
  show "distinct (ks n)" and "set (ks n) = pairsK n"
    using finite_pairsK by (simp_all add: ks_def)
  have sl: "sorted_wrt (<) (ks n)"
    by (metis ks_def distinct_sorted_list_of_set sorted_sorted_list_of_set strict_sorted_iff)
  show "sorted_wrt (\<lambda>a b. dd n b + 2 \<le> dd n a) (ks n)"
  proof (rule sorted_wrt_mono_rel[OF _ sl])
    fix x y assume "x \<in> set (ks n)" "y \<in> set (ks n)" "x < y"
    thus "dd n y + 2 \<le> dd n x" using dd_gap[OF assms] \<open>set (ks n) = pairsK n\<close> by blast
  qed
qed

subsection \<open>The coefficient is a partial sum of the \<open>\<epsilon>\<close>\<close>

lemma sum_list_filter_map:
  "sum_list (map (\<lambda>k. if P k then f k else 0) xs) = sum_list (map f (filter P xs))"
  by (induct xs) simp_all

lemma filter_antitone_prefix:
  assumes "sorted_wrt (\<lambda>a b. g b \<le> g a) xs"
  shows "filter (\<lambda>x. c \<le> (g x :: nat)) xs = take (length (filter (\<lambda>x. c \<le> g x) xs)) xs"
  using assms
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "c \<le> g x")
    case True
    with Cons show ?thesis by simp
  next
    case False
    have "filter (\<lambda>y. c \<le> g y) xs = []"
    proof (rule filter_False, rule ballI)
      fix y assume "y \<in> set xs"
      with Cons.prems have "g y \<le> g x" by simp
      with False show "\<not> c \<le> g y" by simp
    qed
    with False show ?thesis by simp
  qed
qed

lemma filter_eq_takeWhile_antitone:
  assumes "sorted_wrt (\<lambda>a b. g b \<le> g a) xs"
  shows "filter (\<lambda>x. c \<le> (g x :: nat)) xs = takeWhile (\<lambda>x. c \<le> g x) xs"
  using assms
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "c \<le> g x")
    case True
    with Cons show ?thesis by simp
  next
    case False
    have "filter (\<lambda>y. c \<le> g y) xs = []"
    proof (rule filter_False, rule ballI)
      fix y assume "y \<in> set xs"
      with Cons.prems have "g y \<le> g x" by simp
      with False show "\<not> c \<le> g y" by simp
    qed
    with False show ?thesis by simp
  qed
qed

theorem acoef_eq_hh:
  assumes "n > 0"
  shows "acoef n i = hh n (JJ n i)"
proof -
  have s: "sorted_wrt (\<lambda>a b. dd n b \<le> dd n a) (ks n)"
    by (rule sorted_wrt_mono_rel[OF _ ks_props(3)[OF assms]]) auto
  have "acoef n i = sum_list (map eps (filter (\<lambda>k. 2 * i + 1 \<le> dd n k) (ks n)))"
    by (simp add: acoef_def sum_list_filter_map)
  also have "filter (\<lambda>k. 2 * i + 1 \<le> dd n k) (ks n) = take (JJ n i) (ks n)"
    unfolding JJ_def by (rule filter_antitone_prefix[OF s])
  finally show ?thesis by (simp add: hh_def)
qed

subsection \<open>Shape of \<open>J\<close>: antitone, \<open>J(0) = K\<close>, \<open>J(i) \<ge> 1\<close>, every value in \<open>[1,K]\<close> is attained\<close>

lemma length_filter_mono:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> P x \<Longrightarrow> Q x"
  shows "length (filter P xs) \<le> length (filter Q xs)"
  using assms by (induct xs) (auto simp: le_Suc_eq)

theorem JJ_antitone:
  assumes "i \<le> i'"
  shows "JJ n i' \<le> JJ n i"
  unfolding JJ_def using assms by (intro length_filter_mono) auto

theorem JJ_zero:
  assumes "n > 0"
  shows "JJ n 0 = length (ks n)"
proof -
  have "filter (\<lambda>k. 2 * 0 + 1 \<le> dd n k) (ks n) = ks n"
  proof (rule filter_True, rule ballI)
    fix k assume "k \<in> set (ks n)"
    hence "k \<in> pairsK n" using ks_props(2)[OF assms] by simp
    hence "odd (dd n k)" by (rule dd_odd[OF assms])
    hence "0 < dd n k" by (rule odd_pos)
    thus "2 * 0 + 1 \<le> dd n k" by simp
  qed
  thus ?thesis by (simp add: JJ_def)
qed

lemma one_in_pairsK:
  assumes "n > 0" shows "1 \<in> pairsK n"
  using assms by (simp add: pairsK_def)

theorem JJ_pos:
  assumes "n > 0" "i \<le> n - 1"
  shows "1 \<le> JJ n i"
proof -
  have "1 \<in> set (ks n)" using one_in_pairsK[OF assms(1)] ks_props(2)[OF assms(1)] by simp
  moreover have "2 * i + 1 \<le> dd n 1" using assms by (simp add: dd_def)
  ultimately have "1 \<in> set (filter (\<lambda>k. 2 * i + 1 \<le> dd n k) (ks n))" by simp
  hence "filter (\<lambda>k. 2 * i + 1 \<le> dd n k) (ks n) \<noteq> []" by (metis empty_iff list.set(1))
  thus ?thesis unfolding JJ_def by (simp add: Suc_le_eq)
qed

lemma dd_le:
  assumes "k \<in> pairsK n" shows "dd n k \<le> 2 * n - 1"
proof -
  have "k > 0" using assms by (simp add: pairsK_def)
  have "2 * n div k \<le> 2 * n" by (rule div_le_dividend)
  thus ?thesis unfolding dd_def using \<open>k > 0\<close> by arith
qed

theorem JJ_surj:
  assumes "n > 0" "1 \<le> j" "j \<le> length (ks n)"
  shows "\<exists>i. i \<le> n - 1 \<and> JJ n i = j"
proof -
  let ?xs = "ks n"
  let ?c = "dd n (?xs ! (j - 1))"
  have sw: "sorted_wrt (\<lambda>a b. dd n b + 2 \<le> dd n a) ?xs" by (rule ks_props(3)[OF assms(1)])
  have mem: "?xs ! (j - 1) \<in> pairsK n" using assms ks_props(2)[OF assms(1)] by (metis One_nat_def
      Suc_le_lessD diff_less less_Suc_eq_le nth_mem zero_less_one le_neq_implies_less
      order_le_less_trans diff_Suc_less less_le_trans)
  have odd_c: "odd ?c" by (rule dd_odd[OF assms(1) mem])
  obtain i where i: "?c = 2 * i + 1" using odd_c by (auto elim: oddE)
  have ile: "i \<le> n - 1" using dd_le[OF mem] i by simp
  have P: "filter (\<lambda>k. 2 * i + 1 \<le> dd n k) ?xs = take j ?xs"
  proof -
    have "filter (\<lambda>k. 2 * i + 1 \<le> dd n k) ?xs = takeWhile (\<lambda>k. 2 * i + 1 \<le> dd n k) ?xs"
    proof (rule filter_eq_takeWhile_antitone)
      show "sorted_wrt (\<lambda>a b. dd n b \<le> dd n a) ?xs"
        by (rule sorted_wrt_mono_rel[OF _ sw]) auto
    qed
    also have "\<dots> = take j ?xs"
    proof (rule takeWhile_eq_take_P_nth)
      fix l assume l: "l < j" "l < length ?xs"
      show "2 * i + 1 \<le> dd n (?xs ! l)"
      proof (cases "l = j - 1")
        case True thus ?thesis using i by simp
      next
        case False
        hence "l < j - 1" using l by simp
        hence "dd n (?xs ! (j - 1)) + 2 \<le> dd n (?xs ! l)"
          using sorted_wrt_nth_less[OF sw, of l "j - 1"] assms by simp
        thus ?thesis using i by simp
      qed
    next
      assume jl: "j < length ?xs"
      have "dd n (?xs ! j) + 2 \<le> dd n (?xs ! (j - 1))"
        using sorted_wrt_nth_less[OF sw, of "j - 1" j] jl assms by simp
      thus "\<not> 2 * i + 1 \<le> dd n (?xs ! j)" using i by simp
    qed
    finally show ?thesis .
  qed
  have "JJ n i = j" using P assms by (simp add: JJ_def)
  with ile show ?thesis by blast
qed

end
