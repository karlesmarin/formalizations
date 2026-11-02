(*  Title:      Sandor_Antichain.thy
    Author:     Carles Marin

    Sandor's subset-sum antichain (Erdos problem 882): for m >= 1 no two distinct nonempty subsets of
    {2^i + m 2^m : i < m} have sums dividing one another.  This is erdos_882.variants.sandor of
    google-deepmind/formal-conjectures; the construction is reported in P. Erdos, Some of my new and
    almost new problems and results in combinatorial number theory, Number theory (Eger, 1996), 1998.
*)
theory Sandor_Antichain
  imports Main
begin

text \<open>Sandor's subset-sum antichain (Erdos problem 882): for \<^latex>\<open>$m \ge 1$\<close> the set
  of the numbers \<^latex>\<open>$2^i + m\,2^m$\<close> with \<^latex>\<open>$i < m$\<close> has no two distinct nonempty subsets with one sum dividing the other.\<close>

definition subset_sum_antichain :: "nat set \<Rightarrow> bool" where
  "subset_sum_antichain A \<longleftrightarrow>
    (\<forall>S1\<subseteq>A. \<forall>S2\<subseteq>A. S1 \<noteq> {} \<longrightarrow> S2 \<noteq> {} \<longrightarrow> S1 \<noteq> S2 \<longrightarrow> \<not> (\<Sum>S1) dvd (\<Sum>S2))"

section \<open>Number of ones in binary\<close>

fun pc :: "nat \<Rightarrow> nat" where
  "pc n = (if n = 0 then 0 else n mod 2 + pc (n div 2))"

declare pc.simps [simp del]

lemma pc_0 [simp]: "pc 0 = 0" by (subst pc.simps) simp

lemma split2: fixes a :: nat obtains a' x where "a = 2 * a' + x" "x < 2"
  by (rule that [of "a div 2" "a mod 2"]) simp_all

lemma pc_rec: "x < 2 \<Longrightarrow> pc (2 * a + x) = x + pc a"
proof -
  assume that: "x < 2"
  have d: "(2 * a + x) div 2 = a" and m: "(2 * a + x) mod 2 = x" using that by auto
  show ?thesis
  proof (cases "2 * a + x = 0")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis using d m by (subst pc.simps) simp
  qed
qed

lemma pc_double: "pc (2 * a) = pc a"
  using pc_rec[of 0 a] by simp

lemma pc_one [simp]: "pc 1 = 1"
  using pc_rec[of 1 0] by simp

lemma pc_Suc0 [simp]: "pc (Suc 0) = Suc 0"
  using pc_one by simp

lemma pc_add: "pc (a + b) \<le> pc a + pc b"
proof (induction "a + b" arbitrary: a b rule: less_induct)
  case less
  show ?case
  proof (cases "a + b = 0")
    case True then show ?thesis by simp
  next
    case False
    obtain a' x where a: "a = 2 * a' + x" "x < 2" by (rule split2)
    obtain b' y where b: "b = 2 * b' + y" "y < 2" by (rule split2)
    define c where "c = (x + y) div 2"
    define z where "z = (x + y) mod 2"
    have cz: "x + y = 2 * c + z" "z < 2" "c \<le> 1" unfolding c_def z_def using a(2) b(2) by auto
    have sum: "a + b = 2 * (a' + b' + c) + z" using a b cz by simp
    have lt1: "a' + b' < a + b" using False a b by arith
    have lt2: "a' + b' + c < a + b" using False a b cz by arith
    have h1: "pc (a' + b') \<le> pc a' + pc b'" using less(1)[OF lt1] by blast
    have h2: "pc (a' + b' + c) \<le> pc (a' + b') + pc c"
      by (rule less(1)[OF lt2])
    have pcc: "pc c = c"
    proof -
      have "c = 0 \<or> c = 1" using cz(3) by arith
      then show ?thesis by auto
    qed
    have "pc (a + b) = pc (2 * (a' + b' + c) + z)" using sum by (rule arg_cong)
    also have "\<dots> = z + pc (a' + b' + c)" by (rule pc_rec[OF cz(2)])
    also have "\<dots> \<le> z + (pc a' + pc b') + c" using h1 h2 pcc by simp
    also have "\<dots> \<le> x + pc a' + (y + pc b')" using cz by arith
    also have "\<dots> = pc a + pc b" using pc_rec a b by simp
    finally show ?thesis .
  qed
qed

lemma pc_mult: "pc (q * b) \<le> pc q * pc b"
proof (induction q rule: less_induct)
  case (less q)
  show ?case
  proof (cases "q = 0")
    case True then show ?thesis by simp
  next
    case False
    obtain q' x where q: "q = 2 * q' + x" "x < 2" by (rule split2)
    have lt: "q' < q" using False q by simp
    have eq: "q * b = 2 * (q' * b) + x * b" using q by (simp add: algebra_simps)
    have px: "pc (x * b) \<le> x * pc b"
    proof (cases "x = 0")
      case True then show ?thesis by simp
    next
      case False
      with q(2) have "x = 1" by simp
      then show ?thesis by simp
    qed
    have "pc (q * b) \<le> pc (2 * (q' * b)) + pc (x * b)" using pc_add eq by metis
    also have "\<dots> \<le> pc q' * pc b + x * pc b"
      using less(1)[OF lt] pc_double px by simp
    also have "\<dots> = pc q * pc b" using pc_rec q by (simp add: algebra_simps)
    finally show ?thesis .
  qed
qed

lemma pc_le: "pc q \<le> q"
proof (induction q rule: less_induct)
  case (less q)
  show ?case
  proof (cases "q = 0")
    case True then show ?thesis by simp
  next
    case False
    obtain q' x where q: "q = 2 * q' + x" "x < 2" by (rule split2)
    have "q' < q" using False q by simp
    from less(1)[OF this] show ?thesis using pc_rec q by simp
  qed
qed

lemma pc_less: "q \<ge> 2 \<Longrightarrow> pc q < q"
proof -
  assume that: "q \<ge> 2"
  obtain q' x where q: "q = 2 * q' + x" "x < 2" by (rule split2)
  have "q' \<ge> 1" using that q by simp
  moreover have "pc q' \<le> q'" by (rule pc_le)
  ultimately show ?thesis using pc_rec q by simp
qed

lemma pc_pow_add: "s < 2 ^ m \<Longrightarrow> pc (2 ^ m + s) = Suc (pc s)"
proof (induction m arbitrary: s)
  case 0 then show ?case by (simp add: pc_one)
next
  case (Suc m)
  have e: "2 ^ Suc m + s = 2 * (2 ^ m + s div 2) + s mod 2" by simp
  have lt: "s div 2 < 2 ^ m" using Suc.prems by simp
  have "pc (2 ^ Suc m + s) = pc (2 * (2 ^ m + s div 2) + s mod 2)" using e by (rule arg_cong)
  also have "\<dots> = s mod 2 + pc (2 ^ m + s div 2)" by (rule pc_rec) simp
  also have "\<dots> = s mod 2 + Suc (pc (s div 2))" using Suc.IH[OF lt] by simp
  finally have 1: "pc (2 ^ Suc m + s) = s mod 2 + Suc (pc (s div 2))" .
  have "pc s = pc (2 * (s div 2) + s mod 2)" by simp
  also have "\<dots> = s mod 2 + pc (s div 2)" by (rule pc_rec) simp
  finally show ?case using 1 by simp
qed

section \<open>Sums of distinct powers of two\<close>

lemma bits_sum: "I \<subseteq> {..<m} \<Longrightarrow> (\<Sum>i\<in>I. 2 ^ i :: nat) < 2 ^ m \<and> pc (\<Sum>i\<in>I. 2 ^ i) = card I"
proof (induction m arbitrary: I)
  case 0 then show ?case by simp
next
  case (Suc m)
  let ?J = "I - {m}"
  have J: "?J \<subseteq> {..<m}" using Suc.prems by auto
  from Suc.IH[OF J] have IH: "(\<Sum>i\<in>?J. 2 ^ i :: nat) < 2 ^ m" "pc (\<Sum>i\<in>?J. 2 ^ i) = card ?J" by auto
  show ?case
  proof (cases "m \<in> I")
    case True
    have fin: "finite I" using Suc.prems finite_subset by auto
    have e: "(\<Sum>i\<in>I. 2 ^ i :: nat) = 2 ^ m + (\<Sum>i\<in>?J. 2 ^ i)"
      using sum.remove[OF fin True] by simp
    have c: "card I = Suc (card ?J)" using card_Suc_Diff1[OF fin True] by simp
    show ?thesis using IH pc_pow_add[of _ m] e c by simp
  next
    case False
    hence "?J = I" by auto
    with IH show ?thesis by auto
  qed
qed

lemma bits_inj:
  assumes "I \<subseteq> {..<m}" "J \<subseteq> {..<m}" "(\<Sum>i\<in>I. 2 ^ i :: nat) = (\<Sum>i\<in>J. 2 ^ i)"
  shows "I = J"
  using assms
proof (induction m arbitrary: I J)
  case 0 then show ?case by simp
next
  case (Suc m)
  have fI: "finite I" and fJ: "finite J" using Suc.prems finite_subset by auto
  let ?I = "I - {m}" and ?J = "J - {m}"
  have I': "?I \<subseteq> {..<m}" and J': "?J \<subseteq> {..<m}" using Suc.prems by auto
  have bI: "(\<Sum>i\<in>?I. 2 ^ i :: nat) < 2 ^ m" and bJ: "(\<Sum>i\<in>?J. 2 ^ i :: nat) < 2 ^ m"
    using bits_sum[OF I'] bits_sum[OF J'] by auto
  show ?case
  proof (cases "m \<in> I")
    case mI: True
    have eI: "(\<Sum>i\<in>I. 2 ^ i :: nat) = 2 ^ m + (\<Sum>i\<in>?I. 2 ^ i)" using sum.remove[OF fI mI] by simp
    show ?thesis
    proof (cases "m \<in> J")
      case mJ: True
      have eJ: "(\<Sum>i\<in>J. 2 ^ i :: nat) = 2 ^ m + (\<Sum>i\<in>?J. 2 ^ i)" using sum.remove[OF fJ mJ] by simp
      from Suc.prems(3) eI eJ have "(\<Sum>i\<in>?I. 2 ^ i :: nat) = (\<Sum>i\<in>?J. 2 ^ i)" by simp
      from Suc.IH[OF I' J' this] mI mJ show ?thesis by auto
    next
      case mJ: False
      hence "?J = J" by auto
      with Suc.prems(3) eI bJ show ?thesis by simp
    qed
  next
    case mI: False
    hence IE: "?I = I" by auto
    show ?thesis
    proof (cases "m \<in> J")
      case mJ: True
      have eJ: "(\<Sum>i\<in>J. 2 ^ i :: nat) = 2 ^ m + (\<Sum>i\<in>?J. 2 ^ i)" using sum.remove[OF fJ mJ] by simp
      with Suc.prems(3) IE bI show ?thesis by simp
    next
      case mJ: False
      hence "?J = J" by auto
      with IE Suc.IH[OF I' J'] Suc.prems(3) show ?thesis by simp
    qed
  qed
qed

section \<open>Euclidean uniqueness\<close>

lemma euclid_unique: "a * K + b = c * K + d \<Longrightarrow> b < K \<Longrightarrow> d < K \<Longrightarrow> a = c \<and> b = (d :: nat)"
proof -
  assume e: "a * K + b = c * K + d" and b: "b < K" and d: "d < K"
  have "(a * K + b) div K = a" using b by (simp add: div_nat_eqI)
  moreover have "(c * K + d) div K = c" using d by (simp add: div_nat_eqI)
  ultimately have "a = c" using e by metis
  with e show ?thesis by simp
qed

section \<open>The Sandor set\<close>

definition sf :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "sf m i = 2 ^ i + m * 2 ^ m"

lemma sf_inj: "inj (sf m)" by (auto simp: inj_on_def sf_def)

lemma sigma_image:
  assumes "finite I"
  shows "(\<Sum>(sf m ` I)) = card I * (m * 2 ^ m) + (\<Sum>i\<in>I. 2 ^ i)"
proof -
  have "(\<Sum>(sf m ` I)) = (\<Sum>i\<in>I. sf m i)"
    by (subst sum.reindex[OF inj_on_subset[OF sf_inj subset_UNIV]]) simp
  also have "\<dots> = (\<Sum>i\<in>I. 2 ^ i) + card I * (m * 2 ^ m)" by (simp add: sf_def sum.distrib)
  finally show ?thesis by simp
qed

theorem sandor_antichain:
  assumes "1 \<le> m"
  shows "subset_sum_antichain ((\<lambda>i. 2 ^ i + m * 2 ^ m) ` {..<m})"
  unfolding subset_sum_antichain_def
proof (intro allI impI)
  fix S1 S2 :: "nat set"
  assume h1: "S1 \<subseteq> (\<lambda>i. 2 ^ i + m * 2 ^ m) ` {..<m}" and h2: "S2 \<subseteq> (\<lambda>i. 2 ^ i + m * 2 ^ m) ` {..<m}"
    and ne1: "S1 \<noteq> {}" and ne2: "S2 \<noteq> {}" and neq: "S1 \<noteq> S2"
  have sfd: "(\<lambda>i. 2 ^ i + m * 2 ^ m) = sf m" by (rule ext) (simp add: sf_def)
  define K where "K = m * 2 ^ m"
  have h1': "S1 \<subseteq> sf m ` {..<m}" and h2': "S2 \<subseteq> sf m ` {..<m}" using h1 h2 by (metis sfd)+
  obtain I1 where I1: "I1 \<subseteq> {..<m}" "S1 = sf m ` I1" using h1' by (auto simp: subset_image_iff)
  obtain I2 where I2: "I2 \<subseteq> {..<m}" "S2 = sf m ` I2" using h2' by (auto simp: subset_image_iff)
  have f1: "finite I1" and f2: "finite I2" using I1(1) I2(1) finite_subset by auto
  define t1 where "t1 = card I1"
  define t2 where "t2 = card I2"
  define b1 where "b1 = (\<Sum>i\<in>I1. 2 ^ i :: nat)"
  define b2 where "b2 = (\<Sum>i\<in>I2. 2 ^ i :: nat)"
  have s1: "\<Sum>S1 = t1 * K + b1" using sigma_image[OF f1, of m] I1 unfolding t1_def b1_def K_def by simp
  have s2: "\<Sum>S2 = t2 * K + b2" using sigma_image[OF f2, of m] I2 unfolding t2_def b2_def K_def by simp
  have bb1: "b1 < 2 ^ m" "pc b1 = t1" using bits_sum[OF I1(1)] unfolding b1_def t1_def by auto
  have bb2: "b2 < 2 ^ m" "pc b2 = t2" using bits_sum[OF I2(1)] unfolding b2_def t2_def by auto
  have t1pos: "t1 > 0" using I1 ne1 f1 unfolding t1_def by (auto simp: card_gt_0_iff)
  have t2pos: "t2 > 0" using I2 ne2 f2 unfolding t2_def by (auto simp: card_gt_0_iff)
  have t2m: "t2 \<le> m"
    using card_mono[OF finite_lessThan I2(1)] unfolding t2_def by simp
  have Kpos: "K > 0" using assms unfolding K_def by simp
  have bK: "2 ^ m \<le> K" using assms unfolding K_def by simp
  have b1K: "b1 < K" and b2K: "b2 < K" using bb1 bb2 bK by simp_all
  show "\<not> (\<Sum>S1) dvd (\<Sum>S2)"
  proof
    assume "(\<Sum>S1) dvd (\<Sum>S2)"
    then obtain q where q: "\<Sum>S2 = \<Sum>S1 * q" by auto
    have sp2: "\<Sum>S2 > 0" using s2 t2pos Kpos by simp
    have qpos: "q > 0" using q sp2 by (metis mult_0_right gr0I)
    show False
    proof (cases "q = 1")
      case True
      with q have "\<Sum>S2 = \<Sum>S1" by simp
      with s1 s2 b1K b2K have "t1 = t2 \<and> b1 = b2" using euclid_unique by metis
      hence "I1 = I2" using bits_inj[OF I1(1) I2(1)] unfolding b1_def b2_def by simp
      with I1 I2 neq show False by simp
    next
      case False
      with qpos have q2: "q \<ge> 2" by simp
      have a1: "K \<le> t1 * K" using mult_le_mono1[of 1 t1 K] t1pos by simp
      have a2: "t1 * K \<le> \<Sum>S1" using s1 by simp
      have a3: "K \<le> \<Sum>S1" using a1 a2 by (rule order_trans)
      have "q * K \<le> q * \<Sum>S1" using a3 by (rule mult_le_mono2)
      hence "q * K \<le> \<Sum>S2" using q by (simp add: mult.commute)
      moreover have "\<Sum>S2 < (m + 1) * K"
      proof -
        have "t2 * K + b2 < t2 * K + K" using b2K by simp
        also have "\<dots> = (t2 + 1) * K" by (simp add: algebra_simps)
        also have "\<dots> \<le> (m + 1) * K" using t2m by simp
        finally show ?thesis using s2 by simp
      qed
      ultimately have qKlt: "q * K < (m + 1) * K" by simp
      have qm: "q \<le> m"
      proof (rule ccontr)
        assume "\<not> q \<le> m"
        hence "(m + 1) * K \<le> q * K" by (intro mult_le_mono1) simp
        with qKlt show False by simp
      qed
      have qb: "q * b1 < K"
      proof -
        have "q * b1 < q * 2 ^ m" using bb1 qpos by simp
        also have "\<dots> \<le> m * 2 ^ m" using qm by simp
        finally show ?thesis unfolding K_def .
      qed
      have "(q * t1) * K + q * b1 = t2 * K + b2" using s1 s2 q by (simp add: algebra_simps)
      from euclid_unique[OF this qb b2K] have e: "q * t1 = t2" "q * b1 = b2" by auto
      have "t2 = pc (q * b1)" using e bb2 by simp
      also have "\<dots> \<le> pc q * pc b1" by (rule pc_mult)
      also have "\<dots> = pc q * t1" using bb1 by simp
      also have "\<dots> < q * t1" using pc_less[OF q2] t1pos by simp
      finally show False using e by simp
    qed
  qed
qed

end
