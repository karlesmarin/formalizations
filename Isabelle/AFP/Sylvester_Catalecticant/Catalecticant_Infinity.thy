(*  Title:      Catalecticant_Infinity.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

theory Catalecticant_Infinity
  imports Catalecticant_Converse
begin

section \<open>Sylvester's catalecticant: the converse with a point at infinity\<close>

text \<open>
  Points @{text "(\<alpha>_k : \<beta>_k) \<noteq> (0:0)"}, pairwise distinct as projective points.
  At most one has @{text "\<beta> = 0"} (the point @{text "(1:0)"}).  Then
  @{text "h(\<alpha>,\<beta>) = \<Sum> c_l \<alpha>^{r-l}\<beta>^l"} vanishes at it iff @{text "c_0 = 0"}, so the
  hypothesis @{text "c_0 \<noteq> 0"} of the finite case is replaced by the natural one:
  @{text "h"} is not identically zero (some @{text "c_l \<noteq> 0"}).  In the finite case
  it implies @{text "c_0 \<noteq> 0"} (r distinct roots of a nonzero polynomial of degree
  at most r); with a point at infinity it gives @{text "c_{l+1} \<noteq> 0"} for some l.
  The term of the point at infinity in @{text "a_i = \<Sum> \<lambda>_k \<alpha>_k^{n-i}\<beta>_k^i"} is
  non-zero only for @{text "i = 0"}.  Reduction: @{text "h = y \<cdot> h_1"}, with
  @{text "h_1"} of order @{text "r-1"}, applied to the sequence @{text "i \<mapsto> a_{i+1}"}.
\<close>

lemma proj_hz_affine:
  fixes al be :: "nat \<Rightarrow> 'a::field" and c :: "nat \<Rightarrow> 'a"
  assumes bk: "be k \<noteq> 0"
    and hz: "(\<Sum>l\<in>{..r}. c l * al k ^ (r - l) * be k ^ l) = 0"
  shows "(\<Sum>l\<in>{..r}. c l * (al k / be k) ^ (r - l)) = 0"
proof -
  have "be k ^ r * (\<Sum>l\<in>{..r}. c l * (al k / be k) ^ (r - l))
      = (\<Sum>l\<in>{..r}. c l * al k ^ (r - l) * be k ^ l)"
    unfolding sum_distrib_left
  proof (rule sum.cong[OF refl])
    fix l assume "l \<in> {..r}"
    then have "r = (r - l) + l" by auto
    then have "be k ^ r = be k ^ (r - l) * be k ^ l"
      by (metis power_add)
    then show "be k ^ r * (c l * (al k / be k) ^ (r - l)) = c l * al k ^ (r - l) * be k ^ l"
      using bk by (simp add: power_divide field_simps)
  qed
  also have "\<dots> = 0" by (rule hz)
  finally show ?thesis using bk by simp
qed

lemma c0_nonzero_affine:
  fixes t :: "nat \<Rightarrow> 'a::field" and c :: "nat \<Rightarrow> 'a"
  assumes inj: "inj_on t {..<r}"
    and hz: "\<And>k. k < r \<Longrightarrow> (\<Sum>l\<in>{..r}. c l * t k ^ (r - l)) = 0"
    and cnz: "\<exists>l\<le>r. c l \<noteq> 0"
  shows "c 0 \<noteq> 0"
proof -
  define h where "h = (\<Sum>i\<le>r. monom (c (r - i)) i)"
  define P where "P = (\<Prod>k<r. [:-t k, 1:])"
  have coh: "\<And>i. coeff h i = (if i \<le> r then c (r - i) else 0)"
    by (simp add: h_def coeff_sum coeff_monom)
  have ph: "\<And>x. poly h x = (\<Sum>l\<in>{..r}. c l * x ^ (r - l))"
  proof -
    fix x
    have "poly h x = (\<Sum>i\<le>r. c (r - i) * x ^ i)"
      by (simp add: h_def poly_sum poly_monom)
    also have "\<dots> = (\<Sum>i\<le>r. (\<lambda>l. c l * x ^ (r - l)) (r - i))"
      by (rule sum.cong[OF refl]) auto
    also have "\<dots> = (\<Sum>l\<le>r. c l * x ^ (r - l))" by (rule reflect_sum)
    finally show "poly h x = (\<Sum>l\<in>{..r}. c l * x ^ (r - l))" .
  qed
  have dh: "degree h \<le> r" by (rule degree_le) (simp add: coh)
  obtain l where l: "l \<le> r" "c l \<noteq> 0" using cnz by blast
  have h0: "h \<noteq> 0"
  proof
    assume "h = 0"
    then have "coeff h (r - l) = 0" by simp
    then show False using coh l by simp
  qed
  have "P dvd h" unfolding P_def
    by (rule prod_lin_dvd[OF inj]) (simp add: ph hz)
  then obtain q where hq: "h = P * q" by blast
  have Pn: "P \<noteq> 0" and Pd: "degree P = r" using prod_lin_degree[of t r] by (simp_all add: P_def)
  have q0: "q \<noteq> 0" using h0 hq by auto
  have "degree h = r + degree q" using hq Pd Pn q0 by (simp add: degree_mult_eq)
  then have dr: "degree h = r" using dh by simp
  have "coeff h (degree h) \<noteq> 0" using h0 by simp
  then have "coeff h r \<noteq> 0" using dr by simp
  then show ?thesis using coh by simp
qed

theorem projective_cnz:
  fixes al be :: "nat \<Rightarrow> 'a::field" and c a :: "nat \<Rightarrow> 'a"
  assumes be0: "\<And>k. k < r \<Longrightarrow> be k \<noteq> 0"
    and dist: "\<And>j k. j < r \<Longrightarrow> k < r \<Longrightarrow> j \<noteq> k \<Longrightarrow> al j * be k \<noteq> al k * be j"
    and cnz: "\<exists>l\<le>r. c l \<noteq> 0" and rn: "r \<le> n"
    and hz: "\<And>k. k < r \<Longrightarrow> (\<Sum>l\<in>{..r}. c l * al k ^ (r - l) * be k ^ l) = 0"
    and rec: "\<And>j. j + r \<le> n \<Longrightarrow> (\<Sum>l\<in>{..r}. a (j + l) * c l) = 0"
  shows "\<exists>mu. \<forall>i\<le>n. a i = coef_pow mu al be {..<r} n i"
proof -
  define t where "t = (\<lambda>k. al k / be k)"
  have inj: "inj_on t {..<r}"
  proof (rule inj_onI)
    fix j k assume jk: "j \<in> {..<r}" "k \<in> {..<r}" "t j = t k"
    then have "al j * be k = al k * be j"
      using be0 by (simp add: t_def field_simps)
    then show "j = k" using dist jk by auto
  qed
  have hz': "\<And>k. k < r \<Longrightarrow> (\<Sum>l\<in>{..r}. c l * t k ^ (r - l)) = 0"
    unfolding t_def by (rule proj_hz_affine[OF be0 hz])
  have c0: "c 0 \<noteq> 0" by (rule c0_nonzero_affine[OF inj hz' cnz])
  show ?thesis by (rule catalecticant_converse_projective[OF be0 dist c0 rn hz rec])
qed

definition skip :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "skip k0 k = (if k < k0 then k else Suc k)"

lemma skip_inj: "skip k0 j = skip k0 k \<Longrightarrow> j = k"
  unfolding skip_def by (auto split: if_splits)

lemma skip_lt: "k < m \<Longrightarrow> k0 < Suc m \<Longrightarrow> skip k0 k < Suc m \<and> skip k0 k \<noteq> k0"
  unfolding skip_def by (auto split: if_splits)

lemma skip_image: "k0 < Suc m \<Longrightarrow> skip k0 ` {..<m} = {..<Suc m} - {k0}"
proof (rule set_eqI)
  fix x assume k0: "k0 < Suc m"
  show "x \<in> skip k0 ` {..<m} \<longleftrightarrow> x \<in> {..<Suc m} - {k0}"
  proof
    assume "x \<in> skip k0 ` {..<m}"
    then obtain k where "k < m" "x = skip k0 k" by blast
    then show "x \<in> {..<Suc m} - {k0}" using skip_lt k0 by auto
  next
    assume x: "x \<in> {..<Suc m} - {k0}"
    show "x \<in> skip k0 ` {..<m}"
    proof (cases "x < k0")
      case True
      then have "x = skip k0 x" "x < m" using k0 by (simp_all add: skip_def)
      then show ?thesis by blast
    next
      case False
      then have "k0 < x" using x by auto
      then obtain y where y: "x = Suc y" using Suc_lessD by (metis less_imp_Suc_add)
      have "y < m" using x y by simp
      moreover have "skip k0 y = x" using y \<open>k0 < x\<close> unfolding skip_def by simp
      ultimately show ?thesis by blast
    qed
  qed
qed

theorem catalecticant_converse_projective_full:
  fixes al be :: "nat \<Rightarrow> 'a::field" and c a :: "nat \<Rightarrow> 'a"
  assumes pt: "\<And>k. k < r \<Longrightarrow> al k \<noteq> 0 \<or> be k \<noteq> 0"
    and dist: "\<And>j k. j < r \<Longrightarrow> k < r \<Longrightarrow> j \<noteq> k \<Longrightarrow> al j * be k \<noteq> al k * be j"
    and cnz: "\<exists>l\<le>r. c l \<noteq> 0" and rn: "r \<le> n"
    and hz: "\<And>k. k < r \<Longrightarrow> (\<Sum>l\<in>{..r}. c l * al k ^ (r - l) * be k ^ l) = 0"
    and rec: "\<And>j. j + r \<le> n \<Longrightarrow> (\<Sum>l\<in>{..r}. a (j + l) * c l) = 0"
  shows "\<exists>mu. \<forall>i\<le>n. a i = coef_pow mu al be {..<r} n i"
proof (cases "\<forall>k<r. be k \<noteq> 0")
  case True
  show ?thesis
    by (rule projective_cnz[OF _ dist cnz rn hz rec]) (use True in auto)
next
  case False
  then obtain k0 where k0: "k0 < r" and b0: "be k0 = 0" by auto
  have a0: "al k0 \<noteq> 0" using pt k0 b0 by blast
  have bne: "\<And>k. k < r \<Longrightarrow> k \<noteq> k0 \<Longrightarrow> be k \<noteq> 0"
  proof
    fix k assume k: "k < r" "k \<noteq> k0" and bk: "be k = 0"
    have "al k * be k0 \<noteq> al k0 * be k" by (rule dist[OF k(1) k0 k(2)])
    then show False using b0 bk by simp
  qed
  obtain m where rm: "r = Suc m" using k0 by (metis less_imp_Suc_add less_Suc_eq_0_disj not0_implies_Suc)
  have k0m: "k0 < Suc m" using k0 rm by simp
  \<comment> \<open>c 0 = 0: the point at infinity is a root\<close>
  have c0z: "c 0 = 0"
  proof -
    have "(\<Sum>l\<in>{..Suc m}. c l * al k0 ^ (Suc m - l) * be k0 ^ l) = 0"
      using hz[OF k0] rm by simp
    then have "c 0 * al k0 ^ Suc m = 0" using b0 by (simp add: sum.atMost_Suc_shift)
    then show ?thesis using a0 by simp
  qed
  have nm: "Suc m \<le> n" using rn rm by simp
  define sg where "sg = skip k0"
  define al' where "al' = (\<lambda>k. al (sg k))"
  define be' where "be' = (\<lambda>k. be (sg k))"
  define c' where "c' = (\<lambda>l. c (Suc l))"
  define a' where "a' = (\<lambda>i. a (Suc i))"
  have sgl: "\<And>k. k < m \<Longrightarrow> sg k < r \<and> sg k \<noteq> k0"
    using skip_lt[OF _ k0m] rm sg_def by auto
  have sgi: "\<And>j k. sg j = sg k \<Longrightarrow> j = k" using skip_inj sg_def by simp
  have be0': "\<And>k. k < m \<Longrightarrow> be' k \<noteq> 0"
    unfolding be'_def using bne sgl by blast
  have dist': "\<And>j k. j < m \<Longrightarrow> k < m \<Longrightarrow> j \<noteq> k \<Longrightarrow> al' j * be' k \<noteq> al' k * be' j"
    unfolding al'_def be'_def using dist sgl sgi by blast
  have cnz': "\<exists>l\<le>m. c' l \<noteq> 0"
  proof -
    obtain l where l: "l \<le> r" "c l \<noteq> 0" using cnz by blast
    have "l \<noteq> 0"
    proof
      assume "l = 0"
      then show False using l(2) c0z by simp
    qed
    then obtain l' where "l = Suc l'" by (metis not0_implies_Suc)
    then show ?thesis using l rm unfolding c'_def by auto
  qed
  have rn': "m \<le> n - 1" using nm by simp
  have hz': "\<And>k. k < m \<Longrightarrow> (\<Sum>l\<in>{..m}. c' l * al' k ^ (m - l) * be' k ^ l) = 0"
  proof -
    fix k assume k: "k < m"
    have s: "sg k < r" using sgl[OF k] by simp
    have h1: "(\<Sum>l\<in>{..r}. c l * al (sg k) ^ (r - l) * be (sg k) ^ l) = 0" by (rule hz[OF s])
    have h2: "(\<Sum>l\<in>{..Suc m}. c l * al (sg k) ^ (Suc m - l) * be (sg k) ^ l) = 0"
      using h1 by (simp only: rm)
    have h3: "c 0 * al (sg k) ^ (Suc m - 0) * be (sg k) ^ 0
        + (\<Sum>l\<in>{..m}. c (Suc l) * al (sg k) ^ (Suc m - Suc l) * be (sg k) ^ Suc l) = 0"
      using h2 by (simp only: sum.atMost_Suc_shift)
    have "(\<Sum>l\<in>{..m}. c (Suc l) * al (sg k) ^ (m - l) * be (sg k) ^ Suc l) = 0"
      using h3 c0z by simp
    then have "be (sg k) * (\<Sum>l\<in>{..m}. c' l * al' k ^ (m - l) * be' k ^ l) = 0"
      by (simp add: sum_distrib_left c'_def al'_def be'_def algebra_simps)
    then show "(\<Sum>l\<in>{..m}. c' l * al' k ^ (m - l) * be' k ^ l) = 0"
      using be0'[OF k] unfolding be'_def by simp
  qed
  have rec': "\<And>j. j + m \<le> n - 1 \<Longrightarrow> (\<Sum>l\<in>{..m}. a' (j + l) * c' l) = 0"
  proof -
    fix j assume j: "j + m \<le> n - 1"
    have jr: "j + r \<le> n" using j nm rm by simp
    have h1: "(\<Sum>l\<in>{..r}. a (j + l) * c l) = 0" by (rule rec[OF jr])
    have h2: "(\<Sum>l\<in>{..Suc m}. a (j + l) * c l) = 0" using h1 by (simp only: rm)
    have h3: "a (j + 0) * c 0 + (\<Sum>l\<in>{..m}. a (j + Suc l) * c (Suc l)) = 0"
      using h2 by (simp only: sum.atMost_Suc_shift)
    have "(\<Sum>l\<in>{..m}. a (j + Suc l) * c (Suc l)) = 0"
      using h3 c0z by simp
    then show "(\<Sum>l\<in>{..m}. a' (j + l) * c' l) = 0"
      by (simp add: a'_def c'_def)
  qed
  obtain nu where nu: "\<forall>i\<le>n - 1. a' i = coef_pow nu al' be' {..<m} (n - 1) i"
    using projective_cnz[where al = al' and be = be' and c = c' and a = a' and r = m and n = "n - 1",
        OF be0' dist' cnz' rn' hz' rec'] by blast
  define tau where "tau = (\<lambda>k. if k < k0 then k else k - 1)"
  have tau_sg: "\<And>k. k < m \<Longrightarrow> tau (sg k) = k"
    unfolding tau_def sg_def skip_def by auto
  define S where "S = (\<Sum>k<m. nu k / be' k * al' k ^ n)"
  define M0 where "M0 = (a 0 - S) / al k0 ^ n"
  define mu where "mu = (\<lambda>k. if k = k0 then M0 else nu (tau k) / be k)"
  have mu_sg: "\<And>k. k < m \<Longrightarrow> mu (sg k) = nu k / be' k"
    using sgl tau_sg unfolding mu_def be'_def by auto
  have split: "\<And>f :: nat \<Rightarrow> 'a. (\<Sum>k<r. f k) = f k0 + (\<Sum>k<m. f (sg k))"
  proof -
    fix f :: "nat \<Rightarrow> 'a"
    have inj: "inj_on sg {..<m}" using sgi by (auto simp: inj_on_def)
    have im: "sg ` {..<m} = {..<r} - {k0}" using skip_image[OF k0m] rm sg_def by simp
    have "(\<Sum>k<r. f k) = f k0 + (\<Sum>k\<in>{..<r} - {k0}. f k)"
      by (rule sum.remove) (use k0 in auto)
    moreover have "(\<Sum>k\<in>{..<r} - {k0}. f k) = (\<Sum>k<m. f (sg k))"
    proof -
      have "(\<Sum>k\<in>{..<r} - {k0}. f k) = (\<Sum>k\<in>sg ` {..<m}. f k)" using im by simp
      also have "\<dots> = (\<Sum>k<m. f (sg k))" using sum.reindex[OF inj, of f] by simp
      finally show ?thesis .
    qed
    ultimately show "(\<Sum>k<r. f k) = f k0 + (\<Sum>k<m. f (sg k))" by simp
  qed
  have "\<forall>i\<le>n. a i = coef_pow mu al be {..<r} n i"
  proof (intro allI impI)
    fix i assume i: "i \<le> n"
    have cp: "coef_pow mu al be {..<r} n i
        = mu k0 * al k0 ^ (n - i) * be k0 ^ i
          + (\<Sum>k<m. mu (sg k) * al' k ^ (n - i) * be' k ^ i)"
      unfolding coef_pow_def by (subst split) (simp add: al'_def be'_def)
    show "a i = coef_pow mu al be {..<r} n i"
    proof (cases i)
      case 0
      have "(\<Sum>k<m. mu (sg k) * al' k ^ (n - 0) * be' k ^ 0) = S"
        unfolding S_def by (rule sum.cong[OF refl]) (simp add: mu_sg)
      moreover have "mu k0 * al k0 ^ (n - 0) * be k0 ^ 0 = a 0 - S"
        using a0 by (simp add: mu_def M0_def)
      ultimately show ?thesis using cp 0 by simp
    next
      case (Suc i')
      have i': "i' \<le> n - 1" using i Suc by simp
      have e0: "mu k0 * al k0 ^ (n - i) * be k0 ^ i = 0" using b0 Suc by simp
      have "(\<Sum>k<m. mu (sg k) * al' k ^ (n - i) * be' k ^ i)
          = (\<Sum>k<m. nu k * al' k ^ (n - 1 - i') * be' k ^ i')"
      proof (rule sum.cong[OF refl])
        fix k assume "k \<in> {..<m}"
        then have km: "k < m" by simp
        have bk: "be' k \<noteq> 0" by (rule be0'[OF km])
        have mk: "mu (sg k) = nu k / be' k" by (rule mu_sg[OF km])
        have ni: "n - i = n - 1 - i'" using Suc by simp
        have "mu (sg k) * al' k ^ (n - i) * be' k ^ i
            = nu k / be' k * al' k ^ (n - 1 - i') * (be' k * be' k ^ i')"
          using mk ni Suc by simp
        also have "\<dots> = nu k * al' k ^ (n - 1 - i') * be' k ^ i'"
          using bk by (simp add: field_simps)
        finally show "mu (sg k) * al' k ^ (n - i) * be' k ^ i
            = nu k * al' k ^ (n - 1 - i') * be' k ^ i'" .
      qed
      also have "\<dots> = a' i'" using nu i' by (simp add: coef_pow_def)
      finally show ?thesis using cp e0 Suc by (simp add: a'_def)
    qed
  qed
  then show ?thesis by blast
qed

end
