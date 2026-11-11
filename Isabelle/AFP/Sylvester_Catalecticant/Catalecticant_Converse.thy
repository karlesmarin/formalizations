(*  Title:      Catalecticant_Converse.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

theory Catalecticant_Converse
  imports Catalecticant "HOL-Computational_Algebra.Polynomial"
begin

section \<open>Sylvester's catalecticant: the converse (sufficiency), affine case\<close>

text \<open>
  Setting.  Points @{text "(t_k : 1)"}, @{text "k < r"}, pairwise distinct
  (the affine chart @{text "\<beta>_k = 1"}), @{text "h(x) = \<Sum>_l c_l x^{r-l}"} vanishing at all
  @{text "t_k"} with @{text "c_0 \<noteq> 0"} (so @{text h} has degree exactly @{text r} and,
  having @{text r} distinct roots, is @{text "c_0 \<Prod>_k (x - t_k)"}).  If
  @{text "\<Sum>_l a_{j+l} c_l = 0"} for @{text "j + r \<le> n"}, then there are
  @{text "\<lambda>_k"} with @{text "a_i = \<Sum>_k \<lambda>_k t_k^{n-i}"}.

  Route (no Vandermonde determinant): induction on @{text r}.  Peeling one root
  @{text "t_r"} turns the sequence @{text b} into @{text "b'(u) = b(u+1) - t_r b(u)"},
  which satisfies the recurrence of the product of the other factors; the
  difference @{text "b - \<Sum> \<lambda>_k t_k^s"} is then geometric of ratio @{text "t_r"}.
  The recurrence is encoded by the linear functional @{text "lfun b s p"} on
  polynomials, with @{text "lfun b s (p * (X - t)) = lfun b' s p"}.
\<close>

definition lfun :: "(nat \<Rightarrow> 'a::comm_ring_1) \<Rightarrow> nat \<Rightarrow> 'a poly \<Rightarrow> 'a" where
  "lfun b s p = (\<Sum>i\<le>degree p. coeff p i * b (s + i))"

lemma lfun_gen:
  assumes "degree p \<le> d"
  shows "lfun b s p = (\<Sum>i\<le>d. coeff p i * b (s + i))"
  unfolding lfun_def
  using assms by (intro sum.mono_neutral_left) (auto simp: coeff_eq_0)

lemma lin_factor_eq:
  fixes t :: "'a::comm_ring_1"
  shows "[:-t, 1:] = [:0, 1:] - [:t:]"
  by (rule poly_eqI) (simp add: coeff_pCons split: nat.split)

lemma const_mult_poly: "[:t:] * p = smult t p"
  by (simp add: mult_pCons_left)

lemma lfun_mult_lin:
  fixes b :: "nat \<Rightarrow> 'a::idom"
  shows "lfun b s (p * [:-t, 1:]) = lfun (\<lambda>u. b (Suc u) - t * b u) s p"
proof -
  define d where "d = degree p"
  have q: "p * [:-t, 1:] = pCons 0 p - smult t p"
  proof -
    have "p * [:-t, 1:] = smult (-t) p + pCons 0 p" by (simp add: mult_pCons_right)
    also have "\<dots> = pCons 0 p - smult t p" by (simp add: smult_minus_left)
    finally show ?thesis .
  qed
  have d1: "degree (pCons 0 p) \<le> Suc d" unfolding d_def by (rule degree_pCons_le)
  have d2: "degree (smult t p) \<le> Suc d"
    using degree_smult_le[of t p] unfolding d_def by simp
  have dq: "degree (p * [:-t, 1:]) \<le> Suc d"
    unfolding q by (rule degree_diff_le[OF d1 d2])
  have cz: "coeff p (Suc d) = 0" unfolding d_def by (simp add: coeff_eq_0)
  have "lfun b s (p * [:-t, 1:]) = (\<Sum>i\<le>Suc d. coeff (p * [:-t, 1:]) i * b (s + i))"
    by (rule lfun_gen[OF dq])
  also have "\<dots> = (\<Sum>i\<le>Suc d. coeff (pCons 0 p) i * b (s + i)) - t * (\<Sum>i\<le>Suc d. coeff p i * b (s + i))"
    by (simp add: q coeff_diff algebra_simps sum_subtractf sum_distrib_left)
  also have "(\<Sum>i\<le>Suc d. coeff (pCons 0 p) i * b (s + i)) = (\<Sum>i\<le>d. coeff p i * b (Suc (s + i)))"
    by (subst sum.atMost_Suc_shift) simp
  also have "(\<Sum>i\<le>Suc d. coeff p i * b (s + i)) = (\<Sum>i\<le>d. coeff p i * b (s + i))"
    using cz by simp
  also have "(\<Sum>i\<le>d. coeff p i * b (Suc (s + i))) - t * (\<Sum>i\<le>d. coeff p i * b (s + i))
      = (\<Sum>i\<le>d. coeff p i * (b (Suc (s + i)) - t * b (s + i)))"
    by (simp add: algebra_simps sum_subtractf sum_distrib_left)
  also have "\<dots> = lfun (\<lambda>u. b (Suc u) - t * b u) s p"
    unfolding lfun_def d_def by simp
  finally show ?thesis .
qed

lemma lfun_smult:
  shows "lfun b s (smult e p) = e * lfun b s p"
proof -
  have "lfun b s (smult e p) = (\<Sum>i\<le>degree p. coeff (smult e p) i * b (s + i))"
    by (rule lfun_gen[OF degree_smult_le])
  then show ?thesis
    by (simp add: lfun_def sum_distrib_left algebra_simps)
qed

lemma lfun_one: "lfun b s 1 = b s"
  by (simp add: lfun_def)

theorem recurrence_solution:
  fixes t :: "nat \<Rightarrow> 'a::field" and b :: "nat \<Rightarrow> 'a"
  shows "inj_on t {..<r} \<Longrightarrow> r \<le> M \<Longrightarrow>
     (\<And>s. s + r < M \<Longrightarrow> lfun b s (\<Prod>k<r. [:-t k, 1:]) = 0) \<Longrightarrow>
     \<exists>lam. \<forall>s<M. b s = (\<Sum>k<r. lam k * t k ^ s)"
proof (induction r arbitrary: b M)
  case 0
  then show ?case by (simp add: lfun_one)
next
  case (Suc r)
  define b' where "b' = (\<lambda>u. b (Suc u) - t r * b u)"
  have inj': "inj_on t {..<r}" using Suc.prems(1) by (auto simp: inj_on_def)
  have rM: "r \<le> M - 1" using Suc.prems(2) by simp
  have rec': "lfun b' s (\<Prod>k<r. [:-t k, 1:]) = 0" if s: "s + r < M - 1" for s
  proof -
    have "lfun b' s (\<Prod>k<r. [:-t k, 1:]) = lfun b s ((\<Prod>k<r. [:-t k, 1:]) * [:-t r, 1:])"
      unfolding b'_def by (rule lfun_mult_lin[symmetric])
    also have "\<dots> = lfun b s (\<Prod>k<Suc r. [:-t k, 1:])" by (simp only: prod.lessThan_Suc)
    also have "\<dots> = 0"
    proof (rule Suc.prems(3))
      show "s + Suc r < M" using s by simp
    qed
    finally show "lfun b' s (\<Prod>k<r. [:-t k, 1:]) = 0" .
  qed
  obtain mu where mu: "\<forall>s<M - 1. b' s = (\<Sum>k<r. mu k * t k ^ s)"
    using Suc.IH[OF inj' rM rec'] by blast
  define lam where "lam = (\<lambda>k. mu k / (t k - t r))"
  have ne: "t k - t r \<noteq> 0" if k: "k < r" for k
  proof -
    have "t k \<noteq> t r" using Suc.prems(1) k by (auto simp: inj_on_def)
    then show "t k - t r \<noteq> 0" by simp
  qed
  have lm: "\<And>k. k < r \<Longrightarrow> lam k * (t k - t r) = mu k"
    using ne by (simp add: lam_def)
  define d where "d = (\<lambda>s. b s - (\<Sum>k<r. lam k * t k ^ s))"
  have step: "d (Suc s) = t r * d s" if s: "s < M - 1" for s
  proof -
    have "(\<Sum>k<r. lam k * t k ^ Suc s) - t r * (\<Sum>k<r. lam k * t k ^ s)
        = (\<Sum>k<r. lam k * (t k - t r) * t k ^ s)"
      by (simp add: sum_distrib_left sum_subtractf algebra_simps)
    also have "\<dots> = (\<Sum>k<r. mu k * t k ^ s)"
      by (rule sum.cong[OF refl]) (simp add: lm)
    finally have e: "(\<Sum>k<r. lam k * t k ^ Suc s) - t r * (\<Sum>k<r. lam k * t k ^ s)
        = (\<Sum>k<r. mu k * t k ^ s)" .
    have "b' s = (\<Sum>k<r. mu k * t k ^ s)" using mu s by blast
    then show "d (Suc s) = t r * d s"
      using e by (simp add: d_def b'_def algebra_simps)
  qed
  have geo: "\<And>s. s < M \<Longrightarrow> d s = d 0 * t r ^ s"
  proof -
    fix s show "s < M \<Longrightarrow> d s = d 0 * t r ^ s"
    proof (induction s)
      case 0 then show ?case by simp
    next
      case (Suc s)
      then have "s < M - 1" by simp
      then show ?case using step Suc.IH Suc.prems by (simp add: algebra_simps)
    qed
  qed
  define lam' where "lam' = (\<lambda>k. if k = r then d 0 else lam k)"
  have "\<forall>s<M. b s = (\<Sum>k<Suc r. lam' k * t k ^ s)"
  proof (intro allI impI)
    fix s assume s: "s < M"
    have "(\<Sum>k<r. lam' k * t k ^ s) = (\<Sum>k<r. lam k * t k ^ s)"
      by (rule sum.cong[OF refl]) (simp add: lam'_def)
    then show "b s = (\<Sum>k<Suc r. lam' k * t k ^ s)"
      using geo[OF s] by (simp add: d_def lam'_def algebra_simps)
  qed
  then show ?case by blast
qed

text \<open>Auxiliary facts on the product of the linear factors.\<close>

lemma prod_lin_degree:
  fixes t :: "nat \<Rightarrow> 'a::idom"
  shows "(\<Prod>k<m. [:-t k, 1:]) \<noteq> 0 \<and> degree (\<Prod>k<m. [:-t k, 1:]) = m"
proof (induction m)
  case 0 then show ?case by simp
next
  case (Suc m)
  have e: "(\<Prod>k<Suc m. [:-t k, 1:]) = (\<Prod>k<m. [:-t k, 1:]) * [:-t m, 1:]"
    by (rule prod.lessThan_Suc)
  have x0: "[:-t m, 1:] \<noteq> 0" by simp
  have dx: "degree [:-t m, 1:] = 1" by simp
  have nz: "(\<Prod>k<m. [:-t k, 1:]) * [:-t m, 1:] \<noteq> 0"
    using Suc.IH x0 by (metis mult_eq_0_iff)
  have "degree ((\<Prod>k<m. [:-t k, 1:]) * [:-t m, 1:])
      = degree (\<Prod>k<m. [:-t k, 1:]) + degree [:-t m, 1:]"
    by (rule degree_mult_eq) (use Suc.IH x0 in auto)
  then show ?case using nz Suc.IH dx e by simp
qed

lemma reflect_sum:
  fixes r :: nat and f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>i\<le>r. f (r - i)) = (\<Sum>l\<le>r. f l)"
proof (rule sum.reindex_bij_witness[where i = "\<lambda>i. r - i" and j = "\<lambda>i. r - i"])
  fix a assume "a \<in> {..r}" then show "r - (r - a) = a" by (auto simp: diff_diff_cancel)
next
  fix a assume "a \<in> {..r}" then show "r - a \<in> {..r}" by simp
next
  fix a assume "a \<in> {..r}" then show "r - (r - a) = a" by (auto simp: diff_diff_cancel)
next
  fix a assume "a \<in> {..r}" then show "r - a \<in> {..r}" by simp
next
  fix a assume "a \<in> {..r}" then show "f (r - a) = f (r - a)" by simp
qed

lemma prod_lin_dvd:
  fixes t :: "nat \<Rightarrow> 'a::field" and h :: "'a poly"
  assumes inj: "inj_on t {..<r}" and hz: "\<And>k. k < r \<Longrightarrow> poly h (t k) = 0"
  shows "(\<Prod>k<r. [:-t k, 1:]) dvd h"
proof -
  have "m \<le> r \<Longrightarrow> (\<Prod>k<m. [:-t k, 1:]) dvd h" for m
  proof (induction m)
    case 0 then show ?case by simp
  next
    case (Suc m)
    then have mr: "m < r" and ih: "(\<Prod>k<m. [:-t k, 1:]) dvd h" by simp_all
    obtain q where hq: "h = (\<Prod>k<m. [:-t k, 1:]) * q" using ih by blast
    have pn: "poly (\<Prod>k<m. [:-t k, 1:]) (t m) \<noteq> 0"
    proof
      assume "poly (\<Prod>k<m. [:-t k, 1:]) (t m) = 0"
      then obtain k where k: "k < m" "t m - t k = 0"
        by (auto simp: poly_prod prod_zero_iff)
      then have "t m = t k" by simp
      then have "m = k" by (rule inj_onD[OF inj]) (use k mr in auto)
      then show False using k(1) by simp
    qed
    have "poly h (t m) = 0" using hz mr by blast
    then have "poly q (t m) = 0" using pn by (simp add: hq)
    then have "[:-t m, 1:] dvd q" by (simp add: poly_eq_0_iff_dvd)
    then have "(\<Prod>k<m. [:-t k, 1:]) * [:-t m, 1:] dvd (\<Prod>k<m. [:-t k, 1:]) * q"
      by (intro mult_dvd_mono) simp
    then show ?case using hq by simp
  qed
  then show ?thesis by simp
qed

theorem catalecticant_converse_affine:
  fixes t :: "nat \<Rightarrow> 'a::field" and c a :: "nat \<Rightarrow> 'a"
  assumes inj: "inj_on t {..<r}" and c0: "c 0 \<noteq> 0" and rn: "r \<le> n"
    and hz: "\<And>k. k < r \<Longrightarrow> (\<Sum>l\<in>{..r}. c l * t k ^ (r - l)) = 0"
    and rec: "\<And>j. j + r \<le> n \<Longrightarrow> (\<Sum>l\<in>{..r}. a (j + l) * c l) = 0"
  shows "\<exists>lam. \<forall>i\<le>n. a i = coef_pow lam t (\<lambda>_. 1) {..<r} n i"
proof -
  define h where "h = (\<Sum>i\<le>r. monom (c (r - i)) i)"
  define P where "P = (\<Prod>k<r. [:-t k, 1:])"
  have coh: "\<And>i. coeff h i = (if i \<le> r then c (r - i) else 0)"
    by (simp add: h_def coeff_sum coeff_monom)
  have ph: "poly h x = (\<Sum>l\<in>{..r}. c l * x ^ (r - l))" for x
  proof -
    have "poly h x = (\<Sum>i\<le>r. c (r - i) * x ^ i)"
      by (simp add: h_def poly_sum poly_monom)
    also have "\<dots> = (\<Sum>i\<le>r. (\<lambda>l. c l * x ^ (r - l)) (r - i))"
      by (rule sum.cong[OF refl]) auto
    also have "\<dots> = (\<Sum>l\<le>r. c l * x ^ (r - l))" by (rule reflect_sum)
    finally show "poly h x = (\<Sum>l\<in>{..r}. c l * x ^ (r - l))" .
  qed
  have dh: "degree h \<le> r" by (rule degree_le) (simp add: coh)
  have h0: "h \<noteq> 0"
  proof
    assume "h = 0" then have "coeff h r = 0" by simp
    then show False using coh c0 by simp
  qed
  have "P dvd h" unfolding P_def
    by (rule prod_lin_dvd[OF inj]) (simp add: ph hz)
  then obtain q where hq: "h = P * q" by blast
  have Pn: "P \<noteq> 0" and Pd: "degree P = r" using prod_lin_degree[of t r] by (simp_all add: P_def)
  have q0: "q \<noteq> 0" using h0 hq by auto
  have "degree h = r + degree q" using hq Pd Pn q0 by (simp add: degree_mult_eq)
  then have "degree q = 0" using dh by simp
  then obtain e where qe: "q = [:e:]" by (rule degree_eq_zeroE)
  then have e0: "e \<noteq> 0" using q0 by auto
  have hP: "h = smult e P" using hq qe by (simp add: mult.commute)
  define b where "b = (\<lambda>u. a (n - u))"
  have recb: "lfun b s P = 0" if s: "s + r < n + 1" for s
  proof -
    define j where "j = n - s - r"
    have jr: "j + r \<le> n" using s j_def by simp
    have "lfun b s h = (\<Sum>i\<le>r. coeff h i * b (s + i))" by (rule lfun_gen[OF dh])
    also have "\<dots> = (\<Sum>i\<le>r. c (r - i) * a (n - (s + i)))"
      by (rule sum.cong[OF refl]) (simp add: coh b_def)
    also have "\<dots> = (\<Sum>i\<le>r. (\<lambda>l. a (j + l) * c l) (r - i))"
    proof (rule sum.cong[OF refl])
      fix i assume "i \<in> {..r}"
      then have "n - (s + i) = j + (r - i)" using s j_def by auto
      then show "c (r - i) * a (n - (s + i)) = (\<lambda>l. a (j + l) * c l) (r - i)"
        by (simp add: mult.commute)
    qed
    also have "\<dots> = (\<Sum>l\<le>r. a (j + l) * c l)" by (rule reflect_sum)
    also have "\<dots> = 0" using rec[OF jr] by simp
    finally have "lfun b s h = 0" .
    then have "e * lfun b s P = 0" by (simp add: hP lfun_smult)
    then show "lfun b s P = 0" using e0 by simp
  qed
  obtain lam where lam: "\<forall>s<n + 1. b s = (\<Sum>k<r. lam k * t k ^ s)"
    using recurrence_solution[OF inj _ recb[unfolded P_def]] rn by (metis Suc_eq_plus1 le_Suc_eq)
  have "\<forall>i\<le>n. a i = coef_pow lam t (\<lambda>_. 1) {..<r} n i"
  proof (intro allI impI)
    fix i assume i: "i \<le> n"
    have "a i = b (n - i)" using i by (simp add: b_def)
    also have "\<dots> = (\<Sum>k<r. lam k * t k ^ (n - i))" using lam i by auto
    finally show "a i = coef_pow lam t (\<lambda>_. 1) {..<r} n i" by (simp add: coef_pow_def)
  qed
  then show ?thesis by blast
qed

subsection \<open>Projective points with @{text "\<beta>_k \<noteq> 0"}\<close>

text \<open>
  Normalisation: @{text "(\<alpha>_k : \<beta>_k) = \<beta>_k (t_k : 1)"} with @{text "t_k = \<alpha>_k/\<beta>_k"};
  distinctness as projective points, @{text "\<alpha>_j \<beta>_k \<noteq> \<alpha>_k \<beta>_j"}, is exactly
  @{text "t_j \<noteq> t_k"}, and @{text "\<alpha>^{n-i} \<beta>^i = \<beta>^n t^{n-i}"}, so the weights become
  @{text "\<mu>_k = \<lambda>_k / \<beta>_k^n"}.  The point at infinity (@{text "\<beta>_k = 0"}) is NOT
  treated: it is an explicit hypothesis (@{text "\<beta>_k \<noteq> 0"}) here.
\<close>

theorem catalecticant_converse_projective:
  fixes al be :: "nat \<Rightarrow> 'a::field" and c a :: "nat \<Rightarrow> 'a"
  assumes be0: "\<And>k. k < r \<Longrightarrow> be k \<noteq> 0"
    and dist: "\<And>j k. j < r \<Longrightarrow> k < r \<Longrightarrow> j \<noteq> k \<Longrightarrow> al j * be k \<noteq> al k * be j"
    and c0: "c 0 \<noteq> 0" and rn: "r \<le> n"
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
  have hz': "(\<Sum>l\<in>{..r}. c l * t k ^ (r - l)) = 0" if k: "k < r" for k
  proof -
    have bk: "be k \<noteq> 0" by (rule be0[OF k])
    have "be k ^ r * (\<Sum>l\<in>{..r}. c l * t k ^ (r - l))
        = (\<Sum>l\<in>{..r}. c l * al k ^ (r - l) * be k ^ l)"
      unfolding sum_distrib_left
    proof (rule sum.cong[OF refl])
      fix l assume "l \<in> {..r}"
      then have "r = (r - l) + l" by auto
      then have "be k ^ r = be k ^ (r - l) * be k ^ l"
        by (metis power_add)
      then show "be k ^ r * (c l * t k ^ (r - l)) = c l * al k ^ (r - l) * be k ^ l"
        using bk by (simp add: t_def power_divide field_simps)
    qed
    also have "\<dots> = 0" by (rule hz[OF k])
    finally show "(\<Sum>l\<in>{..r}. c l * t k ^ (r - l)) = 0" using bk by simp
  qed
  obtain lam where lam: "\<forall>i\<le>n. a i = coef_pow lam t (\<lambda>_. 1) {..<r} n i"
    using catalecticant_converse_affine[OF inj c0 rn hz' rec] by blast
  have "\<forall>i\<le>n. a i = coef_pow (\<lambda>k. lam k / be k ^ n) al be {..<r} n i"
  proof (intro allI impI)
    fix i assume i: "i \<le> n"
    have "a i = (\<Sum>k<r. lam k * t k ^ (n - i))" using lam i by (simp add: coef_pow_def)
    also have "\<dots> = (\<Sum>k<r. lam k / be k ^ n * al k ^ (n - i) * be k ^ i)"
    proof (rule sum.cong[OF refl])
      fix k assume "k \<in> {..<r}"
      then have bk: "be k \<noteq> 0" using be0 by simp
      have "n = (n - i) + i" using i by simp
      then have "be k ^ n = be k ^ (n - i) * be k ^ i" by (metis power_add)
      then show "lam k * t k ^ (n - i) = lam k / be k ^ n * al k ^ (n - i) * be k ^ i"
        using bk by (simp add: t_def power_divide field_simps)
    qed
    finally show "a i = coef_pow (\<lambda>k. lam k / be k ^ n) al be {..<r} n i"
      by (simp add: coef_pow_def)
  qed
  then show ?thesis by blast
qed

end
