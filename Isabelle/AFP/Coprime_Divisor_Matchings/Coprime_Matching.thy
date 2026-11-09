(*  Title:      Coprime_Matching.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

(* encaje: Lemma 2.1 and Theorem 1.2 of Alekseyev and Beyer de Ryke, Coprime matchings of divisor sets (arXiv:2610.37512) *)
theory Coprime_Matching
  imports "Jordan_Normal_Form.Determinant" "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
    "HOL-Computational_Algebra.Primes"
begin

section \<open>Definitions\<close>

text \<open>@{term "Dset n"} is the set of positive divisors of @{term n}.  A coprime matching of
  @{term "Dset n"} with a set @{term P} of integers is a bijection under which corresponding
  integers are coprime.  @{term "prog a b N"} is the arithmetic progression
  @{text "a, a+b, ..., a+(N-1)b"}.\<close>

definition Dset :: "nat \<Rightarrow> nat set" where
  "Dset n = {d. d dvd n}"

definition coprime_matching :: "nat \<Rightarrow> int set \<Rightarrow> bool" where
  "coprime_matching n P \<longleftrightarrow>
     (\<exists>f. bij_betw f (Dset n) P \<and> (\<forall>d\<in>Dset n. coprime (int d) (f d)))"

definition prog :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int set" where
  "prog a b N = (\<lambda>t. a + b * int t) ` {0..<N}"

text \<open>@{text "M"}-numbers (McNew--Pomerance): no prime power @{text "p^p"} divides @{text n}.
  Strongly matchable: @{term "Dset n"} admits a coprime matching with every primitive
  progression (first term and common difference coprime, common difference positive) of
  length @{text "\<tau>(n)"}.\<close>

definition M_number :: "nat \<Rightarrow> bool" where
  "M_number n \<longleftrightarrow> 0 < n \<and> (\<forall>p. prime p \<longrightarrow> \<not> p ^ p dvd n)"

definition strongly_matchable :: "nat \<Rightarrow> bool" where
  "strongly_matchable n \<longleftrightarrow> 0 < n \<and>
     (\<forall>a b. 0 < b \<longrightarrow> coprime a b \<longrightarrow> coprime_matching n (prog a b (card (Dset n))))"

lemma finite_Dset: "0 < n \<Longrightarrow> finite (Dset n)"
  by (simp add: Dset_def)

lemma one_in_Dset: "1 \<in> Dset n"
  by (simp add: Dset_def)

text \<open>The library lemmas on @{const multiplicity} carry side conditions; restate them for
  primes in @{typ nat}.\<close>

lemma pow_dvd_iff_mult:
  fixes p x :: nat
  assumes "prime p" "x \<noteq> 0"
  shows "p ^ k dvd x \<longleftrightarrow> k \<le> multiplicity p x"
proof -
  have "\<not> is_unit p" using assms(1) by (meson not_prime_unit)
  from power_dvd_iff_le_multiplicity[OF assms(2) this] show ?thesis .
qed

lemma mult_zero_iff_nat:
  fixes p x :: nat
  assumes "prime p" "x \<noteq> 0"
  shows "multiplicity p x = 0 \<longleftrightarrow> \<not> p dvd x"
  using prime_elem_multiplicity_eq_zero_iff[OF prime_imp_prime_elem[OF assms(1)] assms(2)] .

section \<open>Lemma 2.1: the algebraic construction\<close>

subsection \<open>Arithmetic preliminaries\<close>

lemma norm_prod_c:
  fixes g :: "nat \<Rightarrow> complex"
  shows "norm (prod g S) = (\<Prod>x\<in>S. norm (g x))"
  by (induct S rule: infinite_finite_induct) (simp_all add: norm_mult)

lemma coprime_iff_primes:
  fixes x d :: nat
  shows "coprime x d \<longleftrightarrow> (\<forall>p. prime p \<longrightarrow> p dvd x \<longrightarrow> \<not> p dvd d)"
proof
  assume c: "coprime x d"
  show "\<forall>p. prime p \<longrightarrow> p dvd x \<longrightarrow> \<not> p dvd d"
  proof (intro allI impI notI)
    fix p assume pp: "prime p" and px: "p dvd x" and pd: "p dvd d"
    have "is_unit p" by (rule coprime_common_divisor[OF c px pd])
    with pp show False by simp
  qed
next
  assume H: "\<forall>p. prime p \<longrightarrow> p dvd x \<longrightarrow> \<not> p dvd d"
  show "coprime x d"
  proof (rule ccontr)
    assume nc: "\<not> coprime x d"
    then have "gcd x d \<noteq> 1" by (simp add: coprime_iff_gcd_eq_1)
    then obtain p where p: "prime p" "p dvd gcd x d"
      using prime_factor_nat[of "gcd x d"] by blast
    then have "p dvd x" "p dvd d" by simp_all
    with H p(1) show False by blast
  qed
qed

subsection \<open>Roots of unity\<close>

text \<open>For a prime @{term p} we pick (by the fundamental theorem of algebra) a complex root of
  unity @{term "zeta p"} with @{text "\<zeta>^p = 1"} and @{text "\<zeta> \<noteq> 1"}.\<close>

lemma zero_pow_pos: "0 < p \<Longrightarrow> (0::complex) ^ p = 0"
  by (cases p) simp_all

lemma geom_identity: "(x - 1) * (\<Sum>i<p. x ^ i) = x ^ p - 1" for x :: "'a :: comm_ring_1"
  by (induct p) (simp_all add: algebra_simps)

lemma exists_root_of_unity:
  assumes "prime p"
  shows "\<exists>z::complex. z ^ p = 1 \<and> z \<noteq> 1"
proof -
  have p2: "2 \<le> p" using assms by (rule prime_ge_2_nat)
  define Phi :: "complex poly" where "Phi = (\<Sum>i<p. monom 1 i)"
  have pl: "poly Phi x = (\<Sum>i<p. x ^ i)" for x
    unfolding Phi_def by (simp add: poly_sum poly_monom)
  have p0: "poly Phi 0 = 1"
  proof -
    have "(0 - 1) * poly Phi 0 = (0::complex) ^ p - 1" using geom_identity[of 0 p] pl by simp
    moreover have "(0::complex) ^ p = 0" using p2 by (intro zero_pow_pos) simp
    ultimately show ?thesis by simp
  qed
  have p1: "poly Phi 1 = of_nat p" by (simp add: pl)
  have "\<not> constant (poly Phi)"
  proof
    assume "constant (poly Phi)"
    then have "poly Phi 0 = poly Phi 1" by (simp add: constant_def)
    with p0 p1 p2 show False by simp
  qed
  from fundamental_theorem_of_algebra[OF this] obtain z where z: "poly Phi z = 0" by blast
  have "z ^ p = 1"
    using geom_identity[of z p] z pl by (simp add: algebra_simps)
  moreover have "z \<noteq> 1"
  proof
    assume "z = 1"
    with z p1 p2 show False by simp
  qed
  ultimately show ?thesis by blast
qed

definition zeta :: "nat \<Rightarrow> complex" where
  "zeta p = (SOME z. z ^ p = 1 \<and> z \<noteq> 1)"

lemma zeta_props:
  assumes "prime p"
  shows "zeta p ^ p = 1" "zeta p \<noteq> 1"
  using someI_ex[OF exists_root_of_unity[OF assms]] unfolding zeta_def by blast+

lemma zeta_ne_0:
  assumes "prime p"
  shows "zeta p \<noteq> 0"
proof
  assume "zeta p = 0"
  with zeta_props(1)[OF assms] have "(0::complex) ^ p = 1" by simp
  moreover have "(0::complex) ^ p = 0" using prime_gt_0_nat[OF assms] by (intro zero_pow_pos)
  ultimately show False by simp
qed

lemma norm_zeta:
  assumes "prime p"
  shows "norm (zeta p) = 1"
proof -
  have p0: "0 < p" using prime_gt_0_nat[OF assms] by simp
  have h: "norm (zeta p) ^ p = (1::real) ^ p"
  proof -
    have "norm (zeta p ^ p) = norm (1::complex)" using zeta_props(1)[OF assms] by simp
    then show ?thesis by (simp add: norm_power)
  qed
  have n0: "0 \<le> norm (zeta p)" by simp
  have "(0::real) \<le> 1" by simp
  from power_eq_imp_eq_base[OF h n0 this p0] show ?thesis .
qed

lemma zeta_pow_eq_1:
  assumes p: "prime p"
  shows "zeta p ^ k = 1 \<longleftrightarrow> p dvd k"
proof
  assume "p dvd k"
  then obtain c where "k = p * c" by blast
  then show "zeta p ^ k = 1" by (simp add: power_mult zeta_props[OF p])
next
  assume h: "zeta p ^ k = 1"
  define r where "r = k mod p"
  have kr: "k = p * (k div p) + r" unfolding r_def by simp
  have "zeta p ^ k = zeta p ^ (p * (k div p) + r)" by (rule arg_cong[OF kr])
  also have "\<dots> = (zeta p ^ p) ^ (k div p) * zeta p ^ r" by (simp add: power_add power_mult)
  finally have zr: "zeta p ^ r = 1" using h zeta_props(1)[OF p] by simp
  show "p dvd k"
  proof (rule ccontr)
    assume nd: "\<not> p dvd k"
    then have r0: "r \<noteq> 0" unfolding r_def by (simp add: dvd_eq_mod_eq_0)
    have rlt: "r < p" unfolding r_def using prime_gt_0_nat[OF p] by simp
    have "\<not> p dvd r" using r0 rlt by (simp add: nat_dvd_not_less)
    then have cop: "coprime r p" using p by (simp add: coprime_commute prime_imp_coprime)
    from bezout_nat[of r p] r0 obtain x y where "r * x = p * y + gcd r p" by blast
    with cop have e: "r * x = p * y + 1" by simp
    have h1: "zeta p ^ (p * y + 1) = zeta p"
    proof -
      have "zeta p ^ (p * y + 1) = (zeta p ^ p) ^ y * zeta p" by (simp add: power_add power_mult)
      then show ?thesis by (simp add: zeta_props[OF p])
    qed
    have h2: "zeta p ^ (r * x) = 1"
    proof -
      have "zeta p ^ (r * x) = (zeta p ^ r) ^ x" by (simp add: power_mult)
      then show ?thesis using zr by simp
    qed
    have h3: "zeta p ^ (p * y + 1) = 1" using h2 by (simp only: e)
    have "zeta p = 1" by (rule trans[OF h1[symmetric] h3])
    with zeta_props(2)[OF p] show False by simp
  qed
qed

lemma zeta_pow_eq:
  assumes p: "prime p" and eq: "zeta p ^ x = zeta p ^ y" and le: "y \<le> x"
  shows "p dvd x - y"
proof -
  have ne: "zeta p \<noteq> 0" using zeta_ne_0[OF p] .
  have xe: "x = y + (x - y)" using le by simp
  have "zeta p ^ x = zeta p ^ (y + (x - y))" by (rule arg_cong[OF xe])
  also have "\<dots> = zeta p ^ y * zeta p ^ (x - y)" by (simp add: power_add)
  finally have "zeta p ^ x = zeta p ^ y * zeta p ^ (x - y)" .
  with eq have "zeta p ^ y * zeta p ^ (x - y) = zeta p ^ y * 1" by simp
  then have "zeta p ^ (x - y) = 1" using ne by simp
  then show ?thesis using zeta_pow_eq_1[OF p] by blast
qed

lemma exps_le_eq:
  assumes p: "prime p" and cop: "coprime p k" and eq: "zeta p ^ (k * u) = zeta p ^ (k * v)"
    and le: "v \<le> u" and lt: "u < p"
  shows "u = v"
proof -
  have le': "k * v \<le> k * u" using le by (rule mult_le_mono2)
  from zeta_pow_eq[OF p eq le'] have "p dvd k * u - k * v" .
  then have "p dvd k * (u - v)" by (simp add: diff_mult_distrib2)
  then have dv: "p dvd u - v" using coprime_dvd_mult_right_iff[OF cop] by blast
  have "u - v = 0"
  proof (rule ccontr)
    assume ne: "u - v \<noteq> 0"
    from dvd_imp_le[OF dv] ne have "p \<le> u - v" by simp
    with lt show False by simp
  qed
  with le show ?thesis by simp
qed

lemma exps_eq:
  assumes p: "prime p" and cop: "coprime p k" and eq: "zeta p ^ (k * u) = zeta p ^ (k * v)"
    and lu: "u < p" and lv: "v < p"
  shows "u = v"
proof (cases "v \<le> u")
  case True
  from exps_le_eq[OF p cop eq True lu] show ?thesis .
next
  case False
  then have "u \<le> v" by simp
  from exps_le_eq[OF p cop eq[symmetric] this lv] show ?thesis by simp
qed

subsection \<open>The construction\<close>

locale CM =
  fixes m a b :: nat
  assumes m_pos: "0 < m" and b_pos: "0 < b"
    and hyp: "\<And>p. prime p \<Longrightarrow> p dvd m \<Longrightarrow> p dvd b \<or> Suc (multiplicity p m) \<le> p"
    and cop: "\<And>p. prime p \<Longrightarrow> p dvd m \<Longrightarrow> p dvd b \<Longrightarrow> \<not> p dvd a"
begin

definition PR :: "nat set" where "PR = prime_factors m"

definition Q :: nat where "Q = card (Dset m)"

definition ydef :: "nat \<Rightarrow> nat \<Rightarrow> complex" where
  "ydef p t = (if p dvd b then of_nat p ^ t else zeta p ^ (a + b * t) - 1)"

definition Mf :: "nat \<Rightarrow> nat \<Rightarrow> complex" where
  "Mf t d = (\<Prod>p\<in>PR. ydef p t ^ multiplicity p d)"

definition Ap :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
  "Ap p c e = (if p dvd b then (if c = e then 1 else 0)
               else (-1) ^ (e - c) * of_nat (e choose c) * zeta p ^ (a * c))"

definition mup :: "nat \<Rightarrow> nat \<Rightarrow> complex" where
  "mup p c = (if p dvd b then of_nat p ^ c else zeta p ^ (b * c))"

definition Af :: "nat \<Rightarrow> nat \<Rightarrow> complex" where
  "Af f d = (\<Prod>p\<in>PR. Ap p (multiplicity p f) (multiplicity p d))"

definition mu :: "nat \<Rightarrow> complex" where
  "mu f = (\<Prod>p\<in>PR. mup p (multiplicity p f))"

lemma PR_finite: "finite PR" by (simp add: PR_def)

lemma PR_iff: "p \<in> PR \<longleftrightarrow> prime p \<and> p dvd m"
  using m_pos by (auto simp: PR_def in_prime_factors_iff)

lemma Dset_dvd: "d \<in> Dset m \<Longrightarrow> d dvd m" by (simp add: Dset_def)

lemma Dset_pos: "d \<in> Dset m \<Longrightarrow> 0 < d"
  using m_pos by (auto simp: Dset_def intro: Nat.gr0I)

lemma Dset_finite: "finite (Dset m)" using m_pos by (rule finite_Dset)

lemma Q_pos: "0 < Q"
  unfolding Q_def using Dset_finite one_in_Dset by (auto simp: card_gt_0_iff)

lemma mult_le_m:
  assumes "d \<in> Dset m"
  shows "multiplicity p d \<le> multiplicity p m"
  using assms m_pos by (intro dvd_imp_multiplicity_le) (auto simp: Dset_def)

lemma mult_zero_outside:
  assumes "d \<in> Dset m" "prime p" "p \<notin> PR"
  shows "multiplicity p d = 0"
proof -
  have "\<not> p dvd d"
  proof
    assume "p dvd d"
    then have "p dvd m" using Dset_dvd[OF assms(1)] by (rule dvd_trans)
    with assms(2) have "p \<in> PR" by (simp add: PR_iff)
    with assms(3) show False by simp
  qed
  then show ?thesis by (rule not_dvd_imp_multiplicity_0)
qed

text \<open>The divisors of @{term m} correspond to exponent vectors.\<close>

lemma bij_exp:
  "bij_betw (\<lambda>f. restrict (\<lambda>p. multiplicity p f) PR) (Dset m)
            (PiE PR (\<lambda>p. {0..multiplicity p m}))"
proof (rule bij_betwI')
  fix x y assume x: "x \<in> Dset m" and y: "y \<in> Dset m"
  show "restrict (\<lambda>p. multiplicity p x) PR = restrict (\<lambda>p. multiplicity p y) PR \<longleftrightarrow> x = y"
  proof
    assume eq: "restrict (\<lambda>p. multiplicity p x) PR = restrict (\<lambda>p. multiplicity p y) PR"
    have mm: "multiplicity p x = multiplicity p y" if p: "prime p" for p
    proof (cases "p \<in> PR")
      case True
      then have "restrict (\<lambda>p. multiplicity p x) PR p = restrict (\<lambda>p. multiplicity p y) PR p"
        using eq by simp
      with True show ?thesis by simp
    next
      case False
      then show ?thesis using x y p mult_zero_outside by simp
    qed
    show "x = y" by (rule multiplicity_eq_nat[OF Dset_pos[OF x] Dset_pos[OF y] mm])
  qed simp
next
  fix x assume x: "x \<in> Dset m"
  then show "restrict (\<lambda>p. multiplicity p x) PR \<in> PiE PR (\<lambda>p. {0..multiplicity p m})"
    using mult_le_m by (auto simp: PiE_def extensional_def)
next
  fix g assume g: "g \<in> PiE PR (\<lambda>p. {0..multiplicity p m})"
  define f where "f = (\<Prod>p\<in>PR. p ^ g p)"
  have gle: "g p \<le> multiplicity p m" if "p \<in> PR" for p using g that by (auto simp: PiE_def)
  have prm: "\<And>p. p \<in> PR \<Longrightarrow> prime p" using PR_iff by blast
  have mm: "m = (\<Prod>p\<in>PR. p ^ multiplicity p m)"
    using prod_prime_factors[of m] m_pos by (simp add: PR_def)
  have fd: "f dvd m"
  proof -
    have "f dvd (\<Prod>p\<in>PR. p ^ multiplicity p m)"
      unfolding f_def
    proof (rule prod_dvd_prod)
      fix p assume p: "p \<in> PR"
      show "p ^ g p dvd p ^ multiplicity p m" by (rule le_imp_power_dvd[OF gle[OF p]])
    qed
    with mm show ?thesis by simp
  qed
  have mf: "multiplicity q f = (if q \<in> PR then g q else 0)" if "prime q" for q
    unfolding f_def using PR_finite prm that by (rule multiplicity_prod_prime_powers)
  show "\<exists>x\<in>Dset m. g = restrict (\<lambda>p. multiplicity p x) PR"
  proof (intro bexI[of _ f])
    show "f \<in> Dset m" using fd by (simp add: Dset_def)
    show "g = restrict (\<lambda>p. multiplicity p f) PR"
    proof (rule PiE_ext[OF g])
      show "restrict (\<lambda>p. multiplicity p f) PR \<in> PiE PR (\<lambda>p. {0..multiplicity p m})"
        using mf gle prm by (auto simp: PiE_def extensional_def)
      fix p assume "p \<in> PR"
      with mf prm show "g p = restrict (\<lambda>p. multiplicity p f) PR p" by simp
    qed
  qed
qed

subsection \<open>Support: nonzero entries correspond to coprime pairs\<close>

lemma ydef_nonzero:
  assumes "p \<in> PR"
  shows "ydef p t \<noteq> 0 \<longleftrightarrow> \<not> p dvd a + b * t"
proof (cases "p dvd b")
  case True
  have pm: "prime p" "p dvd m" using assms PR_iff by blast+
  from True have "\<not> p dvd a + b * t" using cop[OF pm True] by (simp add: dvd_add_left_iff)
  with True pm show ?thesis by (simp add: ydef_def prime_gt_0_nat)
next
  case False
  have pm: "prime p" using assms PR_iff by blast
  have "ydef p t = 0 \<longleftrightarrow> zeta p ^ (a + b * t) = 1" using False by (simp add: ydef_def)
  also have "\<dots> \<longleftrightarrow> p dvd a + b * t" using zeta_pow_eq_1[OF pm] by blast
  finally show ?thesis using False by simp
qed

lemma Mf_nonzero_iff:
  assumes "d \<in> Dset m"
  shows "Mf t d \<noteq> 0 \<longleftrightarrow> coprime (a + b * t) d"
proof -
  have "Mf t d \<noteq> 0 \<longleftrightarrow> (\<forall>p\<in>PR. ydef p t ^ multiplicity p d \<noteq> 0)"
    unfolding Mf_def using PR_finite by (simp add: prod_zero_iff)
  also have "\<dots> \<longleftrightarrow> (\<forall>p\<in>PR. multiplicity p d = 0 \<or> ydef p t \<noteq> 0)"
    by (auto simp: power_eq_0_iff)
  also have "\<dots> \<longleftrightarrow> (\<forall>p\<in>PR. p dvd d \<longrightarrow> \<not> p dvd a + b * t)"
  proof (intro ball_cong refl)
    fix p assume p: "p \<in> PR"
    have pr: "prime p" using p PR_iff by blast
    have d0: "d \<noteq> 0" using Dset_pos[OF assms] by simp
    have "multiplicity p d = 0 \<longleftrightarrow> \<not> p dvd d" by (rule mult_zero_iff_nat[OF pr d0])
    then show "(multiplicity p d = 0 \<or> ydef p t \<noteq> 0) \<longleftrightarrow> (p dvd d \<longrightarrow> \<not> p dvd a + b * t)"
      using ydef_nonzero[OF p] by blast
  qed
  also have "\<dots> \<longleftrightarrow> coprime (a + b * t) d"
  proof -
    have "(\<forall>p. prime p \<longrightarrow> p dvd a + b * t \<longrightarrow> \<not> p dvd d) \<longleftrightarrow>
          (\<forall>p\<in>PR. p dvd d \<longrightarrow> \<not> p dvd a + b * t)"
    proof (intro iffI ballI allI impI)
      fix p assume H: "\<forall>p. prime p \<longrightarrow> p dvd a + b * t \<longrightarrow> \<not> p dvd d" and "p \<in> PR" "p dvd d"
      then show "\<not> p dvd a + b * t" using PR_iff by blast
    next
      fix p assume H: "\<forall>p\<in>PR. p dvd d \<longrightarrow> \<not> p dvd a + b * t"
        and pp: "prime p" and pa: "p dvd a + b * t"
      show "\<not> p dvd d"
      proof
        assume pd: "p dvd d"
        have "p dvd m" using pd Dset_dvd[OF assms] by (rule dvd_trans)
        then have "p \<in> PR" using pp by (simp add: PR_iff)
        from bspec[OF H this] have "p dvd d \<longrightarrow> \<not> p dvd a + b * t" .
        with pd pa show False by simp
      qed
    qed
    then show ?thesis by (simp add: coprime_iff_primes)
  qed
  finally show ?thesis .
qed

subsection \<open>The expansion M = V A\<close>

lemma ydef_expand:
  assumes "p \<in> PR" "e \<le> multiplicity p m"
  shows "ydef p t ^ e = (\<Sum>c\<in>{0..multiplicity p m}. Ap p c e * mup p c ^ t)"
proof (cases "p dvd b")
  case True
  have "(\<Sum>c\<in>{0..multiplicity p m}. Ap p c e * mup p c ^ t)
      = (\<Sum>c\<in>{0..multiplicity p m}. if c = e then (of_nat p ^ c) ^ t else 0)"
    using True by (intro sum.cong) (auto simp: Ap_def mup_def)
  also have "\<dots> = (of_nat p ^ e) ^ t" using assms(2) by (simp add: sum.delta)
  also have "\<dots> = ydef p t ^ e" using True by (simp add: ydef_def power_mult_distrib flip: power_mult
                                                    mult.commute)
  finally show ?thesis by simp
next
  case False
  define x where "x = zeta p ^ (a + b * t)"
  have yx: "ydef p t = x - 1" using False by (simp add: ydef_def x_def)
  have trm: "Ap p c e * mup p c ^ t = of_nat (e choose c) * x ^ c * (-1) ^ (e - c)" for c
  proof -
    have "x ^ c = zeta p ^ (a * c) * (zeta p ^ (b * c)) ^ t"
      unfolding x_def
      by (simp flip: power_mult power_add add: algebra_simps)
    then show ?thesis using False by (simp add: Ap_def mup_def algebra_simps)
  qed
  have "(\<Sum>c\<in>{0..multiplicity p m}. Ap p c e * mup p c ^ t)
      = (\<Sum>c\<in>{0..multiplicity p m}. of_nat (e choose c) * x ^ c * (-1) ^ (e - c))"
    by (simp add: trm)
  also have "\<dots> = (\<Sum>c\<in>{..e}. of_nat (e choose c) * x ^ c * (-1) ^ (e - c))"
  proof (rule sum.mono_neutral_cong_left[symmetric])
    show "finite {0..multiplicity p m}" by simp
    show "{..e} \<subseteq> {0..multiplicity p m}" using assms(2) by auto
    show "\<forall>c\<in>{0..multiplicity p m} - {..e}. of_nat (e choose c) * x ^ c * (-1) ^ (e - c) = 0"
      by auto
  qed simp
  also have "\<dots> = (x + (-1)) ^ e" by (rule binomial_ring[symmetric])
  finally show ?thesis using yx by simp
qed

lemma Mf_expand:
  assumes d: "d \<in> Dset m"
  shows "Mf t d = (\<Sum>f\<in>Dset m. Af f d * mu f ^ t)"
proof -
  have "Mf t d = (\<Prod>p\<in>PR. \<Sum>c\<in>{0..multiplicity p m}. Ap p c (multiplicity p d) * mup p c ^ t)"
    unfolding Mf_def using mult_le_m[OF d] by (intro prod.cong refl ydef_expand) auto
  also have "\<dots> = (\<Sum>g\<in>PiE PR (\<lambda>p. {0..multiplicity p m}).
                   \<Prod>p\<in>PR. Ap p (g p) (multiplicity p d) * mup p (g p) ^ t)"
    by (rule prod_sum_PiE) (simp_all add: PR_finite)
  also have "\<dots> = (\<Sum>f\<in>Dset m. \<Prod>p\<in>PR.
        Ap p (restrict (\<lambda>p. multiplicity p f) PR p) (multiplicity p d) *
        mup p (restrict (\<lambda>p. multiplicity p f) PR p) ^ t)"
    by (rule sum.reindex_bij_betw[OF bij_exp, symmetric])
  also have "\<dots> = (\<Sum>f\<in>Dset m. Af f d * mu f ^ t)"
    by (intro sum.cong refl)
       (simp add: Af_def mu_def prod.distrib prod_power_distrib)
  finally show ?thesis .
qed

lemma Af_nonzero_imp_dvd:
  assumes "f \<in> Dset m" "d \<in> Dset m" "Af f d \<noteq> 0"
  shows "f dvd d"
proof -
  have le: "multiplicity p f \<le> multiplicity p d" if "p \<in> PR" for p
  proof -
    from assms(3) that have "Ap p (multiplicity p f) (multiplicity p d) \<noteq> 0"
      unfolding Af_def using PR_finite by (simp add: prod_zero_iff)
    then show ?thesis
      by (cases "p dvd b") (auto simp: Ap_def binomial_eq_0_iff split: if_splits)
  qed
  have "multiplicity p f \<le> multiplicity p d" if "prime p" for p
  proof (cases "p \<in> PR")
    case True then show ?thesis by (rule le)
  next
    case False then show ?thesis using mult_zero_outside[OF assms(1) that] by simp
  qed
  then show ?thesis using Dset_pos[OF assms(1)] by (intro multiplicity_le_imp_dvd) auto
qed

lemma Af_diag: "Af d d \<noteq> 0"
proof -
  have "Ap p c c \<noteq> 0" if "p \<in> PR" for p c
  proof -
    have pr: "prime p" using that PR_iff by blast
    show ?thesis using zeta_ne_0[OF pr] by (cases "p dvd b") (simp_all add: Ap_def)
  qed
  then show ?thesis unfolding Af_def using PR_finite by (simp add: prod_zero_iff)
qed

subsection \<open>The nodes are distinct\<close>

lemma mu_inj:
  assumes f: "f \<in> Dset m" and g: "g \<in> Dset m" and eq: "mu f = mu g"
  shows "f = g"
proof -
  define I1 where "I1 = {p \<in> PR. p dvd b}"
  define I0 where "I0 = {p \<in> PR. \<not> p dvd b}"
  have fin: "finite I1" "finite I0" by (simp_all add: I1_def I0_def PR_finite)
  have un: "PR = I1 \<union> I0" and dis: "I1 \<inter> I0 = {}" by (auto simp: I1_def I0_def)
  have pI1: "prime p" if "p \<in> I1" for p using that PR_iff I1_def by blast
  have pI0: "prime p" if "p \<in> I0" for p using that PR_iff I0_def by blast
  define F1 where "F1 h = (\<Prod>p\<in>I1. p ^ multiplicity p h)" for h
  define U where "U h = (\<Prod>p\<in>I0. zeta p ^ (b * multiplicity p h))" for h
  have mu_split: "mu h = of_nat (F1 h) * U h" for h
  proof -
    have "mu h = (\<Prod>p\<in>I1. mup p (multiplicity p h)) * (\<Prod>p\<in>I0. mup p (multiplicity p h))"
      unfolding mu_def by (subst un) (simp add: prod.union_disjoint fin dis)
    also have "(\<Prod>p\<in>I1. mup p (multiplicity p h)) = of_nat (F1 h)"
      unfolding F1_def by (simp add: mup_def I1_def)
    also have "(\<Prod>p\<in>I0. mup p (multiplicity p h)) = U h"
      unfolding U_def by (intro prod.cong refl) (simp add: mup_def I0_def)
    finally show ?thesis .
  qed
  have nU: "norm (U h) = 1" for h
  proof -
    have "norm (U h) = (\<Prod>p\<in>I0. norm (zeta p) ^ (b * multiplicity p h))"
      unfolding U_def by (simp add: norm_prod_c norm_power)
    also have "\<dots> = 1" using norm_zeta pI0 by (intro prod.neutral) simp
    finally show ?thesis .
  qed
  have F1pos: "0 < F1 h" for h
    unfolding F1_def using pI1 by (intro prod_pos) (auto simp: prime_gt_0_nat)
  have "norm (mu f) = real (F1 f)" using mu_split nU by (simp add: norm_mult)
  moreover have "norm (mu g) = real (F1 g)" using mu_split nU by (simp add: norm_mult)
  ultimately have F1eq: "F1 f = F1 g" using eq by simp
  have Ueq: "U f = U g"
  proof -
    from eq mu_split[of f] mu_split[of g] have "of_nat (F1 f) * U f = of_nat (F1 g) * U g" by simp
    with F1eq F1pos[of f] show ?thesis by simp
  qed
  have m1: "multiplicity p f = multiplicity p g" if "p \<in> I1" for p
  proof -
    have "multiplicity p (F1 f) = (if p \<in> I1 then multiplicity p f else 0)"
      unfolding F1_def using fin(1) pI1 pI1[OF that] by (rule multiplicity_prod_prime_powers)
    moreover have "multiplicity p (F1 g) = (if p \<in> I1 then multiplicity p g else 0)"
      unfolding F1_def using fin(1) pI1 pI1[OF that] by (rule multiplicity_prod_prime_powers)
    ultimately show ?thesis using F1eq that by simp
  qed
  have m0: "multiplicity j f = multiplicity j g" if j: "j \<in> I0" for j
  proof -
    define Pj where "Pj = (\<Prod>i\<in>I0 - {j}. i)"
    have pj: "prime j" using pI0 j .
    have jb: "\<not> j dvd b" using j by (simp add: I0_def)
    have jP: "\<not> j dvd Pj"
    proof
      assume "j dvd Pj"
      then have "\<exists>i\<in>I0 - {j}. j dvd i"
        using prime_dvd_prod_iff[OF finite_Diff[OF fin(2)] pj, of "\<lambda>i. i"] unfolding Pj_def by simp
      then obtain i where i: "i \<in> I0 - {j}" "j dvd i" by blast
      have "prime i" using pI0 i(1) by blast
      with primes_dvd_imp_eq[OF pj \<open>prime i\<close> i(2)] have "j = i" by simp
      with i(1) show False by simp
    qed
    have key: "(U h) ^ Pj = zeta j ^ (b * multiplicity j h * Pj)" for h
    proof -
      have "(U h) ^ Pj = (\<Prod>p\<in>I0. (zeta p ^ (b * multiplicity p h)) ^ Pj)"
        unfolding U_def by (simp add: prod_power_distrib)
      also have "\<dots> = (zeta j ^ (b * multiplicity j h)) ^ Pj *
                      (\<Prod>p\<in>I0 - {j}. (zeta p ^ (b * multiplicity p h)) ^ Pj)"
        using j fin(2) by (simp add: prod.remove)
      also have "(\<Prod>p\<in>I0 - {j}. (zeta p ^ (b * multiplicity p h)) ^ Pj) = 1"
      proof (intro prod.neutral ballI)
        fix p assume p: "p \<in> I0 - {j}"
        have "p dvd Pj" unfolding Pj_def using p fin by (intro dvd_prodI) auto
        then have "zeta p ^ Pj = 1" using zeta_pow_eq_1[OF pI0[of p]] p by blast
        have "(zeta p ^ (b * multiplicity p h)) ^ Pj = (zeta p ^ Pj) ^ (b * multiplicity p h)"
          by (simp flip: power_mult add: mult.commute)
        then show "(zeta p ^ (b * multiplicity p h)) ^ Pj = 1" using \<open>zeta p ^ Pj = 1\<close> by simp
      qed
      finally show ?thesis by (simp flip: power_mult)
    qed
    have hz: "zeta j ^ (b * multiplicity j f * Pj) = zeta j ^ (b * multiplicity j g * Pj)"
      using key[of f] key[of g] Ueq by simp
    have lt: "multiplicity j f < j" "multiplicity j g < j"
    proof -
      have jm: "j dvd m" using j PR_iff I0_def by blast
      from hyp[OF pj jm] jb have "Suc (multiplicity j m) \<le> j" by blast
      with mult_le_m[OF f, of j] mult_le_m[OF g, of j] show "multiplicity j f < j" "multiplicity j g < j"
        by linarith+
    qed
    have cpj: "coprime j (b * Pj)"
    proof -
      have "coprime j b" using pj jb by (simp add: prime_imp_coprime)
      moreover have "coprime j Pj" using pj jP by (simp add: prime_imp_coprime)
      ultimately show ?thesis by (simp add: coprime_mult_right_iff)
    qed
    have hz': "zeta j ^ ((b * Pj) * multiplicity j f) = zeta j ^ ((b * Pj) * multiplicity j g)"
      using hz by (simp add: ac_simps)
    from exps_eq[OF pj cpj hz' lt(1) lt(2)] show ?thesis .
  qed
  have "restrict (\<lambda>p. multiplicity p f) PR = restrict (\<lambda>p. multiplicity p g) PR"
  proof (rule restrict_ext)
    fix p assume "p \<in> PR"
    then show "multiplicity p f = multiplicity p g" using m1 m0 un by blast
  qed
  with bij_exp f g show ?thesis by (auto simp: bij_betw_def inj_on_def)
qed

end

subsection \<open>Nonsingularity of the Vandermonde matrix\<close>

lemma vandermonde_nonsingular:
  fixes z :: "nat \<Rightarrow> complex"
  assumes inj: "inj_on z {0..<Q}"
  shows "det (Matrix.mat Q Q (\<lambda>(t, k). z k ^ t)) \<noteq> 0"
proof (cases "Q = 0")
  case True
  then show ?thesis by (simp add: det_def)
next
  case Qpos: False
  define V where "V = Matrix.mat Q Q (\<lambda>(k, t). z k ^ t)"
  have Vc: "V \<in> carrier_mat Q Q" by (simp add: V_def)
  have tr: "Matrix.mat Q Q (\<lambda>(t, k). z k ^ t) = transpose_mat V"
    by (rule eq_matI) (simp_all add: V_def)
  have "det V \<noteq> 0"
  proof
    assume "det V = 0"
    from det_0_iff_vec_prod_zero_field[OF Vc] this obtain x where
      x: "x \<in> carrier_vec Q" "x \<noteq> 0\<^sub>v Q" "V *\<^sub>v x = 0\<^sub>v Q" by blast
    define pp :: "complex poly" where "pp = (\<Sum>t<Q. monom (x $ t) t)"
    have cf: "coeff pp n = (if n < Q then x $ n else 0)" for n
      unfolding pp_def by (simp add: coeff_sum coeff_monom)
    have pl: "poly pp w = (\<Sum>t<Q. x $ t * w ^ t)" for w
      unfolding pp_def by (simp add: poly_sum poly_monom)
    have roots: "poly pp (z k) = 0" if "k < Q" for k
    proof -
      have "(V *\<^sub>v x) $ k = 0" using x(3) that by simp
      then have "(\<Sum>t<Q. z k ^ t * x $ t) = 0"
        using that x(1) by (simp add: V_def scalar_prod_def atLeast0LessThan)
      then show ?thesis by (simp add: pl mult.commute)
    qed
    have "pp = 0"
    proof (rule ccontr)
      assume ne: "pp \<noteq> 0"
      have deg: "degree pp < Q"
      proof -
        have "degree pp \<le> Q - 1"
        proof (rule degree_le)
          show "\<forall>i>Q - 1. coeff pp i = 0"
          proof (intro allI impI)
            fix i assume "Q - 1 < i"
            then have "\<not> i < Q" by arith
            then show "coeff pp i = 0" by (simp add: cf)
          qed
        qed
        with Qpos show ?thesis by simp
      qed
      have sub: "z ` {0..<Q} \<subseteq> {w. poly pp w = 0}" using roots by auto
      have "Q = card (z ` {0..<Q})" using inj by (simp add: card_image)
      also have "\<dots> \<le> card {w. poly pp w = 0}"
        using poly_roots_finite[OF ne] sub by (intro card_mono)
      also have "\<dots> \<le> degree pp" by (rule poly_roots_degree[OF ne])
      finally show False using deg by simp
    qed
    then have "x $ n = 0" if "n < Q" for n using cf[of n] that by simp
    with x(1) have "x = 0\<^sub>v Q" by (intro eq_vecI) auto
    with x(2) show False by simp
  qed
  then show ?thesis by (simp add: tr det_transpose[OF Vc])
qed

subsection \<open>The matrix identity and the matching\<close>

context CM
begin

definition dv :: "nat \<Rightarrow> nat" where
  "dv j = sorted_list_of_set (Dset m) ! j"

lemma len_dv: "length (sorted_list_of_set (Dset m)) = Q"
  unfolding Q_def by (simp add: length_sorted_list_of_set Dset_finite)

lemma dv_in: "j < Q \<Longrightarrow> dv j \<in> Dset m"
proof -
  assume j: "j < Q"
  have "sorted_list_of_set (Dset m) ! j \<in> set (sorted_list_of_set (Dset m))"
    using j len_dv by (intro nth_mem) simp
  then show ?thesis unfolding dv_def using Dset_finite by simp
qed

lemma dv_less: "i < j \<Longrightarrow> j < Q \<Longrightarrow> dv i < dv j"
proof -
  assume ij: "i < j" "j < Q"
  have sw: "sorted_wrt (<) (sorted_list_of_set (Dset m))" by (rule strict_sorted_list_of_set)
  have jl: "j < length (sorted_list_of_set (Dset m))" using ij(2) len_dv by simp
  from sorted_wrt_nth_less[OF sw ij(1) jl] show ?thesis unfolding dv_def by simp
qed

lemma dv_le_imp: "i < Q \<Longrightarrow> j < Q \<Longrightarrow> dv i \<le> dv j \<Longrightarrow> i \<le> j"
proof (rule ccontr)
  assume iQ: "i < Q" and "dv i \<le> dv j" and "\<not> i \<le> j"
  then have "j < i" by simp
  from dv_less[OF this iQ] \<open>dv i \<le> dv j\<close> show False by simp
qed

lemma dv_bij: "bij_betw dv {0..<Q} (Dset m)"
proof (rule bij_betwI')
  fix x y assume "x \<in> {0..<Q}" "y \<in> {0..<Q}"
  then show "dv x = dv y \<longleftrightarrow> x = y"
    by (cases x y rule: linorder_cases) (auto dest: dv_less)
next
  fix x assume "x \<in> {0..<Q}"
  then show "dv x \<in> Dset m" using dv_in by simp
next
  fix y assume y: "y \<in> Dset m"
  then have "y \<in> set (sorted_list_of_set (Dset m))" using Dset_finite by simp
  then obtain i where "i < length (sorted_list_of_set (Dset m))" "sorted_list_of_set (Dset m) ! i = y"
    by (auto simp: in_set_conv_nth)
  then show "\<exists>x\<in>{0..<Q}. y = dv x" using len_dv by (auto simp: dv_def)
qed

definition Vm :: "complex mat" where "Vm = Matrix.mat Q Q (\<lambda>(t, k). mu (dv k) ^ t)"
definition Am :: "complex mat" where "Am = Matrix.mat Q Q (\<lambda>(k, j). Af (dv k) (dv j))"
definition Mm :: "complex mat" where "Mm = Matrix.mat Q Q (\<lambda>(t, j). Mf t (dv j))"

lemma Vm_c: "Vm \<in> carrier_mat Q Q" by (simp add: Vm_def)
lemma Am_c: "Am \<in> carrier_mat Q Q" by (simp add: Am_def)
lemma Mm_c: "Mm \<in> carrier_mat Q Q" by (simp add: Mm_def)

lemma Mm_eq: "Mm = Vm * Am"
proof (rule eq_matI)
  show "dim_row Mm = dim_row (Vm * Am)" "dim_col Mm = dim_col (Vm * Am)"
    by (simp_all add: Mm_def Vm_def Am_def)
next
  fix i j assume i: "i < dim_row (Vm * Am)" and j: "j < dim_col (Vm * Am)"
  then have iQ: "i < Q" and jQ: "j < Q" by (simp_all add: Vm_def Am_def)
  have dj: "dv j \<in> Dset m" using dv_in jQ .
  have "(Vm * Am) $$ (i, j) = (\<Sum>k<Q. mu (dv k) ^ i * Af (dv k) (dv j))"
    using iQ jQ by (simp add: Vm_def Am_def scalar_prod_def atLeast0LessThan)
  also have "\<dots> = (\<Sum>k\<in>{0..<Q}. Af (dv k) (dv j) * mu (dv k) ^ i)"
    by (rule sum.cong) (simp_all add: atLeast0LessThan mult.commute)
  also have "\<dots> = (\<Sum>f\<in>Dset m. Af f (dv j) * mu f ^ i)"
    by (rule sum.reindex_bij_betw[OF dv_bij])
  also have "\<dots> = Mf i (dv j)" using Mf_expand[OF dj] by simp
  finally show "Mm $$ (i, j) = (Vm * Am) $$ (i, j)" using iQ jQ by (simp add: Mm_def)
qed

lemma det_Vm: "det Vm \<noteq> 0"
proof -
  have "inj_on (\<lambda>k. mu (dv k)) {0..<Q}"
  proof (rule inj_onI)
    fix x y assume "x \<in> {0..<Q}" "y \<in> {0..<Q}" "mu (dv x) = mu (dv y)"
    then have "dv x = dv y" using mu_inj dv_in by auto
    with dv_bij \<open>x \<in> _\<close> \<open>y \<in> _\<close> show "x = y" by (auto simp: bij_betw_def inj_on_def)
  qed
  then show ?thesis unfolding Vm_def by (rule vandermonde_nonsingular)
qed

lemma det_Am: "det Am \<noteq> 0"
proof -
  have ut: "upper_triangular Am"
    unfolding upper_triangular_def
  proof (intro allI impI)
    fix i j assume "i < dim_row Am" "j < i"
    then have iQ: "i < Q" and jQ: "j < Q" by (simp_all add: Am_def)
    show "Am $$ (i, j) = 0"
    proof (rule ccontr)
      assume "Am $$ (i, j) \<noteq> 0"
      then have ne: "Af (dv i) (dv j) \<noteq> 0" using iQ jQ by (simp add: Am_def)
      from Af_nonzero_imp_dvd[OF dv_in[OF iQ] dv_in[OF jQ] ne] have "dv i dvd dv j" .
      then have "dv i \<le> dv j" using Dset_pos[OF dv_in[OF jQ]] by (simp add: dvd_imp_le)
      then have "i \<le> j" using dv_le_imp iQ jQ by blast
      with \<open>j < i\<close> show False by simp
    qed
  qed
  have "0 \<notin> set (diag_mat Am)"
    using Af_diag by (auto simp: diag_mat_def Am_def)
  then show ?thesis using det_upper_triangular[OF ut Am_c] by (simp add: prod_list_zero_iff)
qed

lemma main_sigma:
  "\<exists>\<sigma>. bij_betw \<sigma> {0..<Q} (Dset m) \<and> (\<forall>t<Q. coprime (a + b * t) (\<sigma> t))"
proof -
  have "det Mm \<noteq> 0" using Mm_eq det_mult[OF Vm_c Am_c] det_Vm det_Am by simp
  then have "(\<Sum>p | p permutes {0..<Q}. signof p * (\<Prod>i = 0..<Q. Mm $$ (i, p i))) \<noteq> 0"
    using det_def'[OF Mm_c] by simp
  then obtain p where p: "p permutes {0..<Q}"
    and ne: "signof p * (\<Prod>i = 0..<Q. Mm $$ (i, p i)) \<noteq> 0"
    by (auto elim: sum.not_neutral_contains_not_neutral)
  have "(\<Prod>i = 0..<Q. Mm $$ (i, p i)) \<noteq> 0" using ne by auto
  then have nz: "Mm $$ (i, p i) \<noteq> 0" if "i \<in> {0..<Q}" for i
    using that by (auto simp: prod_zero_iff)
  have pin: "p i \<in> {0..<Q}" if "i \<in> {0..<Q}" for i using p that by (simp add: permutes_in_image)
  show ?thesis
  proof (intro exI[of _ "dv \<circ> p"] conjI allI impI)
    show "bij_betw (dv \<circ> p) {0..<Q} (Dset m)"
      by (rule bij_betw_trans[OF permutes_imp_bij[OF p] dv_bij])
    fix t assume t: "t < Q"
    have ptQ: "p t < Q" using pin[of t] t by simp
    have "Mf t (dv (p t)) \<noteq> 0" using nz[of t] t ptQ by (simp add: Mm_def)
    then show "coprime (a + b * t) ((dv \<circ> p) t)"
      using Mf_nonzero_iff[OF dv_in[OF ptQ]] by simp
  qed
qed

end

section \<open>Lemma 2.1: proof\<close>

lemma coprime_shift_aux:
  fixes x y d :: int
  assumes "d dvd (x - y)" "coprime x d"
  shows "coprime y d"
proof (rule coprimeI)
  fix c assume cy: "c dvd y" and cd: "c dvd d"
  have c1: "c dvd (x - y)" using cd assms(1) by (rule dvd_trans)
  have "c dvd (x - y) + y" using c1 cy by (rule dvd_add)
  then have "c dvd x" by simp
  from coprime_common_divisor[OF assms(2) this cd] show "is_unit c" .
qed

theorem lemma_2_1:
  fixes m :: nat and a b :: int
  assumes m: "0 < m" and b: "0 < b" and ab: "coprime a b"
    and hyp: "\<And>p. prime p \<Longrightarrow> p dvd m \<Longrightarrow> int p dvd b \<or> Suc (multiplicity p m) \<le> p"
  shows "coprime_matching m (prog a b (card (Dset m)))"
proof -
  define b' where "b' = nat b"
  define a' where "a' = nat (a mod int m)"
  have bb: "int b' = b" using b by (simp add: b'_def)
  have aa: "int a' = a mod int m" using m by (simp add: a'_def)
  have e: "int p dvd b \<longleftrightarrow> p dvd b'" for p by (simp flip: bb)
  interpret CM m a' b'
  proof
    show "0 < m" by fact
    show "0 < b'" using b by (simp add: b'_def)
    fix p assume p: "prime p" "p dvd m"
    show "p dvd b' \<or> Suc (multiplicity p m) \<le> p"
      using hyp[OF p] e by blast
  next
    fix p assume p: "prime p" "p dvd m" and pb: "p dvd b'"
    show "\<not> p dvd a'"
    proof
      assume pa: "p dvd a'"
      have "int p dvd int a'" using pa by simp
      then have "int p dvd a mod int m" by (simp add: aa)
      then have pa': "int p dvd a" using p(2) by (simp add: dvd_mod_iff)
      have pb': "int p dvd b" using pb e by simp
      have "is_unit (int p)" by (rule coprime_common_divisor[OF ab pa' pb'])
      with p(1) show False by simp
    qed
  qed
  obtain \<sigma> where sb: "bij_betw \<sigma> {0..<Q} (Dset m)" and sc: "\<forall>t<Q. coprime (a' + b' * t) (\<sigma> t)"
    using main_sigma by blast
  have Qd: "Q = card (Dset m)" by (simp add: Q_def)
  define s where "s = inv_into {0..<Q} \<sigma>"
  have sb': "bij_betw s (Dset m) {0..<Q}" unfolding s_def by (rule bij_betw_inv_into[OF sb])
  define f where "f d = a + b * int (s d)" for d
  have bij1: "bij_betw (\<lambda>t. a + b * int t) {0..<Q} (prog a b (card (Dset m)))"
    unfolding prog_def Qd[symmetric]
  proof (rule bij_betw_imageI)
    show "inj_on (\<lambda>t. a + b * int t) {0..<Q}" using b by (auto intro!: inj_onI)
  qed simp
  have fcomp: "f = (\<lambda>t. a + b * int t) \<circ> s" unfolding f_def by (rule ext) simp
  have bf: "bij_betw f (Dset m) (prog a b (card (Dset m)))"
    unfolding fcomp by (rule bij_betw_trans[OF sb' bij1])
  have cf: "coprime (int d) (f d)" if d: "d \<in> Dset m" for d
  proof -
    define t where "t = s d"
    have tQ: "t \<in> {0..<Q}" unfolding t_def by (rule bij_betw_apply[OF sb' d])
    have st: "\<sigma> t = d" unfolding t_def s_def using sb d by (simp add: bij_betw_inv_into_right)
    from sc tQ st have "coprime (a' + b' * t) d" by auto
    then have c1: "coprime (int (a' + b' * t)) (int d)"
      by (rule iffD2[OF coprime_int_iff])
    have diff: "int m dvd int (a' + b' * t) - (a + b * int t)"
    proof -
      have h: "int m * (a div int m) + a mod int m = a" by (rule mult_div_mod_eq)
      have e1: "int (a' + b' * t) = a mod int m + b * int t" using aa bb by simp
      have "int (a' + b' * t) - (a + b * int t) = - (int m * (a div int m))"
        using e1 h by linarith
      then show ?thesis by simp
    qed
    have dm: "int d dvd int m" using Dset_dvd[OF d] by simp
    have dd: "int d dvd int (a' + b' * t) - (a + b * int t)" by (rule dvd_trans[OF dm diff])
    have "coprime (a + b * int t) (int d)" by (rule coprime_shift_aux[OF dd c1])
    then show ?thesis unfolding f_def t_def by (simp add: coprime_commute)
  qed
  show ?thesis unfolding coprime_matching_def using bf cf by blast
qed

section \<open>Theorem 1.2\<close>

subsection \<open>Easy direction: strongly matchable implies M-number (counting)\<close>

lemma strongly_matchable_imp_M:
  assumes "strongly_matchable n"
  shows "M_number n"
proof (rule ccontr)
  from assms have n: "0 < n"
    and sm: "\<And>a b. 0 < b \<Longrightarrow> coprime a b \<Longrightarrow> coprime_matching n (prog a b (card (Dset n)))"
    by (auto simp: strongly_matchable_def)
  assume "\<not> M_number n"
  with n obtain p where p: "prime p" and pd: "p ^ p dvd n"
    by (auto simp: M_number_def)
  have pe: "prime_elem p" using p by simp
  define nu where "nu = multiplicity p n"
  define N where "N = card (Dset n)"
  define D' where "D' = {d \<in> Dset n. \<not> p dvd d}"
  define T where "T = card D'"
  have n0: "n \<noteq> 0" using n by simp
  have nu_ge: "p \<le> nu"
    using pd pow_dvd_iff_mult[OF p n0, of p] by (simp add: nu_def)
  have p1: "1 < p" by (rule prime_gt_1_nat[OF p])
  have fin: "finite (Dset n)" using n by (rule finite_Dset)
  have finD': "finite D'" using fin by (simp add: D'_def)
  have T_pos: "0 < T"
  proof -
    have "1 \<in> D'" using p1 by (simp add: D'_def Dset_def)
    with finD' show ?thesis by (auto simp: T_def card_gt_0_iff)
  qed
  \<comment> \<open>@{text "(nu + 1) * T \<le> N"}: the divisors @{text "p ^ e * d"} with @{text d} prime to @{text p}.\<close>
  have A: "(nu + 1) * T \<le> N"
  proof -
    define g where "g = (\<lambda>x::nat \<times> nat. p ^ fst x * snd x)"
    have inj: "inj_on g ({0..nu} \<times> D')"
    proof (rule inj_onI)
      fix x y assume x: "x \<in> {0..nu} \<times> D'" and y: "y \<in> {0..nu} \<times> D'" and eq: "g x = g y"
      obtain e d where xe: "x = (e, d)" by (cases x)
      obtain e' d' where ye: "y = (e', d')" by (cases y)
      from x xe have d: "d \<in> Dset n" "\<not> p dvd d" by (auto simp: D'_def)
      from y ye have d': "d' \<in> Dset n" "\<not> p dvd d'" by (auto simp: D'_def)
      have dpos: "d \<noteq> 0" "d' \<noteq> 0" using d d' n by (auto simp: Dset_def)
      have eq': "p ^ e * d = p ^ e' * d'" using eq xe ye by (simp add: g_def)
      have mult: "multiplicity p (p ^ e * d) = e" if "d \<noteq> 0" "\<not> p dvd d" for e d
        using that pe p1
        by (simp add: prime_elem_multiplicity_mult_distrib not_dvd_imp_multiplicity_0)
      have "e = e'"
        using mult[OF dpos(1) d(2), of e] mult[OF dpos(2) d'(2), of e'] eq' by simp
      with eq' p1 have "d = d'" by simp
      with \<open>e = e'\<close> xe ye show "x = y" by simp
    qed
    have sub: "g ` ({0..nu} \<times> D') \<subseteq> Dset n"
    proof
      fix y assume "y \<in> g ` ({0..nu} \<times> D')"
      then obtain e d where ed: "y = p ^ e * d" "e \<le> nu" "d \<in> D'" by (auto simp: g_def)
      from ed(3) have d: "d \<in> Dset n" and pd: "\<not> p dvd d" by (simp_all add: D'_def)
      have h1: "p ^ e dvd n" using ed(2) by (simp add: nu_def pow_dvd_iff_mult[OF p n0])
      have h2: "d dvd n" using d by (simp add: Dset_def)
      have h3: "coprime (p ^ e) d"
      proof -
        have "coprime p d" by (rule prime_imp_coprime[OF p pd])
        then show ?thesis by simp
      qed
      show "y \<in> Dset n" using divides_mult[OF h1 h2 h3] ed(1) by (simp add: Dset_def)
    qed
    have "(nu + 1) * T = card ({0..nu} \<times> D')" by (simp add: card_cartesian_product T_def)
    also have "\<dots> = card (g ` ({0..nu} \<times> D'))" by (rule card_image[symmetric, OF inj])
    also have "\<dots> \<le> N" unfolding N_def using sub fin by (intro card_mono)
    finally show ?thesis .
  qed
  \<comment> \<open>@{text "N \<le> p * T"}: the multiples of p in the progression need distinct divisors prime to p.\<close>
  obtain f where bf: "bij_betw f (Dset n) (prog (int p) 1 N)"
    and cf: "\<forall>d\<in>Dset n. coprime (int d) (f d)"
    using sm[of 1 "int p"] unfolding coprime_matching_def N_def by auto
  define S where "S = {t \<in> {0..<N}. p dvd t}"
  define g where "g t = inv_into (Dset n) f (int p + int t)" for t
  have fimg: "f ` Dset n = prog (int p) 1 N" using bf by (simp add: bij_betw_def)
  have g_in: "g t \<in> D'" if t: "t \<in> S" for t
  proof -
    from t have tN: "t < N" and pt: "p dvd t" by (auto simp: S_def)
    have mem: "int p + int t \<in> f ` Dset n" using tN fimg by (auto simp: prog_def)
    have gd: "g t \<in> Dset n" unfolding g_def using mem by (rule inv_into_into)
    have fg: "f (g t) = int p + int t" unfolding g_def using mem by (rule f_inv_into_f)
    have "\<not> p dvd g t"
    proof
      assume "p dvd g t"
      then have "int p dvd int (g t)" by simp
      moreover have "int p dvd f (g t)" using fg pt by simp
      ultimately have "is_unit (int p)" using cf gd by (blast intro: coprime_common_divisor)
      with p show False by simp
    qed
    with gd show ?thesis by (simp add: D'_def)
  qed
  have g_inj: "inj_on g S"
  proof (rule inj_onI)
    fix s t assume s: "s \<in> S" and t: "t \<in> S" and eq: "g s = g t"
    have mem: "\<And>t. t \<in> S \<Longrightarrow> int p + int t \<in> f ` Dset n"
      using fimg by (auto simp: prog_def S_def)
    have hs: "f (g s) = int p + int s" unfolding g_def using mem[OF s] by (rule f_inv_into_f)
    have ht: "f (g t) = int p + int t" unfolding g_def using mem[OF t] by (rule f_inv_into_f)
    have "int p + int s = f (g s)" by (rule hs[symmetric])
    also have "\<dots> = f (g t)" by (rule arg_cong[OF eq])
    also have "\<dots> = int p + int t" by (rule ht)
    finally have "int s = int t" by simp
    then show "s = t" by simp
  qed
  have SleT: "card S \<le> T"
    unfolding T_def using g_in g_inj finD' by (intro card_inj_on_le) auto
  have NleS: "N \<le> p * card S"
  proof -
    define h where "h t = (p * (t div p), t mod p)" for t
    have "inj_on h {0..<N}"
    proof (rule inj_onI)
      fix s t assume "h s = h t"
      then have e1: "p * (s div p) = p * (t div p)" and e2: "s mod p = t mod p"
        by (simp_all add: h_def)
      have "s = p * (s div p) + s mod p" by (rule mult_div_mod_eq[symmetric])
      also have "\<dots> = p * (t div p) + t mod p" by (simp only: e1 e2)
      also have "\<dots> = t" by (rule mult_div_mod_eq)
      finally show "s = t" .
    qed
    moreover have "h ` {0..<N} \<subseteq> S \<times> {0..<p}"
    proof
      fix y assume "y \<in> h ` {0..<N}"
      then obtain t where tN: "t < N" and y: "y = h t" by auto
      have le: "p * (t div p) \<le> t" by simp
      have a1: "p * (t div p) < N" using le tN by linarith
      have "p * (t div p) \<in> S" unfolding S_def using a1 by simp
      moreover have "t mod p \<in> {0..<p}" using p1 by simp
      ultimately show "y \<in> S \<times> {0..<p}" unfolding y h_def by simp
    qed
    ultimately have "card {0..<N} \<le> card (S \<times> {0..<p})"
      by (intro card_inj_on_le) (simp_all add: S_def)
    then show ?thesis by (simp add: card_cartesian_product mult.commute)
  qed
  have "(p + 1) * T \<le> (nu + 1) * T" using nu_ge by simp
  also have "\<dots> \<le> N" by fact
  also have "\<dots> \<le> p * card S" by fact
  also have "\<dots> \<le> p * T" using SleT by simp
  finally show False using T_pos by simp
qed

subsection \<open>Hard direction via Lemma 2.1\<close>

lemma M_imp_strongly_matchable:
  assumes "M_number n"
  shows "strongly_matchable n"
proof -
  from assms have n: "0 < n" and np: "\<And>p. prime p \<Longrightarrow> \<not> p ^ p dvd n"
    by (auto simp: M_number_def)
  have n0: "n \<noteq> 0" using n by simp
  have "coprime_matching n (prog a b (card (Dset n)))"
    if "0 < b" "coprime a b" for a b :: int
  proof (rule lemma_2_1[OF n that])
    fix p assume "prime p" "p dvd n"
    from np[OF \<open>prime p\<close>] have "\<not> p ^ p dvd n" .
    then have "\<not> p \<le> multiplicity p n"
      using pow_dvd_iff_mult[OF \<open>prime p\<close> n0, of p] by simp
    then show "int p dvd b \<or> Suc (multiplicity p n) \<le> p" by simp
  qed
  with n show ?thesis by (simp add: strongly_matchable_def)
qed

theorem theorem_1_2: "strongly_matchable n \<longleftrightarrow> M_number n"
  using strongly_matchable_imp_M M_imp_strongly_matchable by blast

end
