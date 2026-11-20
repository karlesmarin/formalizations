(*  Title:      Rational_Hilbert_Symbol.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   An executable evaluator of the Hilbert symbol (a,b)_v over the rationals, total on rational inputs, with its
   basic properties proved on the executable definition itself (no theory of Q_p is used).

   For nonzero rationals a, b and a prime p, write a = p^alpha u, b = p^beta v with u, v p-adic units, computed
   on the integer X(a) = numerator * denominator (which equals a up to a rational square).  Then
     p odd :  (a,b)_p = (-1)^(alpha beta (p-1)/2) (u/p)^beta (v/p)^alpha   (Legendre symbol),
     p = 2 :  (a,b)_2 = (-1)^(eps(u) eps(v) + alpha omega(v) + beta omega(u)),
              eps(z) = (z-1)/2 mod 2,  omega(z) = (z^2-1)/8 mod 2,
     p = infinity :  -1 iff a < 0 and b < 0.
   The Legendre symbol is evaluated by Euler's criterion on residues (executable) and proved equal to
   HOL-Number_Theory's Legendre.

   Proved (nothing assumed, no unfinished proof):  values in {1,-1};  symmetry;  invariance under squares;
   multiplicativity in the first argument at every prime including 2;  (a,-a)_p = 1;  Steinberg (a,1-a)_p = 1;
   the Hilbert reciprocity law is checked by eval for all integers 1 <= |a|,|b| <= 30 (not proved in general);
   Hasse invariants of diagonal forms, with checks by eval.
*)
theory Rational_Hilbert_Symbol
  imports "HOL-Number_Theory.Number_Theory"
begin

section \<open>Signs\<close>

definition sg :: "int \<Rightarrow> int" where
  "sg k = (if even k then 1 else -1)"

lemma sg_even: "even k \<Longrightarrow> sg k = 1"
  by (simp add: sg_def)

lemma sg_odd: "odd k \<Longrightarrow> sg k = -1"
  by (simp add: sg_def)

lemma sg_add: "sg (a + b) = sg a * sg b"
  unfolding sg_def by (cases "even a"; cases "even b"; simp)

lemma sg_zero [simp]: "sg 0 = 1"
  by (simp add: sg_def)

lemma sg_sq: "sg k * sg k = 1"
  unfolding sg_def by simp

lemma sg_pm: "sg k = 1 \<or> sg k = -1"
  unfolding sg_def by simp

lemma sg_cong:
  assumes "even (k - l)"
  shows "sg k = sg l"
proof -
  have "k = l + (k - l)" by simp
  then have "sg k = sg l * sg (k - l)" using sg_add by metis
  then show ?thesis using sg_even[OF assms] by simp
qed

lemma sg_pow: "sg k ^ n = sg (k * int n)"
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc n)
  have "k * int (Suc n) = k * int n + k" by (simp add: algebra_simps)
  then show ?case using Suc by (simp add: sg_add)
qed

lemma sg_neg_one_pow: "(-1 :: int) ^ n = sg (int n)"
  by (simp add: sg_def minus_one_power_iff)

section \<open>Valuation and unit part at a prime\<close>

text \<open>@{term "vu p n"} is the pair (valuation of n at p, unit part n / p^valuation), for nonzero n.\<close>

function vu :: "nat \<Rightarrow> int \<Rightarrow> nat \<times> int" where
  "vu p n = (if p \<le> 1 \<or> n = 0 \<or> \<not> int p dvd n then (0, n)
             else (case vu p (n div int p) of (k, u) \<Rightarrow> (Suc k, u)))"
  by pat_completeness auto

termination
proof (relation "measure (\<lambda>(p, n). nat \<bar>n\<bar>)")
  show "wf (measure (\<lambda>(p, n). nat \<bar>n\<bar>))" by simp
next
  fix p n
  assume h: "\<not> (p \<le> 1 \<or> n = 0 \<or> \<not> int p dvd n)"
  then obtain m where m: "n = int p * m" by blast
  have p2: "int p \<ge> 2" using h by simp
  have m0: "m \<noteq> 0" using h m by auto
  have lt: "\<bar>m\<bar> < \<bar>int p * m\<bar>"
  proof -
    have "\<bar>m\<bar> \<ge> 1" using m0 by simp
    then have "int p * \<bar>m\<bar> > 1 * \<bar>m\<bar>" using p2 by (intro mult_strict_right_mono) simp_all
    then show ?thesis by (simp add: abs_mult)
  qed
  have dm: "n div int p = m" using m p2 by simp
  have "nat \<bar>m\<bar> < nat \<bar>n\<bar>" using lt m by arith
  then show "((p, n div int p), (p, n)) \<in> measure (\<lambda>(p, n). nat \<bar>n\<bar>)" using dm by simp
qed

definition vp :: "nat \<Rightarrow> int \<Rightarrow> nat" where "vp p n = fst (vu p n)"
definition un :: "nat \<Rightarrow> int \<Rightarrow> int" where "un p n = snd (vu p n)"

lemma vu_base:
  assumes "p \<le> 1 \<or> n = 0 \<or> \<not> int p dvd n"
  shows "vu p n = (0, n)"
  using assms by (subst vu.simps) simp

lemma vu_step:
  assumes "\<not> (p \<le> 1 \<or> n = 0 \<or> \<not> int p dvd n)"
  shows "vu p n = (Suc (vp p (n div int p)), un p (n div int p))"
  using assms by (subst vu.simps) (simp add: vp_def un_def case_prod_unfold)

lemma vp_base: "\<lbrakk>p \<le> 1 \<or> n = 0 \<or> \<not> int p dvd n\<rbrakk> \<Longrightarrow> vp p n = 0"
  by (simp add: vp_def vu_base)

lemma un_base: "\<lbrakk>p \<le> 1 \<or> n = 0 \<or> \<not> int p dvd n\<rbrakk> \<Longrightarrow> un p n = n"
  by (simp add: un_def vu_base)

lemma vu_decomp:
  assumes "1 < p" "n \<noteq> 0"
  shows "n = int p ^ vp p n * un p n \<and> \<not> int p dvd un p n"
  using assms
proof (induction p n rule: vu.induct)
  case (1 p n)
  show ?case
  proof (cases "p \<le> 1 \<or> n = 0 \<or> \<not> int p dvd n")
    case True
    then show ?thesis using 1 by (simp add: vp_base un_base)
  next
    case False
    then obtain m where m: "n = int p * m" by blast
    have m0: "m \<noteq> 0" using False m by auto
    have dm: "n div int p = m" using m 1 by simp
    have IH: "m = int p ^ vp p m * un p m \<and> \<not> int p dvd un p m"
      using 1(1)[OF False] 1(2) m0 dm by simp
    have "vp p n = Suc (vp p m)" "un p n = un p m"
      using vu_step[OF False] dm by (simp_all add: vp_def un_def)
    then show ?thesis using IH m by simp
  qed
qed

lemma un_ne0:
  assumes "1 < p" "n \<noteq> 0"
  shows "un p n \<noteq> 0"
  using vu_decomp[OF assms] by auto

lemma pow_unit_unique:
  fixes q :: int
  assumes "prime q" "\<not> q dvd u" "\<not> q dvd u'" "q ^ k * u = q ^ j * u'"
  shows "k = j \<and> u = u'"
  using assms
proof (induction k arbitrary: j)
  case 0
  show ?case
  proof (cases "j = 0")
    case True then show ?thesis using "0.prems"(4) by simp
  next
    case False
    then obtain j' where j: "j = Suc j'" using not0_implies_Suc by blast
    have "u = q * (q ^ j' * u')" using "0.prems"(4) j by (simp add: algebra_simps)
    then have "q dvd u" by simp
    then show ?thesis using "0.prems"(2) by contradiction
  qed
next
  case (Suc k)
  show ?case
  proof (cases "j = 0")
    case True
    then have "u' = q * (q ^ k * u)" using Suc.prems(4) by (simp add: algebra_simps)
    then have "q dvd u'" by simp
    then show ?thesis using Suc.prems(3) by contradiction
  next
    case False
    then obtain j' where j: "j = Suc j'" using not0_implies_Suc by blast
    have q0: "q \<noteq> 0" using Suc.prems(1) by auto
    have "q * (q ^ k * u) = q * (q ^ j' * u')"
      using Suc.prems(4) j by (simp add: algebra_simps)
    then have "q ^ k * u = q ^ j' * u'" using q0 by simp
    then have "k = j' \<and> u = u'" using Suc.IH[of j'] Suc.prems(1-3) by simp
    then show ?thesis using j by simp
  qed
qed

lemma vu_unique:
  assumes "prime p" "n = int p ^ k * u" "\<not> int p dvd u"
  shows "vu p n = (k, u)"
proof -
  have p1: "1 < p" by (rule prime_gt_1_nat[OF assms(1)])
  have qp: "prime (int p)" using assms(1) by simp
  have u0: "u \<noteq> 0" using assms(3) by auto
  have n0: "n \<noteq> 0" using assms(2) u0 qp by auto
  have d: "n = int p ^ vp p n * un p n \<and> \<not> int p dvd un p n" using vu_decomp[OF p1 n0] .
  have "vp p n = k \<and> un p n = u"
    using pow_unit_unique[OF qp _ assms(3), of "un p n" "vp p n" k] d assms(2) by metis
  then show ?thesis by (simp add: vp_def un_def prod_eq_iff)
qed

lemma vu_mult:
  assumes "prime p" "a \<noteq> 0" "b \<noteq> 0"
  shows "vp p (a * b) = vp p a + vp p b" "un p (a * b) = un p a * un p b"
proof -
  have p1: "1 < p" by (rule prime_gt_1_nat[OF assms(1)])
  have qp: "prime (int p)" using assms(1) by simp
  have da: "a = int p ^ vp p a * un p a \<and> \<not> int p dvd un p a" using vu_decomp[OF p1 assms(2)] .
  have db: "b = int p ^ vp p b * un p b \<and> \<not> int p dvd un p b" using vu_decomp[OF p1 assms(3)] .
  have e: "a * b = int p ^ (vp p a + vp p b) * (un p a * un p b)"
  proof -
    have "a * b = (int p ^ vp p a * un p a) * (int p ^ vp p b * un p b)"
      using da db by metis
    also have "\<dots> = int p ^ (vp p a + vp p b) * (un p a * un p b)"
      by (simp add: power_add algebra_simps)
    finally show ?thesis .
  qed
  have nd: "\<not> int p dvd un p a * un p b"
    using da db qp by (simp add: prime_dvd_mult_iff)
  have "vu p (a * b) = (vp p a + vp p b, un p a * un p b)" using vu_unique[OF assms(1) e nd] .
  then show "vp p (a * b) = vp p a + vp p b" "un p (a * b) = un p a * un p b"
    by (simp_all add: vp_def un_def)
qed

lemma vu_neg_one:
  assumes "1 < p"
  shows "vp p (-1) = 0" "un p (-1) = -1"
  using assms by (simp_all add: vp_base un_base)

section \<open>The Legendre symbol, executable\<close>

definition lgx :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "lgx p z = (let r = (z mod int p) ^ ((p - 1) div 2) mod int p in
              if r = 0 then 0 else if r = 1 then 1 else -1)"

lemma small_cong:
  fixes x y q :: int
  assumes "x \<in> {-1, 0, 1}" "y \<in> {-1, 0, 1}" "[x = y] (mod q)" "3 \<le> q"
  shows "x = y"
proof -
  have "q dvd (x - y)" using assms(3) by (simp add: cong_iff_dvd_diff)
  then obtain k where k: "x - y = q * k" by blast
  have "\<bar>x - y\<bar> \<le> 2" using assms(1,2) by auto
  show ?thesis
  proof (cases "k = 0")
    case True then show ?thesis using k by simp
  next
    case False
    then have "\<bar>k\<bar> \<ge> 1" by simp
    have "q * 1 \<le> q * \<bar>k\<bar>" using \<open>1 \<le> \<bar>k\<bar>\<close> assms(4) by (intro mult_left_mono) simp_all
    moreover have "\<bar>x - y\<bar> = q * \<bar>k\<bar>" using k assms(4) by (simp add: abs_mult)
    ultimately have "\<bar>x - y\<bar> \<ge> q" by simp
    then show ?thesis using \<open>\<bar>x - y\<bar> \<le> 2\<close> assms(4) by simp
  qed
qed

lemma leg_vals: "Legendre a q \<in> {-1, 0, 1}"
  by (simp add: Legendre_def)

lemma leg_zero_iff: "Legendre a q = 0 \<longleftrightarrow> q dvd a"
  by (simp add: Legendre_def cong_0_iff)

lemma leg_cong:
  assumes "[a = b] (mod q)"
  shows "Legendre a q = Legendre b q"
proof -
  have 1: "[a = 0] (mod q) \<longleftrightarrow> [b = 0] (mod q)" using assms by (metis cong_sym cong_trans)
  have 2: "QuadRes q a \<longleftrightarrow> QuadRes q b"
    unfolding QuadRes_def using assms by (metis cong_sym cong_trans)
  show ?thesis by (simp add: Legendre_def 1 2)
qed

context
  fixes p :: nat
  assumes pp: "prime p" and p2: "p \<noteq> 2"
begin

lemma p_gt2: "2 < p"
  using prime_gt_1_nat[OF pp] p2 by arith

lemma leg_euler: "[Legendre a (int p) = a ^ ((p - 1) div 2)] (mod int p)"
  using euler_criterion[OF pp p_gt2, of a] .

lemma leg_mult: "Legendre (a * b) (int p) = Legendre a (int p) * Legendre b (int p)"
proof -
  have "[Legendre (a * b) (int p) = (a * b) ^ ((p - 1) div 2)] (mod int p)" by (rule leg_euler)
  also have "[(a * b) ^ ((p - 1) div 2) = a ^ ((p - 1) div 2) * b ^ ((p - 1) div 2)] (mod int p)"
    by (simp add: power_mult_distrib)
  also have "[a ^ ((p - 1) div 2) * b ^ ((p - 1) div 2) = Legendre a (int p) * Legendre b (int p)] (mod int p)"
    using leg_euler cong_mult cong_sym by metis
  finally have c: "[Legendre (a * b) (int p) = Legendre a (int p) * Legendre b (int p)] (mod int p)" .
  have "Legendre a (int p) * Legendre b (int p) \<in> {-1, 0, 1}"
    using leg_vals[of a "int p"] leg_vals[of b "int p"] by auto
  then show ?thesis using small_cong[OF leg_vals _ c] p_gt2 by simp
qed

lemma leg_minus1: "Legendre (-1) (int p) = sg (int ((p - 1) div 2))"
proof -
  have c: "[Legendre (-1) (int p) = (-1) ^ ((p - 1) div 2)] (mod int p)" by (rule leg_euler)
  have "((-1) :: int) ^ ((p - 1) div 2) \<in> {-1, 0, 1}" by (simp add: minus_one_power_iff)
  then have "Legendre (-1) (int p) = (-1) ^ ((p - 1) div 2)"
    using small_cong[OF leg_vals _ c] p_gt2 by simp
  then show ?thesis by (simp add: sg_neg_one_pow)
qed

lemma lgx_eq: "lgx p z = Legendre z (int p)"
proof -
  have c: "[Legendre z (int p) = z ^ ((p - 1) div 2)] (mod int p)" by (rule leg_euler)
  have r: "(z mod int p) ^ ((p - 1) div 2) mod int p = z ^ ((p - 1) div 2) mod int p"
    by (simp add: power_mod)
  have m: "Legendre z (int p) mod int p = (z mod int p) ^ ((p - 1) div 2) mod int p"
    using c r by (simp add: cong_def)
  have p3: "(3 :: int) \<le> int p" using p_gt2 by simp
  consider "Legendre z (int p) = 0" | "Legendre z (int p) = 1" | "Legendre z (int p) = -1"
    using leg_vals[of z "int p"] by auto
  then show ?thesis
  proof cases
    case 1 then show ?thesis using m unfolding lgx_def by (simp add: Let_def)
  next
    case 2 then show ?thesis using m p3 unfolding lgx_def by (simp add: Let_def)
  next
    case 3
    then have "(z mod int p) ^ ((p - 1) div 2) mod int p = int p - 1"
      using m p3 by (simp add: zmod_minus1)
    then show ?thesis using 3 p3 unfolding lgx_def by (simp add: Let_def)
  qed
qed

lemma lgx_mult: "lgx p (a * b) = lgx p a * lgx p b"
  by (simp add: lgx_eq leg_mult)

lemma lgx_pm:
  assumes "\<not> int p dvd z"
  shows "lgx p z = 1 \<or> lgx p z = -1"
proof -
  have "Legendre z (int p) \<noteq> 0" using assms leg_zero_iff by simp
  then show ?thesis using leg_vals[of z "int p"] by (auto simp: lgx_eq)
qed

lemma lgx_sq:
  assumes "\<not> int p dvd z"
  shows "lgx p z * lgx p z = 1"
  using lgx_pm[OF assms] by auto

lemma lgx_cong:
  assumes "int p dvd a - b"
  shows "lgx p a = lgx p b"
  using assms leg_cong[of a b "int p"] by (simp add: lgx_eq cong_iff_dvd_diff)

lemma lgx_m1: "lgx p (-1) = sg (int ((p - 1) div 2))"
  by (simp add: lgx_eq leg_minus1)

lemma lgx_neg: "lgx p (-z) = sg (int ((p - 1) div 2)) * lgx p z"
proof -
  have "lgx p (-z) = lgx p ((-1) * z)" by simp
  also have "\<dots> = lgx p (-1) * lgx p z" by (rule lgx_mult)
  also have "lgx p (-1) = sg (int ((p - 1) div 2))" by (rule lgx_m1)
  finally show ?thesis .
qed

end

section \<open>The tables for p = 2\<close>

definition e2 :: "int \<Rightarrow> int" where "e2 z = ((z - 1) div 2) mod 2"
definition w2 :: "int \<Rightarrow> int" where "w2 z = ((z * z - 1) div 8) mod 2"

definition E8 :: "int \<Rightarrow> int" where "E8 r = (if r = 3 \<or> r = 7 then 1 else 0)"
definition W8 :: "int \<Rightarrow> int" where "W8 r = (if r = 3 \<or> r = 5 then 1 else 0)"

text \<open>All finite checks on odd residues modulo 8 are done by evaluation on the list of residues.\<close>

lemma res_set: "r \<in> {1, 3, 5, 7 :: int} \<Longrightarrow> r \<in> set [1, 3, 5, 7 :: int]"
  by simp

lemma tab_div8: "\<forall>r \<in> set [1, 3, 5, 7 :: int]. 8 dvd (r * r - 1) \<and> ((r * r - 1) div 8) mod 2 = W8 r"
  by eval

lemma tab_sq8: "\<forall>r \<in> set [1, 3, 5, 7 :: int]. (r * r) mod 8 = 1"
  by eval

lemma tab_neg8: "\<forall>r \<in> set [1, 3, 5, 7 :: int]. E8 r * E8 (8 - r) = 0"
  by eval

lemma tab_mult8:
  "\<forall>r \<in> set [1, 3, 5, 7 :: int]. \<forall>s \<in> set [1, 3, 5, 7].
     even (E8 ((r * s) mod 8) - E8 r - E8 s) \<and> even (W8 ((r * s) mod 8) - W8 r - W8 s)"
  by eval

lemma odd_mod8:
  fixes z :: int
  assumes "odd z"
  shows "z mod 8 \<in> {1, 3, 5, 7}"
proof -
  from assms have "odd z" by simp
  then have "z mod 2 = 1" by (simp add: odd_iff_mod_2_eq_one)
  then show ?thesis by (simp add: insert_iff) presburger
qed

lemma e2_mod8:
  assumes "odd z"
  shows "e2 z = E8 (z mod 8)"
proof -
  have "z mod 2 = 1" using assms by (simp add: odd_iff_mod_2_eq_one)
  then have "(z mod 8 = 1 \<and> e2 z = 0) \<or> (z mod 8 = 3 \<and> e2 z = 1) \<or> (z mod 8 = 5 \<and> e2 z = 0)
             \<or> (z mod 8 = 7 \<and> e2 z = 1)"
    unfolding e2_def by presburger
  then show ?thesis unfolding E8_def by auto
qed

lemma w2_mod8:
  assumes "odd z"
  shows "w2 z = W8 (z mod 8)"
proof -
  define q where "q = z div 8"
  define r where "r = z mod 8"
  have z: "z = 8 * q + r" by (simp add: q_def r_def)
  have r4: "r \<in> {1, 3, 5, 7}" using odd_mod8[OF assms] by (simp add: r_def)
  have sq: "z * z - 1 = 8 * (8 * q * q + 2 * q * r) + (r * r - 1)"
    by (simp add: z algebra_simps)
  define K where "K = 8 * q * q + 2 * q * r"
  have Keven: "even K" by (simp add: K_def)
  have "(z * z - 1) div 8 = K + (r * r - 1) div 8"
  proof -
    have "8 dvd (r * r - 1)" using bspec[OF tab_div8 res_set[OF r4]] by simp
    then show ?thesis using sq by (simp add: K_def)
  qed
  then have "w2 z = (K + (r * r - 1) div 8) mod 2" by (simp add: w2_def)
  also have "\<dots> = ((r * r - 1) div 8) mod 2"
    using Keven by (simp add: mod2_eq_if)
  also have "\<dots> = W8 r" using bspec[OF tab_div8 res_set[OF r4]] by simp
  finally show ?thesis by (simp add: r_def)
qed

lemma res_mult_E8:
  assumes "r \<in> {1, 3, 5, 7}" "s \<in> {1, 3, 5, 7}"
  shows "even (E8 ((r * s) mod 8) - E8 r - E8 s)"
  using bspec[OF bspec[OF tab_mult8 res_set[OF assms(1)]] res_set[OF assms(2)]] by simp

lemma res_mult_W8:
  assumes "r \<in> {1, 3, 5, 7}" "s \<in> {1, 3, 5, 7}"
  shows "even (W8 ((r * s) mod 8) - W8 r - W8 s)"
  using bspec[OF bspec[OF tab_mult8 res_set[OF assms(1)]] res_set[OF assms(2)]] by simp

lemma e2_mult:
  assumes "odd u" "odd u'"
  shows "even (e2 (u * u') - e2 u - e2 u')"
proof -
  have o: "odd (u * u')" using assms by simp
  have "(u * u') mod 8 = ((u mod 8) * (u' mod 8)) mod 8" by (simp add: mod_simps)
  then show ?thesis
    using res_mult_E8[OF odd_mod8[OF assms(1)] odd_mod8[OF assms(2)]]
    by (simp add: e2_mod8[OF o] e2_mod8[OF assms(1)] e2_mod8[OF assms(2)])
qed

lemma w2_mult:
  assumes "odd u" "odd u'"
  shows "even (w2 (u * u') - w2 u - w2 u')"
proof -
  have o: "odd (u * u')" using assms by simp
  have "(u * u') mod 8 = ((u mod 8) * (u' mod 8)) mod 8" by (simp add: mod_simps)
  then show ?thesis
    using res_mult_W8[OF odd_mod8[OF assms(1)] odd_mod8[OF assms(2)]]
    by (simp add: w2_mod8[OF o] w2_mod8[OF assms(1)] w2_mod8[OF assms(2)])
qed

lemma e2_w2_sq:
  assumes "odd u"
  shows "e2 (u * u) = 0" "w2 (u * u) = 0"
proof -
  have o: "odd (u * u)" using assms by simp
  have "(u * u) mod 8 = ((u mod 8) * (u mod 8)) mod 8" by (simp add: mod_simps)
  moreover have "((u mod 8) * (u mod 8)) mod 8 = 1"
    using bspec[OF tab_sq8 res_set[OF odd_mod8[OF assms]]] by simp
  ultimately have "(u * u) mod 8 = 1" by simp
  then show "e2 (u * u) = 0" "w2 (u * u) = 0"
    by (simp_all add: e2_mod8[OF o] w2_mod8[OF o] E8_def W8_def)
qed

lemma e2_neg:
  assumes "odd u"
  shows "e2 u * e2 (-u) = 0"
proof -
  have o: "odd (-u)" using assms by simp
  have "(-u) mod 8 = 8 - u mod 8" using odd_mod8[OF assms] by (simp add: insert_iff) presburger
  then show ?thesis
    using bspec[OF tab_neg8 res_set[OF odd_mod8[OF assms]]]
    by (simp add: e2_mod8[OF assms] e2_mod8[OF o])
qed

lemma w2_neg: "w2 (-u) = w2 u"
  by (simp add: w2_def)

lemma e2_prod:
  assumes "odd a" "odd b"
  shows "e2 (a * b) = E8 (((a mod 8) * (b mod 8)) mod 8)"
proof -
  have "(a * b) mod 8 = ((a mod 8) * (b mod 8)) mod 8" by (simp add: mod_simps)
  then show ?thesis using e2_mod8[of "a * b"] assms by simp
qed

lemma w2_prod:
  assumes "odd a" "odd b"
  shows "w2 (a * b) = W8 (((a mod 8) * (b mod 8)) mod 8)"
proof -
  have "(a * b) mod 8 = ((a mod 8) * (b mod 8)) mod 8" by (simp add: mod_simps)
  then show ?thesis using w2_mod8[of "a * b"] assms by simp
qed

section \<open>The local symbol on nonzero integers\<close>

definition hZ :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "hZ p a b =
    (if p = 2
     then sg (e2 (un p a) * e2 (un p b) + int (vp p a) * w2 (un p b) + int (vp p b) * w2 (un p a))
     else sg (int (vp p a * vp p b) * int ((p - 1) div 2)) * lgx p (un p a) ^ vp p b * lgx p (un p b) ^ vp p a)"

lemma hZ2:
  assumes "p = 2"
  shows "hZ p a b = sg (e2 (un p a) * e2 (un p b) + int (vp p a) * w2 (un p b) + int (vp p b) * w2 (un p a))"
  using assms unfolding hZ_def by simp

lemma hZo:
  assumes "p \<noteq> 2"
  shows "hZ p a b = sg (int (vp p a * vp p b) * int ((p - 1) div 2)) * lgx p (un p a) ^ vp p b * lgx p (un p b) ^ vp p a"
  using assms unfolding hZ_def by simp

lemma hZ_sym: "hZ p a b = hZ p b a"
proof (cases "p = 2")
  case True
  have e: "e2 (un p a) * e2 (un p b) + int (vp p a) * w2 (un p b) + int (vp p b) * w2 (un p a)
      = e2 (un p b) * e2 (un p a) + int (vp p b) * w2 (un p a) + int (vp p a) * w2 (un p b)"
    by (simp add: algebra_simps)
  have "hZ p a b = sg (e2 (un p a) * e2 (un p b) + int (vp p a) * w2 (un p b) + int (vp p b) * w2 (un p a))"
    by (rule hZ2[OF True])
  also have "\<dots> = sg (e2 (un p b) * e2 (un p a) + int (vp p b) * w2 (un p a) + int (vp p a) * w2 (un p b))"
    by (simp only: e)
  also have "\<dots> = hZ p b a" by (rule hZ2[OF True, symmetric])
  finally show ?thesis .
next
  case False
  show ?thesis by (simp add: hZo[OF False] mult.commute)
qed

lemma un_odd2:
  assumes "prime p" "p = 2" "n \<noteq> 0"
  shows "odd (un p n)"
proof -
  have p1: "1 < p" by (rule prime_gt_1_nat[OF assms(1)])
  have "\<not> int p dvd un p n" using vu_decomp[OF p1 assms(3)] by simp
  then show ?thesis using assms(2) by simp
qed

lemma hZ_mult:
  assumes "prime p" "a \<noteq> 0" "a' \<noteq> 0"
  shows "hZ p (a * a') b = hZ p a b * hZ p a' b"
proof (cases "p = 2")
  case True
  have ou: "odd (un p a)" "odd (un p a')" using un_odd2[OF assms(1) True] assms(2,3) by auto
  have d1: "even (e2 (un p a * un p a') - e2 (un p a) - e2 (un p a'))" using e2_mult[OF ou] .
  have d2: "even (w2 (un p a * un p a') - w2 (un p a) - w2 (un p a'))" using w2_mult[OF ou] .
  have vm: "vp p (a * a') = vp p a + vp p a'" "un p (a * a') = un p a * un p a'"
    using vu_mult[OF assms] by simp_all
  let ?v = "un p b"
  let ?E = "e2 (un p a * un p a') * e2 ?v + int (vp p a + vp p a') * w2 ?v + int (vp p b) * w2 (un p a * un p a')"
  let ?E1 = "e2 (un p a) * e2 ?v + int (vp p a) * w2 ?v + int (vp p b) * w2 (un p a)"
  let ?E2 = "e2 (un p a') * e2 ?v + int (vp p a') * w2 ?v + int (vp p b) * w2 (un p a')"
  have "?E - (?E1 + ?E2) =
        (e2 (un p a * un p a') - e2 (un p a) - e2 (un p a')) * e2 ?v
        + int (vp p b) * (w2 (un p a * un p a') - w2 (un p a) - w2 (un p a'))"
    by (simp add: algebra_simps)
  then have "even (?E - (?E1 + ?E2))" using d1 d2 by simp
  then have key: "sg ?E = sg (?E1 + ?E2)" by (rule sg_cong)
  have "hZ p (a * a') b = sg (e2 (un p (a * a')) * e2 ?v + int (vp p (a * a')) * w2 ?v
                              + int (vp p b) * w2 (un p (a * a')))"
    by (rule hZ2[OF True])
  also have "\<dots> = sg ?E" by (simp only: vm)
  also have "\<dots> = sg (?E1 + ?E2)" by (rule key)
  also have "\<dots> = sg ?E1 * sg ?E2" by (rule sg_add)
  also have "\<dots> = hZ p a b * hZ p a' b" by (simp only: hZ2[OF True])
  finally show ?thesis .
next
  case False
  have vm: "vp p (a * a') = vp p a + vp p a'" "un p (a * a') = un p a * un p a'"
    using vu_mult[OF assms] by simp_all
  have s: "int ((vp p a + vp p a') * vp p b) * int ((p - 1) div 2)
        = int (vp p a * vp p b) * int ((p - 1) div 2) + int (vp p a' * vp p b) * int ((p - 1) div 2)"
    by (simp add: algebra_simps)
  have "hZ p (a * a') b = sg (int ((vp p a + vp p a') * vp p b) * int ((p - 1) div 2))
          * lgx p (un p a * un p a') ^ vp p b * lgx p (un p b) ^ (vp p a + vp p a')"
    using hZo[OF False, of "a * a'" b] vm by simp
  also have "\<dots> = sg (int (vp p a * vp p b) * int ((p - 1) div 2)) * lgx p (un p a) ^ vp p b * lgx p (un p b) ^ vp p a
        * (sg (int (vp p a' * vp p b) * int ((p - 1) div 2)) * lgx p (un p a') ^ vp p b * lgx p (un p b) ^ vp p a')"
    by (simp only: s sg_add lgx_mult[OF assms(1) False] power_mult_distrib power_add; simp add: algebra_simps)
  also have "\<dots> = hZ p a b * hZ p a' b" by (simp add: hZo[OF False])
  finally show ?thesis .
qed

section \<open>Basic properties of the local symbol on integers\<close>

lemma un_unit:
  assumes "prime p" "n \<noteq> 0"
  shows "\<not> int p dvd un p n"
  using vu_decomp[of p n] assms prime_gt_1_nat by blast

lemma vp_unit:
  assumes "\<not> int p dvd n"
  shows "vp p n = 0" "un p n = n"
proof -
  have "p \<le> 1 \<or> n = 0 \<or> \<not> int p dvd n" using assms by simp
  then show "vp p n = 0" "un p n = n" by (simp_all add: vp_base un_base)
qed

lemma abs_sg: "\<bar>sg k\<bar> = 1"
  using sg_pm[of k] by auto

lemma pow_aux:
  fixes L c :: int and g :: nat
  assumes "L * L = 1" "even (int (g * g) * c + c * int g)"
  shows "sg (int (g * g) * c) * L ^ g * (sg c * L) ^ g = 1"
proof -
  have "sg c ^ g = sg (c * int g)" by (rule sg_pow)
  moreover have "L ^ g * L ^ g = 1"
    using assms(1) by (metis power_mult_distrib power_one)
  moreover have "sg (int (g * g) * c) * sg (c * int g) = 1"
    using sg_add[of "int (g * g) * c" "c * int g"] sg_even[OF assms(2)] by simp
  ultimately show ?thesis by (simp add: power_mult_distrib algebra_simps)
qed

lemma even_aux: "even (int (g * g) * c + c * int g)"
proof -
  have "int (g * g) * c + c * int g = c * (int g * (int g + 1))" by (simp add: algebra_simps)
  moreover have "even (int g * (int g + 1))" by (cases "even (int g)") simp_all
  ultimately show ?thesis by simp
qed

lemma hZ_abs:
  assumes "prime p" "a \<noteq> 0" "b \<noteq> 0"
  shows "\<bar>hZ p a b\<bar> = 1"
proof (cases "p = 2")
  case True
  then show ?thesis by (simp add: hZ2 abs_sg)
next
  case False
  have 1: "\<bar>lgx p (un p a)\<bar> = 1" using lgx_pm[OF assms(1) False un_unit[OF assms(1) assms(2)]] by auto
  have 2: "\<bar>lgx p (un p b)\<bar> = 1" using lgx_pm[OF assms(1) False un_unit[OF assms(1) assms(3)]] by auto
  show ?thesis by (simp add: hZo[OF False] abs_mult power_abs abs_sg 1 2)
qed

lemma hZ_pm:
  assumes "prime p" "a \<noteq> 0" "b \<noteq> 0"
  shows "hZ p a b = 1 \<or> hZ p a b = -1"
  using hZ_abs[OF assms] by (cases "0 \<le> hZ p a b") auto

lemma hZ_unit_sq:
  assumes "prime p" "t \<noteq> 0" "b \<noteq> 0"
  shows "hZ p (t * t) b = 1"
proof (cases "p = 2")
  case True
  have ou: "odd (un p t)" using un_odd2[OF assms(1) True assms(2)] .
  have vm: "vp p (t * t) = vp p t + vp p t" "un p (t * t) = un p t * un p t"
    using vu_mult[OF assms(1) assms(2) assms(2)] by simp_all
  have z: "e2 (un p t * un p t) = 0" "w2 (un p t * un p t) = 0" using e2_w2_sq[OF ou] by simp_all
  have ev: "even (e2 (un p t * un p t) * e2 (un p b) + int (vp p t + vp p t) * w2 (un p b)
              + int (vp p b) * w2 (un p t * un p t))"
  proof -
    have "int (vp p t + vp p t) = 2 * int (vp p t)" by simp
    then show ?thesis by (simp add: z)
  qed
  have "hZ p (t * t) b = sg (e2 (un p (t * t)) * e2 (un p b) + int (vp p (t * t)) * w2 (un p b)
                            + int (vp p b) * w2 (un p (t * t)))"
    by (rule hZ2[OF True])
  also have "\<dots> = sg (e2 (un p t * un p t) * e2 (un p b) + int (vp p t + vp p t) * w2 (un p b)
                      + int (vp p b) * w2 (un p t * un p t))"
    by (simp only: vm)
  also have "\<dots> = 1" by (rule sg_even[OF ev])
  finally show ?thesis .
next
  case False
  have vm: "vp p (t * t) = vp p t + vp p t" "un p (t * t) = un p t * un p t"
    using vu_mult[OF assms(1) assms(2) assms(2)] by simp_all
  have ut: "lgx p (un p t) * lgx p (un p t) = 1"
    using lgx_sq[OF assms(1) False un_unit[OF assms(1) assms(2)]] .
  have ub: "lgx p (un p b) * lgx p (un p b) = 1"
    using lgx_sq[OF assms(1) False un_unit[OF assms(1) assms(3)]] .
  have ev0: "even (vp p (t * t))" using vm by simp
  have ev: "even (int (vp p (t * t) * vp p b) * int ((p - 1) div 2))" using ev0 by simp
  have "hZ p (t * t) b = sg (int (vp p (t * t) * vp p b) * int ((p - 1) div 2))
          * lgx p (un p (t * t)) ^ vp p b * lgx p (un p b) ^ vp p (t * t)"
    by (rule hZo[OF False])
  also have "\<dots> = 1 * lgx p (un p (t * t)) ^ vp p b * lgx p (un p b) ^ vp p (t * t)"
    by (simp only: sg_even[OF ev])
  also have "\<dots> = 1 * lgx p (un p t * un p t) ^ vp p b * lgx p (un p b) ^ (vp p t + vp p t)"
    by (simp only: vm)
  also have "\<dots> = 1"
  proof -
    have "lgx p (un p t * un p t) = 1" using ut lgx_mult[OF assms(1) False] by metis
    moreover have "lgx p (un p b) ^ (vp p t + vp p t) = 1"
      using ub by (simp add: power_add power_mult_distrib[symmetric])
    ultimately show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma hZ_sq:
  assumes "prime p" "a \<noteq> 0" "t \<noteq> 0" "b \<noteq> 0"
  shows "hZ p (a * (t * t)) b = hZ p a b"
  using hZ_mult[OF assms(1) assms(2), of "t * t" b] hZ_unit_sq[OF assms(1) assms(3) assms(4)] assms(3)
  by simp

lemma hZ_neg:
  assumes "prime p" "a \<noteq> 0"
  shows "hZ p a (-a) = 1"
proof -
  have p1: "1 < p" by (rule prime_gt_1_nat[OF assms(1)])
  have h: "vp p (a * (-1)) = vp p a + vp p (-1)" "un p (a * (-1)) = un p a * un p (-1)"
    using vu_mult[OF assms(1) assms(2), of "-1"] by simp_all
  have vm: "vp p (-a) = vp p a" "un p (-a) = - un p a"
    using h vu_neg_one[OF p1] by simp_all
  show ?thesis
  proof (cases "p = 2")
    case True
    have ou: "odd (un p a)" using un_odd2[OF assms(1) True assms(2)] .
    have ev: "even (e2 (un p a) * e2 (- un p a) + int (vp p a) * w2 (- un p a) + int (vp p a) * w2 (un p a))"
      by (simp add: e2_neg[OF ou] w2_neg)
    have "hZ p a (-a) = sg (e2 (un p a) * e2 (un p (-a)) + int (vp p a) * w2 (un p (-a)) + int (vp p (-a)) * w2 (un p a))"
      by (rule hZ2[OF True])
    also have "\<dots> = sg (e2 (un p a) * e2 (- un p a) + int (vp p a) * w2 (- un p a) + int (vp p a) * w2 (un p a))"
      by (simp only: vm)
    also have "\<dots> = 1" by (rule sg_even[OF ev])
    finally show ?thesis .
  next
    case False
    have ua: "lgx p (un p a) * lgx p (un p a) = 1"
      using lgx_sq[OF assms(1) False un_unit[OF assms(1) assms(2)]] .
    have "hZ p a (-a) = sg (int (vp p a * vp p (-a)) * int ((p - 1) div 2))
            * lgx p (un p a) ^ vp p (-a) * lgx p (un p (-a)) ^ vp p a"
      by (rule hZo[OF False])
    also have "\<dots> = sg (int (vp p a * vp p a) * int ((p - 1) div 2)) * lgx p (un p a) ^ vp p a
            * (sg (int ((p - 1) div 2)) * lgx p (un p a)) ^ vp p a"
      by (simp only: vm lgx_neg[OF assms(1) False])
    also have "\<dots> = 1" by (rule pow_aux[OF ua even_aux])
    finally show ?thesis .
  qed
qed

section \<open>Steinberg relation on integers\<close>

lemma tab_B1: "\<forall>r \<in> set [1, 3, 5, 7 :: int]. \<forall>s \<in> set [1, 3, 5, 7]. \<forall>t \<in> set [1, 3, 5, 7].
    t = (s + 2 * r) mod 8 \<longrightarrow> even (E8 ((r * t) mod 8) * E8 ((s * t) mod 8) + 1 * W8 ((s * t) mod 8))"
  by eval

lemma tab_B2: "\<forall>r \<in> set [1, 3, 5, 7 :: int]. \<forall>s \<in> set [1, 3, 5, 7]. \<forall>t \<in> set [1, 3, 5, 7].
    t = (s + 4 * r) mod 8 \<longrightarrow> even (E8 ((r * t) mod 8) * E8 ((s * t) mod 8) + 2 * W8 ((s * t) mod 8))"
  by eval

lemma tab_B3: "\<forall>r \<in> set [1, 3, 5, 7 :: int]. \<forall>s \<in> set [1, 3, 5, 7]. \<forall>t \<in> set [1, 3, 5, 7].
    t = s \<longrightarrow> even (E8 ((r * t) mod 8) * E8 ((s * t) mod 8)) \<and> even (W8 ((s * t) mod 8))"
  by eval

lemma tab_A1: "\<forall>r \<in> set [1, 3, 5, 7 :: int]. \<forall>s \<in> set [1, 3, 5, 7]. \<forall>t \<in> set [1, 3, 5, 7].
    (r + s) mod 8 = (2 * t) mod 8 \<longrightarrow>
    even (E8 ((r * t) mod 8) * E8 ((s * t) mod 8) + 1 * (W8 ((s * t) mod 8) + W8 ((r * t) mod 8)))"
  by eval

lemma tab_A2: "\<forall>r \<in> set [1, 3, 5, 7 :: int]. \<forall>s \<in> set [1, 3, 5, 7]. \<forall>t \<in> set [1, 3, 5, 7].
    (r + s) mod 8 = 4 \<longrightarrow>
    even (E8 ((r * t) mod 8) * E8 ((s * t) mod 8) + 2 * (W8 ((s * t) mod 8) + W8 ((r * t) mod 8)))"
  by eval

lemma tab_A3: "\<forall>r \<in> set [1, 3, 5, 7 :: int]. \<forall>s \<in> set [1, 3, 5, 7]. \<forall>t \<in> set [1, 3, 5, 7].
    (r + s) mod 8 = 0 \<longrightarrow>
    even (E8 ((r * t) mod 8) * E8 ((s * t) mod 8)) \<and> even (W8 ((s * t) mod 8) + W8 ((r * t) mod 8))"
  by eval

lemma tbB1:
  assumes "r \<in> {1, 3, 5, 7}" "s \<in> {1, 3, 5, 7}" "t \<in> {1, 3, 5, 7}" "t = (s + 2 * r) mod 8"
  shows "even (E8 ((r * t) mod 8) * E8 ((s * t) mod 8) + 1 * W8 ((s * t) mod 8))"
  using bspec[OF bspec[OF bspec[OF tab_B1 res_set[OF assms(1)]] res_set[OF assms(2)]] res_set[OF assms(3)]] assms(4)
  by simp

lemma tbB2:
  assumes "r \<in> {1, 3, 5, 7}" "s \<in> {1, 3, 5, 7}" "t \<in> {1, 3, 5, 7}" "t = (s + 4 * r) mod 8"
  shows "even (E8 ((r * t) mod 8) * E8 ((s * t) mod 8) + 2 * W8 ((s * t) mod 8))"
  using bspec[OF bspec[OF bspec[OF tab_B2 res_set[OF assms(1)]] res_set[OF assms(2)]] res_set[OF assms(3)]] assms(4)
  by simp

lemma tbB3:
  assumes "r \<in> {1, 3, 5, 7}" "s \<in> {1, 3, 5, 7}" "t \<in> {1, 3, 5, 7}" "t = s"
  shows "even (E8 ((r * t) mod 8) * E8 ((s * t) mod 8))" "even (W8 ((s * t) mod 8))"
  using bspec[OF bspec[OF bspec[OF tab_B3 res_set[OF assms(1)]] res_set[OF assms(2)]] res_set[OF assms(3)]] assms(4)
  by simp_all

lemma tbA1:
  assumes "r \<in> {1, 3, 5, 7}" "s \<in> {1, 3, 5, 7}" "t \<in> {1, 3, 5, 7}" "(r + s) mod 8 = (2 * t) mod 8"
  shows "even (E8 ((r * t) mod 8) * E8 ((s * t) mod 8) + 1 * (W8 ((s * t) mod 8) + W8 ((r * t) mod 8)))"
  using bspec[OF bspec[OF bspec[OF tab_A1 res_set[OF assms(1)]] res_set[OF assms(2)]] res_set[OF assms(3)]] assms(4)
  by simp

lemma tbA2:
  assumes "r \<in> {1, 3, 5, 7}" "s \<in> {1, 3, 5, 7}" "t \<in> {1, 3, 5, 7}" "(r + s) mod 8 = 4"
  shows "even (E8 ((r * t) mod 8) * E8 ((s * t) mod 8) + 2 * (W8 ((s * t) mod 8) + W8 ((r * t) mod 8)))"
  using bspec[OF bspec[OF bspec[OF tab_A2 res_set[OF assms(1)]] res_set[OF assms(2)]] res_set[OF assms(3)]] assms(4)
  by simp

lemma tbA3:
  assumes "r \<in> {1, 3, 5, 7}" "s \<in> {1, 3, 5, 7}" "t \<in> {1, 3, 5, 7}" "(r + s) mod 8 = 0"
  shows "even (E8 ((r * t) mod 8) * E8 ((s * t) mod 8))" "even (W8 ((s * t) mod 8) + W8 ((r * t) mod 8))"
  using bspec[OF bspec[OF bspec[OF tab_A3 res_set[OF assms(1)]] res_set[OF assms(2)]] res_set[OF assms(3)]] assms(4)
  by simp_all

lemma m8_B1: fixes x y z u :: int assumes "x = 2 * u" "x + y = z" shows "z mod 8 = (y mod 8 + 2 * (u mod 8)) mod 8"
proof -
  have z: "z = y + 2 * u" using assms by simp
  have "z mod 8 = (y + 2 * u) mod 8" by (simp add: z)
  also have "\<dots> = (y mod 8 + (2 * u) mod 8) mod 8" by (rule mod_add_eq[symmetric])
  also have "(2 * u) mod 8 = (2 * (u mod 8)) mod 8" by (simp add: mod_simps)
  also have "(y mod 8 + (2 * (u mod 8)) mod 8) mod 8 = (y mod 8 + 2 * (u mod 8)) mod 8" by (rule mod_add_right_eq)
  finally show ?thesis .
qed

lemma m8_B2: fixes x y z u :: int assumes "x = 4 * u" "x + y = z" shows "z mod 8 = (y mod 8 + 4 * (u mod 8)) mod 8"
proof -
  have z: "z = y + 4 * u" using assms by simp
  have "z mod 8 = (y + 4 * u) mod 8" by (simp add: z)
  also have "\<dots> = (y mod 8 + (4 * u) mod 8) mod 8" by (rule mod_add_eq[symmetric])
  also have "(4 * u) mod 8 = (4 * (u mod 8)) mod 8" by (simp add: mod_simps)
  also have "(y mod 8 + (4 * (u mod 8)) mod 8) mod 8 = (y mod 8 + 4 * (u mod 8)) mod 8" by (rule mod_add_right_eq)
  finally show ?thesis .
qed

lemma m8_B3: fixes x y z u :: int assumes "x = 8 * u" "x + y = z" shows "z mod 8 = y mod 8"
proof -
  have z: "z = y + 8 * u" using assms by simp
  show ?thesis by (simp add: z)
qed

lemma m8_A1: fixes x y z w :: int assumes "z = 2 * w" "x + y = z" shows "(x mod 8 + y mod 8) mod 8 = (2 * (w mod 8)) mod 8"
proof -
  have "(x mod 8 + y mod 8) mod 8 = (x + y) mod 8" by (simp add: mod_simps)
  also have "\<dots> = (2 * w) mod 8" using assms by simp
  also have "\<dots> = (2 * (w mod 8)) mod 8" by (simp add: mod_simps)
  finally show ?thesis .
qed

lemma m8_A2: fixes x y z w :: int assumes "z = 4 * w" "odd w" "x + y = z" shows "(x mod 8 + y mod 8) mod 8 = 4"
proof -
  obtain k where k: "w = 2 * k + 1" using assms(2) by (auto elim: oddE)
  have "(x mod 8 + y mod 8) mod 8 = (x + y) mod 8" by (simp add: mod_simps)
  also have "\<dots> = (4 + 8 * k) mod 8" using assms k by (simp add: algebra_simps)
  also have "\<dots> = 4" by simp
  finally show ?thesis .
qed

lemma m8_A3: fixes x y z w :: int assumes "z = 8 * w" "x + y = z" shows "(x mod 8 + y mod 8) mod 8 = 0"
proof -
  have "(x mod 8 + y mod 8) mod 8 = (x + y) mod 8" by (simp add: mod_simps)
  also have "\<dots> = (8 * w) mod 8" using assms by simp
  also have "\<dots> = 0" by simp
  finally show ?thesis .
qed

text \<open>Case B: p divides x but not y (so not z = x + y).\<close>

lemma stein_B:
  assumes pp: "prime p" and nz: "x \<noteq> 0" "y \<noteq> 0" "z \<noteq> 0" and s: "x + y = z"
    and dx: "int p dvd x" and ny: "\<not> int p dvd y"
  shows "hZ p (x * z) (y * z) = 1"
proof -
  have p1: "1 < p" by (rule prime_gt_1_nat[OF pp])
  have nz': "\<not> int p dvd z"
  proof
    assume dzz: "int p dvd z"
    have "z - x = y" using s by linarith
    moreover have "int p dvd z - x" using dzz dx by (rule dvd_diff)
    ultimately show False using ny by simp
  qed
  have vz: "vp p z = 0" "un p z = z" using vp_unit[OF nz'] by simp_all
  have vy: "vp p y = 0" "un p y = y" using vp_unit[OF ny] by simp_all
  have vxz: "vp p (x * z) = vp p x" "un p (x * z) = un p x * z"
    using vu_mult[OF pp nz(1) nz(3)] vz by simp_all
  have vyz: "vp p (y * z) = 0" "un p (y * z) = y * z"
    using vu_mult[OF pp nz(2) nz(3)] vz vy by simp_all
  show ?thesis
  proof (cases "p = 2")
    case False
    have zy: "z - y = x" using s by linarith
    have c1: "lgx p z = lgx p y"
    proof (rule lgx_cong[OF pp False])
      show "int p dvd z - y" using dx zy by simp
    qed
    have yy: "lgx p y * lgx p y = 1" using lgx_sq[OF pp False ny] .
    have "hZ p (x * z) (y * z) = sg (int (vp p (x * z) * vp p (y * z)) * int ((p - 1) div 2))
          * lgx p (un p (x * z)) ^ vp p (y * z) * lgx p (un p (y * z)) ^ vp p (x * z)"
      by (rule hZo[OF False])
    also have "\<dots> = lgx p (y * z) ^ vp p x"
      by (simp only: vxz vyz) (simp add: sg_zero)
    also have "\<dots> = 1" by (simp add: lgx_mult[OF pp False] c1 yy)
    finally show ?thesis .
  next
    case True
    have ox: "odd (un p x)" using un_odd2[OF pp True nz(1)] .
    have ip: "int p = 2" using True by simp
    have oy: "odd y" "odd z" using ny nz' ip by simp_all
    have dec: "x = int p ^ vp p x * un p x" using vu_decomp[OF p1 nz(1)] by simp
    have a0: "vp p x \<noteq> 0"
    proof
      assume "vp p x = 0"
      then have "x = un p x" using dec by simp
      then show False using dx ox ip by simp
    qed
    have xe: "x = 2 ^ vp p x * un p x" using dec ip by simp
    have rr: "un p x mod 8 \<in> {1, 3, 5, 7}" "y mod 8 \<in> {1, 3, 5, 7}" "z mod 8 \<in> {1, 3, 5, 7}"
      using odd_mod8 ox oy by simp_all
    have ex: "e2 (un p x * z) = E8 (((un p x mod 8) * (z mod 8)) mod 8)" using e2_prod[OF ox oy(2)] .
    have ey: "e2 (y * z) = E8 (((y mod 8) * (z mod 8)) mod 8)" using e2_prod[OF oy(1) oy(2)] .
    have wy: "w2 (y * z) = W8 (((y mod 8) * (z mod 8)) mod 8)" using w2_prod[OF oy(1) oy(2)] .
    have ev: "even (e2 (un p x * z) * e2 (y * z) + int (vp p x) * w2 (y * z))"
    proof -
      consider (one) "vp p x = 1" | (two) "vp p x = 2" | (big) "vp p x \<ge> 3" using a0 by linarith
      then show ?thesis
      proof cases
        case one
        then have "x = 2 * un p x" using xe by simp
        then have h: "z mod 8 = (y mod 8 + 2 * (un p x mod 8)) mod 8" using m8_B1 s by blast
        show ?thesis unfolding ex ey wy one of_nat_1 by (rule tbB1[OF rr h])
      next
        case two
        then have "x = 4 * un p x" using xe by simp
        then have h: "z mod 8 = (y mod 8 + 4 * (un p x mod 8)) mod 8" using m8_B2 s by blast
        show ?thesis unfolding ex ey wy two of_nat_numeral by (rule tbB2[OF rr h])
      next
        case big
        then obtain m where "vp p x = m + 3" using le_Suc_ex by (metis add.commute)
        then have "x = 8 * (2 ^ m * un p x)" using xe by (simp add: algebra_simps power_add)
        then obtain n where "x = 8 * n" by blast
        then have h: "z mod 8 = y mod 8" using m8_B3 s by blast
        have e1: "even (e2 (un p x * z) * e2 (y * z))" unfolding ex ey by (rule tbB3(1)[OF rr h])
        have e2': "even (w2 (y * z))" unfolding wy by (rule tbB3(2)[OF rr h])
        have "even (int (vp p x) * w2 (y * z))" using e2' by simp
        then show ?thesis using e1 by (metis even_add)
      qed
    qed
    have "hZ p (x * z) (y * z) = sg (e2 (un p (x * z)) * e2 (un p (y * z)) + int (vp p (x * z)) * w2 (un p (y * z))
                                   + int (vp p (y * z)) * w2 (un p (x * z)))"
      by (rule hZ2[OF True])
    also have "\<dots> = sg (e2 (un p x * z) * e2 (y * z) + int (vp p x) * w2 (y * z) + int 0 * w2 (un p x * z))"
      by (simp only: vxz vyz)
    also have "\<dots> = 1"
    proof (rule sg_even)
      show "even (e2 (un p x * z) * e2 (y * z) + int (vp p x) * w2 (y * z) + int 0 * w2 (un p x * z))"
        using ev by simp
    qed
    finally show ?thesis .
  qed
qed

text \<open>Case A: p divides neither x nor y, but divides z = x + y.\<close>

lemma stein_A:
  assumes pp: "prime p" and nz: "x \<noteq> 0" "y \<noteq> 0" "z \<noteq> 0" and s: "x + y = z"
    and nx: "\<not> int p dvd x" and ny: "\<not> int p dvd y" and dz: "int p dvd z"
  shows "hZ p (x * z) (y * z) = 1"
proof -
  have p1: "1 < p" by (rule prime_gt_1_nat[OF pp])
  have vx: "vp p x = 0" "un p x = x" using vp_unit[OF nx] by simp_all
  have vy: "vp p y = 0" "un p y = y" using vp_unit[OF ny] by simp_all
  have vxz: "vp p (x * z) = vp p z" "un p (x * z) = x * un p z"
    using vu_mult[OF pp nz(1) nz(3)] vx by simp_all
  have vyz: "vp p (y * z) = vp p z" "un p (y * z) = y * un p z"
    using vu_mult[OF pp nz(2) nz(3)] vy by simp_all
  have uz: "\<not> int p dvd un p z" using un_unit[OF pp nz(3)] .
  have dec: "z = int p ^ vp p z * un p z" using vu_decomp[OF p1 nz(3)] by simp
  have g0: "vp p z \<noteq> 0"
  proof
    assume "vp p z = 0"
    then have "z = un p z" using dec by simp
    then show False using dz uz by simp
  qed
  show ?thesis
  proof (cases "p = 2")
    case False
    define c where "c = int ((p - 1) div 2)"
    define g where "g = vp p z"
    have qp: "prime (int p)" using pp by (simp add: prime_nat_int_transfer)
    have yx: "lgx p y = sg c * lgx p x"
    proof -
      have e: "y - (-x) = z" using s by linarith
      have "int p dvd y - (-x)" using e dz by metis
      then have "lgx p y = lgx p (-x)" by (rule lgx_cong[OF pp False])
      then show ?thesis using lgx_neg[OF pp False] c_def by simp
    qed
    have Ay: "lgx p (y * un p z) = sg c * lgx p (x * un p z)"
      by (simp add: lgx_mult[OF pp False] yx mult.assoc)
    have nxu: "\<not> int p dvd x * un p z" using qp nx uz by (simp add: prime_dvd_mult_iff)
    have LL: "lgx p (x * un p z) * lgx p (x * un p z) = 1" by (rule lgx_sq[OF pp False nxu])
    have "hZ p (x * z) (y * z) = sg (int (vp p (x * z) * vp p (y * z)) * int ((p - 1) div 2))
          * lgx p (un p (x * z)) ^ vp p (y * z) * lgx p (un p (y * z)) ^ vp p (x * z)"
      by (rule hZo[OF False])
    also have "\<dots> = sg (int (g * g) * c) * lgx p (x * un p z) ^ g * (sg c * lgx p (x * un p z)) ^ g"
      by (simp only: vxz vyz g_def[symmetric] c_def[symmetric] Ay)
    also have "\<dots> = 1" by (rule pow_aux[OF LL even_aux])
    finally show ?thesis .
  next
    case True
    have ow: "odd (un p z)" using un_odd2[OF pp True nz(3)] .
    have ip: "int p = 2" using True by simp
    have ox: "odd x" "odd y" using nx ny ip by simp_all
    have ez: "z = 2 ^ vp p z * un p z" using dec ip by simp
    have rr: "x mod 8 \<in> {1, 3, 5, 7}" "y mod 8 \<in> {1, 3, 5, 7}" "un p z mod 8 \<in> {1, 3, 5, 7}"
      using odd_mod8 ox ow by simp_all
    have ex: "e2 (x * un p z) = E8 (((x mod 8) * (un p z mod 8)) mod 8)" using e2_prod[OF ox(1) ow] .
    have ey: "e2 (y * un p z) = E8 (((y mod 8) * (un p z mod 8)) mod 8)" using e2_prod[OF ox(2) ow] .
    have wx: "w2 (x * un p z) = W8 (((x mod 8) * (un p z mod 8)) mod 8)" using w2_prod[OF ox(1) ow] .
    have wy: "w2 (y * un p z) = W8 (((y mod 8) * (un p z mod 8)) mod 8)" using w2_prod[OF ox(2) ow] .
    have ev: "even (e2 (x * un p z) * e2 (y * un p z) + int (vp p z) * (w2 (y * un p z) + w2 (x * un p z)))"
    proof -
      consider (one) "vp p z = 1" | (two) "vp p z = 2" | (big) "vp p z \<ge> 3" using g0 by linarith
      then show ?thesis
      proof cases
        case one
        then have "z = 2 * un p z" using ez by simp
        then have h: "(x mod 8 + y mod 8) mod 8 = (2 * (un p z mod 8)) mod 8" using m8_A1 s by blast
        show ?thesis unfolding ex ey wx wy one of_nat_1 by (rule tbA1[OF rr h])
      next
        case two
        then have "z = 4 * un p z" using ez by simp
        then have h: "(x mod 8 + y mod 8) mod 8 = 4" using m8_A2 s ow by blast
        show ?thesis unfolding ex ey wx wy two of_nat_numeral by (rule tbA2[OF rr h])
      next
        case big
        then obtain m where "vp p z = m + 3" using le_Suc_ex by (metis add.commute)
        then have "z = 8 * (2 ^ m * un p z)" using ez by (simp add: algebra_simps power_add)
        then obtain n where "z = 8 * n" by blast
        then have h: "(x mod 8 + y mod 8) mod 8 = 0" using m8_A3 s by blast
        have e1: "even (e2 (x * un p z) * e2 (y * un p z))" unfolding ex ey by (rule tbA3(1)[OF rr h])
        have e2': "even (w2 (y * un p z) + w2 (x * un p z))" unfolding wx wy by (rule tbA3(2)[OF rr h])
        have "even (int (vp p z) * (w2 (y * un p z) + w2 (x * un p z)))" using e2' by simp
        then show ?thesis using e1 by (metis even_add)
      qed
    qed
    have "hZ p (x * z) (y * z) = sg (e2 (un p (x * z)) * e2 (un p (y * z)) + int (vp p (x * z)) * w2 (un p (y * z))
                                   + int (vp p (y * z)) * w2 (un p (x * z)))"
      by (rule hZ2[OF True])
    also have "\<dots> = sg (e2 (x * un p z) * e2 (y * un p z) + int (vp p z) * w2 (y * un p z)
                       + int (vp p z) * w2 (x * un p z))"
      by (simp only: vxz vyz)
    also have "\<dots> = 1"
    proof (rule sg_even)
      show "even (e2 (x * un p z) * e2 (y * un p z) + int (vp p z) * w2 (y * un p z)
                  + int (vp p z) * w2 (x * un p z))"
        using ev by (simp add: algebra_simps)
    qed
    finally show ?thesis .
  qed
qed

lemma stein_C:
  assumes pp: "prime p" and nz: "x \<noteq> 0" "y \<noteq> 0" "z \<noteq> 0" and s: "x + y = z"
    and nx: "\<not> int p dvd x" and ny: "\<not> int p dvd y" and nzz: "\<not> int p dvd z"
  shows "hZ p (x * z) (y * z) = 1"
proof (cases "p = 2")
  case True
  have ip: "int p = 2" using True by simp
  have "\<not> (2 :: int) dvd x" "\<not> (2 :: int) dvd y" "\<not> (2 :: int) dvd z" using nx ny nzz ip by simp_all
  then have False using s by presburger
  then show ?thesis by simp
next
  case False
  have "vp p (x * z) = 0" "vp p (y * z) = 0"
    using vu_mult[OF pp nz(1) nz(3)] vu_mult[OF pp nz(2) nz(3)] vp_unit[OF nx] vp_unit[OF ny] vp_unit[OF nzz]
    by simp_all
  then show ?thesis by (simp add: hZo[OF False] sg_zero)
qed

theorem hZ_steinberg_int:
  assumes pp: "prime p" and nz: "x \<noteq> 0" "y \<noteq> 0" "z \<noteq> 0" and s: "x + y = z"
  shows "hZ p (x * z) (y * z) = 1"
proof -
  have p1: "1 < p" by (rule prime_gt_1_nat[OF pp])
  have main: "\<And>n. \<forall>x y z. nat \<bar>z\<bar> = n \<longrightarrow> x \<noteq> 0 \<longrightarrow> y \<noteq> 0 \<longrightarrow> z \<noteq> 0 \<longrightarrow> x + y = z
                  \<longrightarrow> hZ p (x * z) (y * z) = 1"
  proof -
    fix n
    show "\<forall>x y z. nat \<bar>z\<bar> = n \<longrightarrow> x \<noteq> 0 \<longrightarrow> y \<noteq> 0 \<longrightarrow> z \<noteq> 0 \<longrightarrow> x + y = z
                  \<longrightarrow> hZ p (x * z) (y * z) = 1"
    proof (induction n rule: less_induct)
      case (less n)
      show ?case
      proof (intro allI impI)
        fix x y z
        assume hn: "nat \<bar>z\<bar> = n" and nzx: "x \<noteq> 0" and nzy: "y \<noteq> 0" and nzz: "z \<noteq> 0" and s: "x + y = z"
        have nzs: "x \<noteq> 0" "y \<noteq> 0" "z \<noteq> 0" using nzx nzy nzz by simp_all
        show "hZ p (x * z) (y * z) = 1"
        proof (cases "int p dvd x \<and> int p dvd y")
          case True
          then obtain x' y' where x: "x = int p * x'" and y: "y = int p * y'" by blast
          define z' where "z' = x' + y'"
          have z: "z = int p * z'" using s x y z'_def by (simp add: algebra_simps)
          have nz': "x' \<noteq> 0" "y' \<noteq> 0" "z' \<noteq> 0" using nzs x y z by auto
          have lt: "nat \<bar>z'\<bar> < n"
          proof -
            have "\<bar>z'\<bar> \<ge> 1" using nz'(3) by simp
            then have "int p * \<bar>z'\<bar> > 1 * \<bar>z'\<bar>" using p1 by (intro mult_strict_right_mono) simp_all
            then have "\<bar>z'\<bar> < \<bar>z\<bar>" using z by (simp add: abs_mult)
            then show ?thesis using hn by arith
          qed
          have IH: "hZ p (x' * z') (y' * z') = 1"
            using less.IH[OF lt] nz' z'_def by blast
          have pne: "int p \<noteq> 0" using p1 by simp
          have ex: "x * z = (x' * z') * (int p * int p)" using x z by (simp add: algebra_simps)
          have ey: "y * z = (y' * z') * (int p * int p)" using y z by (simp add: algebra_simps)
          have n1: "x' * z' \<noteq> 0" "y' * z' \<noteq> 0" using nz' by simp_all
          have yz0: "y * z \<noteq> 0" using nzy nzz by simp
          have "hZ p (x * z) (y * z) = hZ p ((x' * z') * (int p * int p)) (y * z)" using ex by simp
          also have "\<dots> = hZ p (x' * z') (y * z)" by (rule hZ_sq[OF pp n1(1) pne yz0])
          also have "\<dots> = hZ p (y * z) (x' * z')" by (rule hZ_sym)
          also have "\<dots> = hZ p ((y' * z') * (int p * int p)) (x' * z')" using ey by simp
          also have "\<dots> = hZ p (y' * z') (x' * z')" by (rule hZ_sq[OF pp n1(2) pne n1(1)])
          also have "\<dots> = hZ p (x' * z') (y' * z')" by (rule hZ_sym)
          finally show ?thesis using IH by simp
        next
          case False
          show ?thesis
          proof (cases "int p dvd x")
            case True
            then have "\<not> int p dvd y" using False by simp
            then show ?thesis using stein_B[OF pp nzs s True] by simp
          next
            case nx: False
            show ?thesis
            proof (cases "int p dvd y")
              case True
              have s': "y + x = z" using s by simp
              have "hZ p (y * z) (x * z) = 1" using stein_B[OF pp nzy nzx nzz s' True nx] .
              then show ?thesis using hZ_sym by metis
            next
              case ny: False
              show ?thesis
              proof (cases "int p dvd z")
                case True then show ?thesis using stein_A[OF pp nzs s nx ny] by simp
              next
                case False then show ?thesis using stein_C[OF pp nzs s nx ny] by simp
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  show ?thesis using main[of "nat \<bar>z\<bar>"] nz s by blast
qed

section \<open>The symbol on rationals\<close>

definition X :: "rat \<Rightarrow> int" where
  "X a = fst (quotient_of a) * snd (quotient_of a)"

definition hilbert :: "nat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> int" where
  "hilbert p a b = hZ p (X a) (X b)"

definition hilbert_inf :: "rat \<Rightarrow> rat \<Rightarrow> int" where
  "hilbert_inf a b = (if a < 0 \<and> b < 0 then -1 else 1)"

lemma qparts:
  assumes "a \<noteq> 0"
  obtains n d where "a = of_int n / of_int d" "n \<noteq> 0" "d \<noteq> 0" "X a = n * d"
proof -
  obtain n d where q: "quotient_of a = (n, d)" by (cases "quotient_of a") blast
  have d: "d > 0" using quotient_of_denom_pos[OF q] .
  have a: "a = of_int n / of_int d" using quotient_of_div[OF q] .
  have n: "n \<noteq> 0" using a assms by auto
  show thesis
    using that[of n d] a n d q by (simp add: X_def)
qed

lemma X_ne0:
  assumes "a \<noteq> 0"
  shows "X a \<noteq> 0"
proof -
  obtain n d where nd: "a = of_int n / of_int d" "n \<noteq> 0" "d \<noteq> 0" "X a = n * d" using qparts[OF assms] .
  then show ?thesis by simp
qed

lemma X_rep:
  assumes "a = of_int x / of_int z" "z \<noteq> 0" "a \<noteq> 0"
  obtains d where "d \<noteq> 0" "X a * (z * z) = (x * z) * (d * d)"
proof -
  obtain n d where nd: "a = of_int n / of_int d" "n \<noteq> 0" "d \<noteq> 0" "X a = n * d" using qparts[OF assms(3)] .
  have "(of_int n :: rat) * of_int z = of_int x * of_int d"
    using assms(1) nd(1) assms(2) nd(3) by (simp add: field_simps)
  then have "n * z = x * d" by (metis of_int_eq_iff of_int_mult)
  then have "X a * (z * z) = (x * z) * (d * d)" using nd(4) by (simp add: algebra_simps)
  then show thesis using that nd(3) by blast
qed

lemma hZ_X_rep:
  assumes "prime p" "a = of_int x / of_int z" "x \<noteq> 0" "z \<noteq> 0" "b \<noteq> 0"
  shows "hZ p (X a) b = hZ p (x * z) b"
proof -
  have a0: "a \<noteq> 0" using assms(2,3,4) by simp
  have xz0: "x * z \<noteq> 0" using assms(3,4) by simp
  obtain d where d: "d \<noteq> 0" "X a * (z * z) = (x * z) * (d * d)" using X_rep[OF assms(2) assms(4) a0] .
  have "hZ p (X a) b = hZ p (X a * (z * z)) b" by (rule hZ_sq[OF assms(1) X_ne0[OF a0] assms(4) assms(5), symmetric])
  also have "\<dots> = hZ p ((x * z) * (d * d)) b" by (simp only: d(2))
  also have "\<dots> = hZ p (x * z) b" by (rule hZ_sq[OF assms(1) xz0 d(1) assms(5)])
  finally show ?thesis .
qed

lemma hilbert_sym: "hilbert p a b = hilbert p b a"
  by (simp add: hilbert_def hZ_sym)

lemma hilbert_pm:
  assumes "prime p" "a \<noteq> 0" "b \<noteq> 0"
  shows "hilbert p a b = 1 \<or> hilbert p a b = -1"
  using hZ_pm[OF assms(1) X_ne0[OF assms(2)] X_ne0[OF assms(3)]] by (simp add: hilbert_def)

lemma hilbert_mult:
  assumes "prime p" "a \<noteq> 0" "a' \<noteq> 0" "b \<noteq> 0"
  shows "hilbert p (a * a') b = hilbert p a b * hilbert p a' b"
proof -
  obtain n d where nd: "a = of_int n / of_int d" "n \<noteq> 0" "d \<noteq> 0" "X a = n * d" using qparts[OF assms(2)] .
  obtain n' d' where nd': "a' = of_int n' / of_int d'" "n' \<noteq> 0" "d' \<noteq> 0" "X a' = n' * d'"
    using qparts[OF assms(3)] .
  have e: "a * a' = of_int (n * n') / of_int (d * d')" using nd(1) nd'(1) by simp
  have "hZ p (X (a * a')) (X b) = hZ p ((n * n') * (d * d')) (X b)"
    using hZ_X_rep[OF assms(1) e _ _ X_ne0[OF assms(4)]] nd(2,3) nd'(2,3) by simp
  also have "(n * n') * (d * d') = X a * X a'" using nd(4) nd'(4) by (simp add: algebra_simps)
  also have "hZ p (X a * X a') (X b) = hZ p (X a) (X b) * hZ p (X a') (X b)"
    using hZ_mult[OF assms(1) X_ne0[OF assms(2)] X_ne0[OF assms(3)]] .
  finally show ?thesis by (simp add: hilbert_def)
qed

lemma hilbert_mult_right:
  assumes "prime p" "a \<noteq> 0" "b \<noteq> 0" "b' \<noteq> 0"
  shows "hilbert p a (b * b') = hilbert p a b * hilbert p a b'"
  using hilbert_mult[OF assms(1) assms(3) assms(4) assms(2)] by (simp add: hilbert_sym)

lemma hilbert_square_one:
  assumes "prime p" "c \<noteq> 0" "b \<noteq> 0"
  shows "hilbert p (c * c) b = 1"
proof -
  obtain n d where nd: "c = of_int n / of_int d" "n \<noteq> 0" "d \<noteq> 0" "X c = n * d" using qparts[OF assms(2)] .
  have e: "c * c = of_int (n * n) / of_int (d * d)" using nd(1) by simp
  have "hZ p (X (c * c)) (X b) = hZ p ((n * n) * (d * d)) (X b)"
    using hZ_X_rep[OF assms(1) e _ _ X_ne0[OF assms(3)]] nd(2,3) by simp
  also have "(n * n) * (d * d) = (n * d) * (n * d)" by (simp add: algebra_simps)
  also have "hZ p ((n * d) * (n * d)) (X b) = 1"
    using hZ_unit_sq[OF assms(1) _ X_ne0[OF assms(3)], of "n * d"] nd(2,3) by simp
  finally show ?thesis by (simp add: hilbert_def)
qed

theorem hilbert_square_invariant:
  assumes "prime p" "a \<noteq> 0" "c \<noteq> 0" "b \<noteq> 0"
  shows "hilbert p (a * c\<^sup>2) b = hilbert p a b"
proof -
  have "c * c \<noteq> 0" using assms(3) by simp
  then show ?thesis
    using hilbert_mult[OF assms(1) assms(2) _ assms(4), of "c * c"] hilbert_square_one[OF assms(1) assms(3) assms(4)]
    by (simp add: power2_eq_square)
qed

theorem hilbert_neg:
  assumes "prime p" "a \<noteq> 0"
  shows "hilbert p a (-a) = 1"
proof -
  obtain n d where nd: "a = of_int n / of_int d" "n \<noteq> 0" "d \<noteq> 0" "X a = n * d" using qparts[OF assms(2)] .
  have e: "-a = of_int (-n) / of_int d" using nd(1) by simp
  have "hilbert p a (-a) = hilbert p (-a) a" by (rule hilbert_sym)
  also have "\<dots> = hZ p (X (-a)) (X a)" by (simp add: hilbert_def)
  also have "\<dots> = hZ p ((-n) * d) (X a)"
    using hZ_X_rep[OF assms(1) e _ _ X_ne0[OF assms(2)]] nd(2,3) by simp
  also have "(-n) * d = - (X a)" using nd(4) by simp
  also have "hZ p (- (X a)) (X a) = hZ p (X a) (- (X a))" by (rule hZ_sym)
  also have "\<dots> = 1" using hZ_neg[OF assms(1) X_ne0[OF assms(2)]] .
  finally show ?thesis .
qed

theorem hilbert_steinberg:
  assumes "prime p" "a \<noteq> 0" "a \<noteq> 1"
  shows "hilbert p a (1 - a) = 1"
proof -
  obtain n d where nd: "a = of_int n / of_int d" "n \<noteq> 0" "d \<noteq> 0" "X a = n * d" using qparts[OF assms(2)] .
  have one: "1 - a \<noteq> 0" using assms(3) by simp
  have nd1: "n \<noteq> d" using nd(1,3) assms(3) by auto
  have e: "1 - a = of_int (d - n) / of_int d" using nd(1) nd(3) by (simp add: field_simps)
  have "hilbert p a (1 - a) = hZ p (X a) (X (1 - a))" by (simp add: hilbert_def)
  also have "\<dots> = hZ p (n * d) (X (1 - a))"
    using hZ_X_rep[OF assms(1) nd(1) nd(2) nd(3) X_ne0[OF one]] .
  also have "\<dots> = hZ p (X (1 - a)) (n * d)" by (rule hZ_sym)
  also have "\<dots> = hZ p ((d - n) * d) (n * d)"
    using hZ_X_rep[OF assms(1) e _ nd(3), of "n * d"] nd1 nd(2,3) by simp
  also have "\<dots> = hZ p (n * d) ((d - n) * d)" by (rule hZ_sym)
  also have "\<dots> = 1"
    using hZ_steinberg_int[OF assms(1), of n "d - n" d] nd(2,3) nd1 by simp
  finally show ?thesis .
qed

section \<open>The real place\<close>

lemma hilbert_inf_pm: "hilbert_inf a b = 1 \<or> hilbert_inf a b = -1"
  by (simp add: hilbert_inf_def)

lemma hilbert_inf_sym: "hilbert_inf a b = hilbert_inf b a"
  by (auto simp: hilbert_inf_def)

lemma hilbert_inf_mult:
  assumes "a \<noteq> 0" "a' \<noteq> 0" "b \<noteq> 0"
  shows "hilbert_inf (a * a') b = hilbert_inf a b * hilbert_inf a' b"
  using assms
  by (auto simp: hilbert_inf_def mult_less_0_iff not_less order_le_less)

lemma hilbert_inf_square:
  assumes "c \<noteq> 0"
  shows "hilbert_inf (a * c\<^sup>2) b = hilbert_inf a b"
proof -
  have "c\<^sup>2 > 0" using assms by simp
  then show ?thesis by (auto simp: hilbert_inf_def mult_less_0_iff not_less order_le_less)
qed

lemma hilbert_inf_neg: "hilbert_inf a (-a) = 1"
  by (auto simp: hilbert_inf_def)

lemma hilbert_inf_steinberg: "hilbert_inf a (1 - a) = 1"
  by (auto simp: hilbert_inf_def)

section \<open>Checks by evaluation\<close>

lemma hilbert_value_m1_m1_2: "hilbert 2 (-1) (-1) = -1" by eval
lemma hilbert_value_m1_m1_3: "hilbert 3 (-1) (-1) = 1" by eval
lemma hilbert_value_2_3_3: "hilbert 3 2 3 = -1" by eval
lemma hilbert_value_3_3_2: "hilbert 2 3 3 = -1" by eval
lemma hilbert_value_5_7_inf: "hilbert_inf 5 7 = 1" by eval
lemma hilbert_value_m5_m7_inf: "hilbert_inf (-5) (-7) = -1" by eval
lemma hilbert_value_7_m1_2: "hilbert 2 7 (-1) = -1" by eval

text \<open>A pair with denominators (values of excovery.forma_racional.hilbert).\<close>

lemma hilbert_value_rational:
  "hilbert 2 (-6/35) (10/3) = -1" "hilbert 3 (-6/35) (10/3) = 1"
  "hilbert 5 (-6/35) (10/3) = -1" "hilbert 7 (-6/35) (10/3) = 1"
  by eval+

definition isprime_nat :: "nat \<Rightarrow> bool" where
  "isprime_nat n = (2 \<le> n \<and> list_all (\<lambda>d. \<not> d dvd n) [2..<n])"

lemma isprime_nat_iff: "isprime_nat n \<longleftrightarrow> prime n"
  unfolding isprime_nat_def list_all_iff set_upt prime_nat_iff'
  by (auto simp: prime_nat_iff)

definition bad_primes :: "int \<Rightarrow> int \<Rightarrow> nat list" where
  "bad_primes a b = filter (\<lambda>p. int p dvd 2 * a * b \<and> isprime_nat p) [2..<Suc (nat \<bar>2 * a * b\<bar>)]"

text \<open>The product of the symbols over the real place and over the primes dividing 2ab. At every other
prime the symbol is 1, because a and b are then units and the p-adic valuations vanish.\<close>

definition hilbert_all :: "int \<Rightarrow> int \<Rightarrow> int" where
  "hilbert_all a b = hilbert_inf (of_int a) (of_int b) *
     prod_list (map (\<lambda>p. hilbert p (of_int a) (of_int b)) (bad_primes a b))"

definition nonzero30 :: "int list" where "nonzero30 = filter (\<lambda>n. n \<noteq> 0) [-30..30]"

theorem hilbert_reciprocity_checked_30:
  "list_all (\<lambda>a. list_all (\<lambda>b. hilbert_all a b = 1) nonzero30) nonzero30"
  by eval

section \<open>Hasse invariants of diagonal forms\<close>

fun hasse_with :: "(rat \<Rightarrow> rat \<Rightarrow> int) \<Rightarrow> rat list \<Rightarrow> int" where
  "hasse_with h [] = 1"
| "hasse_with h (a # as) = prod_list (map (h a) as) * hasse_with h as"

definition hasse :: "nat \<Rightarrow> rat list \<Rightarrow> int" where "hasse p = hasse_with (hilbert p)"
definition hasse_inf :: "rat list \<Rightarrow> int" where "hasse_inf = hasse_with hilbert_inf"

text \<open>The Hasse invariant c_p of the form <a_1,...,a_n> is the product of (a_i,a_j)_p over i < j.\<close>

lemma hasse_swap:
  assumes "\<And>x y. h x y = h y x"
  shows "hasse_with h (a # b # cs) = hasse_with h (b # a # cs)"
  using assms by (simp add: algebra_simps)

lemma prod_list_pm:
  fixes f :: "'a \<Rightarrow> int"
  assumes "\<And>y. y \<in> set bs \<Longrightarrow> f y = 1 \<or> f y = -1"
  shows "prod_list (map f bs) = 1 \<or> prod_list (map f bs) = -1"
  using assms
proof (induction bs)
  case Nil then show ?case by simp
next
  case (Cons b bs)
  have "f b = 1 \<or> f b = -1" using Cons.prems by simp
  moreover have "prod_list (map f bs) = 1 \<or> prod_list (map f bs) = -1"
    by (rule Cons.IH) (use Cons.prems in fastforce)
  ultimately show ?case by auto
qed

lemma hasse_pm:
  assumes "\<And>x y. x \<in> set as \<Longrightarrow> y \<in> set as \<Longrightarrow> h x y = 1 \<or> h x y = -1"
  shows "hasse_with h as = 1 \<or> hasse_with h as = -1"
  using assms
proof (induction as)
  case Nil then show ?case by simp
next
  case (Cons a as)
  have "prod_list (map (h a) as) = 1 \<or> prod_list (map (h a) as) = -1"
    by (rule prod_list_pm) (use Cons.prems in fastforce)
  moreover have "hasse_with h as = 1 \<or> hasse_with h as = -1"
    by (rule Cons.IH) (use Cons.prems in fastforce)
  ultimately show ?case by auto
qed

lemma hasse_pm_nonzero:
  assumes "prime p" "\<forall>a \<in> set as. a \<noteq> 0"
  shows "hasse p as = 1 \<or> hasse p as = -1"
  unfolding hasse_def
proof (rule hasse_pm)
  fix x y assume "x \<in> set as" "y \<in> set as"
  then show "hilbert p x y = 1 \<or> hilbert p x y = -1" using assms hilbert_pm by blast
qed

lemma hasse_values_1111:
  "hasse 2 [1, 1, 1, 1] = 1" "hasse 3 [1, 1, 1, 1] = 1" "hasse 5 [1, 1, 1, 1] = 1" "hasse 7 [1, 1, 1, 1] = 1"
  "hasse_inf [1, 1, 1, 1] = 1"
  by (simp_all add: hasse_def hasse_inf_def) eval+

lemma hasse_values_1117:
  "hasse 2 [1, 1, 1, 7] = 1" "hasse 3 [1, 1, 1, 7] = 1" "hasse 5 [1, 1, 1, 7] = 1"
  "hasse 7 [1, 1, 1, 7] = 1" "hasse 11 [1, 1, 1, 7] = 1" "hasse_inf [1, 1, 1, 7] = 1"
  by (simp_all add: hasse_def hasse_inf_def) eval+

text \<open>Nontrivial invariants (values of the Python tool): <3,3,3> has c_2 = c_3 = -1; <3,5,15> has c_2 = c_5 = -1;
<-1,-1,-1> has c_2 = -1; <1/2,3/5> has c_3 = c_5 = -1.\<close>

lemma hasse_values_nontrivial:
  "hasse 2 [3, 3, 3] = -1" "hasse 3 [3, 3, 3] = -1" "hasse 5 [3, 3, 3] = 1" "hasse 7 [3, 3, 3] = 1"
  "hasse 2 [3, 5, 15] = -1" "hasse 3 [3, 5, 15] = 1" "hasse 5 [3, 5, 15] = -1" "hasse 7 [3, 5, 15] = 1"
  "hasse 2 [-1, -1, -1] = -1" "hasse 3 [-1, -1, -1] = 1" "hasse_inf [-1, -1, -1] = -1"
  "hasse 2 [1/2, 3/5] = 1" "hasse 3 [1/2, 3/5] = -1" "hasse 5 [1/2, 3/5] = -1" "hasse 7 [1/2, 3/5] = 1"
  by (simp_all add: hasse_def hasse_inf_def) eval+

end
