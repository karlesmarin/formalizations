(*  Title:      Migotti.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

(* Migotti (1883): for distinct primes p, q the coefficients of the cyclotomic polynomial Phi_pq lie in {-1, 0, 1}.
   Here Phi_pq is the quotient (1 - X^(pq)) (1 - X) / ((1 - X^p) (1 - X^q)), which equals the cyclotomic polynomial for
   distinct primes p, q (Moebius product formula); that identification is classical and not formalized here.
   Proof: Phi_pq = 1 - (1 - X) * B, where B is the sum of X^(pa+qb-pq) over 0 <= a < q, 0 <= b < p with pa+qb >= pq;
   the exponents pa+qb are distinct and (a,b) -> (pa+qb) mod pq is bijective. *)
theory Migotti
  imports "HOL-Computational_Algebra.Polynomial"
begin

definition XX :: "int poly" where "XX = monom 1 1"

lemma XX_eq: "XX = [:0, 1:]"
  unfolding XX_def by (simp add: monom_Suc monom_0)

lemma monom_XX: "monom (1::int) n = XX ^ n"
  unfolding XX_def by (simp add: monom_power)

definition phi_pq :: "nat \<Rightarrow> nat \<Rightarrow> int poly" where
  "phi_pq p q = ((1 - XX ^ (p * q)) * (1 - XX)) div ((1 - XX ^ p) * (1 - XX ^ q))"

lemma geom: fixes Y :: "'a::comm_ring_1" shows "(1 - Y) * (\<Sum>i<n. Y ^ i) = 1 - Y ^ n"
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc n)
  have "(1 - Y) * (\<Sum>i<Suc n. Y ^ i) = (1 - Y) * (\<Sum>i<n. Y ^ i) + (1 - Y) * Y ^ n"
    by (simp add: algebra_simps)
  also have "\<dots> = 1 - Y ^ Suc n" using Suc.IH by (simp add: algebra_simps)
  finally show ?case .
qed

lemma core_alg:
  fixes X M A B G D TT :: "'a::idom"
  assumes h1: "TT = A + M * B" and h2: "A + B = G" and h3: "(1 - X) * G = 1 - M"
    and h4: "D * TT = (1 - M) ^ 2" and h5: "1 - M \<noteq> 0"
  shows "D * (1 - (1 - X) * B) = (1 - X) * (1 - M)"
proof -
  have hA: "A = G - B" using h2 by (simp add: algebra_simps eq_diff_eq)
  have e1: "(1 - X) * TT = (1 - M) * (1 - (1 - X) * B)"
  proof -
    have "(1 - X) * TT = (1 - X) * G - (1 - M) * ((1 - X) * B)"
      by (simp add: h1 hA algebra_simps)
    also have "\<dots> = (1 - M) * (1 - (1 - X) * B)" using h3 by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have "(1 - M) * (D * (1 - (1 - X) * B)) = (1 - M) * ((1 - X) * (1 - M))"
  proof -
    have "(1 - M) * (D * (1 - (1 - X) * B)) = D * ((1 - M) * (1 - (1 - X) * B))"
      by (simp add: algebra_simps)
    also have "\<dots> = D * ((1 - X) * TT)" using e1 by simp
    also have "\<dots> = (1 - X) * (D * TT)" by (simp add: algebra_simps)
    also have "\<dots> = (1 - X) * (1 - M) ^ 2" by (simp only: h4)
    also have "\<dots> = (1 - M) * ((1 - X) * (1 - M))" by (simp add: power2_eq_square algebra_simps)
    finally show ?thesis .
  qed
  then show ?thesis by (rule mult_left_cancel[THEN iffD1, OF h5])
qed

lemma dvd_small: fixes m d :: int assumes "m dvd d" "\<bar>d\<bar> < m" shows "d = 0"
proof (rule ccontr)
  assume "d \<noteq> 0"
  then have pos: "0 < \<bar>d\<bar>" by simp
  have "m dvd \<bar>d\<bar>" using assms(1) by simp
  then have "m \<le> \<bar>d\<bar>" by (rule zdvd_imp_le[OF _ pos])
  with assms(2) show False by simp
qed

locale migotti =
  fixes p q :: nat
  assumes p0: "0 < p" and q0: "0 < q" and cop: "coprime p q"
begin

definition e :: "nat \<times> nat \<Rightarrow> nat" where "e z = p * fst z + q * snd z"
definition P :: "(nat \<times> nat) set" where "P = {..<q} \<times> {..<p}"
definition S0 :: "(nat \<times> nat) set" where "S0 = {z \<in> P. e z < p * q}"
definition S1 :: "(nat \<times> nat) set" where "S1 = {z \<in> P. p * q \<le> e z}"
definition A :: "int poly" where "A = (\<Sum>z\<in>S0. XX ^ e z)"
definition B :: "int poly" where "B = (\<Sum>z\<in>S1. XX ^ (e z - p * q))"
definition T1 :: "int poly" where "T1 = (\<Sum>a<q. (XX ^ p) ^ a)"
definition T2 :: "int poly" where "T2 = (\<Sum>b<p. (XX ^ q) ^ b)"
definition G :: "int poly" where "G = (\<Sum>r<p * q. XX ^ r)"

lemma finP: "finite P" by (simp add: P_def)
lemma finS0: "finite S0" using finP by (simp add: S0_def)
lemma finS1: "finite S1" using finP by (simp add: S1_def)

lemma e_less: assumes "z \<in> P" shows "e z < 2 * (p * q)"
proof -
  obtain a b where z: "z = (a, b)" by (cases z)
  with assms have ab: "a < q" "b < p" by (simp_all add: P_def)
  have "p * a < p * q" using ab(1) p0 by (rule mult_strict_left_mono)
  moreover have "q * b < p * q"
    using mult_strict_left_mono[OF ab(2) q0] by (simp only: mult.commute[of q p])
  ultimately show ?thesis unfolding e_def z by (simp, linarith)
qed

lemma e_inj: assumes "z \<in> P" "z' \<in> P" "e z mod (p * q) = e z' mod (p * q)" shows "z = z'"
proof -
  obtain a b where z: "z = (a, b)" by (cases z)
  obtain a' b' where z': "z' = (a', b')" by (cases z')
  from assms z z' have ab: "a < q" "b < p" "a' < q" "b' < p" and
    h: "(p * a + q * b) mod (p * q) = (p * a' + q * b') mod (p * q)"
    by (simp_all add: P_def e_def)
  have hi: "(int p * int a + int q * int b) mod int (p * q) = (int p * int a' + int q * int b') mod int (p * q)"
    using arg_cong[where f = int, OF h] by (simp add: zmod_int)
  then have d: "int (p * q) dvd (int p * int a + int q * int b) - (int p * int a' + int q * int b')"
    by (simp add: mod_eq_dvd_iff)
  have dp: "int p dvd (int p * int a + int q * int b) - (int p * int a' + int q * int b')"
    using d by (metis dvd_trans dvd_triv_left of_nat_mult)
  have dq: "int q dvd (int p * int a + int q * int b) - (int p * int a' + int q * int b')"
    using d by (metis dvd_trans dvd_triv_right of_nat_mult)
  have cI: "coprime (int p) (int q)" using cop by (simp add: coprime_int_iff)
  have "int p dvd int q * (int b - int b')"
  proof -
    have "(int p * int a + int q * int b) - (int p * int a' + int q * int b')
        = int p * (int a - int a') + int q * (int b - int b')" by (simp add: algebra_simps)
    with dp have "int p dvd int p * (int a - int a') + int q * (int b - int b')" by simp
    then show ?thesis by (simp add: dvd_add_right_iff)
  qed
  then have pb: "int p dvd (int b - int b')" using cI by (simp add: coprime_dvd_mult_right_iff)
  have "int q dvd int p * (int a - int a')"
  proof -
    have "(int p * int a + int q * int b) - (int p * int a' + int q * int b')
        = int p * (int a - int a') + int q * (int b - int b')" by (simp add: algebra_simps)
    with dq have "int q dvd int p * (int a - int a') + int q * (int b - int b')" by simp
    then show ?thesis by (simp add: dvd_add_left_iff)
  qed
  then have qa: "int q dvd (int a - int a')" using cI by (simp add: coprime_dvd_mult_right_iff ac_simps)
  have "int b - int b' = 0" using pb ab(2) ab(4) by (intro dvd_small) auto
  moreover have "int a - int a' = 0" using qa ab(1) ab(3) by (intro dvd_small) auto
  ultimately show ?thesis using z z' by simp
qed

lemma bij_f: "bij_betw (\<lambda>z. e z mod (p * q)) P {..<p * q}"
proof -
  have inj: "inj_on (\<lambda>z. e z mod (p * q)) P" using e_inj by (intro inj_onI) auto
  have sub: "(\<lambda>z. e z mod (p * q)) ` P \<subseteq> {..<p * q}" using p0 q0 by auto
  have c: "card ((\<lambda>z. e z mod (p * q)) ` P) = p * q"
    using card_image[OF inj] by (simp add: P_def mult.commute)
  have "(\<lambda>z. e z mod (p * q)) ` P = {..<p * q}"
    using card_seteq[of "{..<p * q}" "(\<lambda>z. e z mod (p * q)) ` P"] sub c by simp
  with inj show ?thesis unfolding bij_betw_def by simp
qed

lemma e_inj_eq: assumes "z \<in> P" "z' \<in> P" "e z = e z'" shows "z = z'"
  using e_inj[OF assms(1,2)] assms(3) by simp

lemma TT_sum: "T1 * T2 = (\<Sum>z\<in>P. XX ^ e z)"
proof -
  have "T1 * T2 = (\<Sum>a<q. \<Sum>b<p. (XX ^ p) ^ a * (XX ^ q) ^ b)"
    unfolding T1_def T2_def by (simp add: sum_product)
  also have "\<dots> = (\<Sum>z\<in>P. (XX ^ p) ^ fst z * (XX ^ q) ^ snd z)"
    unfolding P_def by (subst sum.cartesian_product) (simp add: case_prod_beta)
  also have "\<dots> = (\<Sum>z\<in>P. XX ^ e z)"
    by (rule sum.cong) (simp_all add: e_def power_add power_mult)
  finally show ?thesis .
qed

lemma P_split: "P = S0 \<union> S1" "S0 \<inter> S1 = {}"
  unfolding S0_def S1_def by auto

lemma sum_P: "(\<Sum>z\<in>P. g z) = (\<Sum>z\<in>S0. g z) + (\<Sum>z\<in>S1. g z)" for g :: "_ \<Rightarrow> 'b::comm_monoid_add"
  by (subst P_split(1)) (rule sum.union_disjoint[OF finS0 finS1 P_split(2)])

lemma TT_decomp: "T1 * T2 = A + XX ^ (p * q) * B"
proof -
  have "XX ^ (p * q) * B = (\<Sum>z\<in>S1. XX ^ e z)"
    unfolding B_def sum_distrib_left
  proof (rule sum.cong[OF refl])
    fix z assume z: "z \<in> S1"
    then have le: "p * q \<le> e z" by (simp add: S1_def)
    have "XX ^ (p * q) * XX ^ (e z - p * q) = XX ^ (p * q + (e z - p * q))" by (simp only: power_add)
    also have "p * q + (e z - p * q) = e z" using le by simp
    finally show "XX ^ (p * q) * XX ^ (e z - p * q) = XX ^ e z" .
  qed
  then show ?thesis
    unfolding TT_sum A_def by (subst sum_P) simp
qed

lemma A_B_G: "A + B = G"
proof -
  have f0: "\<And>z. z \<in> S0 \<Longrightarrow> e z mod (p * q) = e z" by (auto simp: S0_def)
  have f1: "e z mod (p * q) = e z - p * q" if z: "z \<in> S1" for z
  proof -
    from that have "e z < 2 * (p * q)" "p * q \<le> e z" using e_less by (auto simp: S1_def)
    then have "e z - p * q < p * q" by simp
    moreover have "e z = (e z - p * q) + p * q" using \<open>p * q \<le> e z\<close> by simp
    ultimately show "e z mod (p * q) = e z - p * q"
      by (metis mod_add_self2 mod_less)
  qed
  have sA: "A = (\<Sum>z\<in>S0. XX ^ (e z mod (p * q)))"
    unfolding A_def by (rule sum.cong[OF refl]) (simp add: f0)
  have sB: "B = (\<Sum>z\<in>S1. XX ^ (e z mod (p * q)))"
    unfolding B_def by (rule sum.cong[OF refl]) (simp add: f1)
  have "A + B = (\<Sum>z\<in>S0. XX ^ (e z mod (p * q))) + (\<Sum>z\<in>S1. XX ^ (e z mod (p * q)))"
    using sA sB by simp
  also have "\<dots> = (\<Sum>z\<in>P. XX ^ (e z mod (p * q)))" by (rule sum_P[symmetric])
  also have "\<dots> = G" unfolding G_def
    using sum.reindex_bij_betw[OF bij_f, of "\<lambda>r. XX ^ r"] by simp
  finally show ?thesis .
qed

lemma ne1: "1 - XX ^ n \<noteq> (0::int poly)" if "0 < n" for n
proof
  assume "1 - XX ^ n = 0"
  then have "coeff (1 - XX ^ n) 0 = 0" by simp
  moreover have "coeff (1 - XX ^ n) 0 = 1"
    using that by (simp add: monom_XX[symmetric] coeff_monom)
  ultimately show False by simp
qed

lemma phi_identity:
  "((1 - XX ^ p) * (1 - XX ^ q)) * (1 - (1 - XX) * B) = (1 - XX ^ (p * q)) * (1 - XX)"
proof -
  have h3: "(1 - XX) * G = 1 - XX ^ (p * q)" using geom[of XX "p * q"] by (simp add: G_def)
  have e1: "(XX ^ p) ^ q = XX ^ (p * q)" by (simp add: power_mult)
  have e2: "(XX ^ q) ^ p = XX ^ (p * q)"
  proof -
    have "(XX ^ q) ^ p = XX ^ (q * p)" by (simp add: power_mult)
    also have "q * p = p * q" by (rule mult.commute)
    finally show ?thesis .
  qed
  have t1: "(1 - XX ^ p) * T1 = 1 - XX ^ (p * q)"
    unfolding T1_def using geom[of "XX ^ p" q] e1 by simp
  have t2: "(1 - XX ^ q) * T2 = 1 - XX ^ (p * q)"
    unfolding T2_def using geom[of "XX ^ q" p] e2 by simp
  have h4: "((1 - XX ^ p) * (1 - XX ^ q)) * (T1 * T2) = (1 - XX ^ (p * q)) ^ 2"
  proof -
    have "((1 - XX ^ p) * (1 - XX ^ q)) * (T1 * T2) = ((1 - XX ^ p) * T1) * ((1 - XX ^ q) * T2)"
      by (simp add: algebra_simps)
    also have "\<dots> = (1 - XX ^ (p * q)) ^ 2" by (simp add: t1 t2 power2_eq_square)
    finally show ?thesis .
  qed
  have h5: "1 - XX ^ (p * q) \<noteq> (0::int poly)" using ne1 p0 q0 by simp
  show ?thesis
    using core_alg[OF TT_decomp A_B_G h3 h4 h5] by (simp add: mult.commute)
qed

lemma phi_eq: "phi_pq p q = 1 - (1 - XX) * B"
proof -
  have D0: "(1 - XX ^ p) * (1 - XX ^ q) \<noteq> (0::int poly)" using ne1 p0 q0 by simp
  show ?thesis unfolding phi_pq_def
    by (subst phi_identity[symmetric], rule nonzero_mult_div_cancel_left[OF D0])
qed

lemma coeff_B: "coeff B k = 0 \<or> coeff B k = 1"
proof -
  let ?g = "\<lambda>z. e z - p * q"
  have cX: "\<And>n. coeff (XX ^ n) k = (if n = k then 1 else 0)"
    by (simp add: monom_XX[symmetric] coeff_monom)
  have cB: "coeff B k = (\<Sum>z\<in>S1. if ?g z = k then 1 else 0)"
    unfolding B_def coeff_sum cX by simp
  have inj: "z = z'" if hz: "z \<in> S1" and hz': "z' \<in> S1" and h: "?g z = ?g z'" for z z'
  proof -
    from hz hz' have ge: "p * q \<le> e z" "p * q \<le> e z'" by (simp_all add: S1_def)
    have "e z = e z'" using h ge by linarith
    moreover from hz hz' have "z \<in> P" "z' \<in> P" by (simp_all add: S1_def)
    ultimately show "z = z'" by (rule e_inj_eq[rotated 2])
  qed
  show ?thesis
  proof (cases "\<exists>z0\<in>S1. ?g z0 = k")
    case True
    then obtain z0 where z0: "z0 \<in> S1" "?g z0 = k" by blast
    have "(\<Sum>z\<in>S1. if ?g z = k then (1::int) else 0) = (\<Sum>z\<in>S1. if z = z0 then 1 else 0)"
      by (rule sum.cong) (use z0 inj in auto)
    also have "\<dots> = 1" using z0(1) finS1 by (simp add: sum.delta)
    finally show ?thesis using cB by simp
  next
    case False
    then have "(\<Sum>z\<in>S1. if ?g z = k then (1::int) else 0) = 0" by (intro sum.neutral) auto
    then show ?thesis using cB by simp
  qed
qed

theorem phi_flat: "coeff (phi_pq p q) k \<in> {-1, 0, 1}"
proof -
  have eq: "phi_pq p q = 1 - B + monom 1 1 * B" unfolding phi_eq by (simp add: algebra_simps XX_def)
  have "coeff (phi_pq p q) k = (if k = 0 then 1 else 0) - coeff B k + (if 1 \<le> k then coeff B (k - 1) else 0)"
    unfolding eq by (simp add: coeff_monom_mult)
  moreover note coeff_B[of k] coeff_B[of "k - 1"]
  ultimately show ?thesis by (auto split: if_splits)
qed

end

theorem migotti_exact:
  assumes "0 < p" "0 < q" "coprime p q"
  shows "((1 - XX ^ p) * (1 - XX ^ q)) dvd ((1 - XX ^ (p * q)) * (1 - XX))"
proof -
  interpret migotti p q by unfold_locales (use assms in auto)
  show ?thesis by (rule dvdI[OF phi_identity[symmetric]])
qed

theorem migotti_coprime:
  assumes "0 < p" "0 < q" "coprime p q"
  shows "phi_pq p q * ((1 - XX ^ p) * (1 - XX ^ q)) = (1 - XX ^ (p * q)) * (1 - XX)"
    and "coeff (phi_pq p q) k \<in> {-1, 0, 1}"
proof -
  interpret migotti p q by unfold_locales (use assms in auto)
  show "coeff (phi_pq p q) k \<in> {-1, 0, 1}" by (rule phi_flat)
  show "phi_pq p q * ((1 - XX ^ p) * (1 - XX ^ q)) = (1 - XX ^ (p * q)) * (1 - XX)"
    using phi_identity phi_eq by (simp add: mult.commute)
qed

theorem migotti:
  assumes "prime p" "prime q" "p \<noteq> q"
  shows "\<forall>k. coeff (phi_pq p q) k \<in> {-1, 0, 1}"
proof -
  have "coprime p q" using assms by (rule primes_coprime)
  then show ?thesis using migotti_coprime(2)[of p q] assms prime_gt_0_nat by blast
qed

end
