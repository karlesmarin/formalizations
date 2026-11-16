(*  Title:      Erdos_1148_Weaker.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Every n is x^2 + y^2 - z^2 with x^2, y^2, z^2 <= n + 2 sqrt n (weaker form of Erdős problem 1148, formal-conjectures)
*)

theory Erdos_1148_Weaker
  imports Complex_Main
begin

section \<open>Erd\H{o}s problem 1148, weaker property: every n is x^2 + y^2 - z^2 with squares at most n + 2 sqrt n\<close>

text \<open>Transcription of \<open>erdos_1148_weaker_prop\<close> and \<open>erdos_1148.variants.weaker\<close> from
  \<open>FormalConjectures/ErdosProblems/1148.lean\<close>. Subtraction is the truncated subtraction of
  natural numbers, as in Lean's \<open>\<nat>\<close>; the three squares are compared in the reals.\<close>

definition weaker_prop :: "nat \<Rightarrow> bool" where
  "weaker_prop n \<longleftrightarrow> (\<exists>x y z :: nat. n = x ^ 2 + y ^ 2 - z ^ 2 \<and>
    (real x) ^ 2 \<le> real n + 2 * sqrt (real n) \<and>
    (real y) ^ 2 \<le> real n + 2 * sqrt (real n) \<and>
    (real z) ^ 2 \<le> real n + 2 * sqrt (real n))"

section \<open>Integer square root bracket\<close>

lemma ex_sqrt_bracket: "\<exists>s :: nat. s ^ 2 \<le> n \<and> n < (s + 1) ^ 2"
proof (induction n)
  case 0
  show ?case by (rule exI[of _ 0]) simp
next
  case (Suc n)
  then obtain s where s: "s ^ 2 \<le> n" "n < (s + 1) ^ 2" by blast
  show ?case
  proof (cases "(s + 1) ^ 2 \<le> Suc n")
    case True
    have "Suc n < (s + 1 + 1) ^ 2"
      using s(2) by (simp add: power2_eq_square algebra_simps)
    with True show ?thesis by (intro exI[of _ "s + 1"]) simp
  next
    case False
    with s(1) show ?thesis by (intro exI[of _ s]) simp
  qed
qed

section \<open>The construction\<close>

text \<open>Write \<open>n = s^2 + r\<close> with \<open>0 \<le> r \<le> 2 s\<close>. According to \<open>r\<close> modulo 4 we take
  \<open>r = 0\<close>: \<open>(s, 0, 0)\<close>; \<open>r = 2m+1\<close>: \<open>(s, m+1, m)\<close>; \<open>r = 4j+4\<close>: \<open>(s, j+2, j)\<close>;
  \<open>r = 4k+2\<close>: \<open>(s+1, p, p+1)\<close> with \<open>s = p + 2k + 1\<close>.\<close>

lemma construct:
  assumes "s ^ 2 \<le> n" "n < (s + 1) ^ 2"
  shows "\<exists>x y z :: nat. x ^ 2 + y ^ 2 = n + z ^ 2 \<and> y \<le> s \<and> z \<le> s \<and>
    (x \<le> s \<or> (x = s + 1 \<and> s ^ 2 < n))"
proof -
  obtain r where nr: "n = s ^ 2 + r" using assms(1) le_Suc_ex by blast
  have rs: "r \<le> 2 * s"
    using assms(2) nr by (simp add: power2_eq_square algebra_simps)
  have cases: "r = 0 \<or> (\<exists>m. r = 2 * m + 1) \<or> (\<exists>j. r = 4 * j + 4) \<or> (\<exists>k. r = 4 * k + 2)"
  proof -
    have "r = 0 \<or> r mod 2 = 1 \<or> (r mod 4 = 0 \<and> r \<noteq> 0) \<or> r mod 4 = 2" by arith
    then show ?thesis
    proof (elim disjE)
      assume "r mod 2 = 1"
      then show ?thesis by (intro disjI2 disjI1 exI[of _ "r div 2"]) arith
    next
      assume "r mod 4 = 0 \<and> r \<noteq> 0"
      then show ?thesis by (intro disjI2 disjI2 disjI1 exI[of _ "r div 4 - 1"]) arith
    next
      assume "r mod 4 = 2"
      then show ?thesis by (intro disjI2 disjI2 disjI2 exI[of _ "r div 4"]) arith
    qed simp
  qed
  from cases show ?thesis
  proof (elim disjE exE)
    assume r0: "r = 0"
    show ?thesis
      by (rule exI[of _ s], rule exI[of _ 0], rule exI[of _ 0]) (use r0 nr in simp)
  next
    fix m assume rm: "r = 2 * m + 1"
    have "m + 1 \<le> s" using rm rs by arith
    then show ?thesis
      by (intro exI[of _ s] exI[of _ "m + 1"] exI[of _ m])
         (use rm nr in \<open>auto simp: power2_eq_square algebra_simps\<close>)
  next
    fix j assume rj: "r = 4 * j + 4"
    have "j + 2 \<le> s" using rj rs by arith
    then show ?thesis
      by (intro exI[of _ s] exI[of _ "j + 2"] exI[of _ j])
         (use rj nr in \<open>auto simp: power2_eq_square algebra_simps\<close>)
  next
    fix k assume rk: "r = 4 * k + 2"
    have "2 * k + 1 \<le> s" using rk rs by arith
    then obtain p where sp: "s = (2 * k + 1) + p" using le_Suc_ex by blast
    have n_eq: "n = ((2 * k + 1) + p) ^ 2 + (4 * k + 2)" using nr rk sp by simp
    have e: "(s + 1) ^ 2 + p ^ 2 = n + (p + 1) ^ 2"
      unfolding n_eq sp by (simp add: power2_eq_square algebra_simps)
    have lt: "s ^ 2 < n" using nr rk by simp
    have "p \<le> s" "p + 1 \<le> s" using sp by arith+
    then show ?thesis
      using e lt by (intro exI[of _ "s + 1"] exI[of _ p] exI[of _ "p + 1"]) blast
  qed
qed

section \<open>The theorem\<close>

lemma sq_le_real:
  assumes "t \<le> s" "s ^ 2 \<le> n"
  shows "(real t) ^ 2 \<le> real n + 2 * sqrt (real n)"
proof -
  have "t ^ 2 \<le> s ^ 2" using assms(1) by (rule power_mono) simp
  then have "t ^ 2 \<le> n" using assms(2) by linarith
  then have "(real t) ^ 2 \<le> real n" by (metis of_nat_le_iff of_nat_power)
  moreover have "0 \<le> sqrt (real n)" by simp
  ultimately show ?thesis by linarith
qed

lemma sq_succ_real:
  assumes "s ^ 2 < n"
  shows "(real (s + 1)) ^ 2 \<le> real n + 2 * sqrt (real n)"
proof -
  have a: "s ^ 2 + 1 \<le> n" using assms by simp
  have h1: "(real s) ^ 2 + 1 \<le> real n"
    using of_nat_mono[OF a, where 'a=real] by simp
  have "real s \<le> sqrt (real n)"
    by (rule real_le_rsqrt) (use h1 in linarith)
  moreover have e: "(real (s + 1)) ^ 2 = (real s) ^ 2 + 2 * real s + 1"
    by (simp add: power2_eq_square algebra_simps)
  ultimately show ?thesis using h1 by linarith
qed

theorem erdos_1148_weaker: "weaker_prop n"
proof -
  obtain s where s: "s ^ 2 \<le> n" "n < (s + 1) ^ 2" using ex_sqrt_bracket by blast
  obtain x y z where xyz: "x ^ 2 + y ^ 2 = n + z ^ 2" "y \<le> s" "z \<le> s"
    "x \<le> s \<or> (x = s + 1 \<and> s ^ 2 < n)"
    using construct[OF s] by blast
  have eq: "n = x ^ 2 + y ^ 2 - z ^ 2" using xyz(1) by simp
  have hx: "(real x) ^ 2 \<le> real n + 2 * sqrt (real n)"
    using xyz(4)
  proof
    assume "x \<le> s" then show ?thesis using sq_le_real s(1) by blast
  next
    assume "x = s + 1 \<and> s ^ 2 < n" then show ?thesis using sq_succ_real by blast
  qed
  have hy: "(real y) ^ 2 \<le> real n + 2 * sqrt (real n)" using sq_le_real xyz(2) s(1) by blast
  have hz: "(real z) ^ 2 \<le> real n + 2 * sqrt (real n)" using sq_le_real xyz(3) s(1) by blast
  show ?thesis unfolding weaker_prop_def using eq hx hy hz by blast
qed

corollary erdos_1148_weaker_all: "\<forall>n. weaker_prop n"
  using erdos_1148_weaker by blast

end
