(*  Title:      Caballero_Eventos.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín
*)

section \<open>Compression by events: algebraic part\<close>

theory Caballero_Eventos
  imports "HOL-Computational_Algebra.Polynomial" "HOL-Library.Multiset"
begin

text \<open>
  Algebraic part of the event compression (Theorem B and step 3 of the quasi-polynomial section):
  multiplying by \<open>1 - z\<^sup>D\<close> turns a progression of step \<open>s\<close> (\<open>s\<close> divides \<open>D\<close>) into a finite sum of
  events, and the multiplication is injective on \<open>\<int>[z]\<close>. Here \<open>z\<^sup>n\<close> is written \<open>monom 1 n\<close>.

  \<^bold>\<open>Out of scope:\<close> the SMT certificates and the assembly of the pieces of slope 1, 2, 3 and constant
  for \<open>W(2,b)\<close>.
\<close>

abbreviation zp :: "nat \<Rightarrow> int poly" where "zp n \<equiv> monom 1 n"

lemma zp_add: "zp (m + n) = zp m * zp n"
  by (simp add: mult_monom)

lemma zp_pow: "zp (s * n) = (zp s) ^ n"
  by (induction n) (simp_all add: zp_add algebra_simps)

lemma zp_ne1: assumes "s \<ge> 1" shows "1 - zp s \<noteq> (0 :: int poly)"
proof
  assume h: "1 - zp s = 0"
  from arg_cong[OF h, of "\<lambda>p. coeff p s"] assms show False
    by (simp add: coeff_monom)
qed

lemma geom: "(1 - a) * (\<Sum>n<N. a ^ n) = 1 - a ^ N" for a :: "'x :: comm_ring_1"
proof (induction N)
  case 0 then show ?case by simp
next
  case (Suc N)
  have "(1 - a) * (\<Sum>n<Suc N. a ^ n) = (1 - a) * (\<Sum>n<N. a ^ n) + (1 - a) * a ^ N" 
    by (simp add: algebra_simps)
  also have "\<dots> = 1 - a ^ Suc N" using Suc by (simp add: algebra_simps)
  finally show ?case .
qed

lemma geom_swap:
  fixes a :: "'x :: idom"
  assumes "a \<noteq> 1"
  shows "(1 - a ^ k) * (\<Sum>n<N. a ^ n) = (\<Sum>\<rho><k. a ^ \<rho>) * (1 - a ^ N)"
proof -
  have "1 - a \<noteq> 0" using assms by simp
  moreover have "(1 - a) * ((1 - a ^ k) * (\<Sum>n<N. a ^ n)) = (1 - a) * ((\<Sum>\<rho><k. a ^ \<rho>) * (1 - a ^ N))"
    by (simp only: mult.left_commute[of "1 - a"] geom) (simp add: mult.commute mult.left_commute geom)
  ultimately show ?thesis by simp
qed

subsection \<open>(i) Progression of step s\<close>

theorem events_progression:
  assumes "s \<ge> 1" "s dvd D"
  shows "(1 - zp D) * (\<Sum>n<N. zp (u + s * n))
       = (\<Sum>\<rho><D div s. zp (u + s * \<rho>) - zp (u + s * N + s * \<rho>))"
proof -
  obtain k where k: "D = s * k" using assms(2) by auto
  have ks: "D div s = k" using k assms(1) by simp
  have a1: "zp s \<noteq> 1" using zp_ne1[OF assms(1)] by auto
  have t1: "\<And>n. zp (u + s * n) = zp u * (zp s) ^ n" by (simp add: zp_add zp_pow)
  have t2: "\<And>n. zp (u + s * N + s * n) = zp u * (zp s) ^ N * (zp s) ^ n"
    by (simp add: zp_add zp_pow)
  have lhs: "(\<Sum>n<N. zp (u + s * n)) = zp u * (\<Sum>n<N. (zp s) ^ n)"
    by (simp only: t1 sum_distrib_left)
  have rhs: "(\<Sum>\<rho><k. zp (u + s * \<rho>) - zp (u + s * N + s * \<rho>))
           = zp u * ((\<Sum>\<rho><k. (zp s) ^ \<rho>) * (1 - (zp s) ^ N))"
    by (simp only: t1 t2 sum_distrib_left sum_distrib_right sum_subtractf[symmetric])
       (rule sum.cong, simp_all add: algebra_simps)
  have "(1 - zp D) * (\<Sum>n<N. zp (u + s * n)) = (1 - (zp s) ^ k) * (zp u * (\<Sum>n<N. (zp s) ^ n))"
    by (simp only: k zp_pow lhs)
  also have "\<dots> = zp u * ((1 - (zp s) ^ k) * (\<Sum>n<N. (zp s) ^ n))" by (simp only: mult.left_commute)
  also have "\<dots> = zp u * ((\<Sum>\<rho><k. (zp s) ^ \<rho>) * (1 - (zp s) ^ N))"
    using geom_swap[OF a1, of k N] by simp
  also have "\<dots> = (\<Sum>\<rho><k. zp (u + s * \<rho>) - zp (u + s * N + s * \<rho>))" by (simp only: rhs)
  finally show ?thesis by (simp only: ks)
qed

subsection \<open>(ii) Slope 0\<close>

theorem events_constant:
  "(1 - zp D) * (of_nat N * zp u) = of_nat N * zp u - of_nat N * zp (u + D)"
  by (simp add: zp_add algebra_simps)

subsection \<open>(iii) Injectivity of the multiplication by 1 - z^D\<close>

theorem events_cancel:
  assumes "D \<ge> 1" and "(1 - zp D) * M = (1 - zp D) * (M' :: int poly)"
  shows "M = M'"
  using zp_ne1[OF assms(1)] assms(2) by simp

subsection \<open>(iv) Finite multisets of naturals and generating polynomials\<close>

definition genpoly :: "nat multiset \<Rightarrow> int poly" where
  "genpoly A = (\<Sum>x\<in>#A. zp x)"

lemma coeff_genpoly: "coeff (genpoly A) n = int (count A n)"
proof (induction A)
  case empty then show ?case by (simp add: genpoly_def)
next
  case (add x A)
  then show ?case by (simp add: genpoly_def coeff_monom)
qed

theorem genpoly_eq_iff: "genpoly A = genpoly B \<longleftrightarrow> A = B"
proof
  assume "genpoly A = genpoly B"
  then have "\<And>n. count A n = count B n"
    using coeff_genpoly[of A] coeff_genpoly[of B] by (metis of_nat_eq_iff)
  then show "A = B" by (simp add: multiset_eq_iff)
qed simp

end
