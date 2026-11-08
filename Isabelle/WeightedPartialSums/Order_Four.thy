(*  Title:      Order_Four.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

(* encaje: weighted-partial-sums, Proposition prop:ordenalto (b): a character of order 4 splits T(m,chi) into the
   signed sums over residues and non-residues; abstract form over C, independent of the character theory *)
theory Order_Four
  imports Complex_Main
begin

text \<open>Proposition \<open>prop:ordenalto\<close> (b) of ``Weighted partial sums of characters''. For an odd character
  $\chi$ of order $4$ modulo a prime $f$, $\chi^2$ is the Legendre symbol, so $\chi(c)=\varepsilon_c\in\{\pm1\}$ on
  the quadratic residues and $\chi(c)=\mathrm i\,\delta_c$, $\delta_c\in\{\pm1\}$, on the non-residues. Here the
  residues and non-residues below $m$ are any disjoint finite sets $R$, $N$ of naturals, and the signs any
  functions with values $\pm1$: then
  \[ T=\sum_{c\in R}c\,\varepsilon_c+\mathrm i\sum_{c\in N}c\,\delta_c = 0
     \iff \sum_{c\in R}c\,\varepsilon_c=0\ \text{and}\ \sum_{c\in N}c\,\delta_c=0, \]
  and each vanishing signed sum forces the plain sum to be even.\<close>

definition T4 :: "nat set \<Rightarrow> nat set \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> complex" where
  "T4 R N eps del = (\<Sum>c\<in>R. of_nat c * of_int (eps c)) + \<i> * (\<Sum>c\<in>N. of_nat c * of_int (del c))"

lemma T4_split:
  "T4 R N eps del = of_int (\<Sum>c\<in>R. int c * eps c) + \<i> * of_int (\<Sum>c\<in>N. int c * del c)"
  unfolding T4_def by simp

theorem T4_zero_iff:
  "T4 R N eps del = 0 \<longleftrightarrow> (\<Sum>c\<in>R. int c * eps c) = 0 \<and> (\<Sum>c\<in>N. int c * del c) = 0"
proof -
  define a where "a = (\<Sum>c\<in>R. int c * eps c)"
  define b where "b = (\<Sum>c\<in>N. int c * del c)"
  have "T4 R N eps del = Complex (of_int a) (of_int b)"
    unfolding T4_split a_def[symmetric] b_def[symmetric] by (simp add: complex_eq_iff)
  then show ?thesis unfolding a_def[symmetric] b_def[symmetric] by (simp add: complex_eq_iff)
qed

text \<open>A signed sum with signs $\pm1$ has the parity of the plain sum: $c\,\varepsilon_c\equiv c \pmod 2$.\<close>
lemma signed_sum_parity:
  assumes "finite S" and "\<forall>c\<in>S. eps c = 1 \<or> eps c = -1"
  shows "even (\<Sum>c\<in>S. int c * eps c) \<longleftrightarrow> even (\<Sum>c\<in>S. int c)"
  using assms
proof (induction S rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x S)
  have IH: "even (\<Sum>c\<in>S. int c * eps c) \<longleftrightarrow> even (\<Sum>c\<in>S. int c)" using insert by simp
  have "even (int x * eps x) \<longleftrightarrow> even (int x)" using insert.prems by auto
  then show ?case using insert.hyps IH by simp
qed

corollary T4_zero_parity:
  assumes "finite R" "finite N" "\<forall>c\<in>R. eps c = 1 \<or> eps c = -1" "\<forall>c\<in>N. del c = 1 \<or> del c = -1"
    and "T4 R N eps del = 0"
  shows "even (\<Sum>c\<in>R. int c)" and "even (\<Sum>c\<in>N. int c)"
proof -
  have z: "(\<Sum>c\<in>R. int c * eps c) = 0" "(\<Sum>c\<in>N. int c * del c) = 0"
    using T4_zero_iff assms(5) by blast+
  show "even (\<Sum>c\<in>R. int c)" using signed_sum_parity[OF assms(1,3)] z(1) by simp
  show "even (\<Sum>c\<in>N. int c)" using signed_sum_parity[OF assms(2,4)] z(2) by simp
qed

end
