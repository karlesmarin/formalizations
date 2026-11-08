(*  Title:      BSR44_Pieces.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

(* encaje: BSR(4,4) = 11 (nota de noviembre de 2026): las piezas elementales de la prueba (punto regular, cuenta de
   soportes del Lema 3, polar de (x^T b)^2, traza de la seccion 5); los Lemas 1 y 3 y la segunda variacion NO estan *)
theory BSR44_Pieces
  imports Complex_Main
begin

text \<open>Elementary steps of the note ``Every $4\times4$ biquadratic sum of squares is a sum of eleven squares''.
  A multiplier on $A\otimes B$ is stored by its values on basis tensors:
  \<open>H a b c d\<close> $=H(e_a\otimes e_b,\,e_c\otimes e_d)$. Lemmas 1 and 3 themselves (the classification of small-rank
  Hankel multipliers), Proposition 4 and the second-variation arguments of Sections 4 and 5 are not formalized
  here.\<close>

section \<open>The regular point (Section 3)\<close>

text \<open>The ten summands $x_iy_i$ and $x_iy_j+x_jy_i$ span the symmetric tensors; a multiplier vanishing on them in
  its first argument vanishes on every $e_a\otimes e_b+e_b\otimes e_a$. Such a symmetric Hankel multiplier is
  zero.\<close>

theorem regular_point_symmetric:
  fixes H :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" and n :: nat
  assumes sym: "\<And>a b c d. a < n \<Longrightarrow> b < n \<Longrightarrow> c < n \<Longrightarrow> d < n \<Longrightarrow> H a b c d = H c d a b"
    and hankel: "\<And>a b c d. a < n \<Longrightarrow> b < n \<Longrightarrow> c < n \<Longrightarrow> d < n \<Longrightarrow> H a b c d = H a d c b"
    and van: "\<And>a b c d. a < n \<Longrightarrow> b < n \<Longrightarrow> c < n \<Longrightarrow> d < n \<Longrightarrow> H a b c d + H b a c d = 0"
    and idx: "a < n" "b < n" "c < n" "d < n"
  shows "H a b c d = 0"
proof -
  have anti2: "H p q r s = - H p q s r" if "p < n" "q < n" "r < n" "s < n" for p q r s
  proof -
    have "H p q r s = H r s p q" using sym that by blast
    also have "\<dots> = - H s r p q" using van[of r s p q] that by linarith
    also have "H s r p q = H p q s r" using sym that by blast
    finally show ?thesis .
  qed
  have "H a b c d = H a d c b" using hankel idx by blast
  also have "\<dots> = - H a d b c" using anti2 idx by blast
  also have "H a d b c = H a c b d" using hankel idx by blast
  also have "H a c b d = - H a c d b" using anti2 idx by blast
  also have "H a c d b = H a b d c" using hankel idx by blast
  also have "H a b d c = - H a b c d" using anti2 idx by blast
  finally show ?thesis by simp
qed

section \<open>The support count closing Lemma 3\<close>

text \<open>With $2\le a,b_0\le4$, $r\le5$, $r\le(a-1)(b_0-1)$ (the image avoids the Segre variety) and
  $r\ge\max(a,b_0)+1$, only four triples remain.\<close>

lemma support_triples:
  fixes a b r :: nat
  assumes "2 \<le> a" "a \<le> 4" "2 \<le> b" "b \<le> 4" "r \<le> 5" "r \<le> (a - 1) * (b - 1)" "a + 1 \<le> r" "b + 1 \<le> r"
  shows "(a, b, r) \<in> {(4, 4, 5), (4, 3, 5), (3, 4, 5), (3, 3, 4)}"
proof -
  have "a = 2 \<or> a = 3 \<or> a = 4" "b = 2 \<or> b = 3 \<or> b = 4" using assms by auto
  then show ?thesis using assms by auto
qed

section \<open>The polar multiplier of $(x^\top b)^2$ (Lemma 1, case iii)\<close>

text \<open>The map $X\mapsto(\operatorname{tr}(X)I+X^\top)/2$ on $n\times n$ matrices is injective.\<close>

lemma polar_trace_injective:
  fixes X :: "nat \<Rightarrow> nat \<Rightarrow> real" and n :: nat
  assumes zero: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> (if i = j then (\<Sum>k<n. X k k) else 0) + X j i = 0"
    and ij: "i < n" "j < n"
  shows "X i j = 0"
proof -
  define t where "t = (\<Sum>k<n. X k k)"
  have diag: "X k k = - t" if "k < n" for k using zero[of k k] that unfolding t_def by simp
  have "(\<Sum>k<n. X k k) = (\<Sum>k<n. - t)" using diag by simp
  then have "t = - (real n * t)" unfolding t_def[symmetric] by simp
  then have "(real n + 1) * t = 0" by (simp add: algebra_simps)
  then have t0: "t = 0" by (metis add_nonneg_pos of_nat_0_le_iff zero_less_one mult_eq_0_iff less_irrefl)
  show ?thesis
  proof (cases "i = j")
    case True then show ?thesis using diag[OF ij(1)] t0 by simp
  next
    case False then show ?thesis using zero[of j i] ij by simp
  qed
qed

section \<open>The trace count of Section 5\<close>

text \<open>After the congruence by $S^{-1/2}$ the matrix has trace $3$, eigenvalues at most $1$, rank four and a
  negative eigenvalue; its eigenvalues then sum to less than $3$.\<close>

lemma trace_count:
  fixes lam :: "'i \<Rightarrow> real" and I :: "'i set"
  assumes fin: "finite I" and le1: "\<And>i. i \<in> I \<Longrightarrow> lam i \<le> 1"
    and rk: "card {i \<in> I. lam i \<noteq> 0} \<le> 4" and neg: "j \<in> I" "lam j < 0"
  shows "(\<Sum>i\<in>I. lam i) < 3"
proof -
  let ?N = "{i \<in> I. lam i \<noteq> 0}"
  have finN: "finite ?N" using fin by simp
  have jN: "j \<in> ?N" using neg by simp
  have "(\<Sum>i\<in>I. lam i) = (\<Sum>i\<in>?N. lam i)"
    using fin by (intro sum.mono_neutral_right) auto
  also have "\<dots> = lam j + (\<Sum>i\<in>?N - {j}. lam i)"
    using finN jN by (simp add: sum.remove)
  also have "(\<Sum>i\<in>?N - {j}. lam i) \<le> (\<Sum>i\<in>?N - {j}. 1)"
    using le1 by (intro sum_mono) auto
  also have "(\<Sum>i\<in>?N - {j}. (1::real)) = real (card ?N - 1)"
    using finN jN by (simp add: card_Diff_singleton)
  also have "real (card ?N - 1) \<le> 3" using rk by linarith
  finally show ?thesis using neg(2) by linarith
qed

end
