(*  Title:      Row_Lemma.thy
    Author:     Carles Marín Muñoz
    License:    BSD
*)

theory Row_Lemma
  imports "HOL-Analysis.Determinants" "HOL-Computational_Algebra.Polynomial"
begin

text \<open>
  The row lemma of characters\_at\_aP (section sec:cierre).  A determinant
  \<open>D_h(b) = det (L_j h (b_i))_{i,j}\<close> whose entry \<open>(i,j)\<close> depends on the sequence
  \<open>h :: int \<Rightarrow> 'a\<close> only through a shift-compatible map \<open>L_j\<close> evaluated at \<open>b_i\<close>.
  For a polynomial \<open>P\<close>, \<open>(P(S) h)(n) = \<Sum>_k p_k h(n - k)\<close> and
  \<open>(P(T_i) F)(b) = \<Sum>_k p_k F(b with b_i \<mapsto> b_i - k)\<close>.  Then
  \<open>D_{P(S)h}(b) = (\<Prod>_i P(T_i)) D_h(b)\<close>, by multilinearity in rows.
\<close>

section \<open>Shift of the index by a polynomial, and the row operators\<close>

definition pshift :: "'a::comm_ring_1 poly \<Rightarrow> (int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> 'a" where
  "pshift P h n = (\<Sum>k\<le>degree P. coeff P k * h (n - int k))"

lemma pshift_bound:
  assumes "degree P \<le> N"
  shows "pshift P h n = (\<Sum>k\<le>N. coeff P k * h (n - int k))"
proof -
  have "(\<Sum>k\<le>N. coeff P k * h (n - int k)) = (\<Sum>k\<le>degree P. coeff P k * h (n - int k))"
    using assms by (intro sum.mono_neutral_right) (auto simp: coeff_eq_0)
  then show ?thesis by (simp add: pshift_def)
qed

text \<open>\<open>rowop P i\<close> is \<open>P(T_i)\<close>; \<open>rowops P [i_1,...,i_m]\<close> is \<open>P(T_{i_1}) \<circ> ... \<circ> P(T_{i_m})\<close>.\<close>

definition rowop :: "'a::comm_ring_1 poly \<Rightarrow> 'n \<Rightarrow> (('n \<Rightarrow> int) \<Rightarrow> 'a) \<Rightarrow> ('n \<Rightarrow> int) \<Rightarrow> 'a" where
  "rowop P i F b = (\<Sum>k\<le>degree P. coeff P k * F (b(i := b i - int k)))"

lemma rowop_bound:
  assumes "degree P \<le> N"
  shows "rowop P i F b = (\<Sum>k\<le>N. coeff P k * F (b(i := b i - int k)))"
proof -
  have "(\<Sum>k\<le>N. coeff P k * F (b(i := b i - int k))) = (\<Sum>k\<le>degree P. coeff P k * F (b(i := b i - int k)))"
    using assms by (intro sum.mono_neutral_right) (auto simp: coeff_eq_0)
  then show ?thesis by (simp add: rowop_def)
qed

primrec rowops :: "'a::comm_ring_1 poly \<Rightarrow> 'n list \<Rightarrow> (('n \<Rightarrow> int) \<Rightarrow> 'a) \<Rightarrow> ('n \<Rightarrow> int) \<Rightarrow> 'a" where
  "rowops P [] F = F"
| "rowops P (i # is) F = rowop P i (rowops P is F)"

section \<open>The determinant and the row templates\<close>

definition Dmat :: "('n::finite \<Rightarrow> (int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> 'a) \<Rightarrow> (int \<Rightarrow> 'a) \<Rightarrow> ('n \<Rightarrow> int) \<Rightarrow> 'a::comm_ring_1"
  where "Dmat L h b = det (\<chi> i. \<chi> j. L j h (b i))"

text \<open>A row template is compatible with \<open>P(S)\<close> when applying \<open>P(S)\<close> to \<open>h\<close> is the same as
  applying \<open>P\<close> to the evaluation point.\<close>

definition shift_compatible :: "'a::comm_ring_1 poly \<Rightarrow> ('n \<Rightarrow> (int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> 'a) \<Rightarrow> bool" where
  "shift_compatible P L \<longleftrightarrow> (\<forall>j h n. L j (pshift P h) n = (\<Sum>k\<le>degree P. coeff P k * L j h (n - int k)))"

text \<open>General template: entry \<open>(i,j)\<close> is a linear combination \<open>\<Sum>_{e \<in> E_j} c_{j e} h(b_i + e)\<close>.\<close>

definition template :: "('n \<Rightarrow> int set) \<Rightarrow> ('n \<Rightarrow> int \<Rightarrow> 'a::comm_ring_1) \<Rightarrow> 'n \<Rightarrow> (int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> 'a" where
  "template E c j h n = (\<Sum>e\<in>E j. c j e * h (n + e))"

lemma template_shift_compatible: "shift_compatible P (template E c)"
  unfolding shift_compatible_def template_def pshift_def
proof (intro allI)
  fix j h n
  have "(\<Sum>e\<in>E j. c j e * (\<Sum>k\<le>degree P. coeff P k * h (n + e - int k)))
      = (\<Sum>e\<in>E j. \<Sum>k\<le>degree P. coeff P k * (c j e * h (n - int k + e)))"
    by (simp add: sum_distrib_left algebra_simps)
  also have "\<dots> = (\<Sum>k\<le>degree P. \<Sum>e\<in>E j. coeff P k * (c j e * h (n - int k + e)))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>k\<le>degree P. coeff P k * (\<Sum>e\<in>E j. c j e * h (n - int k + e)))"
    by (simp add: sum_distrib_left)
  finally show "(\<Sum>e\<in>E j. c j e * (\<Sum>k\<le>degree P. coeff P k * h (n + e - int k)))
      = (\<Sum>k\<le>degree P. coeff P k * (\<Sum>e\<in>E j. c j e * h (n - int k + e)))" .
qed

text \<open>The row of the symplectic Jacobi--Trudi determinant: \<open>h_{b_i + c_j} + \<sigma> h_{b_i - c_j}\<close>
  (\<open>\<sigma> = 1\<close> in the paper; \<open>\<sigma> = -1\<close> gives the other sign).\<close>

definition sp_row :: "'a \<Rightarrow> ('n \<Rightarrow> int) \<Rightarrow> 'n \<Rightarrow> (int \<Rightarrow> 'a::comm_ring_1) \<Rightarrow> int \<Rightarrow> 'a" where
  "sp_row \<sigma> c j h n = h (n + c j) + \<sigma> * h (n - c j)"

lemma sp_row_shift_compatible: "shift_compatible P (sp_row \<sigma> c)"
  unfolding shift_compatible_def sp_row_def pshift_def
proof (intro allI)
  fix j h n
  show "(\<Sum>k\<le>degree P. coeff P k * h (n + c j - int k)) + \<sigma> * (\<Sum>k\<le>degree P. coeff P k * h (n - c j - int k))
      = (\<Sum>k\<le>degree P. coeff P k * (h (n - int k + c j) + \<sigma> * h (n - int k - c j)))"
    by (simp add: sum_distrib_left sum.distrib algebra_simps)
qed

section \<open>Multilinearity in rows\<close>

text \<open>\<open>Dmix L P h S\<close>: the rows in \<open>S\<close> use \<open>P(S) h\<close>, the others use \<open>h\<close>.\<close>

definition Dmix :: "('n::finite \<Rightarrow> (int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> 'a) \<Rightarrow> 'a::comm_ring_1 poly \<Rightarrow> (int \<Rightarrow> 'a)
    \<Rightarrow> 'n set \<Rightarrow> ('n \<Rightarrow> int) \<Rightarrow> 'a" where
  "Dmix L P h S b = det (\<chi> i. if i \<in> S then (\<chi> j. L j (pshift P h) (b i)) else (\<chi> j. L j h (b i)))"

lemma Dmix_empty: "Dmix L P h {} = Dmat L h"
  by (simp add: fun_eq_iff Dmix_def Dmat_def)

lemma Dmix_UNIV: "Dmix L P h UNIV = Dmat L (pshift P h)"
  by (simp add: fun_eq_iff Dmix_def Dmat_def)

lemma Dmix_insert:
  fixes L :: "'n::finite \<Rightarrow> (int \<Rightarrow> 'a::comm_ring_1) \<Rightarrow> int \<Rightarrow> 'a"
  assumes compat: "shift_compatible P L" and iS: "i \<notin> S"
  shows "Dmix L P h (insert i S) b = rowop P i (Dmix L P h S) b"
proof -
  define r where "r k = (\<chi> j. L j h (b i - int k))" for k
  define c where "c i' = (if i' \<in> S then (\<chi> j. L j (pshift P h) (b i')) else (\<chi> j. L j h (b i')))" for i'
  have row: "(\<chi> j. L j (pshift P h) (b i)) = (\<Sum>k\<le>degree P. coeff P k *s r k)"
    using compat by (simp add: shift_compatible_def vec_eq_iff sum_component r_def)
  have M: "(\<chi> i'. if i' \<in> insert i S then (\<chi> j. L j (pshift P h) (b i')) else (\<chi> j. L j h (b i')))
      = (\<chi> i'. if i' = i then (\<Sum>k\<le>degree P. coeff P k *s r k) else c i')"
    by (simp add: vec_eq_iff row c_def)
  have Mk: "(\<chi> i'. if i' = i then r k else c i')
      = (\<chi> i'. if i' \<in> S then (\<chi> j. L j (pshift P h) ((b(i := b i - int k)) i'))
               else (\<chi> j. L j h ((b(i := b i - int k)) i')))" for k
    using iS by (auto simp: vec_eq_iff r_def c_def)
  have "Dmix L P h (insert i S) b = det (\<chi> i'. if i' = i then (\<Sum>k\<le>degree P. coeff P k *s r k) else c i')"
    unfolding Dmix_def M ..
  also have "\<dots> = (\<Sum>k\<le>degree P. det (\<chi> i'. if i' = i then coeff P k *s r k else c i'))"
    by (rule det_linear_row_sum[where a = "\<lambda>_ k. coeff P k *s r k" and S = "{..degree P}"]) simp
  also have "\<dots> = (\<Sum>k\<le>degree P. coeff P k * det (\<chi> i'. if i' = i then r k else c i'))"
    by (intro sum.cong refl) (rule det_row_mul)
  also have "\<dots> = rowop P i (Dmix L P h S) b"
    by (simp add: rowop_def Dmix_def Mk)
  finally show ?thesis .
qed

lemma Dmix_rowops:
  fixes L :: "'n::finite \<Rightarrow> (int \<Rightarrow> 'a::comm_ring_1) \<Rightarrow> int \<Rightarrow> 'a"
  assumes compat: "shift_compatible P L" and "distinct xs"
  shows "Dmix L P h (set xs) = rowops P xs (Dmat L h)"
  using assms(2)
proof (induct xs)
  case Nil
  then show ?case by (simp add: Dmix_empty)
next
  case (Cons i xs)
  then have "Dmix L P h (set (i # xs)) b = rowop P i (rowops P xs (Dmat L h)) b" for b
    by (simp add: Dmix_insert[OF compat])
  then show ?case by (simp add: fun_eq_iff)
qed

section \<open>The row lemma\<close>

text \<open>Operator form: \<open>D_{P(S)h}(b) = (\<Prod>_i P(T_i)) D_h(b)\<close>, the product taken over any
  enumeration of the rows without repetition.\<close>

theorem row_lemma:
  fixes L :: "'n::finite \<Rightarrow> (int \<Rightarrow> 'a::comm_ring_1) \<Rightarrow> int \<Rightarrow> 'a"
  assumes "shift_compatible P L" and "distinct xs" and "set xs = UNIV"
  shows "Dmat L (pshift P h) b = rowops P xs (Dmat L h) b"
  using Dmix_rowops[OF assms(1,2), of h] assms(3) by (simp add: Dmix_UNIV)

text \<open>Expanded form: the sum over \<open>(k_1, ..., k_m)\<close> of \<open>\<Prod>_i p_{k_i}\<close> times the determinant
  with \<open>h\<close> at \<open>b - (k_1, ..., k_m)\<close>.\<close>

text \<open>Expansion of a product of row operators over distinct rows.  (The library lemma
  \<open>det_linear_rows_sum\<close> fixes the summation index to the row type, so it is not used here.)\<close>

lemma rowops_expand:
  fixes xs :: "'n list" and F :: "('n \<Rightarrow> int) \<Rightarrow> 'a::comm_ring_1"
  assumes "distinct xs"
  shows "rowops P xs F b =
    (\<Sum>g\<in>PiE (set xs) (\<lambda>_. {..degree P}). (\<Prod>j\<in>set xs. coeff P (g j)) *
        F (\<lambda>j. if j \<in> set xs then b j - int (g j) else b j))"
  using assms
proof (induct xs arbitrary: b)
  case Nil
  then show ?case by (simp add: PiE_empty_domain)
next
  case (Cons i xs)
  define K where "K = {..degree P}"
  define S where "S = set xs"
  have iS: "i \<notin> S" and dS: "distinct xs" and finS: "finite S"
    using Cons.prems by (auto simp: S_def)
  define G where "G k f = (\<lambda>j. if j \<in> S then (b(i := b i - int k)) j - int (f j) else (b(i := b i - int k)) j)"
    for k :: nat and f :: "'n \<Rightarrow> nat"
  have prodS: "(\<Prod>j\<in>S. coeff P ((f(i := k)) j)) = (\<Prod>j\<in>S. coeff P (f j))" for f k
    using iS by (intro prod.cong) auto
  have prod1: "(\<Prod>j\<in>insert i S. coeff P ((f(i := k)) j)) = coeff P k * (\<Prod>j\<in>S. coeff P (f j))" for f k
    by (simp add: prod.insert[OF finS iS] prodS fun_upd_same del: fun_upd_apply)
  have argG: "(\<lambda>j. if j \<in> insert i S then b j - int ((f(i := k)) j) else b j) = G k f" for f k
    using iS by (auto simp: G_def fun_eq_iff)
  have "rowops P (i # xs) F b = (\<Sum>k\<in>K. coeff P k * (\<Sum>f\<in>PiE S (\<lambda>_. K). (\<Prod>j\<in>S. coeff P (f j)) * F (G k f)))"
    by (simp add: rowop_def Cons.hyps[OF dS] K_def S_def G_def)
  also have "\<dots> = (\<Sum>(k, f)\<in>K \<times> PiE S (\<lambda>_. K). coeff P k * ((\<Prod>j\<in>S. coeff P (f j)) * F (G k f)))"
    by (simp add: sum_distrib_left sum.cartesian_product)
  also have "\<dots> = (\<Sum>g\<in>PiE (insert i S) (\<lambda>_. K). (\<Prod>j\<in>insert i S. coeff P (g j)) *
        F (\<lambda>j. if j \<in> insert i S then b j - int (g j) else b j))"
    apply (rule sum.reindex_bij_witness[where i = "\<lambda>g. (g i, g(i := undefined))" and j = "\<lambda>(k, f). f(i := k)"])
    subgoal using iS by (auto simp: PiE_iff extensional_def fun_eq_iff)
    subgoal by (auto simp: PiE_iff extensional_def)
    subgoal by (auto simp: fun_eq_iff)
    subgoal using iS by (auto simp: PiE_iff extensional_def)
    subgoal for a
    proof (cases a)
      case (Pair k f)
      show ?thesis unfolding Pair prod.case prod1 argG by (simp add: mult.assoc)
    qed
    done
  finally show ?case by (simp add: S_def K_def)
qed

theorem row_lemma_sum:
  fixes L :: "'n::finite \<Rightarrow> (int \<Rightarrow> 'a::comm_ring_1) \<Rightarrow> int \<Rightarrow> 'a"
  assumes "shift_compatible P L"
  shows "Dmat L (pshift P h) b =
    (\<Sum>f\<in>PiE UNIV (\<lambda>_. {..degree P}). (\<Prod>i\<in>UNIV. coeff P (f i)) * Dmat L h (\<lambda>i. b i - int (f i)))"
proof -
  obtain xs :: "'n list" where xs: "set xs = UNIV" "distinct xs"
    using finite_distinct_list[of "UNIV :: 'n set"] by auto
  show ?thesis
    using row_lemma[OF assms xs(2,1), of h b] rowops_expand[OF xs(2), of P "Dmat L h" b] xs(1) by simp
qed

section \<open>The two cases of the paper\<close>

lemma one_minus_S_sq: "(1 - [:0, 1:])\<^sup>2 = ([:1, -2, 1:] :: 'a::comm_ring_1 poly)"
  by (simp add: power2_eq_square one_pCons algebra_simps)

lemma one_minus_S2: "1 - [:0, 1:]\<^sup>2 = ([:1, 0, -1:] :: 'a::comm_ring_1 poly)"
  by (simp add: power2_eq_square one_pCons algebra_simps)

lemma degree_le_2: "degree [:a, b, c:] \<le> 2"
  by (rule degree_le) (auto simp: coeff_pCons split: nat.split)

lemma pshift_even: "pshift ((1 - [:0, 1:])\<^sup>2) h n = h n - 2 * h (n - 1) + h (n - 2)"
  unfolding one_minus_S_sq pshift_bound[OF degree_le_2]
  by (simp add: eval_nat_numeral)

lemma pshift_odd: "pshift (1 - [:0, 1:]\<^sup>2) h n = h n - h (n - 2)"
  unfolding one_minus_S2 pshift_bound[OF degree_le_2]
  by (simp add: eval_nat_numeral)

lemma rowop_even: "rowop ((1 - [:0, 1:])\<^sup>2) i F b =
    F b - 2 * F (b(i := b i - 1)) + F (b(i := b i - 2))"
  unfolding one_minus_S_sq rowop_bound[OF degree_le_2]
  by (simp add: eval_nat_numeral)

text \<open>\<open>(1 - T_i)\<^sup>2\<close> as an operator is \<open>(1 - T_i)\<close> applied twice.\<close>

lemma rowop_even_twice: "rowop ((1 - [:0, 1:])\<^sup>2) i F b = rowop (1 - [:0, 1:]) i (rowop (1 - [:0, 1:]) i F) b"
proof -
  have d1: "degree (1 - [:0, 1:] :: 'a poly) \<le> 1"
    by (rule degree_le) (auto simp: coeff_pCons one_pCons split: nat.split)
  show ?thesis
    unfolding rowop_even rowop_bound[OF d1]
    by (simp add: one_pCons algebra_simps)
qed

text \<open>The paper's corollaries, for the symplectic Jacobi--Trudi row \<open>h_{b_i+c_j} + \<sigma> h_{b_i-c_j}\<close>:
  \<open>D_A = \<Prod>_i (1 - T_i)\<^sup>2 D'\<close> for \<open>d\<close> even and \<open>D_A = \<Prod>_i (1 - T_i\<^sup>2) D'\<close> for \<open>d\<close> odd.\<close>

corollary row_lemma_even:
  fixes hA h' :: "int \<Rightarrow> 'a::comm_ring_1" and c :: "'n::finite \<Rightarrow> int"
  assumes "\<And>n. hA n = h' n - 2 * h' (n - 1) + h' (n - 2)" and "distinct xs" and "set xs = UNIV"
  shows "Dmat (sp_row \<sigma> c) hA b = rowops ((1 - [:0, 1:])\<^sup>2) xs (Dmat (sp_row \<sigma> c) h') b"
proof -
  have "hA = pshift ((1 - [:0, 1:])\<^sup>2) h'"
    using assms(1) by (simp add: fun_eq_iff pshift_even)
  then show ?thesis
    using row_lemma[OF sp_row_shift_compatible assms(2,3)] by simp
qed

corollary row_lemma_odd:
  fixes hA h' :: "int \<Rightarrow> 'a::comm_ring_1" and c :: "'n::finite \<Rightarrow> int"
  assumes "\<And>n. hA n = h' n - h' (n - 2)" and "distinct xs" and "set xs = UNIV"
  shows "Dmat (sp_row \<sigma> c) hA b = rowops (1 - [:0, 1:]\<^sup>2) xs (Dmat (sp_row \<sigma> c) h') b"
proof -
  have "hA = pshift (1 - [:0, 1:]\<^sup>2) h'"
    using assms(1) by (simp add: fun_eq_iff pshift_odd)
  then show ?thesis
    using row_lemma[OF sp_row_shift_compatible assms(2,3)] by simp
qed

end
