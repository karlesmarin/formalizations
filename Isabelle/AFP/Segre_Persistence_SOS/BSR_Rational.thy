(*  Title:      BSR_Rational.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

(* encaje: orthogonality of the rational coefficient vectors of a diagonal form with C4-free support *)
section \<open>Rational representations of a diagonal form with $C_4$-free support\<close>

theory BSR_Rational
  imports Coefficient_Vectors "HOL-Library.Function_Algebras"
begin

text \<open>A representation of $f=\sum_{(i,j)\in E}c_{ij}x_i^2y_j^2$ as a sum of $r$ squares of bilinear
  forms $s_k=\sum_{ij}v_{ij}(k)\,x_iy_j$ has coefficient vectors $v_{ij}\in\mathbb{Q}^r$. Comparing
  the coefficients of the monomial $x_ix_ky_jy_l$ in $\sum_k s_k^2=f$ gives the polarized identity
  $v_{ij}\cdot v_{kl}+v_{il}\cdot v_{kj}=2\,[i=k\wedge j=l]\,c_{ij}$ (Zhang and Zhu
  @{cite ZhangZhu}, Prop.~2.1, for general coefficients, with $c=0$ off $E$). This identity is
  taken as the definition \<open>polarized\<close> below; the comparison of coefficients that leads to it
  is not formalized.

  The squares are indexed by a finite type \<open>'r\<close>, the vectors are functions \<open>'r \<Rightarrow> rat\<close> and the
  inner product is \<open>dot_on UNIV\<close>. Finiteness of $E$ and of the index types of \<open>i\<close>, \<open>j\<close> is not
  needed here.\<close>

definition polarized :: "('a \<times> 'b) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> rat) \<Rightarrow>
    ('a \<Rightarrow> 'b \<Rightarrow> 'r::finite \<Rightarrow> rat) \<Rightarrow> bool" where
  "polarized E c v \<longleftrightarrow> (\<forall>i j. (i, j) \<notin> E \<longrightarrow> c i j = 0) \<and>
     (\<forall>i j k l. dot_on UNIV (v i j) (v k l) + dot_on UNIV (v i l) (v k j) =
        2 * (if i = k \<and> j = l then c i j else 0))"

lemma dot_on_UNIV_self_zero:
  fixes u :: "'r::finite \<Rightarrow> rat"
  assumes "dot_on UNIV u u = 0"
  shows "u = 0"
proof
  fix k
  have "\<forall>k\<in>UNIV. u k = 0"
    using assms dot_on_self_eq_0[of "UNIV :: 'r set" u] by simp
  then show "u k = 0 k" by (simp add: zero_fun_def)
qed

subsection \<open>Support\<close>

lemma support:
  assumes "polarized E c v" and "(i, j) \<notin> E"
  shows "v i j = 0"
proof -
  have c0: "c i j = 0" using assms unfolding polarized_def by blast
  have "dot_on UNIV (v i j) (v i j) + dot_on UNIV (v i j) (v i j) =
      2 * (if i = i \<and> j = j then c i j else 0)"
    using assms(1) unfolding polarized_def by blast
  then have "dot_on UNIV (v i j) (v i j) = 0" using c0 by simp
  then show ?thesis by (rule dot_on_UNIV_self_zero)
qed

subsection \<open>Distinct edges are orthogonal\<close>

lemma edges_orthogonal:
  assumes P: "polarized E c v" and C: "c4_free E"
    and e1: "(i, j) \<in> E" and e2: "(k, l) \<in> E" and ne: "(i, j) \<noteq> (k, l)"
  shows "dot_on UNIV (v i j) (v k l) = 0"
proof -
  have pol: "\<And>i j k l. dot_on UNIV (v i j) (v k l) + dot_on UNIV (v i l) (v k j) =
      2 * (if i = k \<and> j = l then c i j else 0)"
    using P unfolding polarized_def by blast
  show ?thesis
  proof (cases "i = k")
    case True
    with ne have jl: "j \<noteq> l" by simp
    have "dot_on UNIV (v i j) (v i l) + dot_on UNIV (v i l) (v i j) =
        2 * (if i = i \<and> j = l then c i j else 0)"
      by (rule pol)
    with jl have "dot_on UNIV (v i j) (v i l) + dot_on UNIV (v i l) (v i j) = 0" by simp
    then have "2 * dot_on UNIV (v i j) (v i l) = 0" by (simp add: dot_on_comm)
    then show ?thesis using True by simp
  next
    case ik: False
    show ?thesis
    proof (cases "j = l")
      case True
      have "dot_on UNIV (v i j) (v k j) + dot_on UNIV (v i j) (v k j) =
          2 * (if i = k \<and> j = j then c i j else 0)"
        by (rule pol)
      with ik have "2 * dot_on UNIV (v i j) (v k j) = 0" by simp
      then show ?thesis using True by simp
    next
      case jl: False
      have eq: "dot_on UNIV (v i j) (v k l) + dot_on UNIV (v i l) (v k j) = 0"
        using pol[of i j k l] ik by simp
      have "(i, l) \<notin> E \<or> (k, j) \<notin> E"
        using C ik jl e1 e2 unfolding c4_free_def
        by (metis)
      then have "dot_on UNIV (v i l) (v k j) = 0"
      proof
        assume "(i, l) \<notin> E"
        then have "v i l = 0" by (rule support[OF P])
        then show ?thesis by (simp add: dot_on_def)
      next
        assume "(k, j) \<notin> E"
        then have "v k j = 0" by (rule support[OF P])
        then show ?thesis by (simp add: dot_on_def)
      qed
      with eq show ?thesis by simp
    qed
  qed
qed

subsection \<open>The family $v_e$, $e \in E$, is orthogonal with norms $c_e$\<close>

text \<open>The representation is the function \<open>v\<close> itself, with values in the vector space
  \<open>'r \<Rightarrow> rat\<close> and the standard inner product: it is exactly the coefficient vector of the
  monomial $x_iy_j$ in the $r$ squares. A rational embedding of the form
  $\bigoplus_{e\in E}\langle c_e\rangle$ in $I_r$ is the same as such a family.\<close>

lemma edge_norm:
  assumes "polarized E c v"
  shows "dot_on UNIV (v i j) (v i j) = c i j"
proof -
  have "dot_on UNIV (v i j) (v i j) + dot_on UNIV (v i j) (v i j) =
      2 * (if i = i \<and> j = j then c i j else 0)"
    using assms unfolding polarized_def by blast
  then show ?thesis by simp
qed

theorem embedding:
  assumes P: "polarized E c v" and C: "c4_free E"
  shows "\<forall>e\<in>E. \<forall>e'\<in>E. dot_on UNIV (v (fst e) (snd e)) (v (fst e') (snd e')) =
    (if e = e' then c (fst e) (snd e) else 0)"
proof (intro ballI)
  fix e e' assume e: "e \<in> E" and e': "e' \<in> E"
  obtain i j where ij: "e = (i, j)" by (cases e)
  obtain k l where kl: "e' = (k, l)" by (cases e')
  show "dot_on UNIV (v (fst e) (snd e)) (v (fst e') (snd e')) = (if e = e' then c (fst e) (snd e) else 0)"
  proof (cases "e = e'")
    case True
    then show ?thesis using edge_norm[OF P] ij by simp
  next
    case False
    then have "(i, j) \<noteq> (k, l)" using ij kl by simp
    then have "dot_on UNIV (v i j) (v k l) = 0"
      using edges_orthogonal[OF P C, of i j k l] e e' ij kl by simp
    then have h: "dot_on UNIV (v (fst e) (snd e)) (v (fst e') (snd e')) = 0" using ij kl by simp
    have h2: "(if e = e' then c (fst e) (snd e) else 0) = 0" using False by simp
    show ?thesis using h h2 by simp
  qed
qed

corollary norms_nonneg:
  assumes "polarized E c v" shows "0 \<le> c i j"
  using edge_norm[OF assms, of i j] dot_on_self_nonneg[of UNIV "v i j"] by simp

end
