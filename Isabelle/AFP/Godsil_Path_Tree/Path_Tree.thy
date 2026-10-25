(*  Title:      Path_Tree.thy
    Author:     Carles Marín

Godsil's path tree: the matching polynomial of a graph and of its path tree are related by
mu (G - u) * mu T = mu G * mu (T - root).
*)

theory Path_Tree
  imports Heilmann_Lieb.Matching_Polynomial
begin

section \<open>The path tree\<close>

text \<open>The vertices of the path tree of \<open>G\<close> at \<open>u\<close> are the simple paths of \<open>G\<close> that start at \<open>u\<close>, as lists of
  vertices; a path is joined to each of its one-step extensions.\<close>

definition is_path :: "'a set set \<Rightarrow> 'a list \<Rightarrow> bool" where
  "is_path E p \<longleftrightarrow> p \<noteq> [] \<and> distinct p \<and> (\<forall>i. Suc i < length p \<longrightarrow> {p ! i, p ! Suc i} \<in> E)"

definition pt_V :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'a list set" where
  "pt_V V E u = {p. is_path E p \<and> hd p = u \<and> set p \<subseteq> V}"

definition pt_E :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'a list set set" where
  "pt_E V E u = {{p, p @ [w]} | p w. p \<in> pt_V V E u \<and> p @ [w] \<in> pt_V V E u}"

lemma pt_root: "u \<in> V \<Longrightarrow> [u] \<in> pt_V V E u"
  sorry

lemma graph_pt: "graph V E \<Longrightarrow> u \<in> V \<Longrightarrow> graph (pt_V V E u) (pt_E V E u)"
  sorry

section \<open>Renaming vertices and disjoint unions\<close>

lemma mu_bij:
  assumes "graph V E" and "bij_betw f V W"
  shows "mu W ((`) f ` E) = mu V E"
  sorry

lemma mu_disjoint_union:
  assumes "graph V1 E1" and "graph V2 E2" and "V1 \<inter> V2 = {}"
  shows "mu (V1 \<union> V2) (E1 \<union> E2) = mu V1 E1 * mu V2 E2"
  sorry

lemma mu_UNION:
  assumes "finite I" and "\<forall>i\<in>I. graph (Vs i) (Es i)" and "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> Vs i \<inter> Vs j = {}"
  shows "mu (\<Union>i\<in>I. Vs i) (\<Union>i\<in>I. Es i) = (\<Prod>i\<in>I. mu (Vs i) (Es i))"
  sorry

section \<open>The path tree below its root\<close>

text \<open>Below the root, the path tree of \<open>G\<close> at \<open>u\<close> is the disjoint union, over the neighbours \<open>v\<close> of \<open>u\<close>, of
  copies of the path tree of \<open>G - u\<close> at \<open>v\<close> (each path prefixed by \<open>u\<close>).\<close>

lemma pt_V_minus_root:
  assumes "graph V E" and "u \<in> V"
  shows "pt_V V E u - {[u]} = (\<Union>v\<in>nbrs E u. (#) u ` pt_V (V - {u}) (del1 E u) v)"
  sorry

lemma pt_E_minus_root:
  assumes "graph V E" and "u \<in> V"
  shows "del1 (pt_E V E u) [u] = (\<Union>v\<in>nbrs E u. (`) ((#) u) ` pt_E (V - {u}) (del1 E u) v)"
  sorry

lemma nbrs_pt_root:
  assumes "graph V E" and "u \<in> V"
  shows "nbrs (pt_E V E u) [u] = (\<lambda>v. [u, v]) ` nbrs E u"
  sorry

section \<open>Godsil's identity\<close>

theorem godsil_ratio:
  assumes "graph V E" and "u \<in> V"
  shows "mu (V - {u}) (del1 E u) * mu (pt_V V E u) (pt_E V E u)
       = mu V E * mu (pt_V V E u - {[u]}) (del1 (pt_E V E u) [u])"
  sorry

end
