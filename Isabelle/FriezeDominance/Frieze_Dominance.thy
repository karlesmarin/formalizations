(*  Title:      Frieze_Dominance.thy
    Author:     Carles Marín

Two integer Conway-Coxeter frieze patterns of width 11 (quiddities of length 14) whose middle rows
(row 6, the diameters of the 14-gon) are strictly ordered at all 14 positions: a counterexample, for
friezes of positive integers, to the four-sign-change question of S. Tabachnikov, "A four-vertex theorem
for frieze patterns?", Math. Intelligencer 40 (2018), Problem 1. Port of the Lean module
Formalizations.Combinatorics.Frieze.IntegerDominance. All facts are finite computations proved with
code_simp (the simplifier, proof-producing; no eval, no code generator oracle).
*)

theory Frieze_Dominance
  imports Main
begin

text \<open>The continuant: K() = 1, K(x1) = x1, K(x1..xj) = xj K(x1..x(j-1)) - K(x1..x(j-2)).\<close>

definition continuant :: "int list \<Rightarrow> int" where
  "continuant l = snd (fold (\<lambda>x (p, q). (q, x * q - p)) l (0, 1))"

text \<open>Entry of row k at position i of the frieze with quiddity a (indices modulo length a).\<close>

definition entry :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "entry a k i = continuant (map (\<lambda>t. a ! ((i + t) mod length a)) [0..<k])"

text \<open>Integer Conway-Coxeter frieze of width length a - 3: rows 1..w positive, row w+1 all ones,
  row w+2 all zeros.\<close>

definition is_quiddity :: "int list \<Rightarrow> bool" where
  "is_quiddity a \<longleftrightarrow>
     (\<forall>k \<in> set [1..<length a - 2]. \<forall>i \<in> set [0..<length a]. 0 < entry a k i) \<and>
     (\<forall>i \<in> set [0..<length a]. entry a (length a - 2) i = 1) \<and>
     (\<forall>i \<in> set [0..<length a]. entry a (length a - 1) i = 0)"

definition lower :: "int list" where
  "lower = [1, 2, 2, 2, 2, 3, 1, 3, 2, 2, 2, 2, 1, 11]"

definition upper :: "int list" where
  "upper = [1, 5, 2, 3, 1, 2, 5, 4, 1, 2, 2, 4, 2, 2]"

lemma is_quiddity_lower: "is_quiddity lower"
  by code_simp

lemma is_quiddity_upper: "is_quiddity upper"
  by code_simp

lemma middle_rows_ordered: "\<forall>i \<in> set [0..<14]. entry lower 6 i < entry upper 6 i"
  by code_simp

theorem exists_strictly_ordered_middle_rows:
  "\<exists>a b. is_quiddity a \<and> is_quiddity b \<and> length a = 14 \<and> length b = 14 \<and>
     (\<forall>i < 14. entry a 6 i < entry b 6 i)"
proof -
  have "\<forall>i < 14. entry lower 6 i < entry upper 6 i"
    using middle_rows_ordered by auto
  then show ?thesis
    using is_quiddity_lower is_quiddity_upper by (intro exI[of _ lower] exI[of _ upper]) (simp add: lower_def upper_def)
qed

text \<open>Negative control: the reverse order fails at position 0 (2 < 3).\<close>

lemma "\<not> (entry upper 6 0 < entry lower 6 0)"
  by code_simp

end
