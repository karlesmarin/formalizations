(*  Title:      Frieze_Two_Sign_Changes.thy
    Author:     Carles Marín

    Two integer friezes of width 12 with two sign changes

    Two integer Conway-Coxeter frieze patterns of width 12 (quiddities of length 15) whose rows 6 differ, cyclically,
    with no zero and exactly two sign changes. Row 6 = [12/2] lies in the range 1 <= k <= [w/2] of Problem 1 of
    Tabachnikov, which asks for which k the difference must change sign at least four times. All facts are finite
    computations proved with code_simp. Found by an exhaustive search over all 742 900 friezes of width 12; width 12 is
    the smallest width with such a pair in the range k <= [w/2].

    Main results:
    * exists_two_sign_changes_width_12.

    References:
    * S. Tabachnikov, A four-vertex theorem for frieze patterns?, Math. Intelligencer 40 (2018) 14--18, Problem 1.
*)

theory Frieze_Two_Sign_Changes
  imports Frieze_Dominance
begin

definition lower12 :: "int list" where
  "lower12 = [1, 2, 2, 2, 2, 3, 1, 4, 2, 1, 4, 2, 2, 1, 10]"

definition upper12 :: "int list" where
  "upper12 = [4, 3, 1, 2, 3, 3, 4, 1, 2, 2, 5, 2, 2, 1, 4]"

text \<open>The difference of the rows \<open>k\<close>, and the number of cyclic positions where it changes sign strictly.\<close>

definition diff_row :: "int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "diff_row a b k i = entry b k i - entry a k i"

definition sign_changes :: "int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> nat" where
  "sign_changes a b k = length (filter (\<lambda>i. diff_row a b k i * diff_row a b k ((i + 1) mod length a) < 0)
     [0..<length a])"

lemma is_quiddity_lower12: "is_quiddity lower12"
  by code_simp

lemma is_quiddity_upper12: "is_quiddity upper12"
  by code_simp

lemma row6_no_zero: "\<forall>i \<in> set [0..<15]. diff_row lower12 upper12 6 i \<noteq> 0"
  by code_simp

lemma row6_two_sign_changes: "sign_changes lower12 upper12 6 = 2"
  by code_simp

theorem exists_two_sign_changes_width_12:
  "\<exists>a b. is_quiddity a \<and> is_quiddity b \<and> length a = 15 \<and> length b = 15 \<and>
     (\<forall>i < 15. diff_row a b 6 i \<noteq> 0) \<and> sign_changes a b 6 = 2"
proof -
  have "\<forall>i < 15. diff_row lower12 upper12 6 i \<noteq> 0"
    using row6_no_zero by auto
  then show ?thesis
    using is_quiddity_lower12 is_quiddity_upper12 row6_two_sign_changes
    by (intro exI[of _ lower12] exI[of _ upper12]) (simp add: lower12_def upper12_def)
qed

text \<open>Controls: the counter sees four sign changes where there are four (row 5 of the same pair), and
  a wrong quiddity is rejected.\<close>

lemma "sign_changes lower12 upper12 5 \<ge> 4"
  by code_simp

lemma "\<not> is_quiddity [1, 2, 2, 2, 2, 3, 1, 4, 2, 1, 4, 2, 2, 2, 10]"
  by code_simp

end
