(* encaje: cell bound for C4-free supports and the arithmetic of the width-four comparison *)
section \<open>The cell bound and the width-four comparison\<close>

theory Zarankiewicz_Cells
  imports Coefficient_Vectors
begin

text \<open>Corollaries 4 and 5 of the note @{cite Marin2026}: the cell bound $|E| \le m + \binom n2$
  for $C_4$-free supports $E \subseteq \{0..<m\} \times \{0..<n\}$, and the arithmetic of the
  comparison of $\lfloor 8m/3 \rfloor$ (the lower bound for $\mathrm{BSR}(m,4)$ given by the
  quadratic persistence of $\mathbb{P}^{m-1}\times\mathbb{P}^3$) with
  $\lfloor (5m+6)/2 \rfloor$ (the second order Zarankiewicz number $z_2(m,4)$ for $m\ge15$,
  @{cite ChenChen}). Only the arithmetic is formalized here, not the values of these invariants.\<close>

subsection \<open>A $C_4$-free support has at most $m+\binom n2$ cells\<close>

definition row_cells :: "(nat \<times> nat) set \<Rightarrow> nat \<Rightarrow> nat set" where
  "row_cells E i = {j. (i, j) \<in> E}"

lemma row_cells_subset:
  assumes "E \<subseteq> {0..<m} \<times> {0..<n}"
  shows "row_cells E i \<subseteq> {0..<n}"
  using assms by (auto simp: row_cells_def)

lemma card_eq_sum_row_cells:
  assumes "E \<subseteq> {0..<m} \<times> {0..<n}"
  shows "card E = (\<Sum>i\<in>{0..<m}. card (row_cells E i))"
proof -
  have e: "E = Sigma {0..<m} (row_cells E)"
    using assms by (auto simp: row_cells_def)
  have f: "finite (row_cells E i)" for i
    using row_cells_subset[OF assms] finite_subset by blast
  have "card E = card (Sigma {0..<m} (row_cells E))"
    by (rule arg_cong[where f = card, OF e])
  also have "\<dots> = (\<Sum>i\<in>{0..<m}. card (row_cells E i))"
    by (rule card_SigmaI) (use f in auto)
  finally show ?thesis .
qed

text \<open>Each pair of columns lies in at most one row: $\sum_i\binom{d_i}2\le\binom n2$.\<close>

lemma sum_choose_two_le:
  assumes sub: "E \<subseteq> {0..<m} \<times> {0..<n}" and C: "c4_free E"
  shows "(\<Sum>i\<in>{0..<m}. card (row_cells E i) choose 2) \<le> n choose 2"
proof -
  define Q where "Q i = {S. S \<subseteq> row_cells E i \<and> card S = 2}" for i
  have finR: "finite (row_cells E i)" for i
    using row_cells_subset[OF sub] finite_subset by blast
  have cardQ: "card (Q i) = card (row_cells E i) choose 2" for i
    unfolding Q_def using n_subsets[OF finR] .
  have finQ: "finite (Q i)" for i
    unfolding Q_def by (rule finite_subset[where B = "Pow (row_cells E i)"]) (use finR in auto)
  have disj: "Q i \<inter> Q i' = {}" if "i \<noteq> i'" for i i'
  proof (rule ccontr)
    assume "Q i \<inter> Q i' \<noteq> {}"
    then obtain S where S1: "S \<subseteq> row_cells E i" and S2: "S \<subseteq> row_cells E i'" and c2: "card S = 2"
      unfolding Q_def by blast
    obtain j j' where Sj: "S = {j, j'}" and jj: "j \<noteq> j'"
      using c2 unfolding card_2_iff by (elim exE conjE) simp
    have "(i, j) \<in> E" "(i, j') \<in> E" "(i', j) \<in> E" "(i', j') \<in> E"
      using S1 S2 Sj by (auto simp: row_cells_def)
    then show False
      using C[unfolded c4_free_def, rule_format, OF that jj] by blast
  qed
  have "(\<Sum>i\<in>{0..<m}. card (row_cells E i) choose 2) = (\<Sum>i\<in>{0..<m}. card (Q i))"
    by (simp add: cardQ)
  also have "\<dots> = card (\<Union>i\<in>{0..<m}. Q i)"
    by (rule card_UN_disjoint[symmetric]) (use finQ disj in auto)
  also have "\<dots> \<le> card {S. S \<subseteq> {0..<n} \<and> card S = 2}"
  proof (rule card_mono)
    show "finite {S. S \<subseteq> {0..<n} \<and> card S = (2::nat)}"
      by (rule finite_subset[where B = "Pow {0..<n}"]) auto
    show "(\<Union>i\<in>{0..<m}. Q i) \<subseteq> {S. S \<subseteq> {0..<n} \<and> card S = 2}"
      using row_cells_subset[OF sub] unfolding Q_def by blast
  qed
  also have "\<dots> = n choose 2"
    using n_subsets[where A = "{0..<n}" and k = 2] by simp
  finally show ?thesis .
qed

lemma le_one_plus_choose_two: "d \<le> 1 + (d choose 2)"
proof (cases d)
  case 0
  then show ?thesis by simp
next
  case (Suc k)
  have "Suc k choose 2 = (k choose 1) + (k choose 2)"
    using binomial_Suc_Suc[where n = k and k = 1] by (simp add: numeral_2_eq_2)
  then show ?thesis
    using Suc by simp
qed

theorem c4_free_card_le:
  assumes sub: "E \<subseteq> {0..<m} \<times> {0..<n}" and C: "c4_free E"
  shows "card E \<le> m + n * (n - 1) div 2"
proof -
  have "card E = (\<Sum>i\<in>{0..<m}. card (row_cells E i))"
    by (rule card_eq_sum_row_cells[OF sub])
  also have "\<dots> \<le> (\<Sum>i\<in>{0..<m}. 1 + (card (row_cells E i) choose 2))"
    by (rule sum_mono) (rule le_one_plus_choose_two)
  also have "\<dots> = m + (\<Sum>i\<in>{0..<m}. card (row_cells E i) choose 2)"
    by (subst sum.distrib) simp
  also have "\<dots> \<le> m + (n choose 2)"
    using sum_choose_two_le[OF sub C] by simp
  also have "\<dots> = m + n * (n - 1) div 2"
    by (simp add: choose_two)
  finally show ?thesis .
qed

subsection \<open>The arithmetic of the width-four comparison\<close>

theorem gap_pos: "23 \<le> m \<Longrightarrow> (5 * m + 6) div 2 < 8 * m div 3"
  for m :: nat
proof -
  assume m: "23 \<le> m"
  have r3: "8 * m mod 3 < 3" by simp
  have a: "8 * m div 3 * 3 + 8 * m mod 3 = 8 * m"
    by (rule div_mult_mod_eq)
  have b: "(5 * m + 6) div 2 * 2 + (5 * m + 6) mod 2 = 5 * m + 6"
    by (rule div_mult_mod_eq)
  from m r3 a b show ?thesis by linarith
qed

lemma gap_21: "(5 * 21 + 6) div 2 < 8 * 21 div (3::nat)"
  by simp

lemma gap_21_values: "8 * 21 div (3::nat) = 56" "(5 * 21 + 6) div (2::nat) = 55"
  by simp_all

lemma gap_22: "8 * 22 div (3::nat) = (5 * 22 + 6) div 2"
  by simp

lemma gap_22_values: "8 * 22 div (3::nat) = 58" "(5 * 22 + 6) div (2::nat) = 58"
  by simp_all

theorem gap_linear:
  fixes m :: nat
  shows "int m - 22 \<le> 6 * (int (8 * m div 3) - int ((5 * m + 6) div 2))"
proof -
  have r3: "8 * m mod 3 < 3" by simp
  have a0: "8 * m div 3 * 3 + 8 * m mod 3 = 8 * m"
    by (rule div_mult_mod_eq)
  have a: "3 * (8 * m div 3) + 2 \<ge> 8 * m"
    using a0 r3 by linarith
  have b0: "(5 * m + 6) div 2 * 2 + (5 * m + 6) mod 2 = 5 * m + 6"
    by (rule div_mult_mod_eq)
  have b: "2 * ((5 * m + 6) div 2) \<le> 5 * m + 6"
    using b0 by linarith
  have key: "int m - 22 \<le> 6 * (int x - int y)"
    if "8 * m \<le> 3 * x + 2" "2 * y \<le> 5 * m + 6" for x y :: nat
  proof -
    have h1: "int (8 * m) \<le> int (3 * x + 2)"
      using that(1) by (simp only: of_nat_le_iff)
    have h2: "int (2 * y) \<le> int (5 * m + 6)"
      using that(2) by (simp only: of_nat_le_iff)
    have h1': "8 * int m \<le> 3 * int x + 2"
      using h1 by (simp only: of_nat_add of_nat_mult of_nat_numeral)
    have h2': "2 * int y \<le> 5 * int m + 6"
      using h2 by (simp only: of_nat_add of_nat_mult of_nat_numeral)
    have d: "6 * (int x - int y) = 6 * int x - 6 * int y"
      by (simp only: right_diff_distrib)
    from h1' h2' have "int m - 22 \<le> 6 * int x - 6 * int y"
      by presburger
    then show ?thesis
      by (simp only: d)
  qed
  show ?thesis by (rule key[OF a b])
qed

text \<open>The cell bound in width four: with $z(m,4) = m + 6$ the bound
  $\lfloor (4m + z(m,4))/2 \rfloor$ is $\lfloor (5m+6)/2 \rfloor$.\<close>

theorem cell_count: "(4 * m + (m + 6)) div 2 = (5 * m + 6) div (2::nat)"
proof -
  have "4 * m + (m + 6) = 5 * m + 6" by simp
  then show ?thesis by simp
qed

end
