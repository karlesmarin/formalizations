(*  Title:      MQY_Pieces.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Elementary pieces of the note "On z_2M(21,4): the Hole Extensions of the Chen-Chen
    Configuration Are Reducible, and Extremal Configurations Are Not Unique" (Marín, Qi, Yu):
    the cell count, the heredity of irreducibility, the equality case of the C4-free cell
    bound (every pair of columns in exactly one row), the six-to-four identity and the
    2 x 2 example.
*)
theory MQY_Pieces
  imports Complex_Main "Segre_Width3.Zarankiewicz_Cells"
begin

section \<open>The cell count of a display\<close>

text \<open>Cells are split into 1-edges @{term E1}, main halves @{term Mn} (one per 2-edge),
  the set of secondary halves @{term "sec ` E2"} and the holes.  With @{text "t = e1 + e2"},
  @{text "s = card (sec ` E2)"} and @{text "H"} the number of holes:
  @{text "N + e1 + e2 = 2 t + H + s"}.  At @{text "N = 84"}, @{text "e1 = 27"} and
  @{text "k = e2 - s"} this is @{text "2 (t - 55) = 1 + k - H"}.\<close>

theorem display_cell_count:
  fixes Cells E1 Mn :: "'c set" and E2 :: "'e set" and sec :: "'e \<Rightarrow> 'c"
  assumes fin: "finite Cells"
    and sub: "E1 \<subseteq> Cells" "Mn \<subseteq> Cells" "sec ` E2 \<subseteq> Cells"
    and disj: "E1 \<inter> Mn = {}" "E1 \<inter> sec ` E2 = {}" "Mn \<inter> sec ` E2 = {}"
    and main: "card Mn = card E2"
  shows "card Cells + card E1 + card E2
         = 2 * (card E1 + card E2) + card (Cells - (E1 \<union> Mn \<union> sec ` E2)) + card (sec ` E2)"
proof -
  let ?U = "E1 \<union> Mn \<union> sec ` E2"
  have finU: "finite ?U" using sub fin finite_subset by blast
  have f1: "finite E1" "finite Mn" "finite (sec ` E2)" using sub fin finite_subset by blast+
  have cU: "card ?U = card E1 + card Mn + card (sec ` E2)"
  proof -
    have "card (E1 \<union> Mn) = card E1 + card Mn"
      using card_Un_disjoint[OF f1(1) f1(2) disj(1)] .
    moreover have "(E1 \<union> Mn) \<inter> sec ` E2 = {}" using disj(2,3) by blast
    ultimately show ?thesis
      using card_Un_disjoint[of "E1 \<union> Mn" "sec ` E2"] f1 by simp
  qed
  have "card Cells = card ?U + card (Cells - ?U)"
  proof -
    have "?U \<subseteq> Cells" using sub by blast
    then show ?thesis
      using card_Diff_subset[OF finU] card_mono[OF fin] by (simp add: le_add_diff_inverse)
  qed
  then show ?thesis using cU main by simp
qed

corollary cell_count_21x4:
  fixes t e2 s H k :: int
  assumes "84 + 27 + e2 = 2 * t + H + s" and "t = 27 + e2" and "k = e2 - s"
  shows "2 * (t - 55) = 1 + k - H"
  using assms by simp

corollary no_hole_one_share:
  fixes t e2 s H k :: int
  assumes "2 * (t - 55) = 1 + k - H" and "t = 56" and "H = 0"
  shows "k = 1"
  using assms by simp

section \<open>Inheritance of irreducibility\<close>

text \<open>A form @{term P} has a representation of length @{term n} by squares of forms in @{term F}.\<close>

definition sos_rep :: "('z \<Rightarrow> real) set \<Rightarrow> ('z \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> bool" where
  "sos_rep F P n \<longleftrightarrow> (\<exists>fs. length fs = n \<and> set fs \<subseteq> F \<and> P = (\<lambda>z. \<Sum>f\<leftarrow>fs. (f z)\<^sup>2))"

definition irreducible_at :: "('z \<Rightarrow> real) set \<Rightarrow> ('z \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> bool" where
  "irreducible_at F P t \<longleftrightarrow> (\<forall>n<t. \<not> sos_rep F P n)"

lemma sos_rep_add_square:
  assumes "sos_rep F P n" and "f \<in> F"
  shows "sos_rep F (\<lambda>z. P z + (f z)\<^sup>2) (Suc n)"
proof -
  obtain fs where fs: "length fs = n" "set fs \<subseteq> F" "P = (\<lambda>z. \<Sum>g\<leftarrow>fs. (g z)\<^sup>2)"
    using assms(1) unfolding sos_rep_def by blast
  have "length (f # fs) = Suc n" "set (f # fs) \<subseteq> F" using fs assms(2) by auto
  moreover have "(\<lambda>z. P z + (f z)\<^sup>2) = (\<lambda>z. \<Sum>g\<leftarrow>f # fs. (g z)\<^sup>2)"
    using fs(3) by (simp add: add.commute)
  ultimately show ?thesis unfolding sos_rep_def by blast
qed

text \<open>Deleting one displayed square keeps irreducibility, with one square less.\<close>

theorem irreducible_delete_square:
  assumes "irreducible_at F (\<lambda>z. P z + (f z)\<^sup>2) (Suc t)" and "f \<in> F"
  shows "irreducible_at F P t"
  unfolding irreducible_at_def
proof (intro allI impI)
  fix n assume "n < t"
  show "\<not> sos_rep F P n"
  proof
    assume "sos_rep F P n"
    then have "sos_rep F (\<lambda>z. P z + (f z)\<^sup>2) (Suc n)"
      using sos_rep_add_square assms(2) by blast
    moreover have "Suc n < Suc t" using \<open>n < t\<close> by simp
    ultimately show False using assms(1) unfolding irreducible_at_def by blast
  qed
qed

section \<open>The equality case of the cell bound\<close>

lemma eq_one_plus_choose_two_iff: "d = 1 + (d choose 2) \<longleftrightarrow> d = 1 \<or> d = 2"
proof
  assume h: "d = 1 + (d choose 2)"
  show "d = 1 \<or> d = 2"
  proof (rule ccontr)
    assume "\<not> (d = 1 \<or> d = 2)"
    then have "d = 0 \<or> 3 \<le> d" by auto
    then show False
    proof
      assume "d = 0"
      with h show False by simp
    next
      assume d3: "3 \<le> d"
      have "2 * d \<le> d * (d - 1)" using d3 by simp
      then have "2 * d div 2 \<le> d * (d - 1) div 2" by (rule div_le_mono)
      then have "d \<le> d choose 2" by (simp add: choose_two)
      with h show False by simp
    qed
  qed
next
  assume "d = 1 \<or> d = 2"
  then show "d = 1 + (d choose 2)" by (auto simp: numeral_2_eq_2)
qed

theorem c4_free_extremal_rows:
  assumes sub: "E \<subseteq> {0..<m} \<times> {0..<n}" and C: "c4_free E"
    and eq: "card E = m + (n choose 2)"
  shows "\<forall>i<m. card (row E i) = 1 \<or> card (row E i) = 2"
    and "\<forall>S. S \<subseteq> {0..<n} \<longrightarrow> card S = 2 \<longrightarrow> (\<exists>!i. i < m \<and> S \<subseteq> row E i)"
proof -
  let ?d = "\<lambda>i. card (row E i)"
  have s1: "card E = (\<Sum>i\<in>{0..<m}. ?d i)" by (rule card_eq_sum_rows[OF sub])
  have s2: "(\<Sum>i\<in>{0..<m}. ?d i choose 2) \<le> n choose 2" by (rule sum_choose_two_le[OF sub C])
  have pw: "?d i \<le> 1 + (?d i choose 2)" for i by (rule le_one_plus_choose_two)
  have s3: "(\<Sum>i\<in>{0..<m}. ?d i) \<le> (\<Sum>i\<in>{0..<m}. 1 + (?d i choose 2))"
    by (rule sum_mono) (rule pw)
  have s4: "(\<Sum>i\<in>{0..<m}. 1 + (?d i choose 2)) = m + (\<Sum>i\<in>{0..<m}. ?d i choose 2)"
    by (subst sum.distrib) simp
  have tight: "(\<Sum>i\<in>{0..<m}. ?d i) = (\<Sum>i\<in>{0..<m}. 1 + (?d i choose 2))"
    using s1 s2 s3 s4 eq by linarith
  have pairs: "(\<Sum>i\<in>{0..<m}. ?d i choose 2) = n choose 2"
    using s1 s2 s3 s4 eq by linarith
  show "\<forall>i<m. ?d i = 1 \<or> ?d i = 2"
  proof (intro allI impI)
    fix i assume "i < m"
    then have "?d i = 1 + (?d i choose 2)"
      using sum_mono_inv[OF tight] pw by simp
    then show "?d i = 1 \<or> ?d i = 2" using eq_one_plus_choose_two_iff by blast
  qed
  define Q where "Q i = {S. S \<subseteq> row E i \<and> card S = 2}" for i
  define T where "T = {S. S \<subseteq> {0..<n} \<and> card S = (2::nat)}"
  have finR: "finite (row E i)" for i using row_subset[OF sub] finite_subset by blast
  have cardQ: "card (Q i) = ?d i choose 2" for i unfolding Q_def using n_subsets[OF finR] .
  have finQ: "finite (Q i)" for i
    unfolding Q_def by (rule finite_subset[where B = "Pow (row E i)"]) (use finR in auto)
  have uniq: "i = i'" if S1: "S \<subseteq> row E i" and S2: "S \<subseteq> row E i'" and c2: "card S = 2"
    for S i i'
  proof (rule ccontr)
    assume ne: "i \<noteq> i'"
    obtain j j' where Sj: "S = {j, j'}" and jj: "j \<noteq> j'"
      using c2 unfolding card_2_iff by (elim exE conjE) simp
    have "(i, j) \<in> E" "(i, j') \<in> E" "(i', j) \<in> E" "(i', j') \<in> E"
      using S1 S2 Sj by (auto simp: row_def)
    then show False using C[unfolded c4_free_def, rule_format, OF ne jj] by blast
  qed
  have disj: "Q i \<inter> Q i' = {}" if "i \<noteq> i'" for i i'
    using uniq that unfolding Q_def by blast
  have finT: "finite T" unfolding T_def by (rule finite_subset[where B = "Pow {0..<n}"]) auto
  have UT: "(\<Union>i\<in>{0..<m}. Q i) \<subseteq> T" using row_subset[OF sub] unfolding Q_def T_def by blast
  have "card (\<Union>i\<in>{0..<m}. Q i) = (\<Sum>i\<in>{0..<m}. card (Q i))"
    by (rule card_UN_disjoint) (use finQ disj in auto)
  also have "\<dots> = n choose 2" using pairs by (simp add: cardQ)
  also have "\<dots> = card T" unfolding T_def using n_subsets[where A = "{0..<n}" and k = 2] by simp
  finally have UQ: "(\<Union>i\<in>{0..<m}. Q i) = T" using card_subset_eq[OF finT UT] by blast
  show "\<forall>S. S \<subseteq> {0..<n} \<longrightarrow> card S = 2 \<longrightarrow> (\<exists>!i. i < m \<and> S \<subseteq> row E i)"
  proof (intro allI impI)
    fix S :: "nat set" assume Sn: "S \<subseteq> {0..<n}" and c2: "card S = 2"
    then have "S \<in> T" unfolding T_def by simp
    then obtain i where im: "i \<in> {0..<m}" and SQ: "S \<in> Q i" using UQ by blast
    then have Si: "S \<subseteq> row E i" unfolding Q_def by simp
    show "\<exists>!i. i < m \<and> S \<subseteq> row E i"
    proof (rule ex1I[where a = i])
      show "i < m \<and> S \<subseteq> row E i" using im Si by simp
    next
      fix i' assume "i' < m \<and> S \<subseteq> row E i'"
      then show "i' = i" using uniq[OF _ Si c2] by blast
    qed
  qed
qed

corollary every_column_pair_once_21x4:
  assumes "E \<subseteq> {0..<21} \<times> {0..<4}" and "c4_free E" and "card E = 27"
  shows "\<forall>S. S \<subseteq> {0..<4} \<longrightarrow> card S = 2 \<longrightarrow> (\<exists>!i. i < 21 \<and> S \<subseteq> row E i)"
proof -
  have "card E = 21 + (4 choose 2)" using assms(3) by (simp add: choose_two)
  then show ?thesis using c4_free_extremal_rows(2)[OF assms(1,2)] by blast
qed

section \<open>The six-to-four identity\<close>

text \<open>Two 2-edges with main halves @{text "(i,c)"}, @{text "(j,c)"} and the same secondary half
  @{text "(p,q)"}, and 1-edges @{text "(i,b)"}, @{text "(j,b)"}, @{text "(k,c)"}, @{text "(k,b)"}:
  the six squares are a sum of four squares of bilinear forms.  First with any @{term r} such
  that @{text "r\<^sup>2 = 2"}, then with @{text "sqrt 2"}.\<close>

lemma six_to_four_r:
  fixes xi xj xk xp yb yc yq r :: real
  assumes r: "r\<^sup>2 = 2"
  shows "2 * ((xi * yc + xp * yq)\<^sup>2 + (xj * yc + xp * yq)\<^sup>2
              + (xi * yb)\<^sup>2 + (xj * yb)\<^sup>2 + (xk * yc)\<^sup>2 + (xk * yb)\<^sup>2)
       = ((xi + xj) * yc + 2 * xp * yq)\<^sup>2 + ((xi + xj) * yb)\<^sup>2
         + ((xi - xj) * yc + r * xk * yb)\<^sup>2 + ((xi - xj) * yb - r * xk * yc)\<^sup>2"
proof -
  have "((xi + xj) * yc + 2 * xp * yq)\<^sup>2 + ((xi + xj) * yb)\<^sup>2
         + ((xi - xj) * yc + r * xk * yb)\<^sup>2 + ((xi - xj) * yb - r * xk * yc)\<^sup>2
      = 2 * ((xi * yc + xp * yq)\<^sup>2 + (xj * yc + xp * yq)\<^sup>2
              + (xi * yb)\<^sup>2 + (xj * yb)\<^sup>2)
        + r\<^sup>2 * ((xk * yc)\<^sup>2 + (xk * yb)\<^sup>2)"
    by (simp add: power2_eq_square algebra_simps)
  then show ?thesis using r by (simp add: algebra_simps)
qed

theorem six_to_four:
  fixes xi xj xk xp yb yc yq :: real
  shows "(xi * yc + xp * yq)\<^sup>2 + (xj * yc + xp * yq)\<^sup>2
              + (xi * yb)\<^sup>2 + (xj * yb)\<^sup>2 + (xk * yc)\<^sup>2 + (xk * yb)\<^sup>2
       = (((xi + xj) * yc + 2 * xp * yq) / sqrt 2)\<^sup>2 + (((xi + xj) * yb) / sqrt 2)\<^sup>2
         + (((xi - xj) * yc + sqrt 2 * xk * yb) / sqrt 2)\<^sup>2
         + (((xi - xj) * yb - sqrt 2 * xk * yc) / sqrt 2)\<^sup>2"
proof -
  have r: "(sqrt 2)\<^sup>2 = (2::real)" by simp
  have q: "(X / sqrt 2)\<^sup>2 = X\<^sup>2 / 2" for X :: real by (simp add: power_divide)
  have h: "2 * ((xi * yc + xp * yq)\<^sup>2 + (xj * yc + xp * yq)\<^sup>2
              + (xi * yb)\<^sup>2 + (xj * yb)\<^sup>2 + (xk * yc)\<^sup>2 + (xk * yb)\<^sup>2)
       = ((xi + xj) * yc + 2 * xp * yq)\<^sup>2 + ((xi + xj) * yb)\<^sup>2
         + ((xi - xj) * yc + sqrt 2 * xk * yb)\<^sup>2 + ((xi - xj) * yb - sqrt 2 * xk * yc)\<^sup>2"
    by (rule six_to_four_r[OF r])
  have g: "\<And>L a b c d :: real. 2 * L = a + b + c + d \<Longrightarrow> L = a / 2 + b / 2 + c / 2 + d / 2"
    by linarith
  show ?thesis unfolding q by (rule g[OF h])
qed

section \<open>The $2\times 2$ example: three squares are needed\<close>

text \<open>With @{text "a = x1 y1"}, @{text "b = x1 y2"}, @{text "c = x2 y1"}, @{text "d = x2 y2"},
  the form @{text "a\<^sup>2 + (b + c)\<^sup>2 + (b + d)\<^sup>2"} is not a sum of two squares of bilinear forms.\<close>

definition ex22 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "ex22 x1 x2 y1 y2 = (x1 * y1)\<^sup>2 + (x1 * y2 + x2 * y1)\<^sup>2 + (x1 * y2 + x2 * y2)\<^sup>2"

definition bil :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "bil p1 p2 p3 p4 x1 x2 y1 y2 = p1 * (x1 * y1) + p2 * (x1 * y2) + p3 * (x2 * y1) + p4 * (x2 * y2)"

theorem ex22_not_two_squares:
  "\<not> (\<exists>p1 p2 p3 p4 q1 q2 q3 q4. \<forall>x1 x2 y1 y2.
        ex22 x1 x2 y1 y2 = (bil p1 p2 p3 p4 x1 x2 y1 y2)\<^sup>2 + (bil q1 q2 q3 q4 x1 x2 y1 y2)\<^sup>2)"
proof
  assume "\<exists>p1 p2 p3 p4 q1 q2 q3 q4. \<forall>x1 x2 y1 y2.
        ex22 x1 x2 y1 y2 = (bil p1 p2 p3 p4 x1 x2 y1 y2)\<^sup>2 + (bil q1 q2 q3 q4 x1 x2 y1 y2)\<^sup>2"
  then obtain p1 p2 p3 p4 q1 q2 q3 q4 where H: "\<And>x1 x2 y1 y2.
        ex22 x1 x2 y1 y2 = (bil p1 p2 p3 p4 x1 x2 y1 y2)\<^sup>2 + (bil q1 q2 q3 q4 x1 x2 y1 y2)\<^sup>2"
    by blast
  define M where "M a b = a * b" for a b :: real
  have e11: "p1 * p1 + q1 * q1 = 1" using H[of 1 0 1 0] by (simp add: ex22_def bil_def power2_eq_square)
  have e22: "p2 * p2 + q2 * q2 = 2" using H[of 1 0 0 1] by (simp add: ex22_def bil_def power2_eq_square)
  have e33: "p3 * p3 + q3 * q3 = 1" using H[of 0 1 1 0] by (simp add: ex22_def bil_def power2_eq_square)
  have e44: "p4 * p4 + q4 * q4 = 1" using H[of 0 1 0 1] by (simp add: ex22_def bil_def power2_eq_square)
  have h12: "(p1 + p2) * (p1 + p2) + (q1 + q2) * (q1 + q2) = 3"
    using H[of 1 0 1 1] by (simp add: ex22_def bil_def power2_eq_square)
  have h13: "(p1 + p3) * (p1 + p3) + (q1 + q3) * (q1 + q3) = 2"
    using H[of 1 1 1 0] by (simp add: ex22_def bil_def power2_eq_square)
  have h24: "(p2 + p4) * (p2 + p4) + (q2 + q4) * (q2 + q4) = 5"
    using H[of 1 1 0 1] by (simp add: ex22_def bil_def power2_eq_square)
  have h34: "(p3 + p4) * (p3 + p4) + (q3 + q4) * (q3 + q4) = 2"
    using H[of 0 1 1 1] by (simp add: ex22_def bil_def power2_eq_square)
  have hall: "(p1 + p2 + p3 + p4) * (p1 + p2 + p3 + p4) + (q1 + q2 + q3 + q4) * (q1 + q2 + q3 + q4) = 9"
    using H[of 1 1 1 1] by (simp add: ex22_def bil_def power2_eq_square)
  have m12: "p1 * p2 + q1 * q2 = 0" using h12 e11 e22 by (simp add: algebra_simps)
  have m13: "p1 * p3 + q1 * q3 = 0" using h13 e11 e33 by (simp add: algebra_simps)
  have m24: "p2 * p4 + q2 * q4 = 1" using h24 e22 e44 by (simp add: algebra_simps)
  have m34: "p3 * p4 + q3 * q4 = 0" using h34 e33 e44 by (simp add: algebra_simps)
  define s where "s = p1 * p4 + q1 * q4"
  define t where "t = p2 * p3 + q2 * q3"
  have st: "s + t = 1"
    using hall e11 e22 e33 e44 m12 m13 m24 m34 unfolding s_def t_def by (simp add: algebra_simps)
  text \<open>Two $3\times 3$ minors of the Gram matrix of two squares vanish identically.\<close>
  have minor134: "(p1*p1+q1*q1) * (p3*p3+q3*q3) * (p4*p4+q4*q4)
      + 2 * (p1*p3+q1*q3) * (p3*p4+q3*q4) * (p1*p4+q1*q4)
      - (p1*p1+q1*q1) * (p3*p4+q3*q4)^2 - (p3*p3+q3*q3) * (p1*p4+q1*q4)^2
      - (p4*p4+q4*q4) * (p1*p3+q1*q3)^2 = 0"
    by algebra
  have minor123: "(p1*p1+q1*q1) * (p2*p2+q2*q2) * (p3*p3+q3*q3)
      + 2 * (p1*p2+q1*q2) * (p2*p3+q2*q3) * (p1*p3+q1*q3)
      - (p1*p1+q1*q1) * (p2*p3+q2*q3)^2 - (p2*p2+q2*q2) * (p1*p3+q1*q3)^2
      - (p3*p3+q3*q3) * (p1*p2+q1*q2)^2 = 0"
    by algebra
  have s2: "s * s = 1"
    using minor134 unfolding s_def[symmetric] by (simp add: e11 e33 e44 m13 m34 power2_eq_square)
  have t2: "t * t = 2"
    using minor123 unfolding t_def[symmetric] by (simp add: e11 e22 e33 m12 m13 power2_eq_square)
  have ts: "t = 1 - s" using st by simp
  have ex: "(1 - s) * (1 - s) = 1 - 2 * s + s * s" by (simp add: algebra_simps)
  have "s = 0" using t2 s2 ex unfolding ts by linarith
  then show False using s2 by simp
qed

theorem ex22_three_squares:
  "ex22 x1 x2 y1 y2 = (bil 1 0 0 0 x1 x2 y1 y2)\<^sup>2 + (bil 0 1 1 0 x1 x2 y1 y2)\<^sup>2
     + (bil 0 1 0 1 x1 x2 y1 y2)\<^sup>2"
  by (simp add: ex22_def bil_def)

end
