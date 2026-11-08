(*  Title:      Seven_Embedding.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

(* encaje: unit vectors and a vector of norm 7 in Q^r force r >= e + 3; arithmetic from Three_Squares *)
section \<open>The embedding step: a vector of squared norm 7\<close>

theory Seven_Embedding
  imports Coefficient_Vectors Three_Squares.Three_Squares
begin

text \<open>Orthogonal unit vectors and one vector of squared norm $7$ in $\mathbb{Q}^r$ force
  $r \ge e + 3$ when there are $e - 1$ unit vectors. This is the embedding step of
  Theorem 6 of the note @{cite Marin2026}, and of the bound $\mathrm{BSR}_\mathbb{Q} \ge |E| + 3$
  of the theory \<open>BSR_Union\<close>.

  Vectors are functions @{typ "nat \<Rightarrow> rat"}, with the inner product \<open>dot_upto r\<close> summed over
  the coordinates below \<open>r\<close>. Then the dimension is an ordinary number, and the induction can
  drop one coordinate by shifting indices.\<close>

subsection \<open>Seven is not a sum of three rational squares\<close>

text \<open>The arithmetic input is the theorem of Legendre and Gauss in the form proved in the entry
  \emph{Three\_Squares} @{cite "Three_Squares-AFP"}: a natural number is a sum of three squares
  if and only if it is not of the form $4^a(8k+7)$ (\<open>three_squares_iff\<close>). Clearing denominators
  turns three rational squares with sum $c$ into an integer identity
  $x^2+y^2+z^2 = c\,w^2$, and writing $w = 2^a u$ with $u$ odd shows that $c\,w^2$ has the
  excluded form when $c \equiv 7 \pmod 8$.\<close>

lemma int_two_power_odd:
  fixes w :: int
  assumes "w \<noteq> 0"
  shows "\<exists>a u. w = 2 ^ a * u \<and> odd u"
  using assms
proof (induction "nat \<bar>w\<bar>" arbitrary: w rule: less_induct)
  case less
  show ?case
  proof (cases "even w")
    case False
    then show ?thesis by (intro exI[of _ 0] exI[of _ w]) simp
  next
    case True
    then obtain v where w: "w = 2 * v" by (auto elim: evenE)
    with less.prems have v0: "v \<noteq> 0" by simp
    then have "nat \<bar>v\<bar> < nat \<bar>w\<bar>" using w by auto
    then obtain a u where "v = 2 ^ a * u" "odd u" using less.hyps v0 by blast
    then show ?thesis using w by (intro exI[of _ "Suc a"] exI[of _ u]) simp
  qed
qed

lemma odd_square_mod_8:
  fixes u :: int
  assumes "odd u"
  shows "u\<^sup>2 mod 8 = 1"
proof -
  define n where "n = nat \<bar>u\<bar>"
  have un: "int n = \<bar>u\<bar>" unfolding n_def by simp
  have "odd (int n)" using assms un by simp
  then have "odd n" by simp
  then have on: "odd (n\<^sup>2)" by simp
  have m8: "n\<^sup>2 mod 8 \<in> {0, 1, 4}" by (rule power_two_mod_eight)
  have aux: "X mod 8 = 1" if "odd X" "X mod 8 = 0 \<or> X mod 8 = 1 \<or> X mod 8 = 4" for X :: nat
    using that by presburger
  have n8: "n\<^sup>2 mod 8 = 1" by (rule aux[OF on]) (use m8 in simp)
  have "int (n\<^sup>2) = (int n)\<^sup>2" by (rule of_nat_power)
  also have "\<dots> = \<bar>u\<bar>\<^sup>2" by (simp only: un)
  also have "\<dots> = u\<^sup>2" by (rule power2_abs)
  finally have "u\<^sup>2 = int (n\<^sup>2)" by (rule sym)
  then have "u\<^sup>2 mod 8 = int (n\<^sup>2 mod 8)" by (simp add: of_nat_mod)
  with n8 show ?thesis by simp
qed

lemma four_power_int: "(2::int) ^ a * 2 ^ a = 4 ^ a"
  by (induct a) simp_all

lemma seven_mod_8_no_rational_three_squares:
  fixes c :: int
  assumes c: "c mod 8 = 7"
  shows "x\<^sup>2 + y\<^sup>2 + z\<^sup>2 = c * w\<^sup>2 \<Longrightarrow> w = 0"
proof (rule ccontr)
  assume e: "x\<^sup>2 + y\<^sup>2 + z\<^sup>2 = c * w\<^sup>2" and w0: "w \<noteq> 0"
  obtain a u where wu: "w = 2 ^ a * u" and u: "odd u" using int_two_power_odd[OF w0] by blast
  have u8: "u\<^sup>2 mod 8 = 1" by (rule odd_square_mod_8[OF u])
  have w2: "w\<^sup>2 = 4 ^ a * u\<^sup>2"
    unfolding wu power2_eq_square using four_power_int[of a] by (simp add: algebra_simps)
  have "0 \<le> c * w\<^sup>2" using e[symmetric] by simp
  moreover have "0 < w\<^sup>2" using w0 by simp
  ultimately have c0: "0 \<le> c" by (simp add: zero_le_mult_iff)
  have "(c * u\<^sup>2) mod 8 = ((c mod 8) * (u\<^sup>2 mod 8)) mod 8" by (rule mod_mult_eq[symmetric])
  then have cu8: "(c * u\<^sup>2) mod 8 = 7" using c u8 by simp
  have cu0: "0 \<le> c * u\<^sup>2" using c0 by simp
  have split: "X = 8 * ((X - 7) div 8) + 7 \<and> 0 \<le> (X - 7) div 8"
    if "X mod 8 = 7" "0 \<le> X" for X :: int
    using that by presburger
  define k where "k = nat ((c * u\<^sup>2 - 7) div 8)"
  have cuk: "c * u\<^sup>2 = 8 * int k + 7"
    using split[OF cu8 cu0] unfolding k_def by simp
  define N where "N = (nat \<bar>x\<bar>)\<^sup>2 + (nat \<bar>y\<bar>)\<^sup>2 + (nat \<bar>z\<bar>)\<^sup>2"
  have "int N = x\<^sup>2 + y\<^sup>2 + z\<^sup>2" unfolding N_def by simp
  also have "\<dots> = 4 ^ a * (c * u\<^sup>2)" using e w2 by (simp add: algebra_simps)
  also have "\<dots> = int (4 ^ a * (8 * k + 7))" using cuk by simp
  finally have N: "N = 4 ^ a * (8 * k + 7)" by (simp only: of_nat_eq_iff)
  have "\<exists>x\<^sub>1 x\<^sub>2 x\<^sub>3. N = x\<^sub>1\<^sup>2 + x\<^sub>2\<^sup>2 + x\<^sub>3\<^sup>2" unfolding N_def by blast
  then have no: "\<not> (\<exists>a' k'. N = 4 ^ a' * (8 * k' + 7))" using three_squares_iff[of N] by blast
  from N have "\<exists>a' k'. N = 4 ^ a' * (8 * k' + 7)" by blast
  with no show False by blast
qed

lemma seven_mod_8_rat:
  fixes x y z :: rat and c :: int
  assumes c: "c mod 8 = 7"
  shows "x^2 + y^2 + z^2 \<noteq> of_int c"
proof
  assume e: "x^2 + y^2 + z^2 = of_int c"
  obtain a b where x: "x = of_int a / of_int b" and b: "b \<noteq> 0"
    by (metis Fract_of_int_quotient Rat_cases less_irrefl)
  obtain a' b' where y: "y = of_int a' / of_int b'" and b': "b' \<noteq> 0"
    by (metis Fract_of_int_quotient Rat_cases less_irrefl)
  obtain a'' b'' where z: "z = of_int a'' / of_int b''" and b'': "b'' \<noteq> 0"
    by (metis Fract_of_int_quotient Rat_cases less_irrefl)
  let ?w = "b * b' * b''"
  have "(of_int (a * b' * b'')^2 + of_int (a' * b * b'')^2 + of_int (a'' * b * b')^2 :: rat)
      = of_int c * of_int ?w ^ 2"
    using e b b' b'' unfolding x y z
    by (simp add: field_simps power2_eq_square)
  then have "(a * b' * b'')^2 + (a' * b * b'')^2 + (a'' * b * b')^2 = c * ?w^2"
    by (metis (mono_tags) of_int_add of_int_eq_iff of_int_mult of_int_power)
  then have "?w = 0" using seven_mod_8_no_rational_three_squares[OF c] by blast
  with b b' b'' show False by simp
qed

subsection \<open>Rational Householder reflections\<close>

definition unit0 :: "nat \<Rightarrow> rat" where "unit0 i = (if i = 0 then 1 else 0)"

definition householder_refl :: "nat \<Rightarrow> (nat \<Rightarrow> rat) \<Rightarrow> (nat \<Rightarrow> rat) \<Rightarrow> (nat \<Rightarrow> rat)" where
  "householder_refl r u x = (\<lambda>i. x i - (2 * dot_upto r u x / dot_upto r u u) * u i)"

lemma dot_householder_refl:
  assumes "dot_upto r u u \<noteq> 0"
  shows "dot_upto r (householder_refl r u x) (householder_refl r u y) = dot_upto r x y"
proof -
  define D where "D = dot_upto r u u"
  define a where "a = dot_upto r u x"
  define b where "b = dot_upto r u y"
  define c where "c = 2 * a / D"
  define d where "d = 2 * b / D"
  have D0: "D \<noteq> 0" using assms by (simp add: D_def)
  have "dot_upto r (householder_refl r u x) (householder_refl r u y)
      = dot_upto r (householder_refl r u x) y - d * dot_upto r (householder_refl r u x) u"
    unfolding householder_refl_def[of r u y]
    using dot_on_diff_right[of "{..<r}" "householder_refl r u x" y d u]
    by (simp add: a_def b_def D_def d_def)
  also have "dot_upto r (householder_refl r u x) y = dot_upto r x y - c * b"
    unfolding householder_refl_def using dot_on_diff_left[of "{..<r}" x c u y]
    by (simp add: a_def b_def D_def c_def)
  also have "dot_upto r (householder_refl r u x) u = a - c * D"
    unfolding householder_refl_def using dot_on_diff_left[of "{..<r}" x c u u]
    by (simp add: a_def D_def c_def dot_on_comm[of "{..<r}" x u])
  finally have "dot_upto r (householder_refl r u x) (householder_refl r u y)
      = dot_upto r x y - c * b - d * (a - c * D)" .
  moreover have "c * b + d * (a - c * D) = 0"
    unfolding c_def d_def using D0 by (simp add: field_simps)
  ultimately show ?thesis by simp
qed

lemma dot_unit0_right: "dot_upto (Suc r) x unit0 = x 0"
  unfolding dot_on_def
  by (subst sum.lessThan_Suc_shift) (simp add: unit0_def)

lemma dot_unit0: "dot_upto (Suc r) unit0 unit0 = 1"
  using dot_unit0_right[of r unit0] by (simp add: unit0_def)

lemma householder:
  fixes x e :: "nat \<Rightarrow> rat"
  assumes "dot_upto r x x = 1" "dot_upto r e e = 1"
  shows "\<exists>R. (\<forall>y z. dot_upto r (R y) (R z) = dot_upto r y z) \<and> (\<forall>i<r. R x i = e i)"
proof (cases "\<forall>i<r. x i = e i")
  case True
  then show ?thesis
    by (intro exI[where x = "\<lambda>y. y"]) auto
next
  case False
  define u where "u = (\<lambda>i. x i - 1 * e i)"
  have uu: "dot_upto r u u \<noteq> 0"
  proof
    assume "dot_upto r u u = 0"
    then have "\<forall>i<r. u i = 0" using dot_upto_self_zero by blast
    then have "\<forall>i<r. x i = e i" by (simp add: u_def)
    with False show False by simp
  qed
  have dux: "dot_upto r u x = dot_upto r x x - 1 * dot_upto r e x"
    unfolding u_def by (rule dot_on_diff_left)
  have duu: "dot_upto r u u = dot_upto r x u - 1 * dot_upto r e u"
    unfolding u_def by (rule dot_on_diff_left)
  have dxu: "dot_upto r x u = dot_upto r x x - 1 * dot_upto r x e"
    unfolding u_def by (rule dot_on_diff_right)
  have deu: "dot_upto r e u = dot_upto r e x - 1 * dot_upto r e e"
    unfolding u_def by (rule dot_on_diff_right)
  have "dot_upto r u u = 2 - 2 * dot_upto r e x"
    using duu dxu deu assms by (simp add: dot_on_comm[of "{..<r}" e x])
  moreover have "dot_upto r u x = 1 - dot_upto r e x" using dux assms by simp
  ultimately have c1: "2 * dot_upto r u x / dot_upto r u u = 1" using uu by (simp add: field_simps)
  have rx: "\<forall>i<r. householder_refl r u x i = e i"
    using c1 unfolding householder_refl_def u_def by auto
  show ?thesis
    by (intro exI[where x = "householder_refl r u"]) (use dot_householder_refl[OF uu] rx in auto)
qed

subsection \<open>The embedding bound\<close>

lemma shift_dot:
  assumes "x 0 = 0"
  shows "dot_upto (Suc r) x y = dot_upto r (\<lambda>i. x (Suc i)) (\<lambda>i. y (Suc i))"
  unfolding dot_on_def
  by (subst sum.lessThan_Suc_shift) (simp add: assms)

lemma base_case:
  assumes "dot_upto r w w = (7::rat)"
  shows "4 \<le> r"
proof (rule ccontr)
  assume "\<not> 4 \<le> r"
  then have r3: "r \<le> 3" by simp
  obtain w' where w'_def: "w' = (\<lambda>i. if i < r then w i else 0)" by simp
  have "dot_upto r w w = (\<Sum>i<3. w' i * w' i)"
  proof -
    have "(\<Sum>i<r. w i * w i) = (\<Sum>i<r. w' i * w' i)"
      by (intro sum.cong refl) (simp add: w'_def)
    also have "\<dots> = (\<Sum>i<3. w' i * w' i)"
      by (rule sum.mono_neutral_left) (use r3 in \<open>auto simp: w'_def\<close>)
    finally show ?thesis by (simp add: dot_on_def)
  qed
  then have "w' 0 ^ 2 + w' (Suc 0) ^ 2 + w' (Suc (Suc 0)) ^ 2 = 7"
    using assms by (simp add: numeral_3_eq_3 power2_eq_square)
  moreover have "w' 0 ^ 2 + w' (Suc 0) ^ 2 + w' (Suc (Suc 0)) ^ 2 \<noteq> of_int 7"
    by (rule seven_mod_8_rat) simp
  ultimately show False by simp
qed

lemma embedding_aux:
  "\<forall>r v w. (\<forall>i<k. dot_upto r (v i) (v i) = (1::rat)) \<longrightarrow>
     (\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> dot_upto r (v i) (v j) = 0)
     \<longrightarrow> (\<forall>i<k. dot_upto r (v i) w = 0) \<longrightarrow> dot_upto r w w = 7 \<longrightarrow> k + 4 \<le> r"
proof (induction k)
  case 0
  then show ?case using base_case by auto
next
  case (Suc k)
  show ?case
  proof (intro allI impI)
    fix r v w
    assume n1: "\<forall>i<Suc k. dot_upto r (v i) (v i) = (1::rat)"
      and o1: "\<forall>i<Suc k. \<forall>j<Suc k. i \<noteq> j \<longrightarrow> dot_upto r (v i) (v j) = 0"
      and o2: "\<forall>i<Suc k. dot_upto r (v i) w = 0" and nw: "dot_upto r w w = 7"
    have r0: "r \<noteq> 0"
    proof
      assume "r = 0"
      then have "dot_upto r (v 0) (v 0) = 0" by (simp add: dot_on_def)
      with n1 show False by simp
    qed
    then obtain r' where r: "r = Suc r'" using r0 by (cases r) auto
    have v0: "dot_upto r (v 0) (v 0) = 1" using n1 by simp
    have e: "dot_upto r unit0 unit0 = 1" unfolding r by (rule dot_unit0)
    obtain R where R: "\<And>y z. dot_upto r (R y) (R z) = dot_upto r y z" "\<forall>i<r. R (v 0) i = unit0 i"
      using householder[OF v0 e] by blast
    obtain v' where v'_def: "v' = (\<lambda>j i. R (v (Suc j)) (Suc i))" by simp
    obtain w' where w'_def: "w' = (\<lambda>i. R w (Suc i))" by simp
    have z: "\<And>y. dot_upto r y (v 0) = 0 \<Longrightarrow> R y 0 = 0"
    proof -
      fix y assume "dot_upto r y (v 0) = 0"
      then have "dot_upto r (R y) (R (v 0)) = 0" using R(1)[of y "v 0"] by simp
      moreover have "dot_upto r (R y) (R (v 0)) = dot_upto r (R y) unit0"
        by (rule dot_on_cong_right) (use R(2) in simp)
      ultimately have "dot_upto r (R y) unit0 = 0" by simp
      then show "R y 0 = 0" unfolding r by (simp add: dot_unit0_right)
    qed
    have z1: "\<And>j. j < k \<Longrightarrow> R (v (Suc j)) 0 = 0"
    proof (rule z)
      fix j assume j: "j < k"
      show "dot_upto r (v (Suc j)) (v 0) = 0" using o1[rule_format, of "Suc j" 0] j by simp
    qed
    have zw: "R w 0 = 0" by (rule z) (use o2 dot_on_comm[of "{..<r}" w "v 0"] in auto)
    have "\<forall>i<k. dot_upto r' (v' i) (v' i) = 1"
    proof (intro allI impI)
      fix j assume j: "j < k"
      have "dot_upto r' (v' j) (v' j) = dot_upto r (R (v (Suc j))) (R (v (Suc j)))"
        unfolding v'_def r by (rule sym[OF shift_dot[where x = "R (v (Suc j))" and y = "R (v (Suc j))" and r = r', OF z1[OF j]]])
      also have "\<dots> = 1" using R(1) n1 j by simp
      finally show "dot_upto r' (v' j) (v' j) = 1" .
    qed
    moreover have "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> dot_upto r' (v' i) (v' j) = 0"
    proof (intro allI impI)
      fix i j assume i: "i < k" and j: "j < k" and ij: "i \<noteq> j"
      have "dot_upto r' (v' i) (v' j) = dot_upto r (R (v (Suc i))) (R (v (Suc j)))"
        unfolding v'_def r by (rule sym[OF shift_dot[where x = "R (v (Suc i))" and y = "R (v (Suc j))" and r = r', OF z1[OF i]]])
      also have "\<dots> = 0" using R(1) o1 i j ij by simp
      finally show "dot_upto r' (v' i) (v' j) = 0" .
    qed
    moreover have "\<forall>i<k. dot_upto r' (v' i) w' = 0"
    proof (intro allI impI)
      fix i assume i: "i < k"
      have "dot_upto r' (v' i) w' = dot_upto r (R (v (Suc i))) (R w)"
        unfolding v'_def w'_def r by (rule sym[OF shift_dot[where x = "R (v (Suc i))" and y = "R w" and r = r', OF z1[OF i]]])
      also have "\<dots> = 0" using R(1) o2 i by simp
      finally show "dot_upto r' (v' i) w' = 0" .
    qed
    moreover have "dot_upto r' w' w' = 7"
    proof -
      have "dot_upto r' w' w' = dot_upto r (R w) (R w)"
        unfolding w'_def r by (rule sym[OF shift_dot[where x = "R w" and y = "R w" and r = r', OF zw]])
      also have "\<dots> = 7" using R(1) nw by simp
      finally show ?thesis .
    qed
    ultimately have "k + 4 \<le> r'" using Suc.IH[rule_format, of r' v' w'] by blast
    then show "Suc k + 4 \<le> r" by (simp add: r)
  qed
qed

theorem seven_embedding:
  fixes v :: "nat \<Rightarrow> nat \<Rightarrow> rat" and w :: "nat \<Rightarrow> rat" and e r :: nat
  assumes e: "1 \<le> e"
    and n1: "\<And>i. i < e - 1 \<Longrightarrow> dot_upto r (v i) (v i) = 1"
    and o1: "\<And>i j. i < e - 1 \<Longrightarrow> j < e - 1 \<Longrightarrow> i \<noteq> j \<Longrightarrow> dot_upto r (v i) (v j) = 0"
    and o2: "\<And>i. i < e - 1 \<Longrightarrow> dot_upto r (v i) w = 0"
    and nw: "dot_upto r w w = 7"
  shows "e + 3 \<le> r"
proof -
  have H: "(\<forall>i<e - 1. dot_upto r (v i) (v i) = 1) \<longrightarrow>
      (\<forall>i<e - 1. \<forall>j<e - 1. i \<noteq> j \<longrightarrow> dot_upto r (v i) (v j) = 0) \<longrightarrow>
      (\<forall>i<e - 1. dot_upto r (v i) w = 0) \<longrightarrow> dot_upto r w w = 7 \<longrightarrow> e - 1 + 4 \<le> r"
    by (rule embedding_aux[of "e - 1", THEN spec, THEN spec, THEN spec])
  have "e - 1 + 4 \<le> r"
    by (rule H[rule_format]) (use n1 o1 o2 nw in blast)+
  then show ?thesis using e by simp
qed

text \<open>The smallest case: no three pairwise orthogonal vectors of squared norms $1, 1, 7$ in
  $\mathbb{Q}^5$. This is the diagonal form $x_1^2y_1^2 + x_2^2y_2^2 + 7x_3^2y_3^2$, which is a sum of
  three real squares and needs six rational ones.\<close>

corollary no_orthogonal_1_1_7:
  fixes v1 v2 w :: "nat \<Rightarrow> rat"
  assumes "dot_upto 5 v1 v1 = 1" "dot_upto 5 v2 v2 = 1" "dot_upto 5 v1 v2 = 0"
    "dot_upto 5 v1 w = 0" "dot_upto 5 v2 w = 0" "dot_upto 5 w w = 7"
  shows False
proof -
  define v where "v i = (if i = 0 then v1 else v2)" for i :: nat
  have "3 + 3 \<le> (5::nat)"
  proof (rule seven_embedding[where v = v and w = w])
    show "1 \<le> (3::nat)" by simp
    show "dot_upto 5 (v i) (v i) = 1" if "i < 3 - 1" for i
      using that assms by (auto simp: v_def)
    show "dot_upto 5 (v i) (v j) = 0" if "i < 3 - 1" "j < 3 - 1" "i \<noteq> j" for i j
      using that assms dot_on_comm[of "{..<5}" v1 v2] by (auto simp: v_def)
    show "dot_upto 5 (v i) w = 0" if "i < 3 - 1" for i
      using that assms by (auto simp: v_def)
    show "dot_upto 5 w w = 7" by (rule assms(6))
  qed
  then show False by simp
qed

end
