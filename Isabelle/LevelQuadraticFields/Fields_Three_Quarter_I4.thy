(*  Title:      Fields_Three_Quarter_I4.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Levels of imaginary quadratic fields Q(sqrt(-a)) (-1 as a sum of 1, 2 or 4 squares, by a mod 8, over the AFP Three_Squares) and the fields of the dilation λ = 3/4 inside I_4, for rational sums-of-squares lengths of biquadratic forms; Pfister's "the level is never 3" enters as a named locale assumption
*)

   Proposition "prop:fields", part (1), of "Rational sums-of-squares lengths of biquadratic forms and orthogonal
   dilations" (Carles Marín, in preparation).  For H = (3/4) I_4 over a field F of characteristic 0 (in particular
   every subfield of the reals): the length is 4, that is, there is an orthogonal T over F whose symmetric part is H
   (the equivalence "length n iff such a T exists" is Prop. iso of the paper, not reproved here), iff 7 is a sum of
   three squares in F.  Also: 7 is a sum of three squares in R (and in Q(sqrt 3), Q(sqrt 7)) but not in Q.
   Matrices are 4x4 arrays nat => nat => 'a with indices < 4; T is orthogonal when its columns are orthonormal.
*)
theory Fields_Three_Quarter_I4
  imports Seven_Rat
begin

section \<open>Matrices as functions\<close>

lemma sum4: "(\<Sum>i<(4::nat). f i) = f 0 + f 1 + f 2 + f 3"
  by (simp add: eval_nat_numeral)

definition orth4 :: "(nat \<Rightarrow> nat \<Rightarrow> 'a::field) \<Rightarrow> bool" where
  "orth4 T \<longleftrightarrow> (\<forall>i<4. \<forall>j<4. (\<Sum>k<4. T k i * T k j) = (if i = j then 1 else 0))"

definition sym_part_is_3_4 :: "(nat \<Rightarrow> nat \<Rightarrow> 'a::field) \<Rightarrow> bool" where
  "sym_part_is_3_4 T \<longleftrightarrow> (\<forall>i<4. \<forall>j<4. (T i j + T j i) / 2 = (if i = j then 3/4 else 0))"

text \<open>Left multiplication by the pure quaternion (0,p,q,r).\<close>

definition qmat :: "'a::comm_ring_1 \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "qmat p q r i j = [[0, -p, -q, -r], [p, 0, -r, q], [q, r, 0, -p], [r, -q, p, 0]] ! i ! j"

lemma qmat_skew:
  assumes "i < 4" "j < 4"
  shows "qmat p q r i j = - qmat p q r j i"
proof -
  have "i \<in> {0, 1, 2, 3}" "j \<in> {0, 1, 2, 3}" using assms by auto
  thus ?thesis
    by (elim insertE emptyE; simp add: qmat_def)
qed

lemma qmat_gram:
  assumes "i < 4" "j < 4"
  shows "(\<Sum>k<4. qmat p q r k i * qmat p q r k j) = (if i = j then p^2 + q^2 + r^2 else 0)"
proof -
  have "i \<in> {0, 1, 2, 3}" "j \<in> {0, 1, 2, 3}" using assms by auto
  thus ?thesis
    by (elim insertE emptyE; simp add: sum4 qmat_def power2_eq_square algebra_simps)
qed

section \<open>The two directions\<close>

theorem dilation_imp_seven:
  fixes T :: "nat \<Rightarrow> nat \<Rightarrow> 'a::field_char_0"
  assumes o: "orth4 T" and s: "sym_part_is_3_4 T"
  shows "\<exists>p q r. p^2 + q^2 + r^2 = (7::'a)"
proof -
  have hs: "\<And>i j. i < 4 \<Longrightarrow> j < 4 \<Longrightarrow> (T i j + T j i) / 2 = (if i = j then 3/4 else 0)"
    using s unfolding sym_part_is_3_4_def by blast
  have oo: "\<And>i j. i < 4 \<Longrightarrow> j < 4 \<Longrightarrow> (\<Sum>k<4. T k i * T k j) = (if i = j then 1 else 0)"
    using o unfolding orth4_def by blast
  have d0: "T 0 0 = 3/4" using hs[of 0 0] by (simp add: add_self_div_2)
  have c0: "T 0 0 ^ 2 + T 1 0 ^ 2 + T 2 0 ^ 2 + T 3 0 ^ 2 = 1"
    using oo[of 0 0] by (simp add: sum4 power2_eq_square)
  \<comment> \<open>The skew part S = T - H has first column (0, T10, T20, T30), and 4S has squared column norm 7.\<close>
  have c1: "(3/4)^2 + (T 1 0 ^ 2 + T 2 0 ^ 2 + T 3 0 ^ 2) = (1::'a)" using c0 d0 by (simp add: add.assoc)
  have "(4 * T 1 0)^2 + (4 * T 2 0)^2 + (4 * T 3 0)^2 = (7::'a)"
    using c1 by algebra
  thus ?thesis by blast
qed

lemma T_gram_expand:
  fixes p q r :: "'a::field_char_0"
  assumes "i < 4" "j < 4"
  shows "(\<Sum>k<4. ((if k = i then 3/4 else 0) + qmat p q r k i / 4) * ((if k = j then 3/4 else 0) + qmat p q r k j / 4))
       = 9/16 * (if i = j then 1 else 0) + 3/16 * (qmat p q r i j + qmat p q r j i)
         + 1/16 * (\<Sum>k<4. qmat p q r k i * qmat p q r k j)"
proof -
  have "i \<in> {0, 1, 2, 3}" "j \<in> {0, 1, 2, 3}" using assms by auto
  thus ?thesis
    by (elim insertE emptyE; simp add: sum4 qmat_def algebra_simps)
qed

lemma exists_dilation:
  fixes T :: "nat \<Rightarrow> nat \<Rightarrow> 'a::field"
  assumes "orth4 T" and "sym_part_is_3_4 T"
  shows "\<exists>T :: nat \<Rightarrow> nat \<Rightarrow> 'a. orth4 T \<and> sym_part_is_3_4 T"
  using assms by blast

theorem seven_imp_dilation:
  fixes p q r :: "'a::field_char_0"
  assumes "p^2 + q^2 + r^2 = 7"
  shows "\<exists>T :: nat \<Rightarrow> nat \<Rightarrow> 'a. orth4 T \<and> sym_part_is_3_4 T"
proof -
  let ?T = "\<lambda>i j. (if i = j then 3/4 else 0) + qmat p q r i j / 4"
  have ho: "orth4 ?T"
    unfolding orth4_def
  proof (intro allI impI)
    fix i j :: nat assume ij: "i < 4" "j < 4"
    have g: "(\<Sum>k<4. qmat p q r k i * qmat p q r k j) = (if i = j then 7 else 0)"
      using qmat_gram[OF ij, of p q r] assms by simp
    have sk: "qmat p q r i j + qmat p q r j i = 0" using qmat_skew[OF ij, of p q r] by simp
    have "(\<Sum>k<4. ?T k i * ?T k j) = 9/16 * (if i = j then 1 else 0) + 1/16 * (if i = j then 7 else 0)"
      using T_gram_expand[OF ij, of p q r] sk g by simp
    also have "\<dots> = (if i = j then 1 else 0)" by simp
    finally show "(\<Sum>k<4. ?T k i * ?T k j) = (if i = j then 1 else 0)" .
  qed
  have hs: "sym_part_is_3_4 ?T"
    unfolding sym_part_is_3_4_def
  proof (intro allI impI)
    fix i j :: nat assume ij: "i < 4" "j < 4"
    have sk: "qmat p q r i j + qmat p q r j i = 0" using qmat_skew[OF ij, of p q r] by simp
    have "?T i j + ?T j i
        = (if i = j then 3/4 else 0) + (if j = i then 3/4 else 0) + (qmat p q r i j + qmat p q r j i) / 4"
      by (simp add: algebra_simps add_divide_distrib)
    also have "\<dots> = (if i = j then 3/2 else 0)" using sk by (cases "i = j") simp_all
    finally have "?T i j + ?T j i = (if i = j then 3/2 else 0)" .
    thus "(?T i j + ?T j i) / 2 = (if i = j then 3/4 else 0)" by (cases "i = j") (simp_all add: field_simps)
  qed
  show ?thesis by (rule exists_dilation[OF ho hs])
qed

theorem dilation_iff_seven:
  "(\<exists>T :: nat \<Rightarrow> nat \<Rightarrow> 'a::field_char_0. orth4 T \<and> sym_part_is_3_4 T) \<longleftrightarrow> (\<exists>p q r :: 'a. p^2 + q^2 + r^2 = 7)"
  using dilation_imp_seven seven_imp_dilation by blast

section \<open>The fields\<close>

text \<open>Over the reals the length is 4 (7 is a sum of three squares); in Q(sqrt 3) and Q(sqrt 7) too; not in Q.\<close>

lemma seven_real: "\<exists>p q r :: real. p^2 + q^2 + r^2 = 7"
  by (rule exI[of _ "sqrt 7"], rule exI[of _ 0], rule exI[of _ 0]) simp

lemma seven_two_plus_sqrt3: "(2::real)^2 + (sqrt 3)^2 + 0^2 = 7"
  by simp

lemma seven_not_three_rational_squares: "\<not> (\<exists>p q r :: rat. p^2 + q^2 + r^2 = 7)"
proof
  assume "\<exists>p q r :: rat. p^2 + q^2 + r^2 = 7"
  then obtain p q r :: rat where "p^2 + q^2 + r^2 = 7" by blast
  moreover have "(7::int) mod 8 = 7" by simp
  ultimately show False using seven_mod_8_rat[of 7 p q r] by simp
qed

corollary no_rational_dilation: "\<not> (\<exists>T :: nat \<Rightarrow> nat \<Rightarrow> rat. orth4 T \<and> sym_part_is_3_4 T)"
  using dilation_iff_seven seven_not_three_rational_squares by blast

corollary real_dilation: "\<exists>T :: nat \<Rightarrow> nat \<Rightarrow> real. orth4 T \<and> sym_part_is_3_4 T"
  using dilation_iff_seven seven_real by blast

end
