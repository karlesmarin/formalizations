(*  Title:      Kn_Witness.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

theory Kn_Witness
  imports Complex_Main
begin

section \<open>Exact witnesses for normalized complete graphs\<close>

text \<open>Exact witnesses for the rational length of the normalized complete graph
  $H_n = (J - I)/(n - 1)$. Each identity, divided by the square of the denominator, writes
  the biquadratic form as a sum of squares of bilinear forms.\<close>

text \<open>$H_5$: 8 squares with denominator 4.\<close>

lemma witness_H5:
  fixes x1 x2 y1 y2 y3 y4 y5 :: "'a::comm_ring_1"
  shows
    "(4 * x1 * y1 + x2 * ((-1) * y2 + 3 * y3 + 2 * y4))^2 +
    (4 * x1 * y2 + x2 * (3 * y1 + (-1) * y4 + 2 * y5))^2 +
    (4 * x1 * y3 + x2 * ((-1) * y1 + 2 * y2 + 1 * y4 + 2 * y5))^2 +
    (4 * x1 * y4 + x2 * (3 * y2 + 1 * y3))^2 +
    (4 * x1 * y5 + x2 * (2 * y1 + 2 * y4))^2 +
    (x2 * ((-1) * y1 + (-1) * y2 + 1 * y3 + (-1) * y4 + 2 * y5))^2 +
    (x2 * (1 * y1 + 1 * y2 + 1 * y3 + (-1) * y4 + (-2) * y5))^2 +
    (x2 * ((-2) * y3 + 2 * y4))^2 =
    16 * ((x1^2 + x2^2) * (y1^2 + y2^2 + y3^2 + y4^2 + y5^2)) + 16 * (x1 * x2 * (y1 * y2 + y1 * y3 + y1 * y4 + y1 * y5 + y2 * y3 + y2 * y4 + y2 * y5 + y3 * y4 + y3 * y5 + y4 * y5))"
  by (simp add: power2_eq_square algebra_simps)

text \<open>$H_7$: 12 squares with denominator 12.\<close>

lemma witness_H7:
  fixes x1 x2 y1 y2 y3 y4 y5 y6 y7 :: "'a::comm_ring_1"
  shows
    "(12 * x1 * y1 + x2 * (12 * y2))^2 +
    (12 * x1 * y2 + x2 * ((-8) * y1 + 4 * y3 + 4 * y4 + 4 * y5 + 4 * y6 + 4 * y7))^2 +
    (12 * x1 * y3 + x2 * (4 * y1 + 10 * y4 + 1 * y5 + 1 * y6 + (-4) * y7))^2 +
    (12 * x1 * y4 + x2 * (4 * y1 + (-6) * y3 + 3 * y5 + 3 * y6 + 8 * y7))^2 +
    (12 * x1 * y5 + x2 * (4 * y1 + 3 * y3 + 1 * y4 + 2 * y6 + 2 * y7))^2 +
    (12 * x1 * y6 + x2 * (4 * y1 + 3 * y3 + 1 * y4 + 2 * y5 + 2 * y7))^2 +
    (12 * x1 * y7 + x2 * (4 * y1 + 8 * y3 + (-4) * y4 + 2 * y5 + 2 * y6))^2 +
    (x2 * ((-5) * y5 + 5 * y6))^2 +
    (x2 * ((-2) * y5 + 2 * y6))^2 +
    (x2 * ((-1) * y5 + 1 * y6))^2 +
    (x2 * (1 * y3 + 1 * y4 + 4 * y5 + (-8) * y6 + 2 * y7))^2 +
    (x2 * (3 * y3 + 3 * y4 + (-8) * y5 + (-4) * y6 + 6 * y7))^2 =
    144 * ((x1^2 + x2^2) * (y1^2 + y2^2 + y3^2 + y4^2 + y5^2 + y6^2 + y7^2)) + 96 * (x1 * x2 * (y1 * y2 + y1 * y3 + y1 * y4 + y1 * y5 + y1 * y6 + y1 * y7 + y2 * y3 + y2 * y4 + y2 * y5 + y2 * y6 + y2 * y7 + y3 * y4 + y3 * y5 + y3 * y6 + y3 * y7 + y4 * y5 + y4 * y6 + y4 * y7 + y5 * y6 + y5 * y7 + y6 * y7))"
  by (simp add: power2_eq_square algebra_simps)

section \<open>Determinants of planes and three squares\<close>

text \<open>Determinants of planes, used in the lower bounds: a plane in $I_2$ has square determinant,
  and a plane in $I_4$ has a determinant that is a sum of three squares.\<close>

lemma plane_in_two_squares:
  fixes a b c d :: "'a::comm_ring_1"
  assumes "a * c + b * d = 0"
  shows "(a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2"
proof -
  have "(a^2 + b^2) * (c^2 + d^2) = (a * c + b * d)^2 + (a * d - b * c)^2"
    by (simp add: power2_eq_square algebra_simps)
  with assms show ?thesis by simp
qed

lemma plane_in_four_squares:
  fixes a b c d e f g h :: "'a::comm_ring_1"
  assumes "a * e + b * f + c * g + d * h = 0"
  shows "(a^2 + b^2 + c^2 + d^2) * (e^2 + f^2 + g^2 + h^2) =
    (a * f - b * e - c * h + d * g)^2 + (a * g + b * h - c * e - d * f)^2 + (a * h - b * g + c * f - d * e)^2"
proof -
  have "(a^2 + b^2 + c^2 + d^2) * (e^2 + f^2 + g^2 + h^2) = (a * e + b * f + c * g + d * h)^2 +
    (a * f - b * e - c * h + d * g)^2 + (a * g + b * h - c * e - d * f)^2 + (a * h - b * g + c * f - d * e)^2"
    by (simp add: power2_eq_square algebra_simps)
  with assms show ?thesis by simp
qed

text \<open>The arithmetic obstruction: an integer $c \equiv 7 \pmod 8$ is not a sum of three rational squares.
  Clearing denominators, $x^2 + y^2 + z^2 = c w^2$ forces $w = 0$, by descent.
  The integer case also follows from the entry Three\_Squares; the descent keeps this theory self-contained.\<close>

lemma mod8_aux: "(a::int) = 8 * t + 1 \<Longrightarrow> a mod 8 = 1" by presburger
lemma mod4_aux: "(a::int) = 4 * t + 1 \<Longrightarrow> a mod 4 = 1" by presburger
lemma add3_mod: "((a::int) + b + c) mod m = (a mod m + b mod m + c mod m) mod m"
proof -
  have 1: "(a + b + c) mod m = ((a + b) mod m + c mod m) mod m" by (rule mod_add_eq[symmetric])
  have 2: "(a mod m + b mod m + c mod m) mod m = ((a mod m + b mod m) mod m + c mod m) mod m"
    by (metis mod_add_eq mod_mod_trivial)
  have 3: "(a + b) mod m = (a mod m + b mod m) mod m" by (rule mod_add_eq[symmetric])
  from 1 2 3 show ?thesis by simp
qed

lemma square_mod_8:
  fixes x :: int
  shows "x^2 mod 8 \<in> {0, 1, 4}"
proof -
  have r: "x mod 8 \<in> {0, 1, 2, 3, 4, 5, 6, 7}" by auto
  have "x^2 mod 8 = (x mod 8)^2 mod 8" by (simp add: power_mod)
  with r show ?thesis by auto
qed

lemma odd_square_mod_8:
  fixes x :: int
  assumes "odd x"
  shows "x^2 mod 8 = 1"
proof -
  from assms obtain k where k: "x = 2 * k + 1" by (auto elim: oddE)
  have "even (k * (k + 1))" by simp
  then obtain j where j: "k * (k + 1) = 2 * j" by (rule evenE)
  have "x^2 = 4 * (k * (k + 1)) + 1" using k by (simp add: power2_eq_square algebra_simps)
  then have "x^2 = 8 * j + 1" using j by simp
  then show ?thesis using mod8_aux by blast
qed

lemma even_square_mod_4:
  fixes x :: int
  assumes "even x"
  shows "x^2 mod 4 = 0"
  using assms by (auto simp: power2_eq_square elim!: evenE)

lemma odd_square_mod_4:
  fixes x :: int
  assumes "odd x"
  shows "x^2 mod 4 = 1"
proof -
  from assms obtain k where "x = 2 * k + 1" by (auto elim: oddE)
  then have "x^2 = 4 * (k^2 + k) + 1" by (simp add: power2_eq_square algebra_simps)
  then show ?thesis using mod4_aux by blast
qed

lemma three_squares_not_7:
  fixes x y z :: int
  shows "(x^2 + y^2 + z^2) mod 8 \<noteq> 7"
proof -
  have e: "(x^2 + y^2 + z^2) mod 8 = (x^2 mod 8 + y^2 mod 8 + z^2 mod 8) mod 8"
    by (rule add3_mod)
  from square_mod_8[of x] square_mod_8[of y] square_mod_8[of z] show ?thesis
    unfolding e by auto
qed

lemma three_squares_mod_4:
  fixes x y z :: int
  assumes "(x^2 + y^2 + z^2) mod 4 = 0"
  shows "even x \<and> even y \<and> even z"
proof (rule ccontr)
  have e: "(x^2 + y^2 + z^2) mod 4 = (x^2 mod 4 + y^2 mod 4 + z^2 mod 4) mod 4"
    by (rule add3_mod)
  have sx: "x^2 mod 4 = (if even x then 0 else 1)" using even_square_mod_4 odd_square_mod_4 by simp
  have sy: "y^2 mod 4 = (if even y then 0 else 1)" using even_square_mod_4 odd_square_mod_4 by simp
  have sz: "z^2 mod 4 = (if even z then 0 else 1)" using even_square_mod_4 odd_square_mod_4 by simp
  assume "\<not> (even x \<and> even y \<and> even z)"
  with assms show False unfolding e sx sy sz by (auto split: if_splits)
qed

lemma seven_mod_8_no_rational_three_squares:
  fixes c :: int
  assumes c: "c mod 8 = 7"
  shows "x^2 + y^2 + z^2 = c * w^2 \<Longrightarrow> w = 0"
proof (induction "nat \<bar>w\<bar>" arbitrary: x y z w rule: less_induct)
  case less
  show ?case
  proof (cases "even w")
    case False
    have "(c * w^2) mod 8 = ((c mod 8) * (w^2 mod 8)) mod 8" by (rule mod_mult_eq[symmetric])
    also have "\<dots> = 7" using c odd_square_mod_8[OF False] by simp
    finally show ?thesis using less.prems three_squares_not_7[of x y z] by simp
  next
    case True
    then obtain v where w: "w = 2 * v" by (auto elim: evenE)
    have "(x^2 + y^2 + z^2) mod 4 = 0"
      using less.prems w by (simp add: power2_eq_square)
    then have "even x" "even y" "even z" using three_squares_mod_4 by auto
    then obtain a b d where x: "x = 2 * a" and y: "y = 2 * b" and z: "z = 2 * d" by (auto elim!: evenE)
    have "4 * (a^2 + b^2 + d^2) = 4 * (c * v^2)"
      using less.prems x y z w by (simp add: power2_eq_square algebra_simps)
    then have e: "a^2 + b^2 + d^2 = c * v^2" by simp
    show ?thesis
    proof (cases "v = 0")
      case True
      then show ?thesis using w by simp
    next
      case False
      then have "nat \<bar>v\<bar> < nat \<bar>w\<bar>" using w by auto
      from less.hyps[OF this e] False show ?thesis by simp
    qed
  qed
qed

text \<open>The same statement for rational numbers, and the identities behind the auxiliary space.\<close>

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

lemma two_squares_over_L:
  fixes n j :: "'a::field_char_0"
  assumes "j^2 = - (n * (n - 2))"
  shows "((n + j) / 2)^2 + ((n - j) / 2)^2 = n"
proof -
  have "((n + j) / 2)^2 + ((n - j) / 2)^2 = (n^2 + j^2) / 2"
    by (simp add: field_simps power2_eq_square)
  also have "\<dots> = n" using assms by (simp add: field_simps power2_eq_square)
  finally show ?thesis .
qed

text \<open>Quaternion multiplication by a pure quaternion: $x$ and $xz$ are orthogonal, and norms multiply.\<close>

lemma quaternion_pure_orthogonal:
  fixes a b c d p q r :: "'a::comm_ring_1"
  shows "a * (- b * p - c * q - d * r) + b * (a * p + c * r - d * q)
       + c * (a * q - b * r + d * p) + d * (a * r + b * q - c * p) = 0"
  by (simp add: algebra_simps)

lemma quaternion_pure_norm:
  fixes a b c d p q r :: "'a::comm_ring_1"
  shows "(- b * p - c * q - d * r)^2 + (a * p + c * r - d * q)^2
       + (a * q - b * r + d * p)^2 + (a * r + b * q - c * p)^2
       = (a^2 + b^2 + c^2 + d^2) * (p^2 + q^2 + r^2)"
  by (simp add: power2_eq_square algebra_simps)

end
