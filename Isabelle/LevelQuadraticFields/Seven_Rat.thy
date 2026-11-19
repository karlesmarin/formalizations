(*  Title:      Seven_Rat.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Levels of imaginary quadratic fields Q(sqrt(-a)) (-1 as a sum of 1, 2 or 4 squares, by a mod 8, over the AFP Three_Squares) and the fields of the dilation λ = 3/4 inside I_4, for rational sums-of-squares lengths of biquadratic forms; Pfister's "the level is never 3" enters as a named locale assumption
*)

   Auxiliary: an integer c = 7 (mod 8) is not a sum of three rational squares (descent, copied from
   Biquadratic_SOS_Length.Kn_Witness.seven_mod_8_rat so that this session does not depend on that one).
*)
theory Seven_Rat
  imports Complex_Main
begin

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

end
