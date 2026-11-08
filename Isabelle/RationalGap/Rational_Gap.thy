(*  Title:      Rational_Gap.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

theory Rational_Gap
  imports Complex_Main
begin

text \<open>Exact witnesses and arithmetic obstructions for the rational length of biquadratic forms
  (the examples $G=\mathrm{diag}(\frac14,\frac14,\frac14,\frac14,-\frac12)$, the product
  $(x_1^2+x_2^2+3x_3^2)(y_1^2+y_2^2+y_3^2)$, and the monomial family with the coefficient $7$).
  The descent argument follows \texttt{seven\_mod\_8\_no\_rational\_three\_squares} of the theory
  Kn\_Witness (entry 140).\<close>

section \<open>Proposition G: twelve rational squares\<close>

text \<open>$T = G$. Five squares $x_1y_i + x_2 G_{ii} y_i$; the defect
  $\frac{15}{16}I_4 \perp \langle\frac34\rangle$ is written with the quaternion
  $q = \frac14(3,2,1,1)$ of norm $\frac{15}{16}$ (four squares) and
  $\frac34 y_5^2 = 3 (y_5/2)^2$ (three squares).\<close>

lemma witness_G:
  fixes x1 x2 y1 y2 y3 y4 y5 :: rat
  shows
    "(x1 * y1 + x2 * (y1 / 4))^2 + (x1 * y2 + x2 * (y2 / 4))^2 +
     (x1 * y3 + x2 * (y3 / 4))^2 + (x1 * y4 + x2 * (y4 / 4))^2 +
     (x1 * y5 - x2 * (y5 / 2))^2 +
     (x2 * ((3/4) * y1 - (1/2) * y2 - (1/4) * y3 - (1/4) * y4))^2 +
     (x2 * ((3/4) * y2 + (1/2) * y1 + (1/4) * y4 - (1/4) * y3))^2 +
     (x2 * ((3/4) * y3 - (1/2) * y4 + (1/4) * y1 + (1/4) * y2))^2 +
     (x2 * ((3/4) * y4 + (1/2) * y3 - (1/4) * y2 + (1/4) * y1))^2 +
     (x2 * (y5 / 2))^2 + (x2 * (y5 / 2))^2 + (x2 * (y5 / 2))^2 =
     (x1^2 + x2^2) * (y1^2 + y2^2 + y3^2 + y4^2 + y5^2) +
       2 * x1 * x2 * ((1/4) * y1^2 + (1/4) * y2^2 + (1/4) * y3^2 + (1/4) * y4^2 - (1/2) * y5^2)"
  by (simp add: power2_eq_square algebra_simps)

section \<open>Proposition product: four squares over Q(sqrt 3), eight over Q\<close>

lemma product_real_four_squares:
  fixes x1 x2 x3 y1 y2 y3 :: real
  shows
    "(- (x2 * y1 + sqrt 3 * x3 * y2))^2 + (x1 * y1 + sqrt 3 * x3 * y3)^2 +
     (x1 * y2 - x2 * y3)^2 + (x1 * y3 + x2 * y2 - sqrt 3 * x3 * y1)^2 =
     (x1^2 + x2^2 + 3 * x3^2) * (y1^2 + y2^2 + y3^2)"
proof -
  have s: "sqrt 3 * sqrt 3 = (3::real)" by simp
  have "(- (x2 * y1 + sqrt 3 * x3 * y2))^2 + (x1 * y1 + sqrt 3 * x3 * y3)^2 +
     (x1 * y2 - x2 * y3)^2 + (x1 * y3 + x2 * y2 - sqrt 3 * x3 * y1)^2 =
     (x1^2 + x2^2 + (sqrt 3 * sqrt 3) * x3^2) * (y1^2 + y2^2 + y3^2)"
    by (simp add: power2_eq_square algebra_simps)
  then show ?thesis using s by simp
qed

lemma product_rational_eight_squares:
  fixes x1 x2 x3 y1 y2 y3 :: rat
  shows
    "(- (x2 * y1))^2 + (x1 * y1)^2 + (x1 * y2 - x2 * y3)^2 + (x1 * y3 + x2 * y2)^2 +
     (- (x3 * (y1 + y2)))^2 + (x3 * (y1 + y3))^2 + (x3 * (y2 - y3))^2 + (x3 * (y2 + y3 - y1))^2 =
     (x1^2 + x2^2 + 3 * x3^2) * (y1^2 + y2^2 + y3^2)"
  by (simp add: power2_eq_square algebra_simps)

section \<open>3 is not a sum of two rational squares\<close>

lemma sq_mod_3:
  fixes x :: int
  shows "x^2 mod 3 = (if x mod 3 = 0 then 0 else 1)"
proof -
  have e: "x^2 mod 3 = (x mod 3)^2 mod 3" by (simp add: power_mod)
  have r: "x mod 3 = 0 \<or> x mod 3 = 1 \<or> x mod 3 = 2" by auto
  from r show ?thesis unfolding e by auto
qed

lemma two_squares_3_aux:
  fixes x y :: int
  assumes "(x^2 + y^2) mod 3 = 0"
  shows "x mod 3 = 0 \<and> y mod 3 = 0"
proof -
  have e: "(x^2 + y^2) mod 3 = (x^2 mod 3 + y^2 mod 3) mod 3" by (rule mod_add_eq[symmetric])
  from assms show ?thesis unfolding e sq_mod_3[of x] sq_mod_3[of y]
    by (auto split: if_splits)
qed

lemma three_no_two_squares_int:
  fixes x y w :: int
  shows "x^2 + y^2 = 3 * w^2 \<Longrightarrow> w = 0"
proof (induction "nat \<bar>w\<bar>" arbitrary: x y w rule: less_induct)
  case less
  have "(x^2 + y^2) mod 3 = 0" using less.prems by simp
  from two_squares_3_aux[OF this] have "3 dvd x" "3 dvd y" by auto
  then obtain a b where x: "x = 3 * a" and y: "y = 3 * b" by (auto elim!: dvdE)
  have "9 * (a^2 + b^2) = 3 * w^2" using less.prems x y by (simp add: power2_eq_square algebra_simps)
  then have wsq: "w^2 = 3 * (a^2 + b^2)" by simp
  then have "w^2 mod 3 = 0" by simp
  then have "w mod 3 = 0" using sq_mod_3[of w] by (auto split: if_splits)
  then have "3 dvd w" by (rule mod_0_imp_dvd)
  then obtain v where w: "w = 3 * v" by (rule dvdE)
  have e: "a^2 + b^2 = 3 * v^2" using wsq w by (simp add: power2_eq_square algebra_simps)
  show ?case
  proof (cases "v = 0")
    case True
    then show ?thesis using w by simp
  next
    case False
    then have "nat \<bar>v\<bar> < nat \<bar>w\<bar>" using w by auto
    from less.hyps[OF this e] False show ?thesis by simp
  qed
qed

lemma three_not_two_rational_squares:
  fixes a b :: rat
  shows "a^2 + b^2 \<noteq> 3"
proof
  assume e: "a^2 + b^2 = 3"
  obtain p q where a: "a = of_int p / of_int q" and q: "q \<noteq> 0"
    by (metis Fract_of_int_quotient Rat_cases less_irrefl)
  obtain p' q' where b: "b = of_int p' / of_int q'" and q': "q' \<noteq> 0"
    by (metis Fract_of_int_quotient Rat_cases less_irrefl)
  let ?w = "q * q'"
  have "(of_int (p * q')^2 + of_int (p' * q)^2 :: rat) = 3 * of_int ?w ^ 2"
    using e q q' unfolding a b by (simp add: field_simps power2_eq_square)
  then have "(p * q')^2 + (p' * q)^2 = 3 * ?w^2"
    by (metis (mono_tags) of_int_add of_int_eq_iff of_int_mult of_int_power of_int_numeral)
  then have "?w = 0" using three_no_two_squares_int by blast
  with q q' show False by simp
qed


text \<open>Copied from Kn_Witness (entry 140): the descent for 7 mod 8.\<close>
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

section \<open>Monomial family, case $k = 3$: no orthogonal vectors of norms $1, 1, 7$ in $\mathbb{Q}^5$\<close>

text \<open>The diagonal embedding behind $\ell_\mathbb{Q}(x_1^2y_1^2 + x_2^2y_2^2 + 7x_3^2y_3^2) = 3 + 3$:
  three pairwise orthogonal vectors of squared norms $1,1,7$ in $\mathbb{Q}^5$ would give, after two
  rational Householder reflections that send the first two to $e_0, e_1$, a vector of norm $7$
  in the last three coordinates, hence $7$ as a sum of three rational squares.\<close>

datatype v5 = V rat rat rat rat rat

fun dot :: "v5 \<Rightarrow> v5 \<Rightarrow> rat" where
  "dot (V a b c d e) (V a' b' c' d' e') = a * a' + b * b' + c * c' + d * d' + e * e'"

fun axpy :: "v5 \<Rightarrow> rat \<Rightarrow> v5 \<Rightarrow> v5" where
  "axpy (V a b c d e) t (V a' b' c' d' e') =
     V (a - t * a') (b - t * b') (c - t * c') (d - t * d') (e - t * e')"

definition refl :: "v5 \<Rightarrow> v5 \<Rightarrow> v5" where
  "refl u x = axpy x (2 * dot u x / dot u u) u"

definition E0 :: v5 where "E0 = V 1 0 0 0 0"
definition E1 :: v5 where "E1 = V 0 1 0 0 0"

lemma dot_comm: "dot x y = dot y x"
  by (cases x; cases y; simp add: algebra_simps)

lemma dot_axpy:
  "dot (axpy x c u) (axpy y d u) = dot x y - c * dot u y - d * dot x u + c * d * dot u u"
  by (cases x; cases y; cases u; simp add: algebra_simps)

lemma dot_refl:
  assumes "dot u u \<noteq> 0"
  shows "dot (refl u x) (refl u y) = dot x y"
proof -
  define c where "c = 2 * dot u x / dot u u"
  define d where "d = 2 * dot u y / dot u u"
  have r: "refl u x = axpy x c u" "refl u y = axpy y d u" by (simp_all add: refl_def c_def d_def)
  have cu: "c * dot u u = 2 * dot u x" using assms by (simp add: c_def)
  have du: "d * dot u u = 2 * dot u y" using assms by (simp add: d_def)
  have cd: "c * dot u y = d * dot x u"
  proof -
    have "(c * dot u y) * dot u u = (d * dot x u) * dot u u"
    proof -
      have "(c * dot u y) * dot u u = (c * dot u u) * dot u y" by simp
      also have "\<dots> = 2 * dot u x * dot u y" using cu by simp
      also have "\<dots> = (d * dot u u) * dot u x" using du by simp
      finally show ?thesis by (simp add: dot_comm[of x u])
    qed
    with assms show ?thesis by simp
  qed
  have e1: "c * d * dot u u = 2 * d * dot x u"
  proof -
    have "c * d * dot u u = d * (c * dot u u)" by simp
    also have "\<dots> = d * (2 * dot u x)" using cu by simp
    finally show ?thesis by (simp add: dot_comm[of u x])
  qed
  show ?thesis unfolding r dot_axpy using cd e1 by simp
qed

lemma dot_self_zero:
  assumes "dot u u = 0"
  shows "u = V 0 0 0 0 0"
proof (cases u)
  case (V a b c d e)
  with assms have h: "a * a + b * b + c * c + d * d + e * e = 0" by simp
  have na: "0 \<le> a * a" "0 \<le> b * b" "0 \<le> c * c" "0 \<le> d * d" "0 \<le> e * e"
    by (rule zero_le_square)+
  have "a * a = 0" "b * b = 0" "c * c = 0" "d * d = 0" "e * e = 0"
    using na h by linarith+
  then show ?thesis using V by simp
qed

lemma refl_fix:
  assumes "dot u E0 = 0"
  shows "refl u E0 = E0"
  using assms by (cases u) (simp add: refl_def E0_def)

lemma householder:
  assumes "dot x x = 1" "dot e e = 1"
  shows "\<exists>R. (\<forall>y z. dot (R y) (R z) = dot y z) \<and> R x = e \<and>
         (dot x E0 = 0 \<longrightarrow> dot e E0 = 0 \<longrightarrow> R E0 = E0)"
proof (cases "x = e")
  case True
  then show ?thesis by (intro exI[where x = "\<lambda>y. y"]) auto
next
  case False
  define u where "u = axpy x 1 e"
  have uu: "dot u u \<noteq> 0"
  proof
    assume "dot u u = 0"
    then have "u = V 0 0 0 0 0" by (rule dot_self_zero)
    then have "x = e" unfolding u_def by (cases x; cases e; simp)
    with False show False by simp
  qed
  have "2 * dot u x - dot u u = dot x x - dot e e"
    unfolding u_def by (cases x; cases e; simp add: algebra_simps)
  then have ux: "2 * dot u x = dot u u" using assms by simp
  have c1: "2 * dot u x / dot u u = 1" using ux uu by simp
  have r1: "refl u x = axpy x 1 u" by (simp only: refl_def c1)
  have r2: "axpy x 1 u = e" unfolding u_def by (cases x; cases e; simp)
  have rx: "refl u x = e" using r1 r2 by simp
  have fixE: "dot x E0 = 0 \<Longrightarrow> dot e E0 = 0 \<Longrightarrow> refl u E0 = E0"
  proof -
    assume "dot x E0 = 0" "dot e E0 = 0"
    then have "dot u E0 = 0" unfolding u_def E0_def by (cases x; cases e; simp)
    then show "refl u E0 = E0" by (rule refl_fix)
  qed
  show ?thesis
    by (intro exI[where x = "refl u"]) (use dot_refl[OF uu] rx fixE in auto)
qed

lemma no_orthogonal_1_1_7:
  assumes "dot v1 v1 = 1" "dot v2 v2 = 1" "dot v1 v2 = 0" "dot v1 w = 0" "dot v2 w = 0"
    "dot w w = 7"
  shows False
proof -
  have E00: "dot E0 E0 = 1" and E11: "dot E1 E1 = 1" and E10: "dot E1 E0 = 0"
    by (simp_all add: E0_def E1_def)
  obtain R1 where R1: "\<And>y z. dot (R1 y) (R1 z) = dot y z" "R1 v1 = E0"
    using householder[OF assms(1) E00] by blast
  define v2' where "v2' = R1 v2"
  have a1: "dot v2' v2' = 1" using R1(1) assms(2) by (simp add: v2'_def)
  have a2: "dot v2' E0 = 0"
    using R1(1)[of v2 v1] R1(2) assms(3) dot_comm[of v2 v1] by (simp add: v2'_def)
  obtain R2 where R2: "\<And>y z. dot (R2 y) (R2 z) = dot y z" "R2 v2' = E1"
    "dot v2' E0 = 0 \<longrightarrow> dot E1 E0 = 0 \<longrightarrow> R2 E0 = E0"
    using householder[OF a1 E11] by blast
  have fixE0: "R2 E0 = E0" using R2(3) a2 E10 by simp
  define w2 where "w2 = R2 (R1 w)"
  have d0: "dot w2 E0 = 0"
  proof -
    have "dot (R2 (R1 w)) (R2 (R1 v1)) = dot w v1" using R1(1) R2(1) by simp
    then show ?thesis using R1(2) fixE0 assms(4) dot_comm[of w v1] by (simp add: w2_def)
  qed
  have d1: "dot w2 E1 = 0"
  proof -
    have "dot (R2 (R1 w)) (R2 (R1 v2)) = dot w v2" using R1(1) R2(1) by simp
    then show ?thesis using R2(2) assms(5) dot_comm[of w v2] by (simp add: w2_def v2'_def)
  qed
  have dn: "dot w2 w2 = 7" using R1(1) R2(1) assms(6) by (simp add: w2_def)
  obtain a b c d e where w2: "w2 = V a b c d e" by (cases w2)
  with d0 d1 have "a = 0" "b = 0" by (simp_all add: E0_def E1_def)
  with dn w2 have "c^2 + d^2 + e^2 = 7" by (simp add: power2_eq_square)
  moreover have "c^2 + d^2 + e^2 \<noteq> of_int 7"
    by (rule seven_mod_8_rat) simp
  ultimately show False by simp
qed

end
