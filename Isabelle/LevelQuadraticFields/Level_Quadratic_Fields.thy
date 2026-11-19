(*  Title:      Level_Quadratic_Fields.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Levels of imaginary quadratic fields Q(sqrt(-a)) (-1 as a sum of 1, 2 or 4 squares, by a mod 8, over the AFP Three_Squares) and the fields of the dilation λ = 3/4 inside I_4, for rational sums-of-squares lengths of biquadratic forms; Pfister's "the level is never 3" enters as a named locale assumption
*)

   The level of L = Q(sqrt(-a)), Lemma "lem:level" of "Rational sums-of-squares lengths of biquadratic forms and
   orthogonal dilations" (Carles Marín, in preparation).
   L is modelled concretely: an element is a pair (x,y) of rationals, standing for x + y w with w^2 = -a, and
   the square of (x,y) is (x^2 - a y^2, 2 x y).  The level s(L) is the least k such that -1 is a sum of k squares.
   Proved: s = 1 iff a = 1 (a squarefree); -1 is a sum of two squares of L iff a is a sum of three rational squares;
   hence s = 2 for a squarefree, a <> 1, a mod 8 <> 7 (uses Legendre's three squares theorem of the AFP entry
   Three_Squares); s <= 4 always (four squares); a mod 8 = 7 gives s > 2 (Seven_Rat).
   s = 4 for a mod 8 = 7 additionally uses Pfister's theorem that a level is never 3, a named assumption
   of the locale pfister_no_three (Lam, Ch. XI); it is not proved here.
*)
theory Level_Quadratic_Fields
  imports Three_Squares.Three_Squares Seven_Rat
begin

section \<open>The level of Q(sqrt(-a)), concretely\<close>

definition sqL :: "rat \<Rightarrow> rat \<times> rat \<Rightarrow> rat \<times> rat" where
  "sqL a z = (fst z ^ 2 - a * snd z ^ 2, 2 * fst z * snd z)"

definition neg1_sos :: "rat \<Rightarrow> nat \<Rightarrow> bool" where
  "neg1_sos a k \<longleftrightarrow> (\<exists>z :: nat \<Rightarrow> rat \<times> rat.
      (\<Sum>i<k. fst (sqL a (z i))) = -1 \<and> (\<Sum>i<k. snd (sqL a (z i))) = 0)"

definition level :: "rat \<Rightarrow> nat" where
  "level a = (LEAST k. neg1_sos a k)"

lemma sum2: "(\<Sum>i<(2::nat). f i) = f 0 + f 1"
  by (simp add: eval_nat_numeral)

lemma sum4: "(\<Sum>i<(4::nat). f i) = f 0 + f 1 + f 2 + f 3"
  by (simp add: eval_nat_numeral)

lemma neg1_sos_orth:
  "neg1_sos a k \<longleftrightarrow> (\<exists>x y :: nat \<Rightarrow> rat.
      (\<Sum>i<k. (x i)^2) + 1 = a * (\<Sum>i<k. (y i)^2) \<and> (\<Sum>i<k. x i * y i) = 0)"
proof
  assume "neg1_sos a k"
  then obtain z where z1: "(\<Sum>i<k. fst (sqL a (z i))) = -1" and z2: "(\<Sum>i<k. snd (sqL a (z i))) = 0"
    unfolding neg1_sos_def by blast
  have e1: "(\<Sum>i<k. fst (sqL a (z i))) = (\<Sum>i<k. (fst (z i))^2) - a * (\<Sum>i<k. (snd (z i))^2)"
    by (simp add: sqL_def sum_subtractf sum_distrib_left)
  have e2: "(\<Sum>i<k. snd (sqL a (z i))) = 2 * (\<Sum>i<k. fst (z i) * snd (z i))"
    by (simp add: sqL_def sum_distrib_left mult.assoc)
  show "\<exists>x y :: nat \<Rightarrow> rat. (\<Sum>i<k. (x i)^2) + 1 = a * (\<Sum>i<k. (y i)^2) \<and> (\<Sum>i<k. x i * y i) = 0"
    by (rule exI[of _ "\<lambda>i. fst (z i)"], rule exI[of _ "\<lambda>i. snd (z i)"]) (use z1 z2 e1 e2 in auto)
next
  assume "\<exists>x y :: nat \<Rightarrow> rat. (\<Sum>i<k. (x i)^2) + 1 = a * (\<Sum>i<k. (y i)^2) \<and> (\<Sum>i<k. x i * y i) = 0"
  then obtain x y where h1: "(\<Sum>i<k. (x i)^2) + 1 = a * (\<Sum>i<k. (y i)^2)" and h2: "(\<Sum>i<k. x i * y i) = 0"
    by blast
  have e1: "(\<Sum>i<k. fst (sqL a (x i, y i))) = (\<Sum>i<k. (x i)^2) - a * (\<Sum>i<k. (y i)^2)"
    by (simp add: sqL_def sum_subtractf sum_distrib_left)
  have e2: "(\<Sum>i<k. snd (sqL a (x i, y i))) = 2 * (\<Sum>i<k. x i * y i)"
    by (simp add: sqL_def sum_distrib_left mult.assoc)
  show "neg1_sos a k"
    unfolding neg1_sos_def by (rule exI[of _ "\<lambda>i. (x i, y i)"]) (use h1 h2 e1 e2 in auto)
qed

lemma not_neg1_sos_0: "\<not> neg1_sos a 0"
  by (simp add: neg1_sos_def)

lemma neg1_sos_Suc: "neg1_sos a k \<Longrightarrow> neg1_sos a (Suc k)"
proof -
  assume "neg1_sos a k"
  then obtain x y :: "nat \<Rightarrow> rat" where h1: "(\<Sum>i<k. (x i)^2) + 1 = a * (\<Sum>i<k. (y i)^2)"
    and h2: "(\<Sum>i<k. x i * y i) = 0" unfolding neg1_sos_orth by blast
  show "neg1_sos a (Suc k)" unfolding neg1_sos_orth
    by (rule exI[of _ "x(k := 0)"], rule exI[of _ "y(k := 0)"]) (use h1 h2 in \<open>simp add: sum.lessThan_Suc\<close>)
qed

section \<open>s = 1 iff a = 1\<close>

lemma neg1_sos_one_square:
  assumes "neg1_sos a 1"
  shows "\<exists>y :: rat. a * y^2 = 1"
proof -
  obtain x y :: "nat \<Rightarrow> rat" where h1: "x 0 ^ 2 + 1 = a * y 0 ^ 2" and h2: "x 0 * y 0 = 0"
    using assms unfolding neg1_sos_orth by auto
  show ?thesis
  proof (cases "x 0 = 0")
    case True
    then show ?thesis using h1 by (intro exI[of _ "y 0"]) simp
  next
    case False
    with h2 have "y 0 = 0" by simp
    with h1 have "x 0 ^ 2 + 1 = 0" by simp
    moreover have "x 0 ^ 2 + 1 > 0" by (simp add: add_nonneg_pos)
    ultimately show ?thesis by simp
  qed
qed

lemma squarefree_rat_square_is_one:
  fixes a :: nat
  assumes sq: "squarefree a" and y: "(of_nat a :: rat) * y^2 = 1"
  shows "a = 1"
proof -
  obtain p q where yq: "y = Rat.Fract p q" and qpos: "q > 0" and cop: "coprime p q"
    by (cases y rule: Rat_cases) auto
  have y': "y = of_int p / of_int q" by (simp add: yq Fract_of_int_quotient)
  have q0: "(of_int q :: rat) \<noteq> 0" using qpos by simp
  have eq: "(of_int (int a * p^2) :: rat) = of_int (q^2)"
    using y y' q0 by (simp add: field_simps power2_eq_square)
  have e: "int a * p^2 = q^2" by (rule of_int_eq_iff[THEN iffD1, OF eq])
  have d1: "p^2 dvd q^2" unfolding e[symmetric] by simp
  have c2: "coprime (p^2) (q^2)" using cop by simp
  have "is_unit (p^2)" by (rule coprime_common_divisor[OF c2 dvd_refl d1])
  hence du: "p^2 dvd 1" by (rule unit_imp_dvd)
  have ple: "p^2 \<le> 1" using zdvd_imp_le[OF du] by simp
  have "p \<noteq> 0" using du by auto
  hence "p^2 > 0" by simp
  hence "p^2 = 1" using ple by linarith
  with e have e2: "int a = q^2" by simp
  have "a = nat q * nat q"
  proof -
    have "int a = int (nat q * nat q)" using qpos e2 by (simp add: power2_eq_square)
    thus ?thesis by (rule iffD1[OF of_nat_eq_iff])
  qed
  have "is_unit (nat q)" by (rule squarefreeD[OF sq]) (simp add: power2_eq_square \<open>a = nat q * nat q\<close>)
  hence "nat q dvd 1" by (rule unit_imp_dvd)
  hence "nat q = 1" by simp
  thus ?thesis using \<open>a = nat q * nat q\<close> by simp
qed

lemma neg1_sos_one_iff:
  fixes a :: nat
  assumes "squarefree a"
  shows "neg1_sos (of_nat a) 1 \<longleftrightarrow> a = 1"
proof
  assume "neg1_sos (of_nat a) 1"
  then obtain y where "(of_nat a :: rat) * y^2 = 1" using neg1_sos_one_square by blast
  from squarefree_rat_square_is_one[OF assms this] show "a = 1" .
next
  assume "a = 1"
  show "neg1_sos (of_nat a) 1" unfolding neg1_sos_orth \<open>a = 1\<close>
    by (rule exI[of _ "\<lambda>_. 0"], rule exI[of _ "\<lambda>_. 1"]) simp
qed

section \<open>Two squares of L: a is a sum of three rational squares\<close>

lemma inv_split:
  fixes u v m :: rat
  assumes "m > 0" and "u^2 + v^2 = m"
  shows "(u / m)^2 + (v / m)^2 = 1 / m"
proof -
  have m0: "m \<noteq> 0" using assms(1) by simp
  show ?thesis
    using assms(2) m0 by (simp add: power_divide add_divide_distrib[symmetric] field_simps power2_eq_square)
qed

lemma alg_core:
  fixes a X d m y0 y1 :: rat
  assumes "m > 0" and "y0^2 + y1^2 = m" and "X + 1 = a * m" and "d^2 = X * m"
  shows "a = (d / m)^2 + (y0 / m)^2 + (y1 / m)^2"
proof -
  have m0: "m \<noteq> 0" using assms(1) by simp
  have 1: "(d / m)^2 = X / m" using assms(4) m0 by (simp add: power_divide field_simps power2_eq_square)
  have 2: "(y0 / m)^2 + (y1 / m)^2 = 1 / m"
    using assms(2) m0 by (simp add: power_divide add_divide_distrib[symmetric] field_simps power2_eq_square)
  have 3: "a = (X + 1) / m" using assms(3) m0 by (simp add: eq_divide_eq)
  show ?thesis using 1 2 3 by (simp add: add_divide_distrib)
qed

lemma two_squares_imp_three:
  fixes a :: rat
  assumes "neg1_sos a 2"
  shows "\<exists>p q r :: rat. p^2 + q^2 + r^2 = a"
proof -
  obtain x y :: "nat \<Rightarrow> rat" where h1: "x 0 ^ 2 + x 1 ^ 2 + 1 = a * (y 0 ^ 2 + y 1 ^ 2)"
    and h2: "x 0 * y 0 + x 1 * y 1 = 0"
    using assms unfolding neg1_sos_orth by (auto simp: sum2)
  obtain m where m: "m = y 0 ^ 2 + y 1 ^ 2" by simp
  have pos: "m > 0"
  proof (rule ccontr)
    assume "\<not> m > 0"
    hence "m = 0" using m zero_le_power2[of "y 0"] zero_le_power2[of "y 1"] by linarith
    hence "x 0 ^ 2 + x 1 ^ 2 + 1 = 0" using h1 m by simp
    moreover have "x 0 ^ 2 + x 1 ^ 2 + 1 > 0" by (simp add: add_nonneg_pos)
    ultimately show False by simp
  qed
  obtain d where d: "d = x 0 * y 1 - x 1 * y 0" by simp
  have lag: "(x 0 ^ 2 + x 1 ^ 2) * m = (x 0 * y 0 + x 1 * y 1)^2 + d^2"
    unfolding m d by (simp add: power2_eq_square algebra_simps)
  with h2 have lag2: "d^2 = (x 0 ^ 2 + x 1 ^ 2) * m" by simp
  have "a = (d / m)^2 + (y 0 / m)^2 + (y 1 / m)^2"
    by (rule alg_core[OF pos _ _ lag2]) (use m h1 in auto)
  thus ?thesis by blast
qed

lemma aux_two_squares:
  fixes a t u v :: rat
  assumes "a * t^2 = 1 + u^2 + v^2"
  shows "neg1_sos a 2"
proof (cases "u^2 + v^2 = 0")
  case True
  have "neg1_sos a 1" unfolding neg1_sos_orth
    by (rule exI[of _ "\<lambda>_. 0"], rule exI[of _ "\<lambda>_. t"]) (use assms True in simp)
  thus ?thesis using neg1_sos_Suc[of a 1, unfolded Suc_1] by blast
next
  case False
  obtain m where m: "m = u^2 + v^2" by simp
  have pos: "m > 0" using False m zero_le_power2[of u] zero_le_power2[of v] by linarith
  have m0: "m \<noteq> 0" using pos by simp
  have a1: "a * t^2 = 1 + m" using assms m by simp
  have isq: "(u / m)^2 + (v / m)^2 = 1 / m" by (rule inv_split[OF pos m[symmetric]])
  have "a * ((t * v / m)^2 + (t * u / m)^2) = (1 + m) / m"
  proof -
    have "(t * v / m)^2 + (t * u / m)^2 = t^2 * ((u / m)^2 + (v / m)^2)"
      by (simp add: power_divide power_mult_distrib algebra_simps)
    also have "\<dots> = t^2 / m" using isq by simp
    finally have "a * ((t * v / m)^2 + (t * u / m)^2) = a * t^2 / m" by (simp add: mult.assoc)
    thus ?thesis using a1 by simp
  qed
  moreover have "(1 + m) / m = 1 / m + 1" using m0 by (simp add: field_simps)
  ultimately have key: "a * ((t * v / m)^2 + (t * u / m)^2) = 1 / m + 1" by simp
  show ?thesis unfolding neg1_sos_orth
  proof (rule exI[of _ "\<lambda>i. if i = 0 then u / m else v / m"],
         rule exI[of _ "\<lambda>i. if i = 0 then - (t * v / m) else t * u / m"])
    show "(\<Sum>i<(2::nat). ((if i = 0 then u / m else v / m))^2) + 1
        = a * (\<Sum>i<(2::nat). ((if i = 0 then - (t * v / m) else t * u / m))^2) \<and>
        (\<Sum>i<(2::nat). (if i = 0 then u / m else v / m) * (if i = 0 then - (t * v / m) else t * u / m)) = 0"
    proof (intro conjI)
      show "(\<Sum>i<(2::nat). ((if i = 0 then u / m else v / m))^2) + 1
          = a * (\<Sum>i<(2::nat). ((if i = 0 then - (t * v / m) else t * u / m))^2)"
        using isq key by (simp add: sum2 power2_minus)
      show "(\<Sum>i<(2::nat). (if i = 0 then u / m else v / m) * (if i = 0 then - (t * v / m) else t * u / m)) = 0"
        by (simp add: sum2 field_simps)
    qed
  qed
qed

lemma three_squares_imp_two:
  fixes a :: rat
  assumes "p^2 + q^2 + r^2 = a" and "a > 0"
  shows "neg1_sos a 2"
proof -
  have key: "\<And>c1 c2 c3 :: rat. c1 \<noteq> 0 \<Longrightarrow> c1^2 + c2^2 + c3^2 = a \<Longrightarrow> neg1_sos a 2"
  proof -
    fix c1 c2 c3 :: rat
    assume c1: "c1 \<noteq> 0" and e: "c1^2 + c2^2 + c3^2 = a"
    have "a * (1 / c1)^2 = 1 + (c2 / c1)^2 + (c3 / c1)^2"
      using c1 e by (simp add: field_simps power2_eq_square)
    thus "neg1_sos a 2" by (rule aux_two_squares)
  qed
  show ?thesis
  proof (cases "p = 0")
    case False
    thus ?thesis using key assms by blast
  next
    case True
    show ?thesis
    proof (cases "q = 0")
      case False
      thus ?thesis using key[of q p r] assms by (simp add: ac_simps)
    next
      case True
      have "r \<noteq> 0" using assms \<open>p = 0\<close> True by auto
      thus ?thesis using key[of r p q] assms by (simp add: ac_simps)
    qed
  qed
qed

theorem two_squares_iff_three_rational:
  fixes a :: rat
  assumes "a > 0"
  shows "neg1_sos a 2 \<longleftrightarrow> (\<exists>p q r :: rat. p^2 + q^2 + r^2 = a)"
  using two_squares_imp_three three_squares_imp_two assms by blast

section \<open>Arithmetic of a: Legendre and mod 8\<close>

lemma squarefree_not_4_power:
  fixes a :: nat
  assumes "squarefree a" and "a mod 8 \<noteq> 7"
  shows "\<nexists>e k. a = 4 ^ e * (8 * k + 7)"
proof
  assume "\<exists>e k. a = 4 ^ e * (8 * k + 7)"
  then obtain e k where ek: "a = 4 ^ e * (8 * k + 7)" by blast
  show False
  proof (cases e)
    case 0
    with ek have "a mod 8 = 7" by simp
    with assms show False by simp
  next
    case (Suc e')
    hence d22: "(2::nat)^2 dvd a" using ek by simp
    have "is_unit (2::nat)" by (rule squarefreeD[OF assms(1) d22])
    hence "(2::nat) dvd 1" by (rule unit_imp_dvd)
    thus False by presburger
  qed
qed

lemma level_le_two:
  fixes a :: nat
  assumes "squarefree a" and "a mod 8 \<noteq> 7" and "a > 0"
  shows "neg1_sos (of_nat a) 2"
proof -
  have "\<exists>x1 x2 x3. a = x1^2 + x2^2 + x3^2"
    using three_squares_iff[of a] squarefree_not_4_power[OF assms(1,2)] by blast
  then obtain x1 x2 x3 :: nat where "a = x1^2 + x2^2 + x3^2" by blast
  hence "(of_nat x1 :: rat)^2 + (of_nat x2)^2 + (of_nat x3)^2 = of_nat a" by simp
  thus ?thesis by (rule three_squares_imp_two) (use assms(3) in simp)
qed

lemma not_two_when_7_mod_8:
  fixes a :: nat
  assumes "a mod 8 = 7"
  shows "\<not> neg1_sos (of_nat a) 2"
proof
  assume "neg1_sos (of_nat a :: rat) 2"
  then obtain p q r :: rat where "p^2 + q^2 + r^2 = of_nat a" using two_squares_imp_three by blast
  moreover have "(int a) mod 8 = 7" using assms by (metis zmod_int of_nat_numeral of_nat_eq_iff)
  ultimately show False using seven_mod_8_rat[of "int a" p q r] by simp
qed

section \<open>Four squares of L always\<close>

lemma neg1_sos_four:
  fixes a :: nat
  assumes "a > 0"
  shows "neg1_sos (of_nat a) 4"
proof -
  obtain c1 c2 c3 c4 :: nat where c: "a = c1^2 + c2^2 + c3^2 + c4^2" using four_squares by blast
  hence cq: "(of_nat c1 :: rat)^2 + (of_nat c2)^2 + (of_nat c3)^2 + (of_nat c4)^2 = of_nat a" by simp
  have a0: "(of_nat a :: rat) \<noteq> 0" using assms by simp
  let ?z = "\<lambda>i::nat. (0::rat, (case i of 0 \<Rightarrow> of_nat c1 | Suc 0 \<Rightarrow> of_nat c2 | Suc (Suc 0) \<Rightarrow> of_nat c3
                                | _ \<Rightarrow> of_nat c4) / of_nat a)"
  show ?thesis unfolding neg1_sos_def
  proof (rule exI[of _ ?z], rule conjI)
    have "(\<Sum>i<4. fst (sqL (of_nat a) (?z i)))
        = - of_nat a * ((of_nat c1 :: rat)^2 + (of_nat c2)^2 + (of_nat c3)^2 + (of_nat c4)^2) / (of_nat a)^2"
      by (simp add: sum4 sqL_def field_simps power2_eq_square)
    also have "\<dots> = - 1" using cq a0 by (simp add: field_simps power2_eq_square)
    finally show "(\<Sum>i<4. fst (sqL (of_nat a) (?z i))) = - 1" .
    show "(\<Sum>i<4. snd (sqL (of_nat a) (?z i))) = 0" by (simp add: sum4 sqL_def)
  qed
qed

section \<open>The values of the level\<close>

lemma level_eq:
  assumes "neg1_sos a k" and "\<And>j. j < k \<Longrightarrow> \<not> neg1_sos a j"
  shows "level a = k"
  unfolding level_def
proof (rule Least_equality)
  show "neg1_sos a k" by fact
next
  fix y assume "neg1_sos a y"
  thus "k \<le> y" using assms(2) by (meson not_less)
qed

theorem level_one:
  fixes a :: nat
  assumes "squarefree a" and "a = 1"
  shows "level (of_nat a) = 1"
  by (rule level_eq) (use assms neg1_sos_one_iff[OF assms(1)] not_neg1_sos_0 in \<open>auto simp: less_Suc_eq\<close>)

theorem level_two:
  fixes a :: nat
  assumes "squarefree a" and "a \<noteq> 1" and "a mod 8 \<noteq> 7" and "a > 0"
  shows "level (of_nat a) = 2"
proof (rule level_eq)
  show "neg1_sos (of_nat a :: rat) 2" using level_le_two assms by blast
  fix j :: nat assume "j < 2"
  hence "j = 0 \<or> j = 1" by auto
  thus "\<not> neg1_sos (of_nat a :: rat) j" using not_neg1_sos_0 neg1_sos_one_iff[OF assms(1)] assms(2) by blast
qed

text \<open>For a = 7 (mod 8) the level is 3 or 4 unconditionally; it is 4 once Pfister's theorem
  (a level is a power of 2, so never 3) is granted.\<close>

theorem level_ge3_le4:
  fixes a :: nat
  assumes "a mod 8 = 7"
  shows "neg1_sos (of_nat a) 4" and "\<not> neg1_sos (of_nat a :: rat) 1" and "\<not> neg1_sos (of_nat a :: rat) 2"
proof -
  have "a > 0" using assms by presburger
  thus "neg1_sos (of_nat a :: rat) 4" by (rule neg1_sos_four)
  show "\<not> neg1_sos (of_nat a :: rat) 2" by (rule not_two_when_7_mod_8[OF assms])
  show "\<not> neg1_sos (of_nat a :: rat) 1"
  proof
    assume "neg1_sos (of_nat a :: rat) 1"
    hence "neg1_sos (of_nat a :: rat) 2" by (rule neg1_sos_Suc[of _ 1, unfolded Suc_1])
    thus False using \<open>\<not> neg1_sos (of_nat a :: rat) 2\<close> by contradiction
  qed
qed

locale pfister_no_three =
  assumes pfister_level_not_three: "\<And>a :: rat. a > 0 \<Longrightarrow> neg1_sos a 3 \<Longrightarrow> neg1_sos a 2"
begin

theorem level_four:
  fixes a :: nat
  assumes "a mod 8 = 7"
  shows "level (of_nat a) = 4"
proof (rule level_eq)
  have a0: "a > 0" using assms by presburger
  show "neg1_sos (of_nat a :: rat) 4" using level_ge3_le4[OF assms] by blast
  fix j :: nat assume "j < 4"
  hence "j = 0 \<or> j = 1 \<or> j = 2 \<or> j = 3" by auto
  moreover have "\<not> neg1_sos (of_nat a :: rat) 3"
    using pfister_level_not_three[of "of_nat a"] a0 level_ge3_le4[OF assms] by auto
  ultimately show "\<not> neg1_sos (of_nat a :: rat) j"
    using not_neg1_sos_0 level_ge3_le4[OF assms] by blast
qed

end

end
