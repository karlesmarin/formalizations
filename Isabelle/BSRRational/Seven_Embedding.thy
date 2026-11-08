(*  Title:      Seven_Embedding.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

theory Seven_Embedding
  imports Complex_Main
begin

text \<open>Orthogonal unit vectors and one vector of squared norm $7$ in $\mathbb{Q}^r$ force
  $r \ge e + 3$ when there are $e - 1$ unit vectors. This is the embedding step of the
  theorem $\mathrm{BSR}_\mathbb{Q}(m,n) \ge z(m,n) + 3$ of the note on rational lengths of biquadratic forms.

  Choice of representation: vectors are functions @{typ "nat \<Rightarrow> rat"}, with the inner product
  summed over the coordinates below $r$. Then the dimension is an ordinary number, the induction
  can drop one coordinate by shifting indices, and no length bookkeeping is needed.

  Copied from entry 143 (Rational_Gap.thy): the descent for 7 mod 8 and \<open>seven_mod_8_rat\<close>
  (the block below). The Householder reflection of 143 (\<open>householder\<close>, \<open>dot_refl\<close>) is
  re-proved here for arbitrary dimension, since 143 has it for a fixed datatype of five
  coordinates.\<close>

text \<open>Block copied from the session RationalGap (Rational_Gap.thy).\<close>

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

section \<open>Inner product on $\mathbb{Q}^r$ and rational Householder reflections\<close>

definition dot :: "nat \<Rightarrow> (nat \<Rightarrow> rat) \<Rightarrow> (nat \<Rightarrow> rat) \<Rightarrow> rat" where
  "dot r x y = (\<Sum>i<r. x i * y i)"

definition e0 :: "nat \<Rightarrow> rat" where "e0 i = (if i = 0 then 1 else 0)"

lemma dot_comm: "dot r x y = dot r y x"
  by (simp add: dot_def mult.commute)

lemma dot_diff_l:
  "dot r (\<lambda>i. x i - c * u i) y = dot r x y - c * dot r u y"
  by (simp add: dot_def algebra_simps sum_subtractf sum_distrib_left)

lemma dot_diff_r:
  "dot r y (\<lambda>i. x i - c * u i) = dot r y x - c * dot r y u"
  using dot_diff_l[of r x c u y] by (simp add: dot_comm[of r y])

lemma dot_self_zero:
  assumes "dot r u u = 0"
  shows "\<forall>i<r. u i = 0"
proof -
  have "(\<forall>i\<in>{..<r}. u i * u i = 0)"
    using assms unfolding dot_def
    by (subst (asm) sum_nonneg_eq_0_iff) (auto intro: zero_le_square)
  then show ?thesis by simp
qed

definition refl :: "nat \<Rightarrow> (nat \<Rightarrow> rat) \<Rightarrow> (nat \<Rightarrow> rat) \<Rightarrow> (nat \<Rightarrow> rat)" where
  "refl r u x = (\<lambda>i. x i - (2 * dot r u x / dot r u u) * u i)"

lemma dot_refl:
  assumes "dot r u u \<noteq> 0"
  shows "dot r (refl r u x) (refl r u y) = dot r x y"
proof -
  define D where "D = dot r u u"
  define a where "a = dot r u x"
  define b where "b = dot r u y"
  define c where "c = 2 * a / D"
  define d where "d = 2 * b / D"
  have D0: "D \<noteq> 0" using assms by (simp add: D_def)
  have "dot r (refl r u x) (refl r u y)
      = dot r (refl r u x) y - d * dot r (refl r u x) u"
    unfolding refl_def[of r u y] using dot_diff_r[of r "refl r u x" y d u]
    by (simp add: a_def b_def D_def d_def)
  also have "dot r (refl r u x) y = dot r x y - c * b"
    unfolding refl_def using dot_diff_l[of r x c u y] by (simp add: a_def b_def D_def c_def)
  also have "dot r (refl r u x) u = a - c * D"
    unfolding refl_def using dot_diff_l[of r x c u u]
    by (simp add: a_def D_def c_def dot_comm[of r x u])
  finally have "dot r (refl r u x) (refl r u y) = dot r x y - c * b - d * (a - c * D)" .
  moreover have "c * b + d * (a - c * D) = 0"
    unfolding c_def d_def using D0 by (simp add: field_simps)
  ultimately show ?thesis by simp
qed

lemma dot_cong_r: "\<forall>i<r. y i = y' i \<Longrightarrow> dot r x y = dot r x y'"
  unfolding dot_def by (intro sum.cong refl) simp

lemma dot_e0_r: "dot (Suc r) x e0 = x 0"
  unfolding dot_def
  by (subst sum.lessThan_Suc_shift) (simp add: e0_def)

lemma dot_e0: "dot (Suc r) e0 e0 = 1"
  using dot_e0_r[of r e0] by (simp add: e0_def)

lemma householder:
  assumes "dot r x x = 1" "dot r e e = 1"
  shows "\<exists>R. (\<forall>y z. dot r (R y) (R z) = dot r y z) \<and> (\<forall>i<r. R x i = e i)"
proof (cases "\<forall>i<r. x i = e i")
  case True
  then show ?thesis
    by (intro exI[where x = "\<lambda>y. y"]) auto
next
  case False
  define u where "u = (\<lambda>i. x i - 1 * e i)"
  have uu: "dot r u u \<noteq> 0"
  proof
    assume "dot r u u = 0"
    then have "\<forall>i<r. u i = 0" by (rule dot_self_zero)
    then have "\<forall>i<r. x i = e i" by (simp add: u_def)
    with False show False by simp
  qed
  have dux: "dot r u x = dot r x x - 1 * dot r e x"
    unfolding u_def by (rule dot_diff_l)
  have duu: "dot r u u = dot r x u - 1 * dot r e u"
    unfolding u_def by (rule dot_diff_l)
  have dxu: "dot r x u = dot r x x - 1 * dot r x e"
    unfolding u_def by (rule dot_diff_r)
  have deu: "dot r e u = dot r e x - 1 * dot r e e"
    unfolding u_def by (rule dot_diff_r)
  have "dot r u u = 2 - 2 * dot r e x"
    using duu dxu deu assms by (simp add: dot_comm[of r e x])
  moreover have "dot r u x = 1 - dot r e x" using dux assms by simp
  ultimately have c1: "2 * dot r u x / dot r u u = 1" using uu by (simp add: field_simps)
  have rx: "\<forall>i<r. refl r u x i = e i"
    using c1 unfolding refl_def u_def by auto
  show ?thesis
    by (intro exI[where x = "refl r u"]) (use dot_refl[OF uu] rx in auto)
qed

section \<open>The embedding bound\<close>

lemma shift_dot:
  assumes "x 0 = 0"
  shows "dot (Suc r) x y = dot r (\<lambda>i. x (Suc i)) (\<lambda>i. y (Suc i))"
  unfolding dot_def
  by (subst sum.lessThan_Suc_shift) (simp add: assms)

lemma base_case:
  assumes "dot r w w = 7"
  shows "4 \<le> r"
proof (rule ccontr)
  assume "\<not> 4 \<le> r"
  then have r3: "r \<le> 3" by simp
  obtain w' where w'_def: "w' = (\<lambda>i. if i < r then w i else 0)" by simp
  have "dot r w w = (\<Sum>i<3. w' i * w' i)"
  proof -
    have "(\<Sum>i<r. w i * w i) = (\<Sum>i<r. w' i * w' i)"
      by (intro sum.cong refl) (simp add: w'_def)
    also have "\<dots> = (\<Sum>i<3. w' i * w' i)"
      by (rule sum.mono_neutral_left) (use r3 in \<open>auto simp: w'_def\<close>)
    finally show ?thesis by (simp add: dot_def)
  qed
  then have "w' 0 ^ 2 + w' (Suc 0) ^ 2 + w' (Suc (Suc 0)) ^ 2 = 7"
    using assms by (simp add: numeral_3_eq_3 power2_eq_square)
  moreover have "w' 0 ^ 2 + w' (Suc 0) ^ 2 + w' (Suc (Suc 0)) ^ 2 \<noteq> of_int 7"
    by (rule seven_mod_8_rat) simp
  ultimately show False by simp
qed

lemma embedding_aux:
  "\<forall>r v w. (\<forall>i<k. dot r (v i) (v i) = 1) \<longrightarrow> (\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> dot r (v i) (v j) = 0)
     \<longrightarrow> (\<forall>i<k. dot r (v i) w = 0) \<longrightarrow> dot r w w = 7 \<longrightarrow> k + 4 \<le> r"
proof (induction k)
  case 0
  then show ?case using base_case by auto
next
  case (Suc k)
  show ?case
  proof (intro allI impI)
    fix r v w
    assume n1: "\<forall>i<Suc k. dot r (v i) (v i) = 1"
      and o1: "\<forall>i<Suc k. \<forall>j<Suc k. i \<noteq> j \<longrightarrow> dot r (v i) (v j) = 0"
      and o2: "\<forall>i<Suc k. dot r (v i) w = 0" and nw: "dot r w w = 7"
    have r0: "r \<noteq> 0"
    proof
      assume "r = 0"
      then have "dot r (v 0) (v 0) = 0" by (simp add: dot_def)
      with n1 show False by simp
    qed
    then obtain r' where r: "r = Suc r'" using r0 by (cases r) auto
    have v0: "dot r (v 0) (v 0) = 1" using n1 by simp
    have e: "dot r e0 e0 = 1" unfolding r by (rule dot_e0)
    obtain R where R: "\<And>y z. dot r (R y) (R z) = dot r y z" "\<forall>i<r. R (v 0) i = e0 i"
      using householder[OF v0 e] by blast
    obtain v' where v'_def: "v' = (\<lambda>j i. R (v (Suc j)) (Suc i))" by simp
    obtain w' where w'_def: "w' = (\<lambda>i. R w (Suc i))" by simp
    have z: "\<And>y. dot r y (v 0) = 0 \<Longrightarrow> R y 0 = 0"
    proof -
      fix y assume "dot r y (v 0) = 0"
      then have "dot r (R y) (R (v 0)) = 0" using R(1)[of y "v 0"] by simp
      then have "dot r (R y) e0 = 0" using dot_cong_r[OF R(2), of "R y"] by simp
      then show "R y 0 = 0" unfolding r by (simp add: dot_e0_r)
    qed
    have z1: "\<And>j. j < k \<Longrightarrow> R (v (Suc j)) 0 = 0"
    proof (rule z)
      fix j assume j: "j < k"
      show "dot r (v (Suc j)) (v 0) = 0" using o1[rule_format, of "Suc j" 0] j by simp
    qed
    have zw: "R w 0 = 0" by (rule z) (use o2 dot_comm[of r w "v 0"] in auto)
    have "\<forall>i<k. dot r' (v' i) (v' i) = 1"
    proof (intro allI impI)
      fix j assume j: "j < k"
      have "dot r' (v' j) (v' j) = dot r (R (v (Suc j))) (R (v (Suc j)))"
        unfolding v'_def r by (rule sym[OF shift_dot[where x = "R (v (Suc j))" and y = "R (v (Suc j))" and r = r', OF z1[OF j]]])
      also have "\<dots> = 1" using R(1) n1 j by simp
      finally show "dot r' (v' j) (v' j) = 1" .
    qed
    moreover have "\<forall>i<k. \<forall>j<k. i \<noteq> j \<longrightarrow> dot r' (v' i) (v' j) = 0"
    proof (intro allI impI)
      fix i j assume i: "i < k" and j: "j < k" and ij: "i \<noteq> j"
      have "dot r' (v' i) (v' j) = dot r (R (v (Suc i))) (R (v (Suc j)))"
        unfolding v'_def r by (rule sym[OF shift_dot[where x = "R (v (Suc i))" and y = "R (v (Suc j))" and r = r', OF z1[OF i]]])
      also have "\<dots> = 0" using R(1) o1 i j ij by simp
      finally show "dot r' (v' i) (v' j) = 0" .
    qed
    moreover have "\<forall>i<k. dot r' (v' i) w' = 0"
    proof (intro allI impI)
      fix i assume i: "i < k"
      have "dot r' (v' i) w' = dot r (R (v (Suc i))) (R w)"
        unfolding v'_def w'_def r by (rule sym[OF shift_dot[where x = "R (v (Suc i))" and y = "R w" and r = r', OF z1[OF i]]])
      also have "\<dots> = 0" using R(1) o2 i by simp
      finally show "dot r' (v' i) w' = 0" .
    qed
    moreover have "dot r' w' w' = 7"
    proof -
      have "dot r' w' w' = dot r (R w) (R w)"
        unfolding w'_def r by (rule sym[OF shift_dot[where x = "R w" and y = "R w" and r = r', OF zw]])
      also have "\<dots> = 7" using R(1) nw by simp
      finally show ?thesis .
    qed
    ultimately have "k + 4 \<le> r'" using Suc.IH by blast
    then show "Suc k + 4 \<le> r" by (simp add: r)
  qed
qed

theorem seven_embedding:
  fixes v :: "nat \<Rightarrow> nat \<Rightarrow> rat" and w :: "nat \<Rightarrow> rat" and e r :: nat
  assumes e: "1 \<le> e"
    and n1: "\<And>i. i < e - 1 \<Longrightarrow> dot r (v i) (v i) = 1"
    and o1: "\<And>i j. i < e - 1 \<Longrightarrow> j < e - 1 \<Longrightarrow> i \<noteq> j \<Longrightarrow> dot r (v i) (v j) = 0"
    and o2: "\<And>i. i < e - 1 \<Longrightarrow> dot r (v i) w = 0"
    and nw: "dot r w w = 7"
  shows "e + 3 \<le> r"
proof -
  have H: "(\<forall>i<e - 1. dot r (v i) (v i) = 1) \<longrightarrow>
      (\<forall>i<e - 1. \<forall>j<e - 1. i \<noteq> j \<longrightarrow> dot r (v i) (v j) = 0) \<longrightarrow>
      (\<forall>i<e - 1. dot r (v i) w = 0) \<longrightarrow> dot r w w = 7 \<longrightarrow> e - 1 + 4 \<le> r"
    by (rule embedding_aux[of "e - 1", THEN spec, THEN spec, THEN spec])
  have "e - 1 + 4 \<le> r"
    by (rule H[rule_format]) (use n1 o1 o2 nw in blast)+
  then show ?thesis using e by simp
qed

end
