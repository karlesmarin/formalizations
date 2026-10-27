(*  Title:      Antipodal_Counterexamples.thy
    Author:     Carles Marín

    Where the antipodal floor fails

    Two exact examples of coefficient sequences whose power series has, at some point of the unit circle, a modulus
    below its value at z = -1: three times monotone coefficients (cex3) and log-convex coefficients (cexLC).
    Lean counterpart: Formalizations.Analysis.SpecialFunctions.Polylog.AntipodalCounterexamples.

    Main results:
    * cex3_monotone_three, cex3_not_four, cex3_antipode, cex3_re, cex3_normSq.
    * cexLC_pos, cexLC_logConvex, cexLC_convex, cexLC_antipode, cexLC_re, cexLC_normSq.
*)

theory Antipodal_Counterexamples
  imports "HOL-Analysis.Analysis"
begin

section \<open>Forward differences\<close>

primrec fdiff :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "fdiff 0 q = q"
| "fdiff (Suc j) q = (\<lambda>k. fdiff j q k - fdiff j q (Suc k))"

lemma fdiff_Suc: "fdiff (Suc j) q k = fdiff j q k - fdiff j q (Suc k)"
  by simp

lemma fdiff_congr:
  assumes "\<And>m. k \<le> m \<Longrightarrow> q m = q' m"
  shows "fdiff j q k = fdiff j q' k"
  using assms
proof (induction j arbitrary: k)
  case 0
  then show ?case by simp
next
  case (Suc j)
  have "fdiff j q k = fdiff j q' k"
    using Suc.IH[of k] Suc.prems by simp
  moreover have "fdiff j q (Suc k) = fdiff j q' (Suc k)"
    using Suc.IH[of "Suc k"] Suc.prems by simp
  ultimately show ?case by (simp add: fdiff_Suc)
qed

lemma fdiff_geom: "fdiff j (\<lambda>k. a * r ^ k) k = a * r ^ k * (1 - r) ^ j"
proof (induction j arbitrary: k)
  case 0
  then show ?case by simp
next
  case (Suc j)
  show ?case
    by (simp add: fdiff_Suc Suc.IH algebra_simps)
qed

lemma re_pow_cis: "Re ((cis \<theta>) ^ k) = cos (real k * \<theta>)"
  by (simp add: Complex.DeMoivre)

section \<open>Three times monotone is not enough\<close>

definition cex3 :: "nat \<Rightarrow> real" where
  "cex3 k = (if k = 0 then 6 else 0) + (if k = 1 then 3 else 0) + (if k = 2 then 1 else 0)
            + (1 / 2) ^ k"

lemma cex3_ge: "3 \<le> k \<Longrightarrow> cex3 k = (1 / 2) ^ k"
  unfolding cex3_def by simp

theorem cex3_monotone_three:
  assumes "j \<le> 3"
  shows "0 \<le> fdiff j cex3 k"
proof (cases "3 \<le> k")
  case True
  have "fdiff j cex3 k = fdiff j (\<lambda>k. 1 * (1 / 2 :: real) ^ k) k"
    by (rule fdiff_congr) (use True cex3_ge in auto)
  also have "\<dots> = 1 * (1 / 2) ^ k * (1 - 1 / 2) ^ j"
    by (rule fdiff_geom)
  finally show ?thesis by simp
next
  case False
  have hk: "k = 0 \<or> k = 1 \<or> k = 2" using False by arith
  have hj: "j = 0 \<or> j = Suc 0 \<or> j = Suc (Suc 0) \<or> j = Suc (Suc (Suc 0))"
    using assms by arith
  show ?thesis
    using hk hj by (elim disjE) (simp_all add: fdiff_Suc cex3_def)
qed

theorem cex3_not_four: "fdiff (Suc (Suc (Suc (Suc 0)))) cex3 1 = -31 / 32"
  by (simp add: fdiff_Suc cex3_def)

lemma cex3_sums:
  fixes z :: complex
  assumes "norm z < 2"
  shows "(\<lambda>k. of_real (cex3 k) * z ^ k) sums (6 + 3 * z + z\<^sup>2 + 1 / (1 - z / 2))"
proof -
  note h0 = sums_single[of 0 "\<lambda>k::nat. (6::complex) * z ^ k"]
  note h1 = sums_single[of 1 "\<lambda>k::nat. (3::complex) * z ^ k"]
  note h2 = sums_single[of 2 "\<lambda>k::nat. (1::complex) * z ^ k"]
  have hr: "norm (z / 2) < 1" using assms by (simp add: norm_divide)
  note h3 = geometric_sums[OF hr]
  note hs = sums_add[OF sums_add[OF sums_add[OF h0 h1] h2] h3]
  have eq: "(\<lambda>k. of_real (cex3 k) * z ^ k) =
    (\<lambda>k. (((if k = 0 then 6 * z ^ k else 0) + (if k = 1 then 3 * z ^ k else 0))
          + (if k = 2 then 1 * z ^ k else 0)) + (z / 2) ^ k)"
    by (rule ext) (auto simp: cex3_def power_divide algebra_simps)
  show ?thesis
    using hs unfolding eq by (simp add: power2_eq_square)
qed

theorem cex3_antipode: "(\<lambda>k. (-1) ^ k * cex3 k) sums (14 / 3)"
proof -
  note h = cex3_sums[of "-1"]
  have "(\<lambda>k. Re (of_real (cex3 k) * (-1 :: complex) ^ k)) sums Re (6 + 3 * (-1) + (-1)\<^sup>2 + 1 / (1 - (-1) / 2))"
    by (rule sums_Re[OF h]) simp
  then show ?thesis
    by (simp add: mult.commute)
qed

theorem cex3_re:
  "(\<lambda>k. cex3 k * cos (real k * arccos (-3 / 4))) sums (73 / 16)"
proof -
  define \<theta> where "\<theta> = arccos (-3 / 4)"
  define z where "z = cis \<theta>"
  have hn: "norm z = 1" by (simp add: z_def)
  note h = cex3_sums[of z]
  have hs: "(\<lambda>k. Re (of_real (cex3 k) * z ^ k)) sums
      Re (6 + 3 * z + z\<^sup>2 + 1 / (1 - z / 2))"
    by (rule sums_Re[OF h]) (simp add: hn)
  have hc: "cos \<theta> = -3 / 4" unfolding \<theta>_def by (rule cos_arccos) simp_all
  have ha: "Re z = -3 / 4" using hc by (simp add: z_def)
  have hb: "(Im z)\<^sup>2 = 7 / 16"
  proof -
    have "(sin \<theta>)\<^sup>2 + (cos \<theta>)\<^sup>2 = 1" by simp
    moreover have "(cos \<theta>)\<^sup>2 = 9 / 16" using hc by (simp add: power_divide)
    ultimately have "(sin \<theta>)\<^sup>2 = 7 / 16" by linarith
    then show ?thesis by (simp add: z_def)
  qed
  have lhs: "(\<lambda>k. Re (of_real (cex3 k) * z ^ k)) = (\<lambda>k. cex3 k * cos (real k * \<theta>))"
    by (rule ext) (simp add: z_def re_pow_cis)
  have rhs: "Re (6 + 3 * z + z\<^sup>2 + 1 / (1 - z / 2)) = 73 / 16"
  proof -
    have hb': "Im z * Im z = 7 / 16" using hb by (simp add: power2_eq_square)
    have e0: "Re (1 / (1 - z / 2)) = (1 - Re z / 2) / ((1 - Re z / 2)\<^sup>2 + (Im z / 2)\<^sup>2)"
      by (simp add: Re_divide)
    have n1: "1 - Re z / 2 = (11 / 8 :: real)" using ha by simp
    have d1: "(Im z / 2)\<^sup>2 = (7 / 64 :: real)" using hb by (simp add: power_divide)
    have e: "Re (1 / (1 - z / 2)) = (11 / 8) / ((11 / 8) ^ 2 + 7 / 64)"
      by (simp only: e0 n1 d1)
    have r1: "Re (z\<^sup>2) = Re z * Re z - Im z * Im z" by (simp add: power2_eq_square)
    have "Re (6 + 3 * z + z\<^sup>2 + 1 / (1 - z / 2)) =
          6 + 3 * Re z + Re (z\<^sup>2) + Re (1 / (1 - z / 2))" by simp
    also have "\<dots> = 6 + 3 * (-3 / 4) + ((-3 / 4) * (-3 / 4) - 7 / 16)
                    + (11 / 8) / ((11 / 8) ^ 2 + 7 / 64)"
      by (simp only: r1 e ha hb')
    also have "\<dots> = 73 / 16" by (simp add: field_simps)
    finally show ?thesis .
  qed
  show ?thesis
    using hs unfolding lhs rhs \<theta>_def .
qed

section \<open>Log-convex and convex is not enough\<close>

definition cexLC :: "nat \<Rightarrow> real" where
  "cexLC k = (if k = 0 then 1 else if k = 1 then 3 / 4 else if k = 2 then 9 / 16
              else 27 / 64 * (7 / 8) ^ (k - 3))"

lemma cexLC_0 [simp]: "cexLC 0 = 1" by (simp add: cexLC_def)
lemma cexLC_1 [simp]: "cexLC 1 = 3 / 4" by (simp add: cexLC_def)
lemma cexLC_2 [simp]: "cexLC 2 = 9 / 16" by (simp add: cexLC_def)
lemma cexLC_add3: "cexLC (m + 3) = 27 / 64 * (7 / 8) ^ m" by (simp add: cexLC_def)

lemma cexLC_4: "cexLC (m + 4) = 27 / 64 * (7 / 8) ^ (m + 1)"
proof -
  have e: "m + 4 = (m + 1) + 3" by simp
  show ?thesis by (subst e) (rule cexLC_add3)
qed
lemma cexLC_5: "cexLC (m + 5) = 27 / 64 * (7 / 8) ^ (m + 2)"
proof -
  have e: "m + 5 = (m + 2) + 3" by simp
  show ?thesis by (subst e) (rule cexLC_add3)
qed
theorem cexLC_pos: "0 < cexLC k"
  by (simp add: cexLC_def)

theorem cexLC_logConvex: "(cexLC (k + 1)) ^ 2 \<le> cexLC k * cexLC (k + 2)"
proof (cases "k = 0 \<or> k = 1 \<or> k = 2")
  case True
  then show ?thesis
    by (elim disjE) (simp_all add: cexLC_def power2_eq_square)
next
  case False
  then have "3 \<le> k" by auto
  then obtain m where "k = 3 + m" using le_Suc_ex by blast
  then have hm: "k = m + 3" by simp
  have e1: "k + 1 = m + 4" using hm by simp
  have e2: "k + 2 = m + 5" using hm by simp
  have a0: "cexLC k = 27 / 64 * (7 / 8) ^ m" using hm cexLC_add3 by simp
  have a1: "cexLC (Suc k) = 27 / 64 * (7 / 8) ^ (m + 1)"
    by (subst Suc_eq_plus1, subst e1) (rule cexLC_4)
  have a2: "cexLC (Suc (Suc k)) = 27 / 64 * (7 / 8) ^ (m + 2)"
  proof -
    have "Suc (Suc k) = m + 5" using hm by simp
    then show ?thesis by (simp only: cexLC_5)
  qed
  show ?thesis
    by (simp add: a0 a1 a2 power2_eq_square power_Suc algebra_simps)
qed

theorem cexLC_convex: "0 \<le> fdiff (Suc (Suc 0)) cexLC k"
proof (cases "k = 0 \<or> k = 1 \<or> k = 2")
  case True
  then show ?thesis
    by (elim disjE) (simp_all add: fdiff_Suc cexLC_def)
next
  case False
  then have "3 \<le> k" by auto
  then obtain m where "k = 3 + m" using le_Suc_ex by blast
  then have hm: "k = m + 3" by simp
  have e1: "k + 1 = m + 4" using hm by simp
  have e2: "k + 2 = m + 5" using hm by simp
  have a0: "cexLC k = 27 / 64 * (7 / 8) ^ m" using hm cexLC_add3 by simp
  have a1: "cexLC (Suc k) = 27 / 64 * (7 / 8) ^ (m + 1)"
    by (subst Suc_eq_plus1, subst e1) (rule cexLC_4)
  have a2: "cexLC (Suc (Suc k)) = 27 / 64 * (7 / 8) ^ (m + 2)"
  proof -
    have "Suc (Suc k) = m + 5" using hm by simp
    then show ?thesis by (simp only: cexLC_5)
  qed
  have eq: "fdiff (Suc (Suc 0)) cexLC k = 27 / 64 * (7 / 8) ^ m * (1 / 64)"
    by (simp add: fdiff_Suc a0 a1 a2 power_Suc algebra_simps)
  show ?thesis by (subst eq) (rule mult_nonneg_nonneg, simp_all)
qed

lemma cexLC_sums:
  fixes z :: complex
  assumes "norm z \<le> 1"
  shows "(\<lambda>k. of_real (cexLC k) * z ^ k)
         sums (1 + 3 / 4 * z + 9 / 16 * z\<^sup>2 + 27 / 64 * z ^ 3 * (1 / (1 - 7 / 8 * z)))"
proof -
  have hr: "norm (7 / 8 * z) < 1"
    using assms by (simp add: norm_mult)
  note g = sums_mult[OF geometric_sums[OF hr], of "27 / 64 * z ^ 3"]
  have h2: "(\<lambda>n. of_real (cexLC (n + 3)) * z ^ (n + 3)) sums (27 / 64 * z ^ 3 * (1 / (1 - 7 / 8 * z)))"
  proof -
    have "(\<lambda>n. of_real (cexLC (n + 3)) * z ^ (n + 3)) = (\<lambda>n. 27 / 64 * z ^ 3 * (7 / 8 * z) ^ n)"
      by (rule ext) (simp only: cexLC_add3 of_real_mult of_real_power of_real_divide of_real_numeral
          power_add power_mult_distrib mult.assoc mult.commute mult.left_commute)
    then show ?thesis using g by simp
  qed
  note h3 = sums_iff_shift[of "\<lambda>k. complex_of_real (cexLC k) * z ^ k" 3
      "27 / 64 * z ^ 3 * (1 / (1 - 7 / 8 * z))"]
  note h4 = iffD1[OF h3 h2]
  have es: "(\<Sum>i<3. of_real (cexLC i) * z ^ i) = 1 + 3 / 4 * z + 9 / 16 * z\<^sup>2"
    by (simp add: eval_nat_numeral lessThan_Suc cexLC_def power2_eq_square)
  have eqv: "27 / 64 * z ^ 3 * (1 / (1 - 7 / 8 * z)) + (\<Sum>i<3. of_real (cexLC i) * z ^ i)
             = 1 + 3 / 4 * z + 9 / 16 * z\<^sup>2 + 27 / 64 * z ^ 3 * (1 / (1 - 7 / 8 * z))"
    by (subst es) (simp only: ac_simps)
  show ?thesis
    by (subst eqv[symmetric]) (rule h4)
qed

theorem cexLC_antipode: "(\<lambda>k. (-1) ^ k * cexLC k) sums (47 / 80)"
proof -
  note h = cexLC_sums[of "-1"]
  have "(\<lambda>k. Re (of_real (cexLC k) * (-1 :: complex) ^ k)) sums
        Re (1 + 3 / 4 * (-1) + 9 / 16 * (-1)\<^sup>2 + 27 / 64 * (-1) ^ 3 * (1 / (1 - 7 / 8 * (-1))))"
    by (rule sums_Re[OF h]) simp
  then show ?thesis
    by (simp add: mult.commute)
qed

theorem cexLC_re:
  "(\<lambda>k. cexLC k * cos (real k * (2 * pi / 3))) sums (47 / 80 - 381 / 27040)"
proof -
  define \<theta> :: real where "\<theta> = 2 * pi / 3"
  define z where "z = cis \<theta>"
  have hn: "norm z = 1" by (simp add: z_def)
  note h = cexLC_sums[of z]
  have hn1: "norm z \<le> 1" using hn by simp
  note hs = sums_Re[OF cexLC_sums[OF hn1]]
  have hc: "cos \<theta> = -1 / 2"
    unfolding \<theta>_def by (rule cos_120)
  have ha: "Re z = -1 / 2" using hc by (simp add: z_def)
  have hb: "Im z * Im z = 3 / 4"
  proof -
    have "(sin \<theta>)\<^sup>2 + (cos \<theta>)\<^sup>2 = 1" by simp
    moreover have "(cos \<theta>)\<^sup>2 = 1 / 4" using hc by (simp add: power_divide)
    ultimately have "(sin \<theta>)\<^sup>2 = 3 / 4" by linarith
    then show ?thesis by (simp add: z_def power2_eq_square)
  qed
  have h3: "z ^ 3 = 1"
  proof -
    have "z ^ 3 = cis (real 3 * \<theta>)" by (simp add: z_def Complex.DeMoivre)
    also have "real 3 * \<theta> = 2 * pi" unfolding \<theta>_def by simp
    finally show ?thesis by simp
  qed
  have lhs: "(\<lambda>k. Re (of_real (cexLC k) * z ^ k)) = (\<lambda>k. cexLC k * cos (real k * \<theta>))"
    by (rule ext) (simp add: z_def re_pow_cis)
  have rhs: "Re (1 + 3 / 4 * z + 9 / 16 * z\<^sup>2 + 27 / 64 * z ^ 3 * (1 / (1 - 7 / 8 * z)))
             = 47 / 80 - 381 / 27040"
  proof -
    have e0: "Re (1 / (1 - 7 / 8 * z)) =
          (1 - 7 / 8 * Re z) / ((1 - 7 / 8 * Re z)\<^sup>2 + (7 / 8 * Im z)\<^sup>2)"
      by (simp add: Re_divide)
    have n1: "1 - 7 / 8 * Re z = (23 / 16 :: real)" using ha by simp
    have d1: "(7 / 8 * Im z)\<^sup>2 = (147 / 256 :: real)" 
    proof -
      have "(7 / 8 * Im z)\<^sup>2 = 49 / 64 * (Im z * Im z)"
        by (simp add: power2_eq_square algebra_simps)
      also have "\<dots> = 147 / 256" using hb by simp
      finally show ?thesis .
    qed
    have e: "Re (1 / (1 - 7 / 8 * z)) = (23 / 16) / ((23 / 16) ^ 2 + 147 / 256)"
      by (simp only: e0 n1 d1)
    have r1: "Re (z\<^sup>2) = Re z * Re z - Im z * Im z" by (simp add: power2_eq_square)
    have r2: "Re (27 / 64 * z ^ 3 * (1 / (1 - 7 / 8 * z))) = 27 / 64 * Re (1 / (1 - 7 / 8 * z))"
    proof -
      have e3: "27 / 64 * z ^ 3 * (1 / (1 - 7 / 8 * z)) = (27 / 64 :: real) *\<^sub>R (1 / (1 - 7 / 8 * z))"
        by (simp only: h3 mult_1_right scaleR_conv_of_real of_real_divide of_real_numeral)
      show ?thesis by (subst e3) simp
    qed
    have "Re (1 + 3 / 4 * z + 9 / 16 * z\<^sup>2 + 27 / 64 * z ^ 3 * (1 / (1 - 7 / 8 * z))) =
          1 + 3 / 4 * Re z + 9 / 16 * Re (z\<^sup>2) + Re (27 / 64 * z ^ 3 * (1 / (1 - 7 / 8 * z)))"
      by simp
    also have "\<dots> = 1 + 3 / 4 * (-1 / 2) + 9 / 16 * ((-1 / 2) * (-1 / 2) - 3 / 4)
                    + 27 / 64 * ((23 / 16) / ((23 / 16) ^ 2 + 147 / 256))"
      by (simp only: r1 r2 e ha hb)
    also have "\<dots> = 47 / 80 - 381 / 27040" by (simp add: field_simps)
    finally show ?thesis .
  qed
  show ?thesis
    using hs unfolding lhs rhs \<theta>_def .
qed

theorem cexLC_normSq:
  "\<exists>F. (\<lambda>k. of_real (cexLC k) * ((-7 + of_real (sqrt 15) * \<i>) / 8 :: complex) ^ k) sums F
     \<and> (cmod F)\<^sup>2 = (47 / 80) ^ 2 - 57 / 42200"
proof -
  define b :: real where "b = sqrt 15 / 8"
  have s: "sqrt 15 * sqrt 15 = (15 :: real)" using real_sqrt_pow2[of 15] by (simp add: power2_eq_square)
  have hb: "b * b = 15 / 64"
  proof -
    have "b * b = (sqrt 15 * sqrt 15) / 64" unfolding b_def by (simp add: field_simps)
    then show ?thesis using s by simp
  qed
  have hb2: "b ^ 2 = 15 / 64" using hb by (simp add: power2_eq_square)
  define z :: complex where "z = Complex (-7 / 8) b"
  have hz: "(-7 + of_real (sqrt 15) * \<i>) / 8 = z"
    unfolding z_def b_def by (simp add: complex_eq_iff)
  have rz: "Re z = -7 / 8" and iz: "Im z = b" by (simp_all add: z_def)
  have hn: "norm z \<le> 1"
  proof -
    have "(cmod z) ^ 2 = 1" by (simp add: z_def cmod_power2 hb2) (simp add: power2_eq_square field_simps)
    then show ?thesis
      using power2_le_imp_le[of "cmod z" 1] by simp
  qed
  have hz2: "z ^ 2 = Complex (17 / 32) (-7 / 4 * b)"
    by (rule complex_eqI) (simp_all add: z_def Re_power2 Im_power2 hb2 power2_eq_square hb)
  have hz3: "z ^ 3 = Complex (-7 / 128) (33 / 16 * b)"
  proof -
    have "z ^ 3 = z * z ^ 2" by (simp add: power3_eq_cube power2_eq_square)
    show ?thesis unfolding \<open>z ^ 3 = z * z ^ 2\<close> hz2
    proof (rule complex_eqI)
      show "Re (z * Complex (17 / 32) (-7 / 4 * b)) = Re (Complex (-7 / 128) (33 / 16 * b))"
        using hb by (simp add: z_def)
      show "Im (z * Complex (17 / 32) (-7 / 4 * b)) = Im (Complex (-7 / 128) (33 / 16 * b))"
        by (simp add: z_def)
    qed
  qed
  have hN: "1 - z / 8 - 3 / 32 * z ^ 2 - 9 / 128 * z ^ 3
            = Complex (17423 / 16384) (-217 / 2048 * b)"
    by (rule complex_eqI) (simp_all add: hz2 hz3 rz iz)
  have hD: "1 - 7 / 8 * z = Complex (113 / 64) (-7 / 8 * b)"
    by (rule complex_eqI) (simp_all add: z_def)
  have hD0: "1 - 7 / 8 * z \<noteq> 0"
proof
    assume h: "1 - 7 / 8 * z = 0"
    have "Complex (113 / 64) (-7 / 8 * b) = 0" by (rule trans[OF hD[symmetric] h])
    then show False by (simp add: complex_eq_iff)
  qed
  have hS: "1 + 3 / 4 * z + 9 / 16 * z\<^sup>2 + 27 / 64 * z ^ 3 * (1 / (1 - 7 / 8 * z))
            = (1 - z / 8 - 3 / 32 * z ^ 2 - 9 / 128 * z ^ 3) / (1 - 7 / 8 * z)"
    using hD0 by (simp add: field_simps power2_eq_square power3_eq_cube)
  have hnorm: "(cmod ((1 - z / 8 - 3 / 32 * z ^ 2 - 9 / 128 * z ^ 3) / (1 - 7 / 8 * z))) ^ 2
               = (47 / 80) ^ 2 - 57 / 42200"
    unfolding hN hD
    by (simp add: norm_divide power_divide cmod_power2 power_mult_distrib hb2)
  show ?thesis
    by (rule exI[of _ "(1 - z / 8 - 3 / 32 * z ^ 2 - 9 / 128 * z ^ 3) / (1 - 7 / 8 * z)"])
       (use cexLC_sums[OF hn] hS hnorm hz in simp)
qed

theorem cex3_normSq:
  "\<exists>F. (\<lambda>k. of_real (cex3 k) * ((-7 + of_real (sqrt 15) * \<i>) / 8 :: complex) ^ k) sums F
     \<and> (cmod F)\<^sup>2 = (14 / 3) ^ 2 - 635 / 2448"
proof -
  define b :: real where "b = sqrt 15 / 8"
  have s: "sqrt 15 * sqrt 15 = (15 :: real)" using real_sqrt_pow2[of 15] by (simp add: power2_eq_square)
  have hb: "b * b = 15 / 64"
  proof -
    have "b * b = (sqrt 15 * sqrt 15) / 64" unfolding b_def by (simp add: field_simps)
    then show ?thesis using s by simp
  qed
  have hb2: "b ^ 2 = 15 / 64" using hb by (simp add: power2_eq_square)
  define z :: complex where "z = Complex (-7 / 8) b"
  have hz: "(-7 + of_real (sqrt 15) * \<i>) / 8 = z"
    unfolding z_def b_def by (simp add: complex_eq_iff)
  have rz: "Re z = -7 / 8" and iz: "Im z = b" by (simp_all add: z_def)
  have hn: "norm z < 2"
  proof -
    have "(cmod z) ^ 2 = 1" by (simp add: z_def cmod_power2 hb2) (simp add: power2_eq_square field_simps)
    then show ?thesis
      using power2_le_imp_le[of "cmod z" 1] by simp
  qed
  have hz2: "z ^ 2 = Complex (17 / 32) (-7 / 4 * b)"
    by (rule complex_eqI) (simp_all add: z_def Re_power2 Im_power2 hb2 power2_eq_square hb)
  have hz3: "z ^ 3 = Complex (-7 / 128) (33 / 16 * b)"
  proof -
    have "z ^ 3 = z * z ^ 2" by (simp add: power3_eq_cube power2_eq_square)
    show ?thesis unfolding \<open>z ^ 3 = z * z ^ 2\<close> hz2
    proof (rule complex_eqI)
      show "Re (z * Complex (17 / 32) (-7 / 4 * b)) = Re (Complex (-7 / 128) (33 / 16 * b))"
        using hb by (simp add: z_def)
      show "Im (z * Complex (17 / 32) (-7 / 4 * b)) = Im (Complex (-7 / 128) (33 / 16 * b))"
        by (simp add: z_def)
    qed
  qed
  have hN: "14 - z ^ 2 - z ^ 3 = Complex (1731 / 128) (-5 / 16 * b)"
    by (rule complex_eqI) (simp_all add: hz2 hz3)
  have hD: "2 - z = Complex (23 / 8) (-b)"
    by (rule complex_eqI) (simp_all add: rz iz)
  have hD0: "2 - z \<noteq> 0"
  proof
    assume h: "2 - z = 0"
    have "Complex (23 / 8) (-b) = 0" by (rule trans[OF hD[symmetric] h])
    then show False by (simp add: complex_eq_iff)
  qed
  have hD1: "1 - z / 2 \<noteq> 0"
  proof
    assume h: "1 - z / 2 = 0"
    have "2 - z = 0" using h by (simp add: field_simps)
    then show False using hD0 by simp
  qed
  have hS: "6 + 3 * z + z\<^sup>2 + 1 / (1 - z / 2) = (14 - z ^ 2 - z ^ 3) / (2 - z)"
    using hD0 hD1 by (simp add: field_simps power2_eq_square power3_eq_cube)
  have hnorm: "(cmod ((14 - z ^ 2 - z ^ 3) / (2 - z))) ^ 2 = (14 / 3) ^ 2 - 635 / 2448"
    unfolding hN hD
    by (simp add: norm_divide power_divide cmod_power2 power_mult_distrib hb2)
  show ?thesis
    by (rule exI[of _ "(14 - z ^ 2 - z ^ 3) / (2 - z)"])
       (use cex3_sums[OF hn] hS hnorm hz in simp)
qed

end
