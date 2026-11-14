(*  Title:      Quasistatic_Average.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License: BSD
*)

section \<open>The averaging step of the quasi-static bound\<close>

theory Quasistatic_Average
  imports "HOL-Probability.Probability" Memory_Access_Quasistatic
begin

text \<open>
  From "Exact limits for writing a quantum memory" (C. Marin, draft, November 2026), Proposition 12(a):
  for offsets that are random but constant during each run, the resonant pulse of duration
  @{text "T0 = pi / (2 G)"} has a transfer amplitude @{text "A * exp (- i * xi * T0)"} with
  @{text "A = qsA (Delta^2 / (4 G^2))"}; the pointwise inequality @{thm [source] qs_pointwise} is
  averaged over the offsets.
\<close>

section \<open>Auxiliary facts on the amplitude\<close>

lemma qsA_ge_minus_one:
  fixes q :: real
  assumes "0 \<le> q"
  shows "- 1 \<le> qsA q"
proof -
  have s1: "1 \<le> sqrt (1 + q)" by (rule qs_s_facts(1)[OF assms])
  have sp: "0 \<le> sqrt (1 + q)" using s1 by simp
  have "- sqrt (1 + q) \<le> sin (pi / 2 * sqrt (1 + q))"
    using sin_ge_minus_one[of "pi / 2 * sqrt (1 + q)"] s1 by argo
  then have "(- sqrt (1 + q)) / sqrt (1 + q) \<le> sin (pi / 2 * sqrt (1 + q)) / sqrt (1 + q)"
    by (rule divide_right_mono[OF _ sp])
  moreover have "(- sqrt (1 + q)) / sqrt (1 + q) = - 1" using s1 by simp
  ultimately show ?thesis unfolding qsA_def by simp
qed

lemma qsA_abs_le_one:
  fixes q :: real
  assumes "0 \<le> q"
  shows "\<bar>qsA q\<bar> \<le> 1"
  using qsA_le_one[OF assms] qsA_ge_minus_one[OF assms] by argo

lemma qsA_measurable: "qsA \<in> borel_measurable borel"
  unfolding qsA_def by measurable

definition qs_amp :: "real \<Rightarrow> real \<Rightarrow> real" where
  "qs_amp G d = qsA (d\<^sup>2 / (4 * G\<^sup>2))"

lemma qs_amp_abs_le_one: "\<bar>qs_amp G d\<bar> \<le> 1"
  unfolding qs_amp_def by (rule qsA_abs_le_one) simp

lemma qs_amp_pointwise:
  fixes G d xi :: real
  assumes "0 < G"
  shows "3 - (qs_amp G d)\<^sup>2 - 2 * qs_amp G d * cos (xi * (pi / (2 * G)))
         \<le> d\<^sup>2 * (1 / (2 * G\<^sup>2)) + xi\<^sup>2 * (pi\<^sup>2 / (4 * G\<^sup>2))"
proof -
  have q0: "0 \<le> d\<^sup>2 / (4 * G\<^sup>2)" by simp
  have "3 - (qsA (d\<^sup>2 / (4 * G\<^sup>2)))\<^sup>2 - 2 * qsA (d\<^sup>2 / (4 * G\<^sup>2)) * cos (xi * (pi / (2 * G)))
        \<le> 2 * (d\<^sup>2 / (4 * G\<^sup>2)) + (xi * (pi / (2 * G)))\<^sup>2"
    by (rule qs_pointwise[OF q0])
  moreover have "2 * (d\<^sup>2 / (4 * G\<^sup>2)) + (xi * (pi / (2 * G)))\<^sup>2
                 = d\<^sup>2 * (1 / (2 * G\<^sup>2)) + xi\<^sup>2 * (pi\<^sup>2 / (4 * G\<^sup>2))"
    using assms by (simp add: field_simps power2_eq_square)
  ultimately show ?thesis unfolding qs_amp_def by simp
qed

lemma qs_amp_measurable:
  assumes "D \<in> borel_measurable M"
  shows "(\<lambda>x. qs_amp G (D x)) \<in> borel_measurable M"
proof -
  have "(\<lambda>x. (D x)\<^sup>2 / (4 * G\<^sup>2)) \<in> borel_measurable M" using assms by measurable
  then have "(\<lambda>x. qsA ((D x)\<^sup>2 / (4 * G\<^sup>2))) \<in> borel_measurable M"
    by (rule measurable_compose[OF _ qsA_measurable])
  then show ?thesis unfolding qs_amp_def .
qed

section \<open>The averaged bound\<close>

text \<open>The transfer deficit of the resonant pulse averaged over the offsets:
  @{text "p = E[A^2]"}, @{text "c = |E[A exp (- i xi T0)]|"}, @{text "r = (3 - p - 2 c) / 6"}.\<close>

definition qs_r :: "'a measure \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real" where
  "qs_r M G D xb = (3 - (\<integral>x. (qs_amp G (D x))\<^sup>2 \<partial>M)
     - 2 * norm (\<integral>x. complex_of_real (qs_amp G (D x))
                    * exp (- (\<i> * complex_of_real (xb x * (pi / (2 * G))))) \<partial>M)) / 6"

lemma norm_ge_Re_integral:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "integrable M f"
  shows "(\<integral>x. Re (f x) \<partial>M) \<le> norm (\<integral>x. f x \<partial>M)"
proof -
  have "(\<integral>x. Re (f x) \<partial>M) = Re (\<integral>x. f x \<partial>M)" by (rule integral_Re[OF assms])
  also have "\<dots> \<le> norm (\<integral>x. f x \<partial>M)" by (rule complex_Re_le_cmod)
  finally show ?thesis .
qed

theorem qs_average_real:
  fixes M :: "'a measure" and D xb :: "'a \<Rightarrow> real" and G c :: real
  assumes "prob_space M" and "D \<in> borel_measurable M" and "xb \<in> borel_measurable M"
    and "integrable M (\<lambda>x. (D x)\<^sup>2)" and "integrable M (\<lambda>x. (xb x)\<^sup>2)" and "0 < G"
    and "(\<integral>x. qs_amp G (D x) * cos (xb x * (pi / (2 * G))) \<partial>M) \<le> c"
  shows "(3 - (\<integral>x. (qs_amp G (D x))\<^sup>2 \<partial>M) - 2 * c) / 6
         \<le> (\<integral>x. (D x)\<^sup>2 \<partial>M) / (12 * G\<^sup>2) + pi\<^sup>2 * (\<integral>x. (xb x)\<^sup>2 \<partial>M) / (24 * G\<^sup>2)"
proof -
  interpret prob_space M by fact
  define A where "A = (\<lambda>x. qs_amp G (D x))"
  define th where "th = (\<lambda>x. xb x * (pi / (2 * G)))"
  have Am: "A \<in> borel_measurable M" unfolding A_def by (rule qs_amp_measurable[OF assms(2)])
  have thmeas: "th \<in> borel_measurable M" unfolding th_def using assms(3) by measurable
  have A1: "\<bar>A x\<bar> \<le> 1" for x unfolding A_def by (rule qs_amp_abs_le_one)
  have iA2: "integrable M (\<lambda>x. (A x)\<^sup>2)"
  proof (rule integrable_const_bound[where B = 1])
    show "AE x in M. norm ((A x)\<^sup>2) \<le> 1"
    proof (rule AE_I2)
      fix x
      have "\<bar>A x\<bar>\<^sup>2 \<le> 1\<^sup>2" by (rule power_mono[OF A1 abs_ge_zero])
      then show "norm ((A x)\<^sup>2) \<le> 1" by simp
    qed
    show "(\<lambda>x. (A x)\<^sup>2) \<in> borel_measurable M" using Am by measurable
  qed
  have iAc: "integrable M (\<lambda>x. A x * cos (th x))"
  proof (rule integrable_const_bound[where B = 1])
    show "AE x in M. norm (A x * cos (th x)) \<le> 1"
    proof (rule AE_I2)
      fix x
      have "\<bar>A x\<bar> * \<bar>cos (th x)\<bar> \<le> 1 * 1" by (rule mult_mono[OF A1 abs_cos_le_one]) simp_all
      then show "norm (A x * cos (th x)) \<le> 1" by (simp add: abs_mult)
    qed
    show "(\<lambda>x. A x * cos (th x)) \<in> borel_measurable M" using Am thmeas by measurable
  qed
  have iD: "integrable M (\<lambda>x. (D x)\<^sup>2 * (1 / (2 * G\<^sup>2)))" using assms(4) by (rule integrable_mult_left)
  have iX: "integrable M (\<lambda>x. (xb x)\<^sup>2 * (pi\<^sup>2 / (4 * G\<^sup>2)))" using assms(5) by (rule integrable_mult_left)
  have iL: "integrable M (\<lambda>x. 3 - (A x)\<^sup>2 - 2 * (A x * cos (th x)))"
    using iA2 iAc by (intro Bochner_Integration.integrable_diff integrable_mult_right) simp_all
  have iR: "integrable M (\<lambda>x. (D x)\<^sup>2 * (1 / (2 * G\<^sup>2)) + (xb x)\<^sup>2 * (pi\<^sup>2 / (4 * G\<^sup>2)))"
    using iD iX by (rule Bochner_Integration.integrable_add)
  have pw: "3 - (A x)\<^sup>2 - 2 * (A x * cos (th x))
            \<le> (D x)\<^sup>2 * (1 / (2 * G\<^sup>2)) + (xb x)\<^sup>2 * (pi\<^sup>2 / (4 * G\<^sup>2))" for x
    using qs_amp_pointwise[OF assms(6), of "D x" "xb x"] unfolding A_def th_def by (simp add: algebra_simps)
  have mono: "(\<integral>x. 3 - (A x)\<^sup>2 - 2 * (A x * cos (th x)) \<partial>M)
              \<le> (\<integral>x. (D x)\<^sup>2 * (1 / (2 * G\<^sup>2)) + (xb x)\<^sup>2 * (pi\<^sup>2 / (4 * G\<^sup>2)) \<partial>M)"
    by (rule integral_mono[OF iL iR pw])
  have lhs: "(\<integral>x. 3 - (A x)\<^sup>2 - 2 * (A x * cos (th x)) \<partial>M)
             = 3 - (\<integral>x. (A x)\<^sup>2 \<partial>M) - 2 * (\<integral>x. A x * cos (th x) \<partial>M)"
  proof -
    have "(\<integral>x. 3 - (A x)\<^sup>2 - 2 * (A x * cos (th x)) \<partial>M)
          = (\<integral>x. 3 - (A x)\<^sup>2 \<partial>M) - (\<integral>x. 2 * (A x * cos (th x)) \<partial>M)"
      using iAc iA2 by (intro Bochner_Integration.integral_diff) simp_all
    also have "(\<integral>x. 3 - (A x)\<^sup>2 \<partial>M) = 3 - (\<integral>x. (A x)\<^sup>2 \<partial>M)"
      using iA2 by (simp add: prob_space)
    also have "(\<integral>x. 2 * (A x * cos (th x)) \<partial>M) = 2 * (\<integral>x. A x * cos (th x) \<partial>M)"
    proof -
      have "(\<integral>x. 2 * (A x * cos (th x)) \<partial>M) = (\<integral>x. (A x * cos (th x)) * 2 \<partial>M)"
        by (simp add: mult.commute)
      also have "\<dots> = (\<integral>x. A x * cos (th x) \<partial>M) * 2" by simp
      finally show ?thesis by simp
    qed
    finally show ?thesis .
  qed
  have rhs: "(\<integral>x. (D x)\<^sup>2 * (1 / (2 * G\<^sup>2)) + (xb x)\<^sup>2 * (pi\<^sup>2 / (4 * G\<^sup>2)) \<partial>M)
             = (\<integral>x. (D x)\<^sup>2 \<partial>M) * (1 / (2 * G\<^sup>2)) + (\<integral>x. (xb x)\<^sup>2 \<partial>M) * (pi\<^sup>2 / (4 * G\<^sup>2))"
    using iD iX by (simp add: Bochner_Integration.integral_add)
  have key: "3 - (\<integral>x. (A x)\<^sup>2 \<partial>M) - 2 * c
             \<le> (\<integral>x. (D x)\<^sup>2 \<partial>M) * (1 / (2 * G\<^sup>2)) + (\<integral>x. (xb x)\<^sup>2 \<partial>M) * (pi\<^sup>2 / (4 * G\<^sup>2))"
    using mono lhs rhs assms(7) unfolding A_def th_def by linarith
  have "(3 - (\<integral>x. (A x)\<^sup>2 \<partial>M) - 2 * c) / 6
        \<le> ((\<integral>x. (D x)\<^sup>2 \<partial>M) * (1 / (2 * G\<^sup>2)) + (\<integral>x. (xb x)\<^sup>2 \<partial>M) * (pi\<^sup>2 / (4 * G\<^sup>2))) / 6"
    by (rule divide_right_mono[OF key]) simp
  also have "\<dots> = (\<integral>x. (D x)\<^sup>2 \<partial>M) / (12 * G\<^sup>2) + pi\<^sup>2 * (\<integral>x. (xb x)\<^sup>2 \<partial>M) / (24 * G\<^sup>2)"
    using assms(6) by (simp add: field_simps)
  finally show ?thesis unfolding A_def .
qed

theorem qs_average:
  fixes M :: "'a measure" and D xb :: "'a \<Rightarrow> real" and G :: real
  assumes "prob_space M" and "D \<in> borel_measurable M" and "xb \<in> borel_measurable M"
    and "integrable M (\<lambda>x. (D x)\<^sup>2)" and "integrable M (\<lambda>x. (xb x)\<^sup>2)" and "0 < G"
  shows "qs_r M G D xb \<le> (\<integral>x. (D x)\<^sup>2 \<partial>M) / (12 * G\<^sup>2) + pi\<^sup>2 * (\<integral>x. (xb x)\<^sup>2 \<partial>M) / (24 * G\<^sup>2)"
proof -
  interpret prob_space M by fact
  define f where "f = (\<lambda>x. complex_of_real (qs_amp G (D x))
                    * exp (- (\<i> * complex_of_real (xb x * (pi / (2 * G))))))"
  have Am: "(\<lambda>x. qs_amp G (D x)) \<in> borel_measurable M" by (rule qs_amp_measurable[OF assms(2)])
  have fm: "f \<in> borel_measurable M" unfolding f_def using Am assms(3) by measurable
  have nf: "norm (f x) \<le> 1" for x
  proof -
    have "norm (f x) = \<bar>qs_amp G (D x)\<bar>" unfolding f_def by (simp add: norm_mult)
    then show ?thesis using qs_amp_abs_le_one[of G "D x"] by simp
  qed
  have if_: "integrable M f" by (rule integrable_const_bound[where B = 1]) (use nf fm in \<open>simp_all\<close>)
  have reF: "Re (f x) = qs_amp G (D x) * cos (xb x * (pi / (2 * G)))" for x
    unfolding f_def by (simp add: Re_exp)
  have "(\<integral>x. qs_amp G (D x) * cos (xb x * (pi / (2 * G))) \<partial>M) \<le> norm (\<integral>x. f x \<partial>M)"
    using norm_ge_Re_integral[OF if_] unfolding reF .
  then have "(3 - (\<integral>x. (qs_amp G (D x))\<^sup>2 \<partial>M) - 2 * norm (\<integral>x. f x \<partial>M)) / 6
             \<le> (\<integral>x. (D x)\<^sup>2 \<partial>M) / (12 * G\<^sup>2) + pi\<^sup>2 * (\<integral>x. (xb x)\<^sup>2 \<partial>M) / (24 * G\<^sup>2)"
    by (rule qs_average_real[OF assms(1-6)])
  then show ?thesis unfolding qs_r_def f_def .
qed

section \<open>Uncorrelated offsets\<close>

corollary qs_average_uncorrelated:
  fixes M :: "'a measure" and xq xm :: "'a \<Rightarrow> real" and G sq sm :: real
  assumes "prob_space M" and "xq \<in> borel_measurable M" and "xm \<in> borel_measurable M"
    and "integrable M (\<lambda>x. (xq x)\<^sup>2)" and "integrable M (\<lambda>x. (xm x)\<^sup>2)"
    and "(\<integral>x. xq x * xm x \<partial>M) = 0"
    and "(\<integral>x. (xq x)\<^sup>2 \<partial>M) = sq\<^sup>2" and "(\<integral>x. (xm x)\<^sup>2 \<partial>M) = sm\<^sup>2" and "0 < G"
  shows "qs_r M G (\<lambda>x. xq x - xm x) (\<lambda>x. (xq x + xm x) / 2)
         \<le> (8 + pi\<^sup>2) * (sq\<^sup>2 + sm\<^sup>2) / (96 * G\<^sup>2)"
proof -
  interpret prob_space M by fact
  have iq: "integrable M (\<lambda>x. (xq x)\<^sup>2)" and im2: "integrable M (\<lambda>x. (xm x)\<^sup>2)" using assms(4,5) by simp_all
  have im: "integrable M (\<lambda>x. xq x * xm x)"
  proof (rule Bochner_Integration.integrable_bound[where f = "\<lambda>x. (xq x)\<^sup>2 + (xm x)\<^sup>2"])
    show "integrable M (\<lambda>x. (xq x)\<^sup>2 + (xm x)\<^sup>2)" using iq im2 by (rule Bochner_Integration.integrable_add)
    show "(\<lambda>x. xq x * xm x) \<in> borel_measurable M" using assms(2,3) by measurable
    show "AE x in M. norm (xq x * xm x) \<le> norm ((xq x)\<^sup>2 + (xm x)\<^sup>2)"
    proof (rule AE_I2)
      fix x
      have "\<bar>xq x * xm x\<bar> \<le> (xq x)\<^sup>2 + (xm x)\<^sup>2"
      proof -
        have h1: "0 \<le> (xq x - xm x) * (xq x - xm x)" by simp
        have h2: "0 \<le> (xq x + xm x) * (xq x + xm x)" by simp
        have h3: "0 \<le> xq x * xq x" and h4: "0 \<le> xm x * xm x" by simp_all
        have e1: "(xq x - xm x) * (xq x - xm x) = xq x * xq x - 2 * (xq x * xm x) + xm x * xm x"
          by (simp add: algebra_simps)
        have e2: "(xq x + xm x) * (xq x + xm x) = xq x * xq x + 2 * (xq x * xm x) + xm x * xm x"
          by (simp add: algebra_simps)
        have u: "xq x * xm x \<le> (xq x)\<^sup>2 + (xm x)\<^sup>2"
          unfolding power2_eq_square using h1 h3 h4 e1 by linarith
        have l: "- ((xq x)\<^sup>2 + (xm x)\<^sup>2) \<le> xq x * xm x"
          unfolding power2_eq_square using h2 h3 h4 e2 by linarith
        show ?thesis using u l by (simp add: abs_le_iff)
      qed
      moreover have "0 \<le> (xq x)\<^sup>2 + (xm x)\<^sup>2" by simp
      ultimately show "norm (xq x * xm x) \<le> norm ((xq x)\<^sup>2 + (xm x)\<^sup>2)" by simp
    qed
  qed
  have eD: "(\<lambda>x. (xq x - xm x)\<^sup>2) = (\<lambda>x. ((xq x)\<^sup>2 + (xm x)\<^sup>2) - 2 * (xq x * xm x))"
    by (simp add: fun_eq_iff power2_eq_square algebra_simps)
  have eX: "(\<lambda>x. ((xq x + xm x) / 2)\<^sup>2) = (\<lambda>x. (((xq x)\<^sup>2 + (xm x)\<^sup>2) + 2 * (xq x * xm x)) * (1 / 4))"
    by (simp add: fun_eq_iff power2_eq_square algebra_simps)
  have iS: "integrable M (\<lambda>x. (xq x)\<^sup>2 + (xm x)\<^sup>2)" using iq im2 by (rule Bochner_Integration.integrable_add)
  have i2m: "integrable M (\<lambda>x. 2 * (xq x * xm x))" using im by (rule integrable_mult_right)
  have iD: "integrable M (\<lambda>x. (xq x - xm x)\<^sup>2)"
    unfolding eD using iS i2m by (rule Bochner_Integration.integrable_diff)
  have iX: "integrable M (\<lambda>x. ((xq x + xm x) / 2)\<^sup>2)"
  proof -
    have "integrable M (\<lambda>x. ((xq x)\<^sup>2 + (xm x)\<^sup>2) + 2 * (xq x * xm x))"
      using iS i2m by (rule Bochner_Integration.integrable_add)
    then show ?thesis unfolding eX by (rule integrable_mult_left)
  qed
  have ED: "(\<integral>x. (xq x - xm x)\<^sup>2 \<partial>M) = sq\<^sup>2 + sm\<^sup>2"
  proof -
    have "(\<integral>x. (xq x - xm x)\<^sup>2 \<partial>M) = (\<integral>x. (xq x)\<^sup>2 + (xm x)\<^sup>2 \<partial>M) - (\<integral>x. 2 * (xq x * xm x) \<partial>M)"
      unfolding eD using iS i2m by (rule Bochner_Integration.integral_diff)
    also have "(\<integral>x. (xq x)\<^sup>2 + (xm x)\<^sup>2 \<partial>M) = sq\<^sup>2 + sm\<^sup>2"
      using iq im2 assms(7,8) by (simp add: Bochner_Integration.integral_add)
    also have "(\<integral>x. 2 * (xq x * xm x) \<partial>M) = 0" using assms(6) by simp
    finally show ?thesis by simp
  qed
  have EX: "(\<integral>x. ((xq x + xm x) / 2)\<^sup>2 \<partial>M) = (sq\<^sup>2 + sm\<^sup>2) / 4"
  proof -
    have "(\<integral>x. ((xq x + xm x) / 2)\<^sup>2 \<partial>M) = (\<integral>x. ((xq x)\<^sup>2 + (xm x)\<^sup>2) + 2 * (xq x * xm x) \<partial>M) * (1 / 4)"
      unfolding eX by simp
    also have "(\<integral>x. ((xq x)\<^sup>2 + (xm x)\<^sup>2) + 2 * (xq x * xm x) \<partial>M) = sq\<^sup>2 + sm\<^sup>2"
      using iS i2m iq im2 assms(6,7,8) by (simp add: Bochner_Integration.integral_add)
    finally show ?thesis by simp
  qed
  have meD: "(\<lambda>x. xq x - xm x) \<in> borel_measurable M" using assms(2,3) by measurable
  have meX: "(\<lambda>x. (xq x + xm x) / 2) \<in> borel_measurable M" using assms(2,3) by measurable
  have "qs_r M G (\<lambda>x. xq x - xm x) (\<lambda>x. (xq x + xm x) / 2)
        \<le> (\<integral>x. (xq x - xm x)\<^sup>2 \<partial>M) / (12 * G\<^sup>2) + pi\<^sup>2 * (\<integral>x. ((xq x + xm x) / 2)\<^sup>2 \<partial>M) / (24 * G\<^sup>2)"
    by (rule qs_average[OF assms(1) meD meX iD iX assms(9)])
  also have "\<dots> = (8 + pi\<^sup>2) * (sq\<^sup>2 + sm\<^sup>2) / (96 * G\<^sup>2)"
    unfolding ED EX using assms(9) by (simp add: field_simps)
  finally show ?thesis .
qed

end
