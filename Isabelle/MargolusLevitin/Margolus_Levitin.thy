(*  Title:      Margolus_Levitin.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín
*)

section \<open>The Margolus--Levitin quantum speed limit and an \<open>L\<^sup>1\<close> Mandelstam--Tamm bound\<close>

theory Margolus_Levitin
  imports "HOL-Analysis.Analysis"
begin

text \<open>
  Let a finite family of weights \<open>p\<^sub>n \<ge> 0\<close> with \<open>\<Sum> p\<^sub>n = 1\<close> sit on energies \<open>E\<^sub>n\<close>, and let
  \<open>S(\<tau>) = \<Sum> p\<^sub>n e\<^sup>-\<^sup>i\<^sup>E\<^sup>n\<^sup>\<tau>\<close> be the autocorrelation (\<open>\<hbar> = 1\<close>). We prove two orthogonalisation-time bounds:
  \<^item> Margolus--Levitin: if \<open>E\<^sub>n \<ge> 0\<close> and \<open>S(\<tau>) = 0\<close> with \<open>\<tau> \<ge> 0\<close>, then \<open>\<pi> \<le> 2 \<langle>E\<rangle> \<tau>\<close>, where
    \<open>\<langle>E\<rangle> = \<Sum> p\<^sub>n E\<^sub>n\<close>;
  \<^item> Mandelstam--Tamm, \<open>L\<^sup>1\<close> form: if \<open>S(\<tau>) = 0\<close> with \<open>\<tau> \<ge> 0\<close>, then \<open>1 \<le> D\<^sub>1 \<tau>\<close>, where
    \<open>D\<^sub>1 = \<Sum> p\<^sub>n |E\<^sub>n - \<bar>E\<bar>|\<close> for an arbitrary reference energy \<open>\<bar>E\<bar>\<close>.

  The Margolus--Levitin proof rests on the cosine inequality
  \<open>cos x \<ge> 1 - (2/\<pi>)(x + sin x)\<close> for \<open>x \<ge> 0\<close>, proved by following the sign of the derivative of
  \<open>cos x - 1 + (2/\<pi>)(x + sin x)\<close>, which equals \<open>2 cos (x/2) ((2/\<pi>) cos (x/2) - sin (x/2))\<close>. The
  Mandelstam--Tamm bound uses \<open>1 - cos x \<le> |x|\<close>. Orthogonality is stated through the real and imaginary parts
  of \<open>S(\<tau>)\<close>, with a corollary in complex form.

  Cited result: C. Marín, \emph{The Clock That Never Ticks}, Zenodo, Theorem 3.
\<close>

subsection \<open>The cosine inequality\<close>

text \<open>The half-angle phase \<open>z\<^sub>0 = arctan (2/\<pi>)\<close>: the sign of \<open>(2/\<pi>) cos z - sin z\<close> changes there.\<close>

lemma phase_facts:
  defines "z0 \<equiv> arctan (2 / pi)"
  shows "0 \<le> z0" "z0 < pi / 2" "sin z0 = 2 / pi * cos z0"
proof -
  have c0: "0 < 2 / pi" using pi_gt_zero by simp
  show "0 \<le> z0"
    unfolding z0_def using arctan_monotone'[of 0 "2 / pi"] c0 by simp
  show "z0 < pi / 2"
    unfolding z0_def by (rule arctan_ubound)
  have lb: "- (pi / 2) < z0" unfolding z0_def by (rule arctan_lbound)
  have "0 < cos z0"
    by (rule cos_gt_zero_pi) (use lb \<open>z0 < pi / 2\<close> in auto)
  moreover have "tan z0 = 2 / pi" unfolding z0_def by (rule tan_arctan)
  ultimately show "sin z0 = 2 / pi * cos z0"
    by (simp add: tan_def field_simps)
qed

lemma q_nonneg:
  assumes "0 \<le> z" "z \<le> arctan (2 / pi)"
  shows "0 \<le> 2 / pi * cos z - sin z"
proof -
  define z0 where "z0 = arctan (2 / pi)"
  have f: "0 \<le> z0" "z0 < pi / 2" "sin z0 = 2 / pi * cos z0"
    using phase_facts unfolding z0_def by simp_all
  have c0: "0 < 2 / pi" using pi_gt_zero by simp
  have zz: "z \<le> z0" using assms(2) unfolding z0_def .
  have "cos z0 \<le> cos z"
    by (rule cos_monotone_0_pi_le) (use assms(1) zz f in \<open>auto simp: pi_gt_zero\<close>)
  moreover have "sin z \<le> sin z0"
    by (rule sin_monotone_2pi_le) (use assms(1) zz f in \<open>auto simp: pi_gt_zero\<close>)
  ultimately have "2 / pi * cos z0 \<le> 2 / pi * cos z" "sin z \<le> 2 / pi * cos z0"
    using mult_left_mono[OF _ c0[THEN less_imp_le]] f(3) by auto
  then show ?thesis by linarith
qed

lemma q_nonpos:
  assumes "arctan (2 / pi) \<le> z" "z \<le> pi / 2"
  shows "2 / pi * cos z - sin z \<le> 0"
proof -
  define z0 where "z0 = arctan (2 / pi)"
  have f: "0 \<le> z0" "z0 < pi / 2" "sin z0 = 2 / pi * cos z0"
    using phase_facts unfolding z0_def by simp_all
  have c0: "0 < 2 / pi" using pi_gt_zero by simp
  have zz: "z0 \<le> z" using assms(1) unfolding z0_def .
  have "cos z \<le> cos z0"
    by (rule cos_monotone_0_pi_le) (use zz f assms(2) in \<open>auto simp: pi_gt_zero\<close>)
  moreover have "sin z0 \<le> sin z"
    by (rule sin_monotone_2pi_le) (use zz f assms(2) in \<open>auto simp: pi_gt_zero\<close>)
  ultimately have "2 / pi * cos z \<le> 2 / pi * cos z0"
    using mult_left_mono[OF _ c0[THEN less_imp_le]] by blast
  then show ?thesis using f(3) \<open>sin z0 \<le> sin z\<close> by linarith
qed

definition ml_aux :: "real \<Rightarrow> real" where
  "ml_aux y = cos y - 1 + 2 / pi * (y + sin y)"

lemma ml_aux_deriv:
  "DERIV ml_aux y :> - sin y + 2 / pi * (1 + cos y)"
  unfolding ml_aux_def
  by (rule DERIV_cong) (auto intro!: derivative_eq_intros)

lemma ml_aux_deriv_factor:
  "- sin y + 2 / pi * (1 + cos y)
     = 2 * cos (y / 2) * (2 / pi * cos (y / 2) - sin (y / 2))"
proof -
  have s: "sin y = 2 * sin (y / 2) * cos (y / 2)"
    using sin_double[of "y / 2"] by simp
  have c: "cos y = 2 * (cos (y / 2))\<^sup>2 - 1"
    using cos_double_cos[of "y / 2"] by simp
  show ?thesis by (simp add: s c algebra_simps power2_eq_square)
qed

lemma ml_aux_zero: "ml_aux 0 = 0"
  by (simp add: ml_aux_def)

lemma ml_aux_pi: "ml_aux pi = 0"
  using pi_gt_zero by (simp add: ml_aux_def)

lemma ml_aux_nonneg_core:
  assumes "0 \<le> x" "x \<le> pi"
  shows "0 \<le> ml_aux x"
proof -
  define z0 where "z0 = arctan (2 / pi)"
  have cos_half: "\<And>y. 0 \<le> y \<Longrightarrow> y \<le> pi \<Longrightarrow> 0 \<le> cos (y / 2)"
    by (rule cos_ge_zero) (auto simp: pi_gt_zero)
  show ?thesis
  proof (cases "x \<le> 2 * z0")
    case True
    have "ml_aux 0 \<le> ml_aux x"
    proof (rule DERIV_nonneg_imp_nondecreasing[where a = 0 and b = x and f = ml_aux])
      show "0 \<le> x" by (rule assms(1))
      fix y assume ya: "0 \<le> y" and yb: "y \<le> x"
      then have y: "0 \<le> y \<and> y \<le> x" by simp
      have "0 \<le> 2 * cos (y / 2) * (2 / pi * cos (y / 2) - sin (y / 2))"
      proof (rule mult_nonneg_nonneg)
        show "0 \<le> 2 * cos (y / 2)"
        proof -
          have "y \<le> pi" using y assms(2) by linarith
          then show ?thesis using cos_half[of y] y by simp
        qed
        show "0 \<le> 2 / pi * cos (y / 2) - sin (y / 2)"
        proof (rule q_nonneg)
          show "0 \<le> y / 2" using y by simp
          show "y / 2 \<le> arctan (2 / pi)" using y True z0_def by linarith
        qed
      qed
      then show "\<exists>d. DERIV ml_aux y :> d \<and> 0 \<le> d"
        using ml_aux_deriv[of y] ml_aux_deriv_factor[of y] by metis
    qed
    then show ?thesis using ml_aux_zero by simp
  next
    case False
    have "(\<lambda>y. - ml_aux y) x \<le> (\<lambda>y. - ml_aux y) pi"
    proof (rule DERIV_nonneg_imp_nondecreasing[OF assms(2)])
      fix y assume ya: "x \<le> y" and yb: "y \<le> pi"
      then have y: "x \<le> y \<and> y \<le> pi" by simp
      have y0: "0 \<le> y" using y assms(1) by simp
      have "2 * cos (y / 2) * (2 / pi * cos (y / 2) - sin (y / 2)) \<le> 0"
      proof (rule mult_nonneg_nonpos)
        show "0 \<le> 2 * cos (y / 2)"
        proof -
          have "y \<le> pi" using y by simp
          then show ?thesis using cos_half[of y] y0 by simp
        qed
        show "2 / pi * cos (y / 2) - sin (y / 2) \<le> 0"
        proof (rule q_nonpos)
          show "arctan (2 / pi) \<le> y / 2" using y False z0_def by linarith
          show "y / 2 \<le> pi / 2" using y by simp
        qed
      qed
      then have d2: "0 \<le> - (- sin y + 2 / pi * (1 + cos y))"
        using ml_aux_deriv_factor[of y] by linarith
      have d1: "DERIV (\<lambda>y. - ml_aux y) y :> - (- sin y + 2 / pi * (1 + cos y))"
        by (rule DERIV_minus[OF ml_aux_deriv])
      show "\<exists>d. DERIV (\<lambda>y. - ml_aux y) y :> d \<and> 0 \<le> d"
        by (rule exI[of _ "- (- sin y + 2 / pi * (1 + cos y))"], rule conjI, rule d1, rule d2)
    qed
    then show ?thesis using ml_aux_pi by simp
  qed
qed

lemma ml_aux_nonneg_tail:
  assumes "pi \<le> x"
  shows "0 \<le> ml_aux x"
proof -
  have "(\<lambda>y. y + sin y) pi \<le> (\<lambda>y. y + sin y) x"
  proof (rule DERIV_nonneg_imp_nondecreasing[where a = pi and b = x and f = "\<lambda>y. y + sin y"])
    show "pi \<le> x" by (rule assms)
    fix y :: real assume "pi \<le> y" "y \<le> x"
    have d1: "DERIV (\<lambda>y. y + sin y) y :> 1 + cos y"
      by (rule DERIV_cong) (auto intro!: derivative_eq_intros)
    have d2: "0 \<le> 1 + cos y" using cos_ge_minus_one[of y] by linarith
    show "\<exists>d. DERIV (\<lambda>y. y + sin y) y :> d \<and> 0 \<le> d"
      using d1 d2 by metis
  qed
  then have h: "pi \<le> x + sin x" by simp
  have "2 \<le> 2 / pi * (x + sin x)"
  proof -
    have "2 = 2 / pi * pi" using pi_gt_zero by simp
    also have "\<dots> \<le> 2 / pi * (x + sin x)"
      by (rule mult_left_mono) (use h pi_gt_zero in simp_all)
    finally show ?thesis .
  qed
  moreover have "- 1 \<le> cos x" by (rule cos_ge_minus_one)
  ultimately show ?thesis unfolding ml_aux_def by linarith
qed

text \<open>The Margolus--Levitin cosine inequality.\<close>

theorem one_sub_le_cos:
  assumes "0 \<le> x"
  shows "1 - 2 / pi * (x + sin x) \<le> cos x"
proof -
  have "0 \<le> ml_aux x"
  proof (cases "x \<le> pi")
    case True then show ?thesis by (rule ml_aux_nonneg_core[OF assms])
  next
    case False then show ?thesis by (intro ml_aux_nonneg_tail) simp
  qed
  then show ?thesis unfolding ml_aux_def by linarith
qed

subsection \<open>The Margolus--Levitin theorem\<close>

theorem margolus_levitin:
  fixes p E :: "'a \<Rightarrow> real" and I :: "'a set" and Ebar \<tau> :: real
  assumes fin: "finite I"
    and p0: "\<And>n. n \<in> I \<Longrightarrow> 0 \<le> p n"
    and E0: "\<And>n. n \<in> I \<Longrightarrow> 0 \<le> E n"
    and t0: "0 \<le> \<tau>"
    and psum: "(\<Sum>n\<in>I. p n) = 1"
    and mean: "Ebar = (\<Sum>n\<in>I. p n * E n)"
    and re0: "(\<Sum>n\<in>I. p n * cos (E n * \<tau>)) = 0"
    and im0: "(\<Sum>n\<in>I. p n * sin (E n * \<tau>)) = 0"
  shows "pi \<le> 2 * Ebar * \<tau>"
proof -
  define c where "c = 2 / pi"
  have termwise: "\<And>n. n \<in> I \<Longrightarrow>
      p n * (1 - c * (E n * \<tau> + sin (E n * \<tau>))) \<le> p n * cos (E n * \<tau>)"
  proof -
    fix n assume n: "n \<in> I"
    have "1 - c * (E n * \<tau> + sin (E n * \<tau>)) \<le> cos (E n * \<tau>)"
      unfolding c_def by (rule one_sub_le_cos) (use E0[OF n] t0 in simp)
    then show "p n * (1 - c * (E n * \<tau> + sin (E n * \<tau>))) \<le> p n * cos (E n * \<tau>)"
      by (rule mult_left_mono) (rule p0[OF n])
  qed
  have lhs: "(\<Sum>n\<in>I. p n * (1 - c * (E n * \<tau> + sin (E n * \<tau>))))
      = (\<Sum>n\<in>I. p n) - c * ((\<Sum>n\<in>I. p n * E n) * \<tau> + (\<Sum>n\<in>I. p n * sin (E n * \<tau>)))"
  proof -
    have "\<And>n. p n * (1 - c * (E n * \<tau> + sin (E n * \<tau>)))
        = p n - c * ((p n * E n) * \<tau> + p n * sin (E n * \<tau>))"
      by (simp add: algebra_simps)
    then show ?thesis
      by (simp add: sum_subtractf sum.distrib sum_distrib_left[symmetric] sum_distrib_right[symmetric])
  qed
  have "(\<Sum>n\<in>I. p n * (1 - c * (E n * \<tau> + sin (E n * \<tau>)))) \<le> (\<Sum>n\<in>I. p n * cos (E n * \<tau>))"
    by (rule sum_mono) (rule termwise)
  then have "1 - c * (Ebar * \<tau>) \<le> 0"
    using lhs psum mean im0 re0 by simp
  then have "1 \<le> 2 * (Ebar * \<tau>) / pi" unfolding c_def by simp
  then have "pi * 1 \<le> pi * (2 * (Ebar * \<tau>) / pi)"
    by (rule mult_left_mono) (use pi_gt_zero in simp)
  then show ?thesis using pi_gt_zero by simp
qed

subsection \<open>The \<open>L\<^sup>1\<close> Mandelstam--Tamm bound\<close>

lemma one_minus_cos_le_abs: "1 - cos (x::real) \<le> \<bar>x\<bar>"
proof -
  have "cos x = 1 - 2 * (sin (x / 2))\<^sup>2"
    using cos_double_sin[of "x / 2"] by simp
  then have e: "1 - cos x = 2 * (sin (x / 2))\<^sup>2" by simp
  have s1: "\<bar>sin (x / 2)\<bar> \<le> 1" by (simp add: abs_le_iff)
  have s2: "\<bar>sin (x / 2)\<bar> \<le> \<bar>x / 2\<bar>" by (rule abs_sin_x_le_abs_x)
  have "(sin (x / 2))\<^sup>2 = \<bar>sin (x / 2)\<bar> * \<bar>sin (x / 2)\<bar>"
    by (simp add: power2_eq_square)
  also have "\<dots> \<le> \<bar>sin (x / 2)\<bar> * 1"
    by (rule mult_left_mono) (use s1 in simp_all)
  finally have "(sin (x / 2))\<^sup>2 \<le> \<bar>sin (x / 2)\<bar>" by simp
  with e s2 show ?thesis by simp
qed

theorem mandelstam_tamm_L1:
  fixes p E :: "'a \<Rightarrow> real" and I :: "'a set" and Ebar D1 \<tau> :: real
  assumes fin: "finite I"
    and p0: "\<And>n. n \<in> I \<Longrightarrow> 0 \<le> p n"
    and t0: "0 \<le> \<tau>"
    and psum: "(\<Sum>n\<in>I. p n) = 1"
    and dev: "D1 = (\<Sum>n\<in>I. p n * \<bar>E n - Ebar\<bar>)"
    and re0: "(\<Sum>n\<in>I. p n * cos (E n * \<tau>)) = 0"
    and im0: "(\<Sum>n\<in>I. p n * sin (E n * \<tau>)) = 0"
  shows "1 \<le> D1 * \<tau>"
proof -
  \<comment> \<open>the autocorrelation centred at @{term Ebar} also vanishes\<close>
  have cen: "(\<Sum>n\<in>I. p n * cos ((E n - Ebar) * \<tau>)) = 0"
  proof -
    have pw: "\<And>n. p n * cos ((E n - Ebar) * \<tau>)
        = cos (Ebar * \<tau>) * (p n * cos (E n * \<tau>)) + sin (Ebar * \<tau>) * (p n * sin (E n * \<tau>))"
    proof -
      fix n
      have "(E n - Ebar) * \<tau> = E n * \<tau> - Ebar * \<tau>" by (simp add: algebra_simps)
      then show "p n * cos ((E n - Ebar) * \<tau>)
        = cos (Ebar * \<tau>) * (p n * cos (E n * \<tau>)) + sin (Ebar * \<tau>) * (p n * sin (E n * \<tau>))"
        by (simp add: cos_diff algebra_simps)
    qed
    have "(\<Sum>n\<in>I. p n * cos ((E n - Ebar) * \<tau>))
        = (\<Sum>n\<in>I. cos (Ebar * \<tau>) * (p n * cos (E n * \<tau>))
            + sin (Ebar * \<tau>) * (p n * sin (E n * \<tau>)))"
      by (rule sum.cong) (simp_all add: pw)
    also have "\<dots> = cos (Ebar * \<tau>) * (\<Sum>n\<in>I. p n * cos (E n * \<tau>))
        + sin (Ebar * \<tau>) * (\<Sum>n\<in>I. p n * sin (E n * \<tau>))"
      by (simp add: sum.distrib sum_distrib_left)
    also have "\<dots> = 0" by (simp add: re0 im0)
    finally show ?thesis .
  qed
  have termwise: "\<And>n. n \<in> I \<Longrightarrow>
      p n * (1 - cos ((E n - Ebar) * \<tau>)) \<le> p n * (\<bar>E n - Ebar\<bar> * \<tau>)"
  proof -
    fix n assume n: "n \<in> I"
    have "1 - cos ((E n - Ebar) * \<tau>) \<le> \<bar>(E n - Ebar) * \<tau>\<bar>" by (rule one_minus_cos_le_abs)
    also have "\<dots> = \<bar>E n - Ebar\<bar> * \<tau>" using t0 by (simp add: abs_mult)
    finally show "p n * (1 - cos ((E n - Ebar) * \<tau>)) \<le> p n * (\<bar>E n - Ebar\<bar> * \<tau>)"
      by (rule mult_left_mono) (rule p0[OF n])
  qed
  have h1: "(\<Sum>n\<in>I. p n * (1 - cos ((E n - Ebar) * \<tau>))) = 1"
    by (simp add: right_diff_distrib sum_subtractf psum cen)
  have h2: "(\<Sum>n\<in>I. p n * (1 - cos ((E n - Ebar) * \<tau>))) \<le> (\<Sum>n\<in>I. p n * (\<bar>E n - Ebar\<bar> * \<tau>))"
    by (rule sum_mono) (rule termwise)
  have "1 \<le> (\<Sum>n\<in>I. p n * (\<bar>E n - Ebar\<bar> * \<tau>))" using h1 h2 by linarith
  moreover have "(\<Sum>n\<in>I. p n * (\<bar>E n - Ebar\<bar> * \<tau>)) = D1 * \<tau>"
    by (simp add: dev sum_distrib_right mult.assoc)
  ultimately show ?thesis by simp
qed

subsection \<open>The complex form of the orthogonality hypothesis\<close>

text \<open>
  With \<open>S(\<tau>) = \<Sum> p\<^sub>n exp (-i E\<^sub>n \<tau>)\<close>, the condition \<open>S(\<tau>) = 0\<close> is equivalent to the vanishing of
  the real sums used above.
\<close>

lemma re_term: "Re (complex_of_real p * exp (complex_of_real y * \<i>)) = p * cos y"
  by (simp add: Re_exp Im_exp)

lemma im_term: "Im (complex_of_real p * exp (complex_of_real y * \<i>)) = p * sin y"
  by (simp add: Re_exp Im_exp)

lemma autocorr_zero_real:
  fixes p E :: "'a \<Rightarrow> real"
  assumes "(\<Sum>n\<in>I. complex_of_real (p n) * exp (complex_of_real (- (E n * \<tau>)) * \<i>)) = 0"
  shows "(\<Sum>n\<in>I. p n * cos (E n * \<tau>)) = 0" "(\<Sum>n\<in>I. p n * sin (E n * \<tau>)) = 0"
proof -
  have re: "\<And>n. Re (complex_of_real (p n) * exp (complex_of_real (- (E n * \<tau>)) * \<i>))
      = p n * cos (E n * \<tau>)"
    by (simp only: re_term cos_minus)
  have im: "\<And>n. Im (complex_of_real (p n) * exp (complex_of_real (- (E n * \<tau>)) * \<i>))
      = - (p n * sin (E n * \<tau>))"
    by (simp only: im_term sin_minus mult_minus_right)
  have "Re (\<Sum>n\<in>I. complex_of_real (p n) * exp (complex_of_real (- (E n * \<tau>)) * \<i>))
      = (\<Sum>n\<in>I. p n * cos (E n * \<tau>))"
    by (simp only: Re_sum re)
  moreover have "Re (\<Sum>n\<in>I. complex_of_real (p n) * exp (complex_of_real (- (E n * \<tau>)) * \<i>)) = 0"
    by (simp only: assms zero_complex.simps)
  ultimately show "(\<Sum>n\<in>I. p n * cos (E n * \<tau>)) = 0" by (rule trans[OF sym])
  have "Im (\<Sum>n\<in>I. complex_of_real (p n) * exp (complex_of_real (- (E n * \<tau>)) * \<i>))
      = - (\<Sum>n\<in>I. p n * sin (E n * \<tau>))"
    by (simp only: Im_sum im sum_negf)
  moreover have "Im (\<Sum>n\<in>I. complex_of_real (p n) * exp (complex_of_real (- (E n * \<tau>)) * \<i>)) = 0"
    by (simp only: assms zero_complex.simps)
  ultimately show "(\<Sum>n\<in>I. p n * sin (E n * \<tau>)) = 0" by linarith
qed

corollary margolus_levitin_complex:
  fixes p E :: "'a \<Rightarrow> real" and I :: "'a set" and Ebar \<tau> :: real
  assumes "finite I" "\<And>n. n \<in> I \<Longrightarrow> 0 \<le> p n" "\<And>n. n \<in> I \<Longrightarrow> 0 \<le> E n" "0 \<le> \<tau>"
    and "(\<Sum>n\<in>I. p n) = 1" "Ebar = (\<Sum>n\<in>I. p n * E n)"
    and "(\<Sum>n\<in>I. complex_of_real (p n) * exp (complex_of_real (- (E n * \<tau>)) * \<i>)) = 0"
  shows "pi \<le> 2 * Ebar * \<tau>"
  using autocorr_zero_real[OF assms(7)] assms(1-6)
  by (intro margolus_levitin) auto

corollary mandelstam_tamm_L1_complex:
  fixes p E :: "'a \<Rightarrow> real" and I :: "'a set" and Ebar D1 \<tau> :: real
  assumes "finite I" "\<And>n. n \<in> I \<Longrightarrow> 0 \<le> p n" "0 \<le> \<tau>" "(\<Sum>n\<in>I. p n) = 1"
    and "D1 = (\<Sum>n\<in>I. p n * \<bar>E n - Ebar\<bar>)"
    and "(\<Sum>n\<in>I. complex_of_real (p n) * exp (complex_of_real (- (E n * \<tau>)) * \<i>)) = 0"
  shows "1 \<le> D1 * \<tau>"
  using autocorr_zero_real[OF assms(6)] assms(1-5)
  by (intro mandelstam_tamm_L1) auto

end
