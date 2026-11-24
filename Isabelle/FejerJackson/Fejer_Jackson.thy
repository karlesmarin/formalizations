(*  Title:      Fejer_Jackson.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín
*)

section \<open>The Fejér--Jackson inequality and a lower bound for the Clausen function\<close>

theory Fejer_Jackson
  imports "HOL-Analysis.Analysis"
begin

text \<open>
  We prove that every partial sum \<open>\<Sum>\<^sub>{k=1..M} sin (k\<theta>) / k\<close> with \<open>M \<ge> 1\<close> is strictly positive on
  \<open>(0, \<pi>)\<close> (Fejér 1910, Jackson 1911), and that the Clausen function \<open>Cl\<^sub>2 \<theta> = \<Sum>\<^sub>{k\<ge>1} sin (k\<theta>) / k\<^sup>2\<close>
  satisfies \<open>Cl\<^sub>2 \<theta> \<ge> sin \<theta> / 2\<close> there.

  The first part follows the classical interior-minimum argument: the derivative is the shifted Dirichlet
  kernel, handled without division through the telescoping identity
  \<open>2 sin (\<theta>/2) \<Sum>\<^sub>{k=1..M} cos (k\<theta>) = sin ((M + 1/2) \<theta>) - sin (\<theta>/2)\<close>. At an interior minimum the
  derivative vanishes, which forces \<open>sin (M \<theta>) \<ge> 0\<close>; hence the minimum is at least the previous partial
  sum, positive by induction, while the boundary values are \<open>0\<close>. The second part is Abel summation.

  Cited result: C. Marín, \emph{The Clock That Never Ticks}, Zenodo, Theorem 2.
\<close>

subsection \<open>The partial sums and their derivative\<close>

definition fj :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "fj M \<theta> = (\<Sum>k<M. sin (real (Suc k) * \<theta>) / real (Suc k))"

lemma fj_zero [simp]: "fj M 0 = 0"
  by (simp add: fj_def)

lemma fj_pi [simp]: "fj M pi = 0"
  unfolding fj_def
proof (rule sum.neutral, intro ballI)
  fix k :: nat
  have "sin (real (Suc k) * pi) = 0" by (rule sin_npi)
  then show "sin (real (Suc k) * pi) / real (Suc k) = 0" by simp
qed

lemma fj_Suc: "fj (Suc M) \<theta> = fj M \<theta> + sin (real (Suc M) * \<theta>) / real (Suc M)"
  by (simp add: fj_def)

lemma DERIV_term:
  "((\<lambda>x. sin (real (Suc k) * x) / real (Suc k)) has_field_derivative
        cos (real (Suc k) * \<theta>)) (at \<theta>)"
proof -
  have "((\<lambda>x. sin (real (Suc k) * x)) has_field_derivative cos (real (Suc k) * \<theta>) * real (Suc k)) (at \<theta>)"
    by (rule DERIV_chain2[OF DERIV_sin DERIV_cmult_Id])
  then have "((\<lambda>x. sin (real (Suc k) * x) / real (Suc k)) has_field_derivative
        cos (real (Suc k) * \<theta>) * real (Suc k) / real (Suc k)) (at \<theta>)"
    by (rule DERIV_cdivide)
  then show ?thesis by simp
qed

lemma DERIV_fj:
  "((fj M) has_field_derivative (\<Sum>k<M. cos (real (Suc k) * \<theta>))) (at \<theta>)"
proof (induction M)
  case 0
  have "fj 0 = (\<lambda>x. 0)" by (rule ext) (simp add: fj_def)
  then show ?case by simp
next
  case (Suc M)
  have "fj (Suc M) = (\<lambda>x. fj M x + sin (real (Suc M) * x) / real (Suc M))"
    by (rule ext) (rule fj_Suc)
  moreover have "((\<lambda>x. fj M x + sin (real (Suc M) * x) / real (Suc M)) has_field_derivative
      (\<Sum>k<M. cos (real (Suc k) * \<theta>)) + cos (real (Suc M) * \<theta>)) (at \<theta>)"
    by (rule DERIV_add[OF Suc.IH DERIV_term])
  ultimately show ?case by simp
qed

lemma continuous_fj: "continuous_on A (fj M)"
  by (rule continuous_at_imp_continuous_on) (auto intro: DERIV_isCont DERIV_fj)

subsection \<open>The division-free Dirichlet kernel identity\<close>

lemma dirichlet_telescope:
  "2 * sin (\<theta> / 2) * (\<Sum>k<M. cos (real (Suc k) * \<theta>)) = sin ((real M + 1 / 2) * \<theta>) - sin (\<theta> / 2)"
proof (induction M)
  case 0
  then show ?case by simp
next
  case (Suc M)
  have e1: "(real (Suc M) + 1 / 2) * \<theta> = real (Suc M) * \<theta> + \<theta> / 2"
    by (simp add: algebra_simps)
  have e2: "(real M + 1 / 2) * \<theta> = real (Suc M) * \<theta> - \<theta> / 2"
    by (simp add: algebra_simps)
  have "2 * sin (\<theta> / 2) * (\<Sum>k<Suc M. cos (real (Suc k) * \<theta>))
      = 2 * sin (\<theta> / 2) * (\<Sum>k<M. cos (real (Suc k) * \<theta>)) + 2 * sin (\<theta> / 2) * cos (real (Suc M) * \<theta>)"
    by (simp add: algebra_simps)
  also have "\<dots> = sin ((real M + 1 / 2) * \<theta>) - sin (\<theta> / 2) + 2 * sin (\<theta> / 2) * cos (real (Suc M) * \<theta>)"
    using Suc.IH by simp
  also have "\<dots> = sin ((real (Suc M) + 1 / 2) * \<theta>) - sin (\<theta> / 2)"
    by (simp only: e1 e2 sin_add sin_diff) (simp add: algebra_simps)
  finally show ?case .
qed

subsection \<open>The critical-point dichotomy\<close>

lemma sin_last_nonneg_at_local_min:
  assumes th: "0 < \<theta>" "\<theta> < pi"
    and min: "\<forall>y. \<bar>\<theta> - y\<bar> < d \<longrightarrow> fj M \<theta> \<le> fj M y" and d: "0 < d"
  shows "0 \<le> sin (real M * \<theta>)"
proof -
  have crit: "(\<Sum>k<M. cos (real (Suc k) * \<theta>)) = 0"
    using DERIV_local_min[OF DERIV_fj d min] by simp
  have tel: "sin ((real M + 1 / 2) * \<theta>) - sin (\<theta> / 2) = 0"
    using dirichlet_telescope[of \<theta> M] crit by simp
  have fact: "2 * sin (real M * \<theta> / 2) * cos ((real M + 1) * \<theta> / 2) = 0"
  proof -
    have "sin ((real M + 1 / 2) * \<theta>) - sin (\<theta> / 2)
        = 2 * sin (((real M + 1 / 2) * \<theta> - \<theta> / 2) / 2) * cos (((real M + 1 / 2) * \<theta> + \<theta> / 2) / 2)"
      by (rule sin_diff_sin)
    moreover have "((real M + 1 / 2) * \<theta> - \<theta> / 2) / 2 = real M * \<theta> / 2"
      by (simp add: algebra_simps)
    moreover have "((real M + 1 / 2) * \<theta> + \<theta> / 2) / 2 = (real M + 1) * \<theta> / 2"
      by (simp add: algebra_simps)
    ultimately show ?thesis using tel by simp
  qed
  have sinth: "0 < sin \<theta>" using th by (intro sin_gt_zero)
  from fact consider "sin (real M * \<theta> / 2) = 0" | "cos ((real M + 1) * \<theta> / 2) = 0" by auto
  then show ?thesis
  proof cases
    case 1
    have "sin (real M * \<theta>) = 2 * sin (real M * \<theta> / 2) * cos (real M * \<theta> / 2)"
      using sin_double[of "real M * \<theta> / 2"] by simp
    then show ?thesis using 1 by simp
  next
    case 2
    define y where "y = (real M + 1) * \<theta>"
    have c0: "cos (y / 2) = 0" using 2 by (simp add: y_def)
    have s2: "(sin (y / 2))\<^sup>2 = 1" using sin_cos_squared_add[of "y / 2"] c0 by simp
    have cy: "cos y = - 1" using cos_double[of "y / 2"] c0 s2 by simp
    have sy: "sin y = 0" using sin_cos_squared_add[of y] cy by simp
    have "real M * \<theta> = y - \<theta>" unfolding y_def by (simp add: algebra_simps)
    then have "sin (real M * \<theta>) = sin y * cos \<theta> - cos y * sin \<theta>"
      by (simp add: sin_diff)
    then show ?thesis using sy cy sinth by simp
  qed
qed

subsection \<open>The Fejér--Jackson inequality\<close>

theorem fejer_jackson:
  assumes "0 < \<theta>" "\<theta> < pi"
  shows "0 < fj (Suc M) \<theta>"
  using assms
proof (induction M arbitrary: \<theta>)
  case 0
  then show ?case by (simp add: fj_def sin_gt_zero)
next
  case (Suc N)
  define K where "K = Suc (Suc N)"
  \<comment> \<open>an interior point at which the sum is minimal on \<open>[0, \<pi>]\<close> has positive value\<close>
  have key: "0 < fj K x"
    if x: "0 < x" "x < pi" and mn: "\<forall>y\<in>{0..pi}. fj K x \<le> fj K y" for x
  proof -
    define d where "d = min x (pi - x)"
    have d0: "0 < d" using x by (simp add: d_def)
    have loc: "\<forall>y. \<bar>x - y\<bar> < d \<longrightarrow> fj K x \<le> fj K y"
    proof (intro allI impI)
      fix y assume "\<bar>x - y\<bar> < d"
      then have "0 \<le> y" "y \<le> pi" by (auto simp: d_def)
      then show "fj K x \<le> fj K y" using mn by auto
    qed
    have last: "0 \<le> sin (real K * x)"
      by (rule sin_last_nonneg_at_local_min[OF x loc d0])
    have "0 < fj (Suc N) x" using Suc.IH x by blast
    moreover have "0 \<le> sin (real K * x) / real K" using last by (simp add: K_def)
    ultimately show ?thesis by (simp add: K_def fj_Suc)
  qed
  show ?case
  proof (rule ccontr)
    assume "\<not> 0 < fj (Suc (Suc N)) \<theta>"
    then have neg: "fj K \<theta> \<le> 0" by (simp add: K_def)
    obtain s where s: "s \<in> {0..pi}" and ms: "\<forall>y\<in>{0..pi}. fj K s \<le> fj K y"
      using continuous_attains_inf[OF compact_Icc _ continuous_fj[of "{0..pi}" K]] pi_gt_zero by auto
    have th: "\<theta> \<in> {0..pi}" using Suc.prems by auto
    have sle: "fj K s \<le> fj K \<theta>" using ms th by blast
    show False
    proof (cases "0 < s \<and> s < pi")
      case True
      then have "0 < fj K s" using key[of s] ms by blast
      with sle neg show False by linarith
    next
      case False
      with s have "s = 0 \<or> s = pi" by auto
      then have z: "fj K s = 0" by auto
      have "\<forall>y\<in>{0..pi}. fj K \<theta> \<le> fj K y" using z neg ms by force
      from key[OF Suc.prems this] neg show False by linarith
    qed
  qed
qed

subsection \<open>The Clausen function and the bound \<open>Cl\<^sub>2 \<theta> \<ge> sin \<theta> / 2\<close>\<close>

definition Cl2 :: "real \<Rightarrow> real" where
  "Cl2 \<theta> = (\<Sum>k. sin (real (Suc k) * \<theta>) / (real (Suc k))\<^sup>2)"

definition clpart :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "clpart M \<theta> = (\<Sum>k<M. sin (real (Suc k) * \<theta>) / (real (Suc k))\<^sup>2)"

lemma summable_Cl2: "summable (\<lambda>k. sin (real (Suc k) * \<theta>) / (real (Suc k))\<^sup>2)"
proof (rule summable_comparison_test)
  show "summable (\<lambda>k. inverse (real (Suc k) ^ 2))"
  proof -
    have "summable (\<lambda>n. inverse (real n ^ 2))" by (rule inverse_power_summable) simp
    then show ?thesis by (subst summable_Suc_iff) simp
  qed
  show "\<exists>N. \<forall>n\<ge>N. norm (sin (real (Suc n) * \<theta>) / (real (Suc n))\<^sup>2) \<le> inverse (real (Suc n) ^ 2)"
  proof (intro exI[of _ 0] allI impI)
    fix n :: nat
    have "\<bar>sin (real (Suc n) * \<theta>)\<bar> \<le> 1" by simp
    then have "\<bar>sin (real (Suc n) * \<theta>)\<bar> / (real (Suc n))\<^sup>2 \<le> 1 / (real (Suc n))\<^sup>2"
      by (intro divide_right_mono) simp_all
    then show "norm (sin (real (Suc n) * \<theta>) / (real (Suc n))\<^sup>2) \<le> inverse (real (Suc n) ^ 2)"
      by (simp add: inverse_eq_divide)
  qed
qed

text \<open>Abel summation, in incremental form: \<open>clpart M \<theta> - fj M \<theta> / M\<close> grows by
  \<open>fj M \<theta> / (M (M+1))\<close> when \<open>M\<close> increases by one.\<close>

lemma abel_step:
  "clpart (Suc (Suc n)) \<theta> - fj (Suc (Suc n)) \<theta> / real (Suc (Suc n))
   = clpart (Suc n) \<theta> - fj (Suc n) \<theta> / real (Suc n)
     + fj (Suc n) \<theta> / (real (Suc n) * real (Suc (Suc n)))"
proof -
  define A where "A = fj (Suc n) \<theta>"
  define B where "B = clpart (Suc n) \<theta>"
  define t where "t = sin (real (Suc (Suc n)) * \<theta>)"
  have h1: "fj (Suc (Suc n)) \<theta> = A + t / real (Suc (Suc n))"
    by (simp add: fj_Suc A_def t_def)
  have h2: "clpart (Suc (Suc n)) \<theta> = B + t / (real (Suc (Suc n)))\<^sup>2"
    by (simp add: clpart_def B_def t_def)
  define u where "u = real (Suc n)"
  have u0: "u \<noteq> 0" by (simp add: u_def)
  have v: "real (Suc (Suc n)) = u + 1" by (simp add: u_def)
  have v0: "u + 1 \<noteq> 0" using u0 by (simp add: u_def)
  have "B + t / (u + 1)\<^sup>2 - (A + t / (u + 1)) / (u + 1) = B - A / u + A / (u * (u + 1))"
    using u0 v0 by (simp add: divide_simps power2_eq_square, algebra)
  then show ?thesis unfolding h1 h2 v u_def[symmetric] A_def[symmetric] B_def[symmetric] by simp
qed

lemma clpart_lower:
  assumes "0 < \<theta>" "\<theta> < pi"
  shows "sin \<theta> / 2 \<le> clpart (Suc (Suc n)) \<theta>"
proof -
  have sinth: "0 < sin \<theta>" using assms by (intro sin_gt_zero)
  have T: "sin \<theta> / 2 \<le> clpart (Suc (Suc n)) \<theta> - fj (Suc (Suc n)) \<theta> / real (Suc (Suc n))"
  proof (induction n)
    case 0
    have a: "clpart (Suc (Suc 0)) \<theta> - fj (Suc (Suc 0)) \<theta> / real (Suc (Suc 0))
        = clpart (Suc 0) \<theta> - fj (Suc 0) \<theta> / real (Suc 0)
          + fj (Suc 0) \<theta> / (real (Suc 0) * real (Suc (Suc 0)))"
      by (rule abel_step)
    have c: "clpart (Suc 0) \<theta> = sin \<theta>" "fj (Suc 0) \<theta> = sin \<theta>"
      by (simp_all add: clpart_def fj_def)
    show ?case using a c by simp
  next
    case (Suc n)
    have "0 \<le> fj (Suc (Suc n)) \<theta>" using fejer_jackson[OF assms, of "Suc n"] by simp
    then have "0 \<le> fj (Suc (Suc n)) \<theta> / (real (Suc (Suc n)) * real (Suc (Suc (Suc n))))"
      by simp
    then show ?case using Suc.IH abel_step[of "Suc n" \<theta>] by linarith
  qed
  have "0 \<le> fj (Suc (Suc n)) \<theta>" using fejer_jackson[OF assms, of "Suc n"] by simp
  then have "0 \<le> fj (Suc (Suc n)) \<theta> / real (Suc (Suc n))" by simp
  with T show ?thesis by linarith
qed

theorem Cl2_lower_bound:
  assumes "0 < \<theta>" "\<theta> < pi"
  shows "sin \<theta> / 2 \<le> Cl2 \<theta>"
proof -
  have lim: "(\<lambda>M. clpart M \<theta>) \<longlonglongrightarrow> Cl2 \<theta>"
    unfolding clpart_def Cl2_def by (rule summable_LIMSEQ[OF summable_Cl2])
  show ?thesis
  proof (rule LIMSEQ_le_const[OF lim])
    show "\<exists>N. \<forall>n\<ge>N. sin \<theta> / 2 \<le> clpart n \<theta>"
    proof (intro exI[of _ 2] allI impI)
      fix n :: nat assume "2 \<le> n"
      then obtain m where "n = 2 + m" using le_Suc_ex by blast
      then have "n = Suc (Suc m)" by simp
      then show "sin \<theta> / 2 \<le> clpart n \<theta>" using clpart_lower[OF assms, of m] by simp
    qed
  qed
qed

end
