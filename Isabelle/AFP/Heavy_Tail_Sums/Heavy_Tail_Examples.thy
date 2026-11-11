(*  Title:      Heavy_Tail_Examples.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

theory Heavy_Tail_Examples
  imports Heavy_Tail_Relations
begin

section \<open>The hypotheses are not vacuous: a Pareto variable\<close>

text \<open>The Pareto law of index \<open>\<alpha> > 0\<close> is built as the image of the uniform law on \<open>(0,1)\<close> under
  \<open>\<omega> \<mapsto> \<omega> powr (-1/\<alpha>)\<close>.  Its tail is \<open>x powr (-\<alpha>)\<close> for \<open>x \<ge> 1\<close> and \<open>1\<close> for \<open>x < 1\<close>.\<close>

definition unif01 :: "real measure" where "unif01 = uniform_measure lborel {0<..<1}"

definition par :: "real \<Rightarrow> real \<Rightarrow> real" where "par \<alpha> \<omega> = \<omega> powr (- 1 / \<alpha>)"

lemma unif01_prob: "prob_space unif01"
  unfolding unif01_def by (rule prob_space_uniform_measure) simp_all

lemma par_meas[measurable]: "par \<alpha> \<in> borel_measurable unif01"
  unfolding par_def unif01_def by simp

lemma unif01_sets[simp]: "sets unif01 = sets (borel :: real measure)"
  unfolding unif01_def by simp

lemma unif01_space[simp]: "space unif01 = UNIV"
  unfolding unif01_def by simp

lemma ennreal_div_one: "(a :: ennreal) / 1 = a"
  by (cases a rule: ennreal_cases)
     (simp_all add: divide_ennreal_def | simp_all add: divide_inverse | simp_all)

lemma par_gt_iff:
  fixes \<alpha> x \<omega> :: real
  assumes \<alpha>: "0 < \<alpha>" and x: "0 < x" and w: "0 < \<omega>"
  shows "x < par \<alpha> \<omega> \<longleftrightarrow> \<omega> < x powr (- \<alpha>)"
proof -
  define z where "z = par \<alpha> \<omega>"
  have zpos: "0 < z" unfolding z_def par_def using w by simp
  have wz: "\<omega> = z powr (- \<alpha>)"
    unfolding z_def par_def using w \<alpha> by (simp add: powr_powr)
  have na: "- \<alpha> < 0" using \<alpha> by simp
  have main: "x < z \<longleftrightarrow> \<omega> < x powr (- \<alpha>)"
  proof
    assume "x < z"
    hence "z powr (- \<alpha>) < x powr (- \<alpha>)" by (rule powr_less_mono2_neg[OF na x])
    thus "\<omega> < x powr (- \<alpha>)" using wz by linarith
  next
    assume h: "\<omega> < x powr (- \<alpha>)"
    show "x < z"
    proof (rule ccontr)
      assume "\<not> x < z"
      hence "z \<le> x" by simp
      hence "x powr (- \<alpha>) \<le> z powr (- \<alpha>)"
        using zpos na by (intro powr_mono2') simp_all
      thus False using h wz by linarith
    qed
  qed
  thus ?thesis unfolding z_def .
qed

lemma par_tail:
  fixes \<alpha> x :: real
  assumes \<alpha>: "0 < \<alpha>"
  shows "prob_space.prob unif01 {\<omega> \<in> space unif01. x < par \<alpha> \<omega>} = (if 1 \<le> x then x powr (- \<alpha>) else 1)"
proof -
  interpret U: prob_space unif01 by (rule unif01_prob)
  have Aset: "{\<omega> \<in> space unif01. x < par \<alpha> \<omega>} \<in> sets unif01" by measurable
  have e: "emeasure unif01 {\<omega> \<in> space unif01. x < par \<alpha> \<omega>}
      = emeasure lborel ({0<..<1} \<inter> {\<omega>. x < par \<alpha> \<omega>})"
    unfolding unif01_def using Aset
    by (simp add: unif01_def emeasure_uniform_measure ennreal_div_one)
  show ?thesis
  proof (cases "1 \<le> x")
    case True
    hence x0: "0 < x" by simp
    have t1: "x powr (- \<alpha>) \<le> 1"
    proof -
      have "x powr (- \<alpha>) = inverse (x powr \<alpha>)" by (simp add: powr_minus inverse_eq_divide)
      moreover have "1 \<le> x powr \<alpha>" using True \<alpha> by (intro ge_one_powr_ge_zero) simp_all
      ultimately show ?thesis by (simp add: inverse_le_1_iff)
    qed
    have t0: "0 < x powr (- \<alpha>)" using x0 by simp
    have "{0<..<1} \<inter> {\<omega>. x < par \<alpha> \<omega>} = {0<..<x powr (- \<alpha>)}"
    proof (rule set_eqI)
      fix \<omega> :: real
      show "\<omega> \<in> {0<..<1} \<inter> {\<omega>. x < par \<alpha> \<omega>} \<longleftrightarrow> \<omega> \<in> {0<..<x powr (- \<alpha>)}"
      proof (cases "0 < \<omega>")
        case True
        hence "x < par \<alpha> \<omega> \<longleftrightarrow> \<omega> < x powr (- \<alpha>)" by (rule par_gt_iff[OF \<alpha> x0])
        thus ?thesis using True t1 by auto
      next
        case False thus ?thesis by simp
      qed
    qed
    hence "emeasure unif01 {\<omega> \<in> space unif01. x < par \<alpha> \<omega>} = ennreal (x powr (- \<alpha>))"
      using e t0 by simp
    hence "ennreal (U.prob {\<omega> \<in> space unif01. x < par \<alpha> \<omega>}) = ennreal (x powr (- \<alpha>))"
      by (simp add: U.emeasure_eq_measure)
    hence "U.prob {\<omega> \<in> space unif01. x < par \<alpha> \<omega>} = x powr (- \<alpha>)"
      using t0 by (subst (asm) ennreal_inj) simp_all
    thus ?thesis using True by simp
  next
    case False
    hence xl: "x < 1" by simp
    have "{0<..<1} \<inter> {\<omega>. x < par \<alpha> \<omega>} = {0<..<1}"
    proof (rule set_eqI)
      fix \<omega> :: real
      show "\<omega> \<in> {0<..<1} \<inter> {\<omega>. x < par \<alpha> \<omega>} \<longleftrightarrow> \<omega> \<in> {0<..<1}"
      proof
        assume "\<omega> \<in> {0<..<1} \<inter> {\<omega>. x < par \<alpha> \<omega>}" thus "\<omega> \<in> {0<..<1}" by simp
      next
        assume w: "\<omega> \<in> {0<..<1}"
        have neg: "- 1 / \<alpha> < 0" using \<alpha> by (simp add: divide_neg_pos)
        have "1 powr (- 1 / \<alpha>) < \<omega> powr (- 1 / \<alpha>)"
          using w by (intro powr_less_mono2_neg[OF neg]) simp_all
        hence "1 < par \<alpha> \<omega>" unfolding par_def by simp
        thus "\<omega> \<in> {0<..<1} \<inter> {\<omega>. x < par \<alpha> \<omega>}" using w xl by simp
      qed
    qed
    hence "emeasure unif01 {\<omega> \<in> space unif01. x < par \<alpha> \<omega>} = 1" using e by simp
    hence "ennreal (U.prob {\<omega> \<in> space unif01. x < par \<alpha> \<omega>}) = ennreal 1"
      by (simp add: U.emeasure_eq_measure)
    hence "U.prob {\<omega> \<in> space unif01. x < par \<alpha> \<omega>} = 1"
      by (subst (asm) ennreal_inj) simp_all
    thus ?thesis using False by simp
  qed
qed

subsection \<open>The Pareto tail is regularly varying of index \<open>-\<alpha>\<close>\<close>

theorem pareto_regularly_varying:
  fixes \<alpha> :: real
  assumes \<alpha>: "0 < \<alpha>"
  shows "prob_space unif01 \<and> par \<alpha> \<in> borel_measurable unif01
    \<and> (\<forall>x. 1 \<le> x \<longrightarrow> prob_space.prob unif01 {\<omega> \<in> space unif01. x < par \<alpha> \<omega>} = x powr (- \<alpha>))
    \<and> regularly_varying (\<lambda>x. prob_space.prob unif01 {\<omega> \<in> space unif01. x < par \<alpha> \<omega>}) (- \<alpha>)"
proof -
  interpret U: prob_space unif01 by (rule unif01_prob)
  have tl: "\<And>x. 1 \<le> x \<Longrightarrow> U.prob {\<omega> \<in> space unif01. x < par \<alpha> \<omega>} = x powr (- \<alpha>)"
    using par_tail[OF \<alpha>] by simp
  have rv: "regularly_varying (\<lambda>x. U.prob {\<omega> \<in> space unif01. x < par \<alpha> \<omega>}) (- \<alpha>)"
  proof (rule regularly_varying_asymp_transfer[OF regularly_varying_powr[of "- \<alpha>"] zero_less_one])
    show "(\<lambda>x. U.prob {\<omega> \<in> space unif01. x < par \<alpha> \<omega>}) \<in> borel_measurable (restrict_space borel {0<..})"
      by (rule U.tail_measurable) measurable
    show "\<And>x. 0 < x \<Longrightarrow> 0 < U.prob {\<omega> \<in> space unif01. x < par \<alpha> \<omega>}"
      using par_tail[OF \<alpha>] by simp
    have "\<forall>\<^sub>F x in at_top. U.prob {\<omega> \<in> space unif01. x < par \<alpha> \<omega>} / x powr (- \<alpha>) = 1"
      using eventually_ge_at_top[of 1]
      by eventually_elim (use tl in \<open>auto simp: field_simps\<close>)
    thus "((\<lambda>x. U.prob {\<omega> \<in> space unif01. x < par \<alpha> \<omega>} / x powr (- \<alpha>)) \<longlongrightarrow> 1) at_top"
      by (rule tendsto_eventually)
  qed
  show ?thesis using unif01_prob par_meas tl rv by blast
qed

subsection \<open>Independence is necessary: a concrete counterexample\<close>

theorem independence_needed_example:
  "\<exists>(M :: real measure) (X :: real \<Rightarrow> real). prob_space M \<and> X \<in> borel_measurable M
    \<and> regularly_varying (\<lambda>x. prob_space.prob M {\<omega> \<in> space M. x < X \<omega>}) (- 2)
    \<and> ((\<lambda>x. prob_space.prob M {\<omega> \<in> space M. x < X \<omega> + X \<omega>} / prob_space.prob M {\<omega> \<in> space M. x < X \<omega>})
        \<longlongrightarrow> 4) at_top
    \<and> \<not> ((\<lambda>x. prob_space.prob M {\<omega> \<in> space M. x < X \<omega> + X \<omega>} / prob_space.prob M {\<omega> \<in> space M. x < X \<omega>})
        \<longlongrightarrow> 2) at_top"
proof -
  have a: "(0 :: real) < 2" by simp
  note P = pareto_regularly_varying[OF a]
  interpret U: prob_space unif01 by (rule unif01_prob)
  have rv: "regularly_varying (\<lambda>x. U.prob {\<omega> \<in> space unif01. x < par 2 \<omega>}) (- 2)"
    using P by simp
  have "((\<lambda>x. U.prob {\<omega> \<in> space unif01. x < par 2 \<omega> + par 2 \<omega>} / U.prob {\<omega> \<in> space unif01. x < par 2 \<omega>})
      \<longlongrightarrow> 2 powr 2) at_top"
    by (rule U.tail_sum_self[OF rv])
  hence l4: "((\<lambda>x. U.prob {\<omega> \<in> space unif01. x < par 2 \<omega> + par 2 \<omega>} / U.prob {\<omega> \<in> space unif01. x < par 2 \<omega>})
      \<longlongrightarrow> 4) at_top"
    by simp
  have not2: "\<not> ((\<lambda>x. U.prob {\<omega> \<in> space unif01. x < par 2 \<omega> + par 2 \<omega>} / U.prob {\<omega> \<in> space unif01. x < par 2 \<omega>})
      \<longlongrightarrow> 2) at_top"
    by (rule U.tail_sum_iid_needs_independence[OF rv]) simp
  show ?thesis using P l4 not2 by blast
qed

subsection \<open>The independent case is non-vacuous\<close>

lemma tail_via_distr:
  assumes "prob_space M" and "Z \<in> borel_measurable M"
  shows "prob_space.prob M {\<omega> \<in> space M. x < Z \<omega>} = measure (distr M borel Z) {x::real<..}"
proof -
  have "measure (distr M borel Z) {x::real<..} = measure M (Z -` {x<..} \<inter> space M)"
  proof -
    have gs: "{x::real<..} \<in> sets (borel :: real measure)" by simp
    have zm: "Z \<in> measurable M borel" using assms by simp
    show ?thesis by (rule measure_distr[OF zm gs])
  qed
  moreover have "Z -` {x<..} \<inter> space M = {\<omega> \<in> space M. x < Z \<omega>}" by auto
  ultimately show ?thesis by simp
qed

lemma distr_snd_unif: "distr (unif01 \<Otimes>\<^sub>M unif01) unif01 snd = unif01"
proof -
  interpret U: prob_space unif01 by (rule unif01_prob)
  have sw: "distr (unif01 \<Otimes>\<^sub>M unif01) (unif01 \<Otimes>\<^sub>M unif01) (\<lambda>(x, y). (y, x)) = unif01 \<Otimes>\<^sub>M unif01"
  proof -
    interpret pair_sigma_finite unif01 unif01 by intro_locales
    show ?thesis by (rule distr_pair_swap[symmetric])
  qed
  have "distr (unif01 \<Otimes>\<^sub>M unif01) unif01 snd
      = distr (distr (unif01 \<Otimes>\<^sub>M unif01) (unif01 \<Otimes>\<^sub>M unif01) (\<lambda>(x, y). (y, x))) unif01 fst"
    by (subst distr_distr) (auto simp: comp_def split_def)
  also have "\<dots> = distr (unif01 \<Otimes>\<^sub>M unif01) unif01 fst" by (simp only: sw)
  also have "\<dots> = unif01" by (rule U.distr_pair_fst)
  finally show ?thesis .
qed

theorem independent_pareto_sum:
  fixes \<alpha> :: real
  assumes \<alpha>: "0 < \<alpha>"
  shows "\<exists>(M :: (real \<times> real) measure) (X :: real \<times> real \<Rightarrow> real) (Y :: real \<times> real \<Rightarrow> real).
    prob_space M \<and> X \<in> borel_measurable M \<and> Y \<in> borel_measurable M
    \<and> prob_space.indep_var M borel X borel Y
    \<and> regularly_varying (\<lambda>x. prob_space.prob M {\<omega> \<in> space M. x < X \<omega>}) (- \<alpha>)
    \<and> regularly_varying (\<lambda>x. prob_space.prob M {\<omega> \<in> space M. x < Y \<omega>}) (- \<alpha>)
    \<and> ((\<lambda>x. prob_space.prob M {\<omega> \<in> space M. x < X \<omega> + Y \<omega>} / prob_space.prob M {\<omega> \<in> space M. x < X \<omega>})
        \<longlongrightarrow> 2) at_top"
proof -
  interpret U: prob_space unif01 by (rule unif01_prob)
  define M where "M = unif01 \<Otimes>\<^sub>M unif01"
  interpret PM: prob_space M unfolding M_def by (rule prob_space_pair[OF unif01_prob unif01_prob])
  define X where "X = (\<lambda>w :: real \<times> real. par \<alpha> (fst w))"
  define Y where "Y = (\<lambda>w :: real \<times> real. par \<alpha> (snd w))"
  have Xm[measurable]: "X \<in> borel_measurable M" unfolding X_def M_def by measurable
  have Ym[measurable]: "Y \<in> borel_measurable M" unfolding Y_def M_def by measurable
  have dX: "distr M borel X = distr unif01 borel (par \<alpha>)"
  proof -
    have "distr M borel X = distr (distr M unif01 fst) borel (par \<alpha>)"
      unfolding X_def by (subst distr_distr) (simp_all add: comp_def M_def)
    also have "distr M unif01 fst = unif01" unfolding M_def by (rule U.distr_pair_fst)
    finally show ?thesis .
  qed
  have dY: "distr M borel Y = distr unif01 borel (par \<alpha>)"
  proof -
    have "distr M borel Y = distr (distr M unif01 snd) borel (par \<alpha>)"
      unfolding Y_def by (subst distr_distr) (simp_all add: comp_def M_def)
    also have "distr M unif01 snd = unif01" unfolding M_def by (rule distr_snd_unif)
    finally show ?thesis .
  qed
  have ind: "prob_space.indep_var M borel X borel Y"
  proof -
    have sf: "sigma_finite_measure (distr unif01 borel (par \<alpha>))"
    proof -
      have pd: "prob_space (distr unif01 borel (par \<alpha>))" by (rule U.prob_space_distr) simp
      interpret P: prob_space "distr unif01 borel (par \<alpha>)" by (rule pd)
      show ?thesis by intro_locales
    qed
    have "distr M borel X \<Otimes>\<^sub>M distr M borel Y = distr M (borel \<Otimes>\<^sub>M borel) (\<lambda>w. (X w, Y w))"
    proof -
      have "distr M borel X \<Otimes>\<^sub>M distr M borel Y = distr unif01 borel (par \<alpha>) \<Otimes>\<^sub>M distr unif01 borel (par \<alpha>)"
        by (simp only: dX dY)
      also have "\<dots> = distr (unif01 \<Otimes>\<^sub>M unif01) (borel \<Otimes>\<^sub>M borel) (\<lambda>(x, y). (par \<alpha> x, par \<alpha> y))"
        by (rule pair_measure_distr[OF par_meas par_meas sf])
      also have "\<dots> = distr M (borel \<Otimes>\<^sub>M borel) (\<lambda>w. (X w, Y w))"
        unfolding M_def X_def Y_def by (simp add: split_def)
      finally show ?thesis .
    qed
    note jd = this
    note iff = PM.indep_var_distribution_eq[of borel X borel Y]
    have rx: "PM.random_variable borel X" using Xm by simp
    have ry: "PM.random_variable borel Y" using Ym by simp
    show ?thesis by (rule iffD2[OF iff]) (intro conjI rx ry jd)
  qed
  have tX: "PM.prob {\<omega> \<in> space M. x < X \<omega>} = U.prob {\<omega> \<in> space unif01. x < par \<alpha> \<omega>}" for x
  proof -
    have "PM.prob {\<omega> \<in> space M. x < X \<omega>} = measure (distr M borel X) {x<..}"
      by (rule tail_via_distr[OF PM.prob_space_axioms Xm])
    also have "\<dots> = measure (distr unif01 borel (par \<alpha>)) {x<..}" by (simp only: dX)
    also have "\<dots> = U.prob {\<omega> \<in> space unif01. x < par \<alpha> \<omega>}"
      by (rule tail_via_distr[symmetric, OF unif01_prob par_meas])
    finally show "PM.prob {\<omega> \<in> space M. x < X \<omega>} = U.prob {\<omega> \<in> space unif01. x < par \<alpha> \<omega>}" .
  qed
  have tY: "PM.prob {\<omega> \<in> space M. x < Y \<omega>} = U.prob {\<omega> \<in> space unif01. x < par \<alpha> \<omega>}" for x
  proof -
    have "PM.prob {\<omega> \<in> space M. x < Y \<omega>} = measure (distr M borel Y) {x<..}"
      by (rule tail_via_distr[OF PM.prob_space_axioms Ym])
    also have "\<dots> = measure (distr unif01 borel (par \<alpha>)) {x<..}" by (simp only: dY)
    also have "\<dots> = U.prob {\<omega> \<in> space unif01. x < par \<alpha> \<omega>}"
      by (rule tail_via_distr[symmetric, OF unif01_prob par_meas])
    finally show "PM.prob {\<omega> \<in> space M. x < Y \<omega>} = U.prob {\<omega> \<in> space unif01. x < par \<alpha> \<omega>}" .
  qed
  have rvU: "regularly_varying (\<lambda>x. U.prob {\<omega> \<in> space unif01. x < par \<alpha> \<omega>}) (- \<alpha>)"
    using pareto_regularly_varying[OF \<alpha>] by simp
  have rvX: "regularly_varying (\<lambda>x. PM.prob {\<omega> \<in> space M. x < X \<omega>}) (- \<alpha>)"
    using rvU by (simp only: tX)
  have rvY: "regularly_varying (\<lambda>x. PM.prob {\<omega> \<in> space M. x < Y \<omega>}) (- \<alpha>)"
    using rvU by (simp only: tY)
  have ratio: "((\<lambda>x. PM.prob {\<omega> \<in> space M. x < Y \<omega>} / PM.prob {\<omega> \<in> space M. x < X \<omega>}) \<longlongrightarrow> 1) at_top"
  proof -
    have "\<forall>\<^sub>F x in at_top. PM.prob {\<omega> \<in> space M. x < Y \<omega>} / PM.prob {\<omega> \<in> space M. x < X \<omega>} = 1"
      using eventually_ge_at_top[of 1]
    proof eventually_elim
      case (elim x)
      have "0 < x powr (- \<alpha>)" using elim by simp
      hence "0 < PM.prob {\<omega> \<in> space M. x < X \<omega>}"
        using tX par_tail[OF \<alpha>] elim by simp
      thus ?case by (simp add: tX tY)
    qed
    thus ?thesis by (rule tendsto_eventually)
  qed
  have "((\<lambda>x. PM.prob {\<omega> \<in> space M. x < X \<omega> + Y \<omega>} / PM.prob {\<omega> \<in> space M. x < X \<omega>})
      \<longlongrightarrow> 1 + 1) at_top"
    by (rule PM.tail_sum_indep_gen[OF Xm Ym ind rvX ratio])
  hence l2: "((\<lambda>x. PM.prob {\<omega> \<in> space M. x < X \<omega> + Y \<omega>} / PM.prob {\<omega> \<in> space M. x < X \<omega>})
      \<longlongrightarrow> 2) at_top" by simp
  show ?thesis using PM.prob_space_axioms Xm Ym ind rvX rvY l2 by blast
qed

end
