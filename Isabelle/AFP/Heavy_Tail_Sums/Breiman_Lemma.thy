theory Breiman_Lemma
  imports Regular_Variation.Regular_Variation "HOL-Probability.Probability"
begin

section \<open>Breiman's lemma\<close>

text \<open>If \<open>X, Z \<ge> 0\<close> are independent, the tail of \<open>X\<close> is regularly varying of index \<open>-\<alpha> < 0\<close> and
  \<open>E Z^(\<alpha>+\<epsilon>) < \<infinity>\<close>, then \<open>P(XZ > x) / P(X > x) \<rightarrow> E Z^\<alpha>\<close>.\<close>

subsection \<open>Real-analysis lemmas\<close>

lemma powr_inv_helper:
  fixes z r :: real
  assumes "0 < z"
  shows "(1 / z) powr r = z powr (- r)"
  using assms by (simp add: powr_def ln_div)

lemma powr_le_one_plus:
  fixes z p q :: real
  assumes z: "0 < z" and p: "0 \<le> p" and pq: "p \<le> q"
  shows "z powr p \<le> 1 + z powr q"
proof (cases "z \<le> 1")
  case True
  hence "z powr p \<le> 1" using z p by (simp add: powr_le1)
  moreover have "0 \<le> z powr q" by simp
  ultimately show ?thesis by linarith
next
  case False
  hence "1 \<le> z" by simp
  hence "z powr p \<le> z powr q" by (rule powr_mono[OF pq])
  thus ?thesis by simp
qed

lemma potter_dom:
  fixes U :: "real \<Rightarrow> real" and \<alpha> \<epsilon> :: real
  assumes rv: "regularly_varying U (- \<alpha>)" and \<alpha>: "0 < \<alpha>" and \<epsilon>: "0 < \<epsilon>"
  shows "\<exists>x0>0. \<exists>A>0. \<forall>x\<ge>x0. \<forall>z>0. x0 \<le> x / z \<longrightarrow> U (x / z) / U x \<le> A * (1 + z powr (\<alpha> + \<epsilon>))"
proof -
  define d where "d = min \<epsilon> (\<alpha> / 2)"
  have d: "0 < d" "d \<le> \<epsilon>" "d \<le> \<alpha> / 2" using \<alpha> \<epsilon> by (auto simp: d_def)
  have A2: "(1::real) < 2" by simp
  obtain x0 where x0: "0 < x0"
    and P: "\<And>x y. x0 \<le> x \<Longrightarrow> x0 \<le> y \<Longrightarrow>
      U y / U x \<le> 2 * max ((y / x) powr (- \<alpha> + d)) ((y / x) powr (- \<alpha> - d))"
    using Potter_bounds[OF rv A2 d(1)] by blast
  show ?thesis
  proof (intro exI[of _ x0] exI[of _ 2] conjI x0, simp, intro allI impI)
    fix x z :: real
    assume x: "x0 \<le> x" and z: "0 < z" and y: "x0 \<le> x / z"
    have xp: "0 < x" using x x0 by simp
    have yx: "(x / z) / x = 1 / z" using xp by (simp add: field_simps)
    have b: "U (x / z) / U x \<le> 2 * max ((1 / z) powr (- \<alpha> + d)) ((1 / z) powr (- \<alpha> - d))"
      using P[OF x y] yx by simp
    have e1: "(1 / z) powr (- \<alpha> + d) = z powr (\<alpha> - d)"
      using powr_inv_helper[OF z, of "- \<alpha> + d"] by simp
    have e2: "(1 / z) powr (- \<alpha> - d) = z powr (\<alpha> + d)"
      using powr_inv_helper[OF z, of "- \<alpha> - d"] by (simp add: add.commute)
    have l1: "z powr (\<alpha> - d) \<le> 1 + z powr (\<alpha> + \<epsilon>)"
      by (rule powr_le_one_plus[OF z]) (use d \<alpha> \<epsilon> in linarith)+
    have l2: "z powr (\<alpha> + d) \<le> 1 + z powr (\<alpha> + \<epsilon>)"
      by (rule powr_le_one_plus[OF z]) (use d \<alpha> \<epsilon> in linarith)+
    show "U (x / z) / U x \<le> 2 * (1 + z powr (\<alpha> + \<epsilon>))"
      using b l1 l2 e1 e2 by (simp add: max_def split: if_splits)
  qed
qed

subsection \<open>Probabilistic part\<close>

context prob_space
begin

lemma tail_F_mono:
  fixes X :: "'a \<Rightarrow> real" and x :: real
  assumes X[measurable]: "X \<in> borel_measurable M" and x: "0 < x"
  shows "mono (\<lambda>z. if 0 < z then prob {\<omega> \<in> space M. x / z < X \<omega>} else 0)"
proof (rule monoI)
  fix a b :: real assume ab: "a \<le> b"
  show "(if 0 < a then prob {\<omega> \<in> space M. x / a < X \<omega>} else 0)
      \<le> (if 0 < b then prob {\<omega> \<in> space M. x / b < X \<omega>} else 0)"
  proof (cases "0 < a")
    case True
    hence b: "0 < b" using ab by simp
    have "x / b \<le> x / a" using x True ab by (simp add: divide_left_mono)
    hence "{\<omega> \<in> space M. x / a < X \<omega>} \<subseteq> {\<omega> \<in> space M. x / b < X \<omega>}" by auto
    hence "prob {\<omega> \<in> space M. x / a < X \<omega>} \<le> prob {\<omega> \<in> space M. x / b < X \<omega>}"
      by (intro finite_measure_mono) auto
    thus ?thesis using True b by simp
  next
    case False
    thus ?thesis by (simp add: measure_nonneg)
  qed
qed

lemma tail_prod_formula:
  fixes X Z :: "'a \<Rightarrow> real" and x :: real
  assumes X[measurable]: "X \<in> borel_measurable M" and Z[measurable]: "Z \<in> borel_measurable M"
    and ind: "indep_var borel X borel Z"
    and X0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> X \<omega>" and Z0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> Z \<omega>"
    and x: "0 < x"
  shows "prob {\<omega> \<in> space M. x < X \<omega> * Z \<omega>} =
    (\<integral>\<omega>. (if 0 < Z \<omega> then prob {\<omega>' \<in> space M. x / Z \<omega> < X \<omega>'} else 0) \<partial>M)"
proof -
  define F where "F z = (if 0 < z then prob {\<omega> \<in> space M. x / z < X \<omega>} else 0)" for z
  have Fm[measurable]: "F \<in> borel_measurable borel"
    unfolding F_def by (rule borel_measurable_mono[OF tail_F_mono[OF X x]])
  have F01: "0 \<le> F z" "F z \<le> 1" for z unfolding F_def by (auto simp: measure_nonneg prob_le_1)
  interpret nu: prob_space "distr M borel X" by (rule prob_space_distr) simp
  interpret mu: prob_space "distr M borel Z" by (rule prob_space_distr) simp
  interpret pair_sigma_finite "distr M borel X" "distr M borel Z" ..
  have dist: "distr M borel X \<Otimes>\<^sub>M distr M borel Z = distr M (borel \<Otimes>\<^sub>M borel) (\<lambda>\<omega>. (X \<omega>, Z \<omega>))"
    using ind unfolding indep_var_distribution_eq by simp
  define S :: "(real \<times> real) set" where "S = {p. 0 < snd p \<and> x < fst p * snd p}"
  have S[measurable]: "S \<in> sets (borel \<Otimes>\<^sub>M borel)"
  proof -
    have "{p \<in> space (borel \<Otimes>\<^sub>M borel :: (real \<times> real) measure). 0 < snd p \<and> x < fst p * snd p}
      \<in> sets (borel \<Otimes>\<^sub>M borel)"
      by measurable
    thus ?thesis unfolding S_def by (simp add: space_pair_measure)
  qed
  have SM: "S \<in> sets (distr M borel X \<Otimes>\<^sub>M distr M borel Z)" using S by simp
  have set_eq: "{\<omega> \<in> space M. x < X \<omega> * Z \<omega>} = (\<lambda>\<omega>. (X \<omega>, Z \<omega>)) -` S \<inter> space M"
  proof (intro set_eqI iffI)
    fix \<omega> assume "\<omega> \<in> {\<omega> \<in> space M. x < X \<omega> * Z \<omega>}"
    hence \<omega>: "\<omega> \<in> space M" "x < X \<omega> * Z \<omega>" by auto
    have "0 < Z \<omega>"
    proof (rule ccontr)
      assume "\<not> 0 < Z \<omega>"
      hence "Z \<omega> = 0" using Z0[OF \<omega>(1)] by simp
      thus False using \<omega>(2) x by simp
    qed
    thus "\<omega> \<in> (\<lambda>\<omega>. (X \<omega>, Z \<omega>)) -` S \<inter> space M" using \<omega> unfolding S_def by auto
  next
    fix \<omega> assume "\<omega> \<in> (\<lambda>\<omega>. (X \<omega>, Z \<omega>)) -` S \<inter> space M"
    thus "\<omega> \<in> {\<omega> \<in> space M. x < X \<omega> * Z \<omega>}" unfolding S_def by auto
  qed
  have 1: "emeasure (distr M borel X \<Otimes>\<^sub>M distr M borel Z) S = ennreal (prob {\<omega> \<in> space M. x < X \<omega> * Z \<omega>})"
  proof -
    have "emeasure (distr M borel X \<Otimes>\<^sub>M distr M borel Z) S = emeasure M ((\<lambda>\<omega>. (X \<omega>, Z \<omega>)) -` S \<inter> space M)"
      unfolding dist by (rule emeasure_distr) (use S in \<open>measurable\<close>)
    also have "\<dots> = ennreal (prob {\<omega> \<in> space M. x < X \<omega> * Z \<omega>})"
      unfolding set_eq[symmetric] by (rule emeasure_eq_ennreal_measure) simp
    finally show ?thesis .
  qed
  have slice: "emeasure (distr M borel X) ((\<lambda>a. (a, z)) -` S) = ennreal (F z)" for z
  proof (cases "0 < z")
    case True
    have eq: "(\<lambda>a. (a, z)) -` S = {a. x / z < a}"
      using True unfolding S_def by (auto simp: field_simps)
    have "emeasure (distr M borel X) {a. x / z < a} = emeasure M (X -` {a. x / z < a} \<inter> space M)"
      by (rule emeasure_distr) simp_all
    also have "X -` {a. x / z < a} \<inter> space M = {\<omega> \<in> space M. x / z < X \<omega>}" by auto
    also have "emeasure M {\<omega> \<in> space M. x / z < X \<omega>} = ennreal (prob {\<omega> \<in> space M. x / z < X \<omega>})"
      by (rule emeasure_eq_ennreal_measure) simp
    finally show ?thesis unfolding eq F_def using True by simp
  next
    case False
    hence "(\<lambda>a. (a, z)) -` S = {}" unfolding S_def by auto
    thus ?thesis using False unfolding F_def by simp
  qed
  have 2: "emeasure (distr M borel X \<Otimes>\<^sub>M distr M borel Z) S = (\<integral>\<^sup>+z. ennreal (F z) \<partial>distr M borel Z)"
    by (subst emeasure_pair_measure_alt2[OF SM]) (simp add: slice)
  have Fint: "integrable (distr M borel Z) F"
    by (rule mu.integrable_const_bound[where B=1]) (use F01 in \<open>auto simp: abs_of_nonneg\<close>)
  have 3: "(\<integral>\<^sup>+z. ennreal (F z) \<partial>distr M borel Z) = ennreal (\<integral>z. F z \<partial>distr M borel Z)"
    by (rule nn_integral_eq_integral[OF Fint]) (use F01 in auto)
  have 4: "(\<integral>z. F z \<partial>distr M borel Z) = (\<integral>\<omega>. F (Z \<omega>) \<partial>M)"
    by (rule integral_distr) simp_all
  have "ennreal (prob {\<omega> \<in> space M. x < X \<omega> * Z \<omega>}) = ennreal (\<integral>\<omega>. F (Z \<omega>) \<partial>M)"
    using 1 2 3 4 by simp
  moreover have "0 \<le> (\<integral>\<omega>. F (Z \<omega>) \<partial>M)" using F01 by (intro integral_nonneg_AE) auto
  ultimately have "prob {\<omega> \<in> space M. x < X \<omega> * Z \<omega>} = (\<integral>\<omega>. F (Z \<omega>) \<partial>M)"
    by (simp add: measure_nonneg)
  thus ?thesis unfolding F_def .
qed

theorem breiman:
  fixes X Z :: "'a \<Rightarrow> real" and \<alpha> \<epsilon> :: real
  assumes X[measurable]: "X \<in> borel_measurable M" and Z[measurable]: "Z \<in> borel_measurable M"
    and ind: "indep_var borel X borel Z"
    and X0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> X \<omega>" and Z0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> Z \<omega>"
    and rv: "regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega>}) (- \<alpha>)" and \<alpha>: "0 < \<alpha>"
    and \<epsilon>: "0 < \<epsilon>"
    and int: "integrable M (\<lambda>\<omega>. Z \<omega> powr (\<alpha> + \<epsilon>))"
  shows "((\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega> * Z \<omega>} / prob {\<omega> \<in> space M. x < X \<omega>})
    \<longlongrightarrow> expectation (\<lambda>\<omega>. Z \<omega> powr \<alpha>)) at_top"
proof -
  define T where "T y = prob {\<omega> \<in> space M. y < X \<omega>}" for y
  have rvT: "regularly_varying T (- \<alpha>)" using rv unfolding T_def .
  have Tpos: "0 < T y" if "0 < y" for y using regularly_varying_pos[OF rvT that] .
  have Tle: "T y \<le> 1" for y unfolding T_def by (rule prob_le_1)
  define q where "q = \<alpha> + \<epsilon>"
  have q: "0 < q" using \<alpha> \<epsilon> by (simp add: q_def)
  obtain x0 A where x0: "0 < x0" and A: "0 < A"
    and pot: "\<And>x z. x0 \<le> x \<Longrightarrow> 0 < z \<Longrightarrow> x0 \<le> x / z \<Longrightarrow> T (x / z) / T x \<le> A * (1 + z powr q)"
    using potter_dom[OF rvT \<alpha> \<epsilon>] unfolding q_def by blast
  define F where "F x z = (if 0 < z then T (x / z) else 0)" for x z
  have Fm: "F x \<in> borel_measurable borel" if "0 < x" for x
    unfolding F_def T_def by (rule borel_measurable_mono[OF tail_F_mono[OF X that]])
  have F01: "0 \<le> F x z" "F x z \<le> 1" for x z unfolding F_def T_def by (auto simp: measure_nonneg prob_le_1)
  define H1 where "H1 x \<omega> = (if 0 < Z \<omega> \<and> Z \<omega> \<le> x / x0 then F x (Z \<omega>) / T x else 0)" for x \<omega>
  define H2 where "H2 x \<omega> = (if x / x0 < Z \<omega> then F x (Z \<omega>) / T x else 0)" for x \<omega>
  define w where "w \<omega> = A * (1 + Z \<omega> powr q)" for \<omega>
  have imr: "integrable M f \<Longrightarrow> integrable M (\<lambda>x. c * f x)" for c and f :: "'a \<Rightarrow> real"
    by (cases "c = 0") (auto intro: integrable_mult_right)
  have Zq0: "integrable M (\<lambda>\<omega>. Z \<omega> powr q)" using int unfolding q_def .
  have wint: "integrable M w"
  proof -
    have c1: "integrable M (\<lambda>_. (1::real))" by simp
    have "integrable M (\<lambda>\<omega>. 1 + Z \<omega> powr q)"
      by (rule Bochner_Integration.integrable_add[OF c1 Zq0])
    thus ?thesis unfolding w_def by (rule imr)
  qed
  have Zq: "integrable M (\<lambda>\<omega>. Z \<omega> powr q)" using int unfolding q_def .
  have H1m: "H1 x \<in> borel_measurable M" if "0 < x" for x
  proof -
    have [measurable]: "F x \<in> borel_measurable borel" by (rule Fm[OF that])
    show ?thesis unfolding H1_def by measurable
  qed
  have H2m: "H2 x \<in> borel_measurable M" if "0 < x" for x
  proof -
    have [measurable]: "F x \<in> borel_measurable borel" by (rule Fm[OF that])
    show ?thesis unfolding H2_def by measurable
  qed
  have H1nn: "0 \<le> H1 x \<omega>" if "0 < x" for x \<omega>
    unfolding H1_def using F01 Tpos[OF that] by (auto intro!: divide_nonneg_pos)
  have H2nn: "0 \<le> H2 x \<omega>" if "0 < x" for x \<omega>
    unfolding H2_def using F01 Tpos[OF that] by (auto intro!: divide_nonneg_pos)
  \<comment> \<open>domination of H1\<close>
  have H1le: "H1 x \<omega> \<le> w \<omega>" if x: "x0 \<le> x" and \<omega>: "\<omega> \<in> space M" for x \<omega>
  proof (cases "0 < Z \<omega> \<and> Z \<omega> \<le> x / x0")
    case True
    hence z: "0 < Z \<omega>" and zx: "Z \<omega> \<le> x / x0" by auto
    have h: "Z \<omega> * x0 \<le> x" using zx x0 by (simp add: pos_le_divide_eq)
    have "x0 \<le> x / Z \<omega>" using h by (simp add: pos_le_divide_eq[OF z] mult.commute)
    from pot[OF x z this] show ?thesis using True unfolding H1_def F_def w_def by simp
  next
    case False
    have "0 \<le> w \<omega>" unfolding w_def using A by simp
    moreover have "H1 x \<omega> = 0" unfolding H1_def by (rule if_not_P[OF False])
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>limit of the near part\<close>
  have lim1': "((\<lambda>t. \<integral>\<omega>. H1 (max t x0) \<omega> \<partial>M) \<longlongrightarrow> \<integral>\<omega>. Z \<omega> powr \<alpha> \<partial>M) at_top"
  proof (rule integral_dominated_convergence_at_top[where w=w])
    show "(\<lambda>\<omega>. Z \<omega> powr \<alpha>) \<in> borel_measurable M" by measurable
    show "\<And>t. (\<lambda>\<omega>. H1 (max t x0) \<omega>) \<in> borel_measurable M"
      using H1m x0 by simp
    show "integrable M w" by (rule wint)
    show "AE \<omega> in M. ((\<lambda>t. H1 (max t x0) \<omega>) \<longlongrightarrow> Z \<omega> powr \<alpha>) at_top"
      using AE_space
    proof eventually_elim
      case (elim \<omega>)
      have z0: "0 \<le> Z \<omega>" using Z0[OF elim] .
      show ?case
      proof (cases "0 < Z \<omega>")
        case False
        hence "Z \<omega> = 0" using z0 by simp
        thus ?thesis by (simp add: H1_def)
      next
        case True
        define z where "z = Z \<omega>"
        have z: "0 < z" using True by (simp add: z_def)
        have b: "((\<lambda>t. T (t * (1 / z)) / T t) \<longlongrightarrow> (1 / z) powr (- \<alpha>)) at_top"
          by (rule regularly_varying_lim[OF rvT]) (use z in simp)
        have e: "(1 / z) powr (- \<alpha>) = z powr \<alpha>" using powr_inv_helper[OF z, of "- \<alpha>"] by simp
        have ev: "\<forall>\<^sub>F t in at_top. T (t * (1 / z)) / T t = H1 (max t x0) \<omega>"
          using eventually_ge_at_top[of x0] eventually_ge_at_top[of "z * x0"]
        proof eventually_elim
          case (elim t)
          have m: "max t x0 = t" using elim by simp
          have "z \<le> t / x0" using elim(2) x0 by (simp add: pos_le_divide_eq mult.commute)
          thus ?case using z unfolding H1_def F_def m z_def[symmetric] by simp
        qed
        show ?thesis unfolding z_def[symmetric] using b e ev by (auto intro: Lim_transform_eventually)
      qed
    qed
    show "\<forall>\<^sub>F t in at_top. AE \<omega> in M. norm (H1 (max t x0) \<omega>) \<le> w \<omega>"
    proof (rule always_eventually, rule allI)
      fix t
      have xp: "0 < max t x0" using x0 by simp
      show "AE \<omega> in M. norm (H1 (max t x0) \<omega>) \<le> w \<omega>"
        using AE_space
      proof eventually_elim
        case (elim \<omega>)
        show ?case using H1nn[OF xp, of \<omega>] H1le[OF max.cobounded2 elim] by (simp add: abs_of_nonneg)
      qed
    qed
  qed
  have lim1: "((\<lambda>x. \<integral>\<omega>. H1 x \<omega> \<partial>M) \<longlongrightarrow> \<integral>\<omega>. Z \<omega> powr \<alpha> \<partial>M) at_top"
  proof (rule Lim_transform_eventually[OF lim1'])
    show "\<forall>\<^sub>F x in at_top. (\<integral>\<omega>. H1 (max x x0) \<omega> \<partial>M) = (\<integral>\<omega>. H1 x \<omega> \<partial>M)"
      using eventually_ge_at_top[of x0] by eventually_elim simp
  qed
  \<comment> \<open>far part\<close>
  define cx where "cx x = x0 powr q * inverse (T x * x powr q)" for x
  have rvU: "regularly_varying (\<lambda>x. T x * x powr q) \<epsilon>"
  proof -
    have "regularly_varying (\<lambda>x. T x * x powr q) (- \<alpha> + q)"
      by (rule regularly_varying_mult[OF rvT regularly_varying_powr])
    moreover have "- \<alpha> + q = \<epsilon>" by (simp add: q_def)
    ultimately show ?thesis by simp
  qed
  have cx0: "(cx \<longlongrightarrow> 0) at_top"
  proof -
    have "filterlim (\<lambda>x. T x * x powr q) at_top at_top" by (rule regularly_varying_pos_at_top[OF rvU \<epsilon>])
    hence "((\<lambda>x. inverse (T x * x powr q)) \<longlongrightarrow> 0) at_top" by (rule tendsto_inverse_0_at_top)
    from tendsto_mult[OF tendsto_const[of "x0 powr q"] this] show ?thesis unfolding cx_def by simp
  qed
  have cxnn: "0 \<le> cx x" if "0 < x" for x
    unfolding cx_def using Tpos[OF that] that by simp
  have H2le: "H2 x \<omega> \<le> cx x * Z \<omega> powr q" if x: "0 < x" and \<omega>: "\<omega> \<in> space M" for x \<omega>
  proof (cases "x / x0 < Z \<omega>")
    case False
    thus ?thesis unfolding H2_def using cxnn[OF x] by simp
  next
    case True
    define z where "z = Z \<omega>"
    define K where "K = (x / x0) powr q"
    have xx: "0 < x / x0" using x x0 by simp
    have zK: "K \<le> z powr q"
      unfolding K_def using True q xx by (auto intro!: powr_mono2 simp: z_def)
    have cK: "cx x * K = 1 / T x"
      unfolding cx_def K_def using Tpos[OF x] x x0 by (simp add: powr_divide field_simps)
    have "H2 x \<omega> = T (x / z) / T x" using True xx unfolding H2_def F_def z_def by simp
    also have "\<dots> \<le> 1 / T x" using Tle Tpos[OF x] by (intro divide_right_mono) auto
    also have "\<dots> = cx x * K" by (rule cK[symmetric])
    also have "\<dots> \<le> cx x * z powr q" using zK cxnn[OF x] by (intro mult_left_mono)
    finally show ?thesis by (simp add: z_def)
  qed
  have ib: "integrable M g \<Longrightarrow> f \<in> borel_measurable M \<Longrightarrow>
      (\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> f \<omega> \<and> f \<omega> \<le> g \<omega>) \<Longrightarrow> integrable M f"
    for f g :: "'a \<Rightarrow> real"
  proof (rule Bochner_Integration.integrable_bound[where f=g])
    assume "integrable M g" "f \<in> borel_measurable M" and h: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> f \<omega> \<and> f \<omega> \<le> g \<omega>"
    show "AE \<omega> in M. norm (f \<omega>) \<le> norm (g \<omega>)"
      using AE_space
    proof eventually_elim
      case (elim \<omega>)
      from h[OF elim] show ?case by (auto simp: abs_of_nonneg)
    qed
  qed
  have H2int: "integrable M (H2 x)" if "0 < x" for x
    by (rule ib[OF imr[OF Zq, of "cx x"] H2m[OF that]]) (use H2nn[OF that] H2le[OF that] in auto)
  have H1int: "integrable M (H1 x)" if "x0 \<le> x" for x
  proof -
    have xp: "0 < x" using that x0 by simp
    show ?thesis
      by (rule ib[OF wint H1m[OF xp]]) (use H1nn[OF xp] H1le[OF that] in auto)
  qed
  have lim2: "((\<lambda>x. \<integral>\<omega>. H2 x \<omega> \<partial>M) \<longlongrightarrow> 0) at_top"
  proof (rule tendsto_sandwich[where f="\<lambda>_. 0" and h="\<lambda>x. cx x * (\<integral>\<omega>. Z \<omega> powr q \<partial>M)"])
    show "\<forall>\<^sub>F x in at_top. 0 \<le> (\<integral>\<omega>. H2 x \<omega> \<partial>M)"
      using eventually_gt_at_top[of 0] by eventually_elim (use H2nn in \<open>auto intro!: integral_nonneg_AE\<close>)
    show "\<forall>\<^sub>F x in at_top. (\<integral>\<omega>. H2 x \<omega> \<partial>M) \<le> cx x * (\<integral>\<omega>. Z \<omega> powr q \<partial>M)"
      using eventually_gt_at_top[of 0]
    proof eventually_elim
      case (elim x)
      have "(\<integral>\<omega>. H2 x \<omega> \<partial>M) \<le> (\<integral>\<omega>. cx x * Z \<omega> powr q \<partial>M)"
        by (rule integral_mono_AE[OF H2int[OF elim] imr[OF Zq]])
          (use AE_space H2le[OF elim] in \<open>auto elim: eventually_mono\<close>)
      thus ?case by simp
    qed
    show "((\<lambda>_. 0::real) \<longlongrightarrow> 0) at_top" by simp
    show "((\<lambda>x. cx x * (\<integral>\<omega>. Z \<omega> powr q \<partial>M)) \<longlongrightarrow> 0) at_top"
      using tendsto_mult[OF cx0 tendsto_const[of "\<integral>\<omega>. Z \<omega> powr q \<partial>M"]] by simp
  qed
  have sumlim: "((\<lambda>x. (\<integral>\<omega>. H1 x \<omega> \<partial>M) + (\<integral>\<omega>. H2 x \<omega> \<partial>M)) \<longlongrightarrow> (\<integral>\<omega>. Z \<omega> powr \<alpha> \<partial>M) + 0) at_top"
    by (rule tendsto_add[OF lim1 lim2])
  have eq: "\<forall>\<^sub>F x in at_top. (\<integral>\<omega>. H1 x \<omega> \<partial>M) + (\<integral>\<omega>. H2 x \<omega> \<partial>M)
      = prob {\<omega> \<in> space M. x < X \<omega> * Z \<omega>} / prob {\<omega> \<in> space M. x < X \<omega>}"
    using eventually_ge_at_top[of x0]
  proof eventually_elim
    case (elim x)
    have xp: "0 < x" using elim x0 by simp
    have f1: "prob {\<omega> \<in> space M. x < X \<omega> * Z \<omega>} = (\<integral>\<omega>. F x (Z \<omega>) \<partial>M)"
      using tail_prod_formula[OF X Z ind X0 Z0 xp] unfolding F_def T_def by simp
    have "(\<integral>\<omega>. H1 x \<omega> \<partial>M) + (\<integral>\<omega>. H2 x \<omega> \<partial>M) = (\<integral>\<omega>. H1 x \<omega> + H2 x \<omega> \<partial>M)"
      by (rule Bochner_Integration.integral_add[symmetric, OF H1int[OF elim] H2int[OF xp]])
    also have "\<dots> = (\<integral>\<omega>. F x (Z \<omega>) / T x \<partial>M)"
    proof (rule Bochner_Integration.integral_cong[OF refl])
      fix \<omega> assume \<omega>: "\<omega> \<in> space M"
      have z0: "0 \<le> Z \<omega>" using Z0[OF \<omega>] .
      have xx: "0 < x / x0" using xp x0 by simp
      show "H1 x \<omega> + H2 x \<omega> = F x (Z \<omega>) / T x"
      proof (cases "0 < Z \<omega>")
        case False
        hence "Z \<omega> = 0" using z0 by simp
        thus ?thesis using xx unfolding H1_def H2_def F_def by simp
      next
        case True
        thus ?thesis unfolding H1_def H2_def by auto
      qed
    qed
    also have "\<dots> = (\<integral>\<omega>. F x (Z \<omega>) \<partial>M) / T x" by simp
    finally show ?case unfolding f1 T_def by simp
  qed
  have "((\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega> * Z \<omega>} / prob {\<omega> \<in> space M. x < X \<omega>})
      \<longlongrightarrow> (\<integral>\<omega>. Z \<omega> powr \<alpha> \<partial>M) + 0) at_top"
    by (rule Lim_transform_eventually[OF sumlim eq])
  thus ?thesis by simp
qed

end

end
