(*  Title:      Regular_Variation_Sums.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

theory Regular_Variation_Sums
  imports Regular_Variation.Regular_Variation "HOL-Probability.Probability"
begin

section \<open>The tail of a sum of independent heavy-tailed variables\<close>

text \<open>If \<open>X\<close> and \<open>Y\<close> are independent and non-negative, the tail of \<open>X\<close> is regularly varying
  of index \<open>-\<alpha> < 0\<close>, and the tail of \<open>Y\<close> is asymptotic to \<open>c\<close> times the tail of \<open>X\<close>, then
  \<open>P(X + Y > x) \<sim> (1 + c) P(X > x)\<close>: a large sum comes from one large summand.  The proof is the
  classical sandwich (Feller; Embrechts, Kl\"uppelberg and Mikosch, Lemma 1.3.1), first for functions and then
  for tails.\<close>

lemma filterlim_times_const_at_top:
  fixes a :: real
  assumes "0 < a"
  shows "filterlim (\<lambda>t. t * a) at_top at_top"
proof -
  have "filterlim (\<lambda>t::real. a * t) at_top at_top"
    by (rule filterlim_tendsto_pos_mult_at_top[OF tendsto_const assms filterlim_ident])
  thus ?thesis by (simp add: mult.commute)
qed

lemma regularly_varying_sum_sandwich:
  fixes T G H :: "real \<Rightarrow> real" and \<alpha> c :: real
  assumes rv: "regularly_varying T (- \<alpha>)" and \<alpha>: "0 < \<alpha>"
    and ratio: "((\<lambda>x. G x / T x) \<longlongrightarrow> c) at_top"
    and low: "\<forall>\<^sub>F x in at_top. T x + G x - T x * G x \<le> H x"
    and up: "\<And>\<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < 1 / 2 \<Longrightarrow>
      \<forall>\<^sub>F x in at_top. H x \<le> T (x * (1 - \<delta>)) + G (x * (1 - \<delta>)) + T (x * \<delta>) * G (x * \<delta>)"
  shows "((\<lambda>x. H x / T x) \<longlongrightarrow> 1 + c) at_top"
proof -
  have Tpos: "\<forall>\<^sub>F x in at_top. 0 < T x"
    using eventually_gt_at_top[of "0::real"]
    by (rule eventually_mono) (rule regularly_varying_pos[OF rv])
  have T0: "(T \<longlongrightarrow> 0) at_top"
    by (rule regularly_varying_neg_at_top[OF rv]) (use \<alpha> in simp)
  have G0: "(G \<longlongrightarrow> 0) at_top"
  proof -
    have "((\<lambda>x. G x / T x * T x) \<longlongrightarrow> 0) at_top"
      using tendsto_mult[OF ratio T0] by simp
    moreover have "\<forall>\<^sub>F x in at_top. G x / T x * T x = G x"
      using Tpos by (rule eventually_mono) simp
    ultimately show ?thesis by (rule Lim_transform_eventually)
  qed
  have lowlim: "((\<lambda>x. 1 + G x / T x - G x) \<longlongrightarrow> 1 + c) at_top"
  proof -
    have "((\<lambda>x. 1 + G x / T x - G x) \<longlongrightarrow> 1 + c - 0) at_top"
      by (intro tendsto_diff tendsto_add tendsto_const ratio G0)
    thus ?thesis by simp
  qed
  have lowev: "\<forall>\<^sub>F x in at_top. 1 + G x / T x - G x \<le> H x / T x"
    using low Tpos
  proof eventually_elim
    case (elim x)
    have "1 + G x / T x - G x = (T x + G x - T x * G x) / T x"
      using elim(2) by (simp add: field_simps)
    also have "\<dots> \<le> H x / T x"
      using elim by (intro divide_right_mono) auto
    finally show ?case .
  qed
  have uplim: "((\<lambda>x. T (x * (1 - \<delta>)) / T x + G (x * (1 - \<delta>)) / T x + T (x * \<delta>) / T x * G (x * \<delta>))
      \<longlongrightarrow> (1 + c) * (1 - \<delta>) powr (- \<alpha>)) at_top" if \<delta>: "0 < \<delta>" "\<delta> < 1 / 2" for \<delta>
  proof -
    define b where "b = 1 - \<delta>"
    have b: "0 < b" using \<delta> by (simp add: b_def)
    have r1: "((\<lambda>x. T (x * b) / T x) \<longlongrightarrow> b powr (- \<alpha>)) at_top"
      by (rule regularly_varying_lim[OF rv b])
    have r2: "((\<lambda>x. T (x * \<delta>) / T x) \<longlongrightarrow> \<delta> powr (- \<alpha>)) at_top"
      by (rule regularly_varying_lim[OF rv \<delta>(1)])
    have g1: "((\<lambda>x. G (x * b) / T (x * b)) \<longlongrightarrow> c) at_top"
      using filterlim_compose[OF ratio filterlim_times_const_at_top[OF b]] by simp
    have g0: "((\<lambda>x. G (x * \<delta>)) \<longlongrightarrow> 0) at_top"
      using filterlim_compose[OF G0 filterlim_times_const_at_top[OF \<delta>(1)]] by simp
    have Tb: "\<forall>\<^sub>F x in at_top. 0 < T (x * b)"
      using eventually_gt_at_top[of "0::real"]
      by (rule eventually_mono) (rule regularly_varying_pos[OF rv], use b in simp)
    have a2: "((\<lambda>x. G (x * b) / T x) \<longlongrightarrow> c * b powr (- \<alpha>)) at_top"
    proof -
      have "((\<lambda>x. G (x * b) / T (x * b) * (T (x * b) / T x)) \<longlongrightarrow> c * b powr (- \<alpha>)) at_top"
        by (rule tendsto_mult[OF g1 r1])
      moreover have "\<forall>\<^sub>F x in at_top. G (x * b) / T (x * b) * (T (x * b) / T x) = G (x * b) / T x"
        using Tb by (rule eventually_mono) simp
      ultimately show ?thesis by (rule Lim_transform_eventually)
    qed
    have "((\<lambda>x. T (x * b) / T x + G (x * b) / T x + T (x * \<delta>) / T x * G (x * \<delta>))
        \<longlongrightarrow> b powr (- \<alpha>) + c * b powr (- \<alpha>) + \<delta> powr (- \<alpha>) * 0) at_top"
      by (intro tendsto_add tendsto_mult r1 a2 r2 g0)
    thus ?thesis by (simp add: b_def algebra_simps)
  qed
  have upev: "\<forall>\<^sub>F x in at_top. H x / T x \<le>
      T (x * (1 - \<delta>)) / T x + G (x * (1 - \<delta>)) / T x + T (x * \<delta>) / T x * G (x * \<delta>)"
    if \<delta>: "0 < \<delta>" "\<delta> < 1 / 2" for \<delta>
    using up[OF \<delta>] Tpos
  proof eventually_elim
    case (elim x)
    have "H x / T x \<le> (T (x * (1 - \<delta>)) + G (x * (1 - \<delta>)) + T (x * \<delta>) * G (x * \<delta>)) / T x"
      using elim by (intro divide_right_mono) auto
    also have "\<dots> = T (x * (1 - \<delta>)) / T x + G (x * (1 - \<delta>)) / T x + T (x * \<delta>) / T x * G (x * \<delta>)"
      by (simp add: add_divide_distrib)
    finally show ?case .
  qed
  show ?thesis
  proof (rule order_tendstoI)
    fix a assume a: "a < 1 + c"
    show "\<forall>\<^sub>F x in at_top. a < H x / T x"
      using order_tendstoD(1)[OF lowlim a] lowev
      by eventually_elim linarith
  next
    fix B assume B: "1 + c < B"
    have "((\<lambda>\<delta>. (1 + c) * (1 - \<delta>) powr (- \<alpha>)) \<longlongrightarrow> (1 + c) * (1 - 0) powr (- \<alpha>)) (at_right (0::real))"
      by (intro tendsto_mult tendsto_const tendsto_powr tendsto_diff tendsto_ident_at) simp
    hence lim: "((\<lambda>\<delta>. (1 + c) * (1 - \<delta>) powr (- \<alpha>)) \<longlongrightarrow> 1 + c) (at_right (0::real))"
      by simp
    have e2: "\<forall>\<^sub>F \<delta> in at_right (0::real). 0 < \<delta> \<and> \<delta> < 1 / 2"
      by (rule eventually_at_rightI[of 0 "1 / 2"]) auto
    obtain \<delta> where \<delta>: "0 < \<delta>" "\<delta> < 1 / 2" and U: "(1 + c) * (1 - \<delta>) powr (- \<alpha>) < B"
      using eventually_happens'[OF trivial_limit_at_right_real eventually_conj[OF order_tendstoD(2)[OF lim B] e2]]
      by auto
    show "\<forall>\<^sub>F x in at_top. H x / T x < B"
      using order_tendstoD(2)[OF uplim[OF \<delta>] U] upev[OF \<delta>]
      by eventually_elim linarith
  qed
qed

context prob_space
begin

theorem tail_sum_indep:
  fixes X Y :: "'a \<Rightarrow> real" and \<alpha> c :: real
  assumes X[measurable]: "X \<in> borel_measurable M" and Y[measurable]: "Y \<in> borel_measurable M"
    and ind: "indep_var borel X borel Y"
    and X0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> X \<omega>" and Y0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> Y \<omega>"
    and rv: "regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega>}) (- \<alpha>)" and \<alpha>: "0 < \<alpha>"
    and ratio: "((\<lambda>x. prob {\<omega> \<in> space M. x < Y \<omega>} / prob {\<omega> \<in> space M. x < X \<omega>}) \<longlongrightarrow> c) at_top"
  shows "((\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega> + Y \<omega>} / prob {\<omega> \<in> space M. x < X \<omega>}) \<longlongrightarrow> 1 + c) at_top"
proof -
  define A where "A x = {\<omega> \<in> space M. x < X \<omega>}" for x
  define B where "B x = {\<omega> \<in> space M. x < Y \<omega>}" for x
  define S where "S x = {\<omega> \<in> space M. x < X \<omega> + Y \<omega>}" for x
  have As[measurable]: "A x \<in> sets M" for x unfolding A_def by measurable
  have Bs[measurable]: "B x \<in> sets M" for x unfolding B_def by measurable
  have Ss[measurable]: "S x \<in> sets M" for x unfolding S_def by measurable
  have both: "prob (A a \<inter> B b) = prob (A a) * prob (B b)" for a b
  proof -
    have sa: "{a<..} \<in> sets (borel :: real measure)" and sb: "{b<..} \<in> sets (borel :: real measure)" by auto
    have "\<P>(\<omega> in M. X \<omega> \<in> {a<..} \<and> Y \<omega> \<in> {b<..}) = \<P>(\<omega> in M. X \<omega> \<in> {a<..}) * \<P>(\<omega> in M. Y \<omega> \<in> {b<..})"
      by (rule prob_indep_random_variable[OF ind sa sb])
    moreover have "A a \<inter> B b = {\<omega> \<in> space M. X \<omega> \<in> {a<..} \<and> Y \<omega> \<in> {b<..}}"
      unfolding A_def B_def by auto
    ultimately show ?thesis
      unfolding A_def B_def by (simp add: Int_def)
  qed
  have low: "\<forall>\<^sub>F x in at_top. prob (A x) + prob (B x) - prob (A x) * prob (B x) \<le> prob (S x)"
  proof (rule always_eventually, intro allI)
    fix x
    have "prob (A x \<union> B x) = prob (A x) + prob (B x) - prob (A x \<inter> B x)"
      by (rule measure_Un3) (auto simp: fmeasurable_eq_sets)
    moreover have "prob (A x \<union> B x) \<le> prob (S x)"
    proof (rule finite_measure_mono)
      show "A x \<union> B x \<subseteq> S x"
      proof
        fix \<omega> assume "\<omega> \<in> A x \<union> B x"
        hence \<omega>: "\<omega> \<in> space M" and d: "x < X \<omega> \<or> x < Y \<omega>"
          unfolding A_def B_def by auto
        have "0 \<le> X \<omega>" "0 \<le> Y \<omega>" using X0[OF \<omega>] Y0[OF \<omega>] by auto
        with d have "x < X \<omega> + Y \<omega>" by linarith
        with \<omega> show "\<omega> \<in> S x" unfolding S_def by simp
      qed
    qed simp
    ultimately show "prob (A x) + prob (B x) - prob (A x) * prob (B x) \<le> prob (S x)"
      using both[of x x] by simp
  qed
  have subadd: "prob (P \<union> Q) \<le> prob P + prob Q" if "P \<in> sets M" "Q \<in> sets M" for P Q
  proof -
    have "prob (P \<union> Q) = prob P + prob Q - prob (P \<inter> Q)"
      by (rule measure_Un3) (use that in \<open>auto simp: fmeasurable_eq_sets\<close>)
    thus ?thesis using measure_nonneg[of M "P \<inter> Q"] by simp
  qed
  have up: "\<forall>\<^sub>F x in at_top. prob (S x) \<le> prob (A (x * (1 - \<delta>))) + prob (B (x * (1 - \<delta>)))
      + prob (A (x * \<delta>)) * prob (B (x * \<delta>))" for \<delta>
  proof (rule always_eventually, intro allI)
    fix x
    define a where "a = x * (1 - \<delta>)"
    define d where "d = x * \<delta>"
    have ad: "a + d = x" by (simp add: a_def d_def algebra_simps)
    have sub: "S x \<subseteq> A a \<union> (B a \<union> (A d \<inter> B d))"
    proof
      fix \<omega> assume "\<omega> \<in> S x"
      hence \<omega>: "\<omega> \<in> space M" "x < X \<omega> + Y \<omega>" unfolding S_def by auto
      show "\<omega> \<in> A a \<union> (B a \<union> (A d \<inter> B d))"
        using \<omega> ad unfolding A_def B_def by auto
    qed
    have "prob (S x) \<le> prob (A a \<union> (B a \<union> (A d \<inter> B d)))"
      by (rule finite_measure_mono[OF sub]) simp
    also have "\<dots> \<le> prob (A a) + prob (B a \<union> (A d \<inter> B d))"
      by (rule subadd) simp_all
    also have "\<dots> \<le> prob (A a) + (prob (B a) + prob (A d \<inter> B d))"
      using subadd[of "B a" "A d \<inter> B d"] by simp
    finally show "prob (S x) \<le> prob (A (x * (1 - \<delta>))) + prob (B (x * (1 - \<delta>)))
      + prob (A (x * \<delta>)) * prob (B (x * \<delta>))"
      using both[of d d] by (simp add: a_def d_def)
  qed
  have rvA: "regularly_varying (\<lambda>x. prob (A x)) (- \<alpha>)" using rv unfolding A_def .
  have raA: "((\<lambda>x. prob (B x) / prob (A x)) \<longlongrightarrow> c) at_top" using ratio unfolding A_def B_def .
  have "((\<lambda>x. prob (S x) / prob (A x)) \<longlongrightarrow> 1 + c) at_top"
    by (rule regularly_varying_sum_sandwich[OF rvA \<alpha> raA low up])
  thus ?thesis unfolding A_def S_def .
qed

text \<open>Two independent copies: the tail doubles.\<close>

corollary tail_sum_iid:
  fixes X Y :: "'a \<Rightarrow> real" and \<alpha> :: real
  assumes X: "X \<in> borel_measurable M" and Y: "Y \<in> borel_measurable M"
    and ind: "indep_var borel X borel Y"
    and X0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> X \<omega>" and Y0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> Y \<omega>"
    and same: "\<And>x. prob {\<omega> \<in> space M. x < Y \<omega>} = prob {\<omega> \<in> space M. x < X \<omega>}"
    and rv: "regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega>}) (- \<alpha>)" and \<alpha>: "0 < \<alpha>"
  shows "((\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega> + Y \<omega>} / prob {\<omega> \<in> space M. x < X \<omega>}) \<longlongrightarrow> 2) at_top"
proof -
  have pos: "\<forall>\<^sub>F x in at_top. 0 < prob {\<omega> \<in> space M. x < X \<omega>}"
    using eventually_gt_at_top[of "0::real"]
    by (rule eventually_mono) (rule regularly_varying_pos[OF rv])
  have "((\<lambda>x. 1 :: real) \<longlongrightarrow> 1) at_top" by simp
  moreover have "\<forall>\<^sub>F x in at_top. 1 = prob {\<omega> \<in> space M. x < Y \<omega>} / prob {\<omega> \<in> space M. x < X \<omega>}"
    using pos by (rule eventually_mono) (simp add: same)
  ultimately have r: "((\<lambda>x. prob {\<omega> \<in> space M. x < Y \<omega>} / prob {\<omega> \<in> space M. x < X \<omega>}) \<longlongrightarrow> 1) at_top"
    by (rule Lim_transform_eventually)
  show ?thesis
    using tail_sum_indep[OF X Y ind X0 Y0 rv \<alpha> r] by simp
qed

end

end
