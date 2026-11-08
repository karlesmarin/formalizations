(*  Title:      Heavy_Tail_Relations.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

theory Heavy_Tail_Relations
  imports Regular_Variation_Sums Breiman_Lemma Extreme_Value_Theory.Domain_of_Attraction
begin

section \<open>Relations between the heavy-tail theorems\<close>

text \<open>Closure of regular variation under asymptotic equivalence, the sum and product theorems for tails
  as regularly varying tails, their consequences for the Fr\'echet domain of attraction, the removal of two
  hypotheses of the sum theorem, the necessity of independence, and the principle of the single big jump.\<close>

subsection \<open>Closure under asymptotic equivalence\<close>

lemma regularly_varying_asymp_transfer:
  fixes T H :: "real \<Rightarrow> real" and \<rho> c :: real
  assumes rv: "regularly_varying T \<rho>" and c: "0 < c"
    and Hm: "H \<in> borel_measurable (restrict_space borel {0<..})"
    and Hpos: "\<And>x. 0 < x \<Longrightarrow> 0 < H x"
    and ratio: "((\<lambda>x. H x / T x) \<longlongrightarrow> c) at_top"
  shows "regularly_varying H \<rho>"
proof (rule regularly_varyingI[OF Hm Hpos])
  fix x :: real assume x: "0 < x"
  have r1: "((\<lambda>t. H (t * x) / T (t * x)) \<longlongrightarrow> c) at_top"
    using filterlim_compose[OF ratio filterlim_times_const_at_top[OF x]] by simp
  have r2: "((\<lambda>t. T (t * x) / T t) \<longlongrightarrow> x powr \<rho>) at_top"
    by (rule regularly_varying_lim[OF rv x])
  have r3: "((\<lambda>t. T t / H t) \<longlongrightarrow> inverse c) at_top"
  proof -
    have "((\<lambda>t. inverse (H t / T t)) \<longlongrightarrow> inverse c) at_top"
      by (rule tendsto_inverse[OF ratio]) (use c in simp)
    thus ?thesis by (simp add: inverse_divide)
  qed
  have A: "((\<lambda>t. H (t * x) / T (t * x) * (T (t * x) / T t) * (T t / H t)) \<longlongrightarrow> c * x powr \<rho> * inverse c) at_top"
    by (intro tendsto_mult r1 r2 r3)
  have C: "c * x powr \<rho> * inverse c = x powr \<rho>" using c by simp
  have B: "\<forall>\<^sub>F t in at_top. H (t * x) / T (t * x) * (T (t * x) / T t) * (T t / H t) = H (t * x) / H t"
  proof (rule eventually_mono[OF eventually_gt_at_top[of "0::real"]])
    fix t :: real assume t: "0 < t"
    have a1: "0 < T (t * x)" by (rule regularly_varying_pos[OF rv]) (use t x in simp)
    have a2: "0 < T t" by (rule regularly_varying_pos[OF rv t])
    have a3: "0 < H t" by (rule Hpos[OF t])
    show "H (t * x) / T (t * x) * (T (t * x) / T t) * (T t / H t) = H (t * x) / H t"
      using a1 a2 a3 by (simp add: field_simps)
  qed
  have D: "((\<lambda>t. H (t * x) / H t) \<longlongrightarrow> c * x powr \<rho> * inverse c) at_top"
    by (rule Lim_transform_eventually[OF A B])
  show "((\<lambda>t. H (t * x) / H t) \<longlongrightarrow> x powr \<rho>) at_top" using D C by simp
qed

subsection \<open>Tails of random variables\<close>

context prob_space
begin

lemma tail_antimono:
  fixes Z :: "'a \<Rightarrow> real"
  assumes Z[measurable]: "Z \<in> borel_measurable M" and xy: "x \<le> y"
  shows "prob {\<omega> \<in> space M. y < Z \<omega>} \<le> prob {\<omega> \<in> space M. x < Z \<omega>}"
proof (rule finite_measure_mono)
  show "{\<omega> \<in> space M. y < Z \<omega>} \<subseteq> {\<omega> \<in> space M. x < Z \<omega>}" using xy by auto
  show "{\<omega> \<in> space M. x < Z \<omega>} \<in> events" by measurable
qed

lemma tail_measurable:
  fixes Z :: "'a \<Rightarrow> real"
  assumes Z[measurable]: "Z \<in> borel_measurable M"
  shows "(\<lambda>x. prob {\<omega> \<in> space M. x < Z \<omega>}) \<in> borel_measurable (restrict_space borel {0<..})"
proof -
  have "mono (\<lambda>x. - prob {\<omega> \<in> space M. x < Z \<omega>})"
  proof (rule monoI)
    fix a b :: real assume "a \<le> b"
    thus "- prob {\<omega> \<in> space M. a < Z \<omega>} \<le> - prob {\<omega> \<in> space M. b < Z \<omega>}"
      using tail_antimono[OF Z \<open>a \<le> b\<close>] by simp
  qed
  hence "(\<lambda>x. - prob {\<omega> \<in> space M. x < Z \<omega>}) \<in> borel_measurable borel"
    by (rule borel_measurable_mono)
  hence "(\<lambda>x. - (- prob {\<omega> \<in> space M. x < Z \<omega>})) \<in> borel_measurable borel"
    by (rule borel_measurable_uminus)
  hence "(\<lambda>x. prob {\<omega> \<in> space M. x < Z \<omega>}) \<in> borel_measurable borel" by simp
  thus ?thesis by (rule measurable_restrict_space1)
qed

lemma cdf_eq_prob:
  fixes Z :: "'a \<Rightarrow> real"
  assumes Z[measurable]: "Z \<in> borel_measurable M"
  shows "cdf (distr M borel Z) x = prob {\<omega> \<in> space M. Z \<omega> \<le> x}"
proof -
  have s: "Z -` {..x} \<inter> space M = {\<omega> \<in> space M. Z \<omega> \<le> x}" by auto
  have "measure (distr M borel Z) {..x} = measure M (Z -` {..x} \<inter> space M)"
    by (rule measure_distr) auto
  thus ?thesis unfolding cdf_def using s by simp
qed

lemma tail_cdf:
  fixes Z :: "'a \<Rightarrow> real"
  assumes Z[measurable]: "Z \<in> borel_measurable M"
  shows "prob {\<omega> \<in> space M. x < Z \<omega>} = 1 - cdf (distr M borel Z) x"
proof -
  have "{\<omega> \<in> space M. x < Z \<omega>} = space M - {\<omega> \<in> space M. Z \<omega> \<le> x}" by auto
  hence "prob {\<omega> \<in> space M. x < Z \<omega>} = prob (space M - {\<omega> \<in> space M. Z \<omega> \<le> x})" by simp
  also have "\<dots> = 1 - prob {\<omega> \<in> space M. Z \<omega> \<le> x}"
    by (rule prob_compl) measurable
  finally show ?thesis using cdf_eq_prob[OF Z] by simp
qed

lemma tail_tendsto_0:
  fixes Z :: "'a \<Rightarrow> real"
  assumes Z[measurable]: "Z \<in> borel_measurable M"
  shows "((\<lambda>x. prob {\<omega> \<in> space M. x < Z \<omega>}) \<longlongrightarrow> 0) at_top"
proof -
  have rd: "real_distribution (distr M borel Z)" by (rule real_distribution_distr) simp
  have "((\<lambda>x. 1 - cdf (distr M borel Z) x) \<longlongrightarrow> 1 - 1) at_top"
    by (intro tendsto_diff tendsto_const real_distribution.cdf_lim_at_top_prob[OF rd])
  moreover have "(\<lambda>x. prob {\<omega> \<in> space M. x < Z \<omega>}) = (\<lambda>x. 1 - cdf (distr M borel Z) x)"
    by (rule ext) (rule tail_cdf[OF Z])
  ultimately show ?thesis by simp
qed

lemma left_tail_tendsto_0:
  fixes Z :: "'a \<Rightarrow> real"
  assumes Z[measurable]: "Z \<in> borel_measurable M"
  shows "((\<lambda>y. prob {\<omega> \<in> space M. Z \<omega> \<le> - y}) \<longlongrightarrow> 0) at_top"
proof -
  have rd: "real_distribution (distr M borel Z)" by (rule real_distribution_distr) simp
  interpret D: real_distribution "distr M borel Z" by (rule rd)
  have u: "filterlim (\<lambda>y::real. - y) at_bot at_top"
    by (rule filterlim_uminus_at_bot_at_top)
  have "((\<lambda>y. cdf (distr M borel Z) (- y)) \<longlongrightarrow> 0) at_top"
    by (rule filterlim_compose[OF D.cdf_lim_at_bot u])
  moreover have "\<And>y. cdf (distr M borel Z) (- y) = prob {\<omega> \<in> space M. Z \<omega> \<le> - y}"
    by (rule cdf_eq_prob[OF Z])
  ultimately show ?thesis by simp
qed

lemma tail_pos_all:
  fixes Z :: "'a \<Rightarrow> real"
  assumes Z[measurable]: "Z \<in> borel_measurable M"
    and ev: "\<forall>\<^sub>F x in at_top. 0 < prob {\<omega> \<in> space M. x < Z \<omega>}"
  shows "0 < prob {\<omega> \<in> space M. x < Z \<omega>}"
proof -
  obtain N where N: "\<And>y. N \<le> y \<Longrightarrow> 0 < prob {\<omega> \<in> space M. y < Z \<omega>}"
    using ev by (auto simp: eventually_at_top_linorder)
  have "0 < prob {\<omega> \<in> space M. max x N < Z \<omega>}" by (rule N) simp
  moreover have "prob {\<omega> \<in> space M. max x N < Z \<omega>} \<le> prob {\<omega> \<in> space M. x < Z \<omega>}"
    by (rule tail_antimono[OF Z]) simp
  ultimately show ?thesis by linarith
qed

text \<open>A tail asymptotic to a positive multiple of a regularly varying function is regularly varying of
  the same index (and positive everywhere).\<close>

lemma tail_rv_of_ratio:
  fixes Z :: "'a \<Rightarrow> real" and T :: "real \<Rightarrow> real" and \<rho> c :: real
  assumes Z[measurable]: "Z \<in> borel_measurable M"
    and rv: "regularly_varying T \<rho>" and c: "0 < c"
    and ratio: "((\<lambda>x. prob {\<omega> \<in> space M. x < Z \<omega>} / T x) \<longlongrightarrow> c) at_top"
  shows "(\<forall>x. 0 < prob {\<omega> \<in> space M. x < Z \<omega>})
    \<and> regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < Z \<omega>}) \<rho>"
proof -
  have Tpos: "\<forall>\<^sub>F x in at_top. 0 < T x"
    using eventually_gt_at_top[of "0::real"] by (rule eventually_mono) (rule regularly_varying_pos[OF rv])
  have ev: "\<forall>\<^sub>F x in at_top. 0 < prob {\<omega> \<in> space M. x < Z \<omega>}"
    using order_tendstoD(1)[OF ratio c] Tpos
    by eventually_elim (auto simp: zero_less_divide_iff)
  have pos: "\<And>x. 0 < prob {\<omega> \<in> space M. x < Z \<omega>}" by (rule tail_pos_all[OF Z ev])
  show ?thesis
    using regularly_varying_asymp_transfer[OF rv c tail_measurable[OF Z] pos ratio] pos by blast
qed

end

subsection \<open>The sum theorem: sandwich without sign conditions\<close>

text \<open>The sandwich lemma of the theory on sums above, without any condition on the index \<open>\<alpha>\<close> and with the lower
  bound \<open>P(X > (1+\<delta>)x, Y > -\<delta>x)\<close> and its symmetric: the hypothesis \<open>T \<longrightarrow> 0\<close> replaces \<open>0 < \<alpha>\<close>;
  \<open>Lx\<close>, \<open>Ly\<close> are the left tails.\<close>

lemma regularly_varying_sum_sandwich_gen:
  fixes T G H Lx Ly :: "real \<Rightarrow> real" and \<alpha> c :: real
  assumes rv: "regularly_varying T (- \<alpha>)" and T0: "(T \<longlongrightarrow> 0) at_top"
    and Lx: "(Lx \<longlongrightarrow> 0) at_top" and Ly: "(Ly \<longlongrightarrow> 0) at_top"
    and ratio: "((\<lambda>x. G x / T x) \<longlongrightarrow> c) at_top"
    and low: "\<And>\<delta>. 0 < \<delta> \<Longrightarrow> \<forall>\<^sub>F x in at_top.
      T (x * (1 + \<delta>)) * (1 - Ly (x * \<delta>)) + G (x * (1 + \<delta>)) * (1 - Lx (x * \<delta>))
        - T (x * (1 + \<delta>)) * G (x * (1 + \<delta>)) \<le> H x"
    and up: "\<And>\<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < 1 / 2 \<Longrightarrow>
      \<forall>\<^sub>F x in at_top. H x \<le> T (x * (1 - \<delta>)) + G (x * (1 - \<delta>)) + T (x * \<delta>) * G (x * \<delta>)"
  shows "((\<lambda>x. H x / T x) \<longlongrightarrow> 1 + c) at_top"
proof -
  have Tpos: "\<forall>\<^sub>F x in at_top. 0 < T x"
    using eventually_gt_at_top[of "0::real"]
    by (rule eventually_mono) (rule regularly_varying_pos[OF rv])
  have G0: "(G \<longlongrightarrow> 0) at_top"
  proof -
    have "((\<lambda>x. G x / T x * T x) \<longlongrightarrow> 0) at_top"
      using tendsto_mult[OF ratio T0] by simp
    moreover have "\<forall>\<^sub>F x in at_top. G x / T x * T x = G x"
      using Tpos by (rule eventually_mono) simp
    ultimately show ?thesis by (rule Lim_transform_eventually)
  qed
  have lowlim: "((\<lambda>x. T (x * (1 + \<delta>)) / T x * (1 - Ly (x * \<delta>)) + G (x * (1 + \<delta>)) / T x * (1 - Lx (x * \<delta>))
      - T (x * (1 + \<delta>)) / T x * G (x * (1 + \<delta>))) \<longlongrightarrow> (1 + c) * (1 + \<delta>) powr (- \<alpha>)) at_top"
    if \<delta>: "0 < \<delta>" for \<delta>
  proof -
    have b: "0 < 1 + \<delta>" using \<delta> by simp
    have r1: "((\<lambda>x. T (x * (1 + \<delta>)) / T x) \<longlongrightarrow> (1 + \<delta>) powr (- \<alpha>)) at_top"
      by (rule regularly_varying_lim[OF rv b])
    have g1: "((\<lambda>x. G (x * (1 + \<delta>)) / T (x * (1 + \<delta>))) \<longlongrightarrow> c) at_top"
      using filterlim_compose[OF ratio filterlim_times_const_at_top[OF b]] by simp
    have g0: "((\<lambda>x. G (x * (1 + \<delta>))) \<longlongrightarrow> 0) at_top"
      using filterlim_compose[OF G0 filterlim_times_const_at_top[OF b]] by simp
    have l1: "((\<lambda>x. Ly (x * \<delta>)) \<longlongrightarrow> 0) at_top"
      using filterlim_compose[OF Ly filterlim_times_const_at_top[OF \<delta>]] by simp
    have l2: "((\<lambda>x. Lx (x * \<delta>)) \<longlongrightarrow> 0) at_top"
      using filterlim_compose[OF Lx filterlim_times_const_at_top[OF \<delta>]] by simp
    have Tb: "\<forall>\<^sub>F x in at_top. 0 < T (x * (1 + \<delta>))"
      using eventually_gt_at_top[of "0::real"]
      by (rule eventually_mono) (rule regularly_varying_pos[OF rv], use b in simp)
    have a2: "((\<lambda>x. G (x * (1 + \<delta>)) / T x) \<longlongrightarrow> c * (1 + \<delta>) powr (- \<alpha>)) at_top"
    proof -
      have "((\<lambda>x. G (x * (1 + \<delta>)) / T (x * (1 + \<delta>)) * (T (x * (1 + \<delta>)) / T x))
          \<longlongrightarrow> c * (1 + \<delta>) powr (- \<alpha>)) at_top"
        by (rule tendsto_mult[OF g1 r1])
      moreover have "\<forall>\<^sub>F x in at_top. G (x * (1 + \<delta>)) / T (x * (1 + \<delta>)) * (T (x * (1 + \<delta>)) / T x)
          = G (x * (1 + \<delta>)) / T x"
        using Tb by (rule eventually_mono) simp
      ultimately show ?thesis by (rule Lim_transform_eventually)
    qed
    have "((\<lambda>x. T (x * (1 + \<delta>)) / T x * (1 - Ly (x * \<delta>)) + G (x * (1 + \<delta>)) / T x * (1 - Lx (x * \<delta>))
        - T (x * (1 + \<delta>)) / T x * G (x * (1 + \<delta>)))
        \<longlongrightarrow> (1 + \<delta>) powr (- \<alpha>) * (1 - 0) + c * (1 + \<delta>) powr (- \<alpha>) * (1 - 0)
          - (1 + \<delta>) powr (- \<alpha>) * 0) at_top"
      by (intro tendsto_diff tendsto_add tendsto_mult tendsto_const r1 a2 g0 l1 l2)
    thus ?thesis by (simp add: algebra_simps)
  qed
  have lowev: "\<forall>\<^sub>F x in at_top. T (x * (1 + \<delta>)) / T x * (1 - Ly (x * \<delta>)) + G (x * (1 + \<delta>)) / T x * (1 - Lx (x * \<delta>))
      - T (x * (1 + \<delta>)) / T x * G (x * (1 + \<delta>)) \<le> H x / T x" if \<delta>: "0 < \<delta>" for \<delta>
    using low[OF \<delta>] Tpos
  proof eventually_elim
    case (elim x)
    have Tx: "T x \<noteq> 0" using elim(2) by simp
    have "T (x * (1 + \<delta>)) / T x * (1 - Ly (x * \<delta>)) + G (x * (1 + \<delta>)) / T x * (1 - Lx (x * \<delta>))
      - T (x * (1 + \<delta>)) / T x * G (x * (1 + \<delta>))
      = (T (x * (1 + \<delta>)) * (1 - Ly (x * \<delta>)) + G (x * (1 + \<delta>)) * (1 - Lx (x * \<delta>))
        - T (x * (1 + \<delta>)) * G (x * (1 + \<delta>))) / T x"
      using Tx by (simp add: field_simps)
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
    have "((\<lambda>\<delta>. (1 + c) * (1 + \<delta>) powr (- \<alpha>)) \<longlongrightarrow> (1 + c) * (1 + 0) powr (- \<alpha>)) (at_right (0::real))"
      by (intro tendsto_mult tendsto_const tendsto_powr tendsto_add tendsto_ident_at) simp
    hence lim: "((\<lambda>\<delta>. (1 + c) * (1 + \<delta>) powr (- \<alpha>)) \<longlongrightarrow> 1 + c) (at_right (0::real))"
      by simp
    obtain \<delta> :: real where \<delta>: "0 < \<delta>" and U: "a < (1 + c) * (1 + \<delta>) powr (- \<alpha>)"
      using eventually_happens'[OF trivial_limit_at_right_real
          eventually_conj[OF order_tendstoD(1)[OF lim a] eventually_at_right_less[of 0]]]
      by auto
    show "\<forall>\<^sub>F x in at_top. a < H x / T x"
      using order_tendstoD(1)[OF lowlim[OF \<delta>] U] lowev[OF \<delta>]
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

text \<open>Theorem C.  Compared with \<open>tail_sum_indep\<close>: no sign condition on \<open>\<alpha>\<close> (here \<open>T \<longrightarrow> 0\<close> comes from
  \<open>T\<close> being the tail of a real random variable; a regularly varying tail of a probability has index
  \<open>-\<alpha> \<le> 0\<close> anyway), and neither \<open>X \<ge> 0\<close> nor \<open>Y \<ge> 0\<close>.\<close>

theorem tail_sum_indep_gen:
  fixes X Y :: "'a \<Rightarrow> real" and \<alpha> c :: real
  assumes X[measurable]: "X \<in> borel_measurable M" and Y[measurable]: "Y \<in> borel_measurable M"
    and ind: "indep_var borel X borel Y"
    and rv: "regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega>}) (- \<alpha>)"
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
  have cA: "prob (A (- d)) = 1 - prob {\<omega> \<in> space M. X \<omega> \<le> - d}" for d
  proof -
    have "A (- d) = space M - {\<omega> \<in> space M. X \<omega> \<le> - d}" unfolding A_def by auto
    hence "prob (A (- d)) = prob (space M - {\<omega> \<in> space M. X \<omega> \<le> - d})" by simp
    also have "\<dots> = 1 - prob {\<omega> \<in> space M. X \<omega> \<le> - d}" by (rule prob_compl) measurable
    finally show ?thesis .
  qed
  have cB: "prob (B (- d)) = 1 - prob {\<omega> \<in> space M. Y \<omega> \<le> - d}" for d
  proof -
    have "B (- d) = space M - {\<omega> \<in> space M. Y \<omega> \<le> - d}" unfolding B_def by auto
    hence "prob (B (- d)) = prob (space M - {\<omega> \<in> space M. Y \<omega> \<le> - d})" by simp
    also have "\<dots> = 1 - prob {\<omega> \<in> space M. Y \<omega> \<le> - d}" by (rule prob_compl) measurable
    finally show ?thesis .
  qed
  have low: "\<forall>\<^sub>F x in at_top.
      prob (A (x * (1 + \<delta>))) * (1 - prob {\<omega> \<in> space M. Y \<omega> \<le> - (x * \<delta>)})
      + prob (B (x * (1 + \<delta>))) * (1 - prob {\<omega> \<in> space M. X \<omega> \<le> - (x * \<delta>)})
      - prob (A (x * (1 + \<delta>))) * prob (B (x * (1 + \<delta>))) \<le> prob (S x)" for \<delta>
  proof (rule always_eventually, intro allI)
    fix x :: real
    define a where "a = x * (1 + \<delta>)"
    define d where "d = x * \<delta>"
    have ad: "a - d = x" by (simp add: a_def d_def algebra_simps)
    define U where "U = A a \<inter> B (- d)"
    define V where "V = B a \<inter> A (- d)"
    have Us[measurable]: "U \<in> sets M" and Vs[measurable]: "V \<in> sets M" unfolding U_def V_def by measurable
    have pU: "prob U = prob (A a) * (1 - prob {\<omega> \<in> space M. Y \<omega> \<le> - d})"
      unfolding U_def by (simp add: both cB)
    have eV: "V = A (- d) \<inter> B a" unfolding V_def by auto
    have pV: "prob V = prob (B a) * (1 - prob {\<omega> \<in> space M. X \<omega> \<le> - d})"
      by (simp add: eV both cA mult.commute)
    have UV: "prob (U \<inter> V) \<le> prob (A a) * prob (B a)"
    proof -
      have "prob (U \<inter> V) \<le> prob (A a \<inter> B a)"
      proof (rule finite_measure_mono)
        show "U \<inter> V \<subseteq> A a \<inter> B a" unfolding U_def V_def by auto
        show "A a \<inter> B a \<in> events" by measurable
      qed
      thus ?thesis by (simp add: both)
    qed
    have un: "prob (U \<union> V) = prob U + prob V - prob (U \<inter> V)"
      by (rule measure_Un3) (auto simp: fmeasurable_eq_sets)
    have sub: "prob (U \<union> V) \<le> prob (S x)"
    proof (rule finite_measure_mono)
      show "U \<union> V \<subseteq> S x"
      proof
        fix \<omega> assume "\<omega> \<in> U \<union> V"
        hence \<omega>: "\<omega> \<in> space M" and d: "(a < X \<omega> \<and> - d < Y \<omega>) \<or> (a < Y \<omega> \<and> - d < X \<omega>)"
          unfolding U_def V_def A_def B_def by auto
        have "x < X \<omega> + Y \<omega>" using d ad by linarith
        with \<omega> show "\<omega> \<in> S x" unfolding S_def by simp
      qed
      show "S x \<in> events" by measurable
    qed
    show "prob (A (x * (1 + \<delta>))) * (1 - prob {\<omega> \<in> space M. Y \<omega> \<le> - (x * \<delta>)})
      + prob (B (x * (1 + \<delta>))) * (1 - prob {\<omega> \<in> space M. X \<omega> \<le> - (x * \<delta>)})
      - prob (A (x * (1 + \<delta>))) * prob (B (x * (1 + \<delta>))) \<le> prob (S x)"
      using pU pV UV un sub unfolding a_def d_def by linarith
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
  have T0: "((\<lambda>x. prob (A x)) \<longlongrightarrow> 0) at_top" unfolding A_def by (rule tail_tendsto_0[OF X])
  have raA: "((\<lambda>x. prob (B x) / prob (A x)) \<longlongrightarrow> c) at_top" using ratio unfolding A_def B_def .
  have "((\<lambda>x. prob (S x) / prob (A x)) \<longlongrightarrow> 1 + c) at_top"
    by (rule regularly_varying_sum_sandwich_gen[OF rvA T0
          left_tail_tendsto_0[OF X] left_tail_tendsto_0[OF Y] raA low up])
  thus ?thesis unfolding A_def S_def .
qed

subsection \<open>Corollaries: the tails of X + Y and of X * Z are regularly varying\<close>

corollary tail_sum_indep_rv:
  fixes X Y :: "'a \<Rightarrow> real" and \<alpha> c :: real
  assumes X[measurable]: "X \<in> borel_measurable M" and Y[measurable]: "Y \<in> borel_measurable M"
    and ind: "indep_var borel X borel Y"
    and rv: "regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega>}) (- \<alpha>)"
    and ratio: "((\<lambda>x. prob {\<omega> \<in> space M. x < Y \<omega>} / prob {\<omega> \<in> space M. x < X \<omega>}) \<longlongrightarrow> c) at_top"
  shows "(\<forall>x. 0 < prob {\<omega> \<in> space M. x < X \<omega> + Y \<omega>})
    \<and> regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega> + Y \<omega>}) (- \<alpha>)"
proof -
  have c0: "0 \<le> c"
  proof (rule tendsto_lowerbound[OF ratio])
    show "\<forall>\<^sub>F x in at_top. 0 \<le> prob {\<omega> \<in> space M. x < Y \<omega>} / prob {\<omega> \<in> space M. x < X \<omega>}"
      by (rule always_eventually, intro allI divide_nonneg_nonneg measure_nonneg)
  qed simp
  have Zm: "(\<lambda>\<omega>. X \<omega> + Y \<omega>) \<in> borel_measurable M" by measurable
  have r: "((\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega> + Y \<omega>} / prob {\<omega> \<in> space M. x < X \<omega>}) \<longlongrightarrow> 1 + c) at_top"
    by (rule tail_sum_indep_gen[OF X Y ind rv ratio])
  have c1: "0 < 1 + c" using c0 by simp
  show ?thesis by (rule tail_rv_of_ratio[OF Zm rv c1 r])
qed

corollary breiman_rv:
  fixes X Z :: "'a \<Rightarrow> real" and \<alpha> \<epsilon> :: real
  assumes X[measurable]: "X \<in> borel_measurable M" and Z[measurable]: "Z \<in> borel_measurable M"
    and ind: "indep_var borel X borel Z"
    and X0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> X \<omega>" and Z0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> Z \<omega>"
    and rv: "regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega>}) (- \<alpha>)" and \<alpha>: "0 < \<alpha>"
    and \<epsilon>: "0 < \<epsilon>"
    and int: "integrable M (\<lambda>\<omega>. Z \<omega> powr (\<alpha> + \<epsilon>))"
    and E: "0 < expectation (\<lambda>\<omega>. Z \<omega> powr \<alpha>)"
  shows "(\<forall>x. 0 < prob {\<omega> \<in> space M. x < X \<omega> * Z \<omega>})
    \<and> regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega> * Z \<omega>}) (- \<alpha>)"
proof -
  have Zm: "(\<lambda>\<omega>. X \<omega> * Z \<omega>) \<in> borel_measurable M" by measurable
  have r: "((\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega> * Z \<omega>} / prob {\<omega> \<in> space M. x < X \<omega>})
    \<longlongrightarrow> expectation (\<lambda>\<omega>. Z \<omega> powr \<alpha>)) at_top"
    by (rule breiman[OF X Z ind X0 Z0 rv \<alpha> \<epsilon> int])
  show ?thesis by (rule tail_rv_of_ratio[OF Zm rv E r])
qed

subsection \<open>Independence is necessary\<close>

text \<open>With \<open>Y = X\<close> (the extreme case of dependence) the ratio tends to \<open>2 powr \<alpha>\<close>, not to \<open>2\<close>.\<close>

theorem tail_sum_self:
  fixes X :: "'a \<Rightarrow> real" and \<alpha> :: real
  assumes rv: "regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega>}) (- \<alpha>)"
  shows "((\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega> + X \<omega>} / prob {\<omega> \<in> space M. x < X \<omega>})
    \<longlongrightarrow> 2 powr \<alpha>) at_top"
proof -
  have h: "prob {\<omega> \<in> space M. x < X \<omega> + X \<omega>} = prob {\<omega> \<in> space M. x * (1 / 2) < X \<omega>}" for x
  proof -
    have "{\<omega> \<in> space M. x < X \<omega> + X \<omega>} = {\<omega> \<in> space M. x * (1 / 2) < X \<omega>}" by auto
    thus ?thesis by simp
  qed
  have lim: "((\<lambda>t. prob {\<omega> \<in> space M. t * (1 / 2) < X \<omega>} / prob {\<omega> \<in> space M. t < X \<omega>})
      \<longlongrightarrow> (1 / 2) powr (- \<alpha>)) at_top"
    by (rule regularly_varying_lim[OF rv]) simp
  have eq2: "(1 / 2 :: real) powr (- \<alpha>) = 2 powr \<alpha>"
    using powr_inv_helper[of 2 "- \<alpha>"] by simp
  have fe: "(\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega> + X \<omega>} / prob {\<omega> \<in> space M. x < X \<omega>})
      = (\<lambda>t. prob {\<omega> \<in> space M. t * (1 / 2) < X \<omega>} / prob {\<omega> \<in> space M. t < X \<omega>})"
    by (rule ext) (simp only: h)
  show ?thesis unfolding fe eq2[symmetric] by (rule lim)
qed

text \<open>Hence the conclusion of \<open>tail_sum_iid\<close> (ratio tends to 2) is false for \<open>Y = X\<close>, which has the same tail
  as \<open>X\<close> and the same sign, as soon as \<open>\<alpha> \<noteq> 1\<close>.\<close>

corollary tail_sum_iid_needs_independence:
  fixes X :: "'a \<Rightarrow> real" and \<alpha> :: real
  assumes rv: "regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega>}) (- \<alpha>)" and \<alpha>: "\<alpha> \<noteq> 1"
  shows "\<not> ((\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega> + X \<omega>} / prob {\<omega> \<in> space M. x < X \<omega>})
    \<longlongrightarrow> 2) at_top"
proof
  assume 2: "((\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega> + X \<omega>} / prob {\<omega> \<in> space M. x < X \<omega>}) \<longlongrightarrow> 2) at_top"
  have "(2 :: real) = 2 powr \<alpha>"
    by (rule tendsto_unique[OF _ 2 tail_sum_self[OF rv]]) simp
  hence h: "(2 :: real) powr 1 = 2 powr \<alpha>" by simp
  have a1: "\<not> \<alpha> < 1"
  proof
    assume "\<alpha> < 1"
    hence "(2::real) powr \<alpha> < 2 powr 1" by (subst powr_less_cancel_iff) simp_all
    thus False using h by linarith
  qed
  have a2: "\<not> 1 < \<alpha>"
  proof
    assume "1 < \<alpha>"
    hence "(2::real) powr 1 < 2 powr \<alpha>" by (subst powr_less_cancel_iff) simp_all
    thus False using h by linarith
  qed
  from a1 a2 have "\<alpha> = 1" by linarith
  with \<alpha> show False by simp
qed

subsection \<open>Connection with extreme value theory: the Fr\'echet domain of attraction\<close>

text \<open>The cdf of \<open>Z\<close> is \<open>cdf (distr M borel Z)\<close>, whose complement is the tail.  By the theorem of the
  entry on extreme value theory (\<open>MDA_regularly_varying_pos\<close>), the cdf is in the domain of attraction of
  \<open>EVD_cdf \<gamma> 0 1\<close> (\<open>\<gamma> > 0\<close>) iff the tail is positive everywhere and regularly varying of index \<open>-1/\<gamma>\<close>.\<close>

lemma frechet_domain_iff_tail:
  fixes Z :: "'a \<Rightarrow> real" and \<gamma> :: real
  assumes Z[measurable]: "Z \<in> borel_measurable M" and \<gamma>: "0 < \<gamma>"
  shows "domain_of_attraction (cdf (distr M borel Z)) (EVD_cdf \<gamma> 0 1)
    \<longleftrightarrow> (\<forall>x. 0 < prob {\<omega> \<in> space M. x < Z \<omega>})
      \<and> regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < Z \<omega>}) (- (1 / \<gamma>))"
proof -
  have rd: "real_distribution (distr M borel Z)" by (rule real_distribution_distr) simp
  have rcm: "right_continuous_mono (cdf (distr M borel Z)) 0 1" by (rule right_continuous_mono_cdf[OF rd])
  have t: "\<And>x. prob {\<omega> \<in> space M. x < Z \<omega>} = 1 - cdf (distr M borel Z) x" by (rule tail_cdf[OF Z])
  have lt: "\<And>x. (0 < prob {\<omega> \<in> space M. x < Z \<omega>}) = (cdf (distr M borel Z) x < 1)" by (simp add: t)
  have M: "domain_of_attraction (cdf (distr M borel Z)) (EVD_cdf \<gamma> 0 1)
    \<longleftrightarrow> (\<forall>x. cdf (distr M borel Z) x < 1)
      \<and> regularly_varying (\<lambda>x. 1 - cdf (distr M borel Z) x) (- 1 / \<gamma>)"
    by (rule MDA_regularly_varying_pos[OF rcm \<gamma>])
  show ?thesis unfolding M by (simp add: lt[symmetric] t[symmetric])
qed

theorem frechet_domain_sum:
  fixes X Y :: "'a \<Rightarrow> real" and \<gamma> c :: real
  assumes X[measurable]: "X \<in> borel_measurable M" and Y[measurable]: "Y \<in> borel_measurable M"
    and ind: "indep_var borel X borel Y" and \<gamma>: "0 < \<gamma>"
    and dom: "domain_of_attraction (cdf (distr M borel X)) (EVD_cdf \<gamma> 0 1)"
    and ratio: "((\<lambda>x. prob {\<omega> \<in> space M. x < Y \<omega>} / prob {\<omega> \<in> space M. x < X \<omega>}) \<longlongrightarrow> c) at_top"
  shows "domain_of_attraction (cdf (distr M borel (\<lambda>\<omega>. X \<omega> + Y \<omega>))) (EVD_cdf \<gamma> 0 1)"
proof -
  have Zm: "(\<lambda>\<omega>. X \<omega> + Y \<omega>) \<in> borel_measurable M" by measurable
  have rvX: "regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega>}) (- (1 / \<gamma>))"
    using dom frechet_domain_iff_tail[OF X \<gamma>] by blast
  have "(\<forall>x. 0 < prob {\<omega> \<in> space M. x < X \<omega> + Y \<omega>})
    \<and> regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega> + Y \<omega>}) (- (1 / \<gamma>))"
    by (rule tail_sum_indep_rv[OF X Y ind rvX ratio])
  thus ?thesis using frechet_domain_iff_tail[OF Zm \<gamma>] by blast
qed

theorem frechet_domain_product:
  fixes X Z :: "'a \<Rightarrow> real" and \<gamma> \<epsilon> :: real
  assumes X[measurable]: "X \<in> borel_measurable M" and Z[measurable]: "Z \<in> borel_measurable M"
    and ind: "indep_var borel X borel Z"
    and X0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> X \<omega>" and Z0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> Z \<omega>"
    and \<gamma>: "0 < \<gamma>" and \<epsilon>: "0 < \<epsilon>"
    and dom: "domain_of_attraction (cdf (distr M borel X)) (EVD_cdf \<gamma> 0 1)"
    and int: "integrable M (\<lambda>\<omega>. Z \<omega> powr (1 / \<gamma> + \<epsilon>))"
    and E: "0 < expectation (\<lambda>\<omega>. Z \<omega> powr (1 / \<gamma>))"
  shows "domain_of_attraction (cdf (distr M borel (\<lambda>\<omega>. X \<omega> * Z \<omega>))) (EVD_cdf \<gamma> 0 1)"
proof -
  have Zm: "(\<lambda>\<omega>. X \<omega> * Z \<omega>) \<in> borel_measurable M" by measurable
  have rvX: "regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega>}) (- (1 / \<gamma>))"
    using dom frechet_domain_iff_tail[OF X \<gamma>] by blast
  have a: "0 < 1 / \<gamma>" using \<gamma> by simp
  have "(\<forall>x. 0 < prob {\<omega> \<in> space M. x < X \<omega> * Z \<omega>})
    \<and> regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < X \<omega> * Z \<omega>}) (- (1 / \<gamma>))"
    by (rule breiman_rv[OF X Z ind X0 Z0 rvX a \<epsilon> int E])
  thus ?thesis using frechet_domain_iff_tail[OF Zm \<gamma>] by blast
qed

subsection \<open>The principle of the single big jump\<close>

lemma prob_max_indep:
  fixes U V :: "'a \<Rightarrow> real"
  assumes U[measurable]: "U \<in> borel_measurable M" and V[measurable]: "V \<in> borel_measurable M"
    and ind: "indep_var borel U borel V"
  shows "prob {\<omega> \<in> space M. x < max (U \<omega>) (V \<omega>)}
    = prob {\<omega> \<in> space M. x < U \<omega>} + prob {\<omega> \<in> space M. x < V \<omega>}
      - prob {\<omega> \<in> space M. x < U \<omega>} * prob {\<omega> \<in> space M. x < V \<omega>}"
proof -
  define P where "P = {\<omega> \<in> space M. x < U \<omega>}"
  define Q where "Q = {\<omega> \<in> space M. x < V \<omega>}"
  have Ps[measurable]: "P \<in> sets M" and Qs[measurable]: "Q \<in> sets M" unfolding P_def Q_def by measurable
  have sa: "{x<..} \<in> sets (borel :: real measure)" by auto
  have "\<P>(\<omega> in M. U \<omega> \<in> {x<..} \<and> V \<omega> \<in> {x<..}) = \<P>(\<omega> in M. U \<omega> \<in> {x<..}) * \<P>(\<omega> in M. V \<omega> \<in> {x<..})"
    by (rule prob_indep_random_variable[OF ind sa sa])
  moreover have "P \<inter> Q = {\<omega> \<in> space M. U \<omega> \<in> {x<..} \<and> V \<omega> \<in> {x<..}}" unfolding P_def Q_def by auto
  moreover have "P = {\<omega> \<in> space M. U \<omega> \<in> {x<..}}" "Q = {\<omega> \<in> space M. V \<omega> \<in> {x<..}}"
    unfolding P_def Q_def by auto
  ultimately have b: "prob (P \<inter> Q) = prob P * prob Q" by simp
  have "{\<omega> \<in> space M. x < max (U \<omega>) (V \<omega>)} = P \<union> Q" unfolding P_def Q_def by auto
  moreover have "prob (P \<union> Q) = prob P + prob Q - prob (P \<inter> Q)"
    by (rule measure_Un3) (auto simp: fmeasurable_eq_sets)
  ultimately show ?thesis using b unfolding P_def Q_def by simp
qed

lemma big_jump_sum_aux:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real" and \<alpha> :: real
  assumes Xm: "\<And>i. X i \<in> borel_measurable M"
    and same: "\<And>i x. prob {\<omega> \<in> space M. x < X i \<omega>} = prob {\<omega> \<in> space M. x < X 0 \<omega>}"
    and rv: "regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < X 0 \<omega>}) (- \<alpha>)"
  shows "indep_vars (\<lambda>_. borel) X {0..<Suc k} \<Longrightarrow>
    ((\<lambda>x. prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<Suc k}. X i \<omega>)} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
      \<longlongrightarrow> real (Suc k)) at_top"
proof (induction k)
  case 0
  have pos: "\<forall>\<^sub>F x in at_top. 0 < prob {\<omega> \<in> space M. x < X 0 \<omega>}"
    using eventually_gt_at_top[of "0::real"]
    by (rule eventually_mono) (rule regularly_varying_pos[OF rv])
  have sb: "\<And>x. prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<Suc 0}. X i \<omega>)} = prob {\<omega> \<in> space M. x < X 0 \<omega>}"
    by simp
  have "((\<lambda>x. 1 :: real) \<longlongrightarrow> 1) at_top" by simp
  moreover have "\<forall>\<^sub>F x in at_top. 1 = prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<Suc 0}. X i \<omega>)}
      / prob {\<omega> \<in> space M. x < X 0 \<omega>}"
    using pos
  proof eventually_elim
    case (elim x)
    hence ne: "prob {\<omega> \<in> space M. x < X 0 \<omega>} \<noteq> 0" by simp
    show ?case by (simp only: sb) (simp add: ne)
  qed
  ultimately have "((\<lambda>x. prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<Suc 0}. X i \<omega>)}
      / prob {\<omega> \<in> space M. x < X 0 \<omega>}) \<longlongrightarrow> 1) at_top"
    by (rule Lim_transform_eventually)
  thus ?case by simp
next
  case (Suc k)
  have indk: "indep_vars (\<lambda>_. borel) X {0..<Suc k}"
    by (rule indep_vars_subset[OF Suc.prems]) auto
  have IH: "((\<lambda>x. prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<Suc k}. X i \<omega>)} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
      \<longlongrightarrow> real (Suc k)) at_top"
    by (rule Suc.IH[OF indk])
  have ins: "indep_vars (\<lambda>_. borel) X (insert (Suc k) {0..<Suc k})"
  proof -
    have "insert (Suc k) {0..<Suc k} = {0..<Suc (Suc k)}" by auto
    thus ?thesis using Suc.prems by simp
  qed
  have ind2: "indep_var borel (X (Suc k)) borel (\<lambda>\<omega>. \<Sum>i\<in>{0..<Suc k}. X i \<omega>)"
    by (rule indep_vars_sum[OF _ _ ins]) simp_all
  have Sm: "(\<lambda>\<omega>. \<Sum>i\<in>{0..<Suc k}. X i \<omega>) \<in> borel_measurable M"
    by (intro borel_measurable_sum Xm)
  have e1: "\<And>x. prob {\<omega> \<in> space M. x < X (Suc k) \<omega>} = prob {\<omega> \<in> space M. x < X 0 \<omega>}"
    by (rule same)
  have rvk: "regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < X (Suc k) \<omega>}) (- \<alpha>)"
    using rv by (simp only: e1)
  have rak: "((\<lambda>x. prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<Suc k}. X i \<omega>)}
      / prob {\<omega> \<in> space M. x < X (Suc k) \<omega>}) \<longlongrightarrow> real (Suc k)) at_top"
    using IH by (simp only: e1)
  have res: "((\<lambda>x. prob {\<omega> \<in> space M. x < X (Suc k) \<omega> + (\<Sum>i\<in>{0..<Suc k}. X i \<omega>)}
      / prob {\<omega> \<in> space M. x < X (Suc k) \<omega>}) \<longlongrightarrow> 1 + real (Suc k)) at_top"
    by (rule tail_sum_indep_gen[OF Xm Sm ind2 rvk rak])
  have se: "\<And>\<omega>. (\<Sum>i\<in>{0..<Suc (Suc k)}. X i \<omega>) = X (Suc k) \<omega> + (\<Sum>i\<in>{0..<Suc k}. X i \<omega>)"
    by (rule sum.atLeast0_lessThan_Suc[THEN trans]) (rule add.commute)
  have "real (Suc (Suc k)) = 1 + real (Suc k)" by simp
  thus ?case using res by (simp only: se e1)
qed

lemma indep_var_Max:
  fixes X :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes I: "finite I" "i \<notin> I" and indep: "indep_vars (\<lambda>_. borel) X (insert i I)"
  shows "indep_var borel (X i) borel (\<lambda>\<omega>. Max ((\<lambda>i. X i \<omega>)`I))"
proof -
  have "indep_var
    borel ((\<lambda>f. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) {i}))
    borel ((\<lambda>f. Max (f`I)) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) I))"
    using I by (intro indep_var_compose[OF indep_var_restrict[OF indep]] borel_measurable_Max) auto
  also have "((\<lambda>f. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) {i})) = X i"
    by auto
  also have "((\<lambda>f. Max (f`I)) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) I)) = (\<lambda>\<omega>. Max ((\<lambda>i. X i \<omega>)`I))"
    by (auto cong: rev_conj_cong)
  finally show ?thesis
    unfolding indep_var_def .
qed

lemma big_jump_max_aux:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real" and \<alpha> :: real
  assumes Xm: "\<And>i. X i \<in> borel_measurable M"
    and same: "\<And>i x. prob {\<omega> \<in> space M. x < X i \<omega>} = prob {\<omega> \<in> space M. x < X 0 \<omega>}"
    and rv: "regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < X 0 \<omega>}) (- \<alpha>)"
  shows "indep_vars (\<lambda>_. borel) X {0..<Suc k} \<Longrightarrow>
    ((\<lambda>x. prob {\<omega> \<in> space M. x < Max ((\<lambda>i. X i \<omega>) ` {0..<Suc k})} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
      \<longlongrightarrow> real (Suc k)) at_top"
proof (induction k)
  case 0
  have pos: "\<forall>\<^sub>F x in at_top. 0 < prob {\<omega> \<in> space M. x < X 0 \<omega>}"
    using eventually_gt_at_top[of "0::real"]
    by (rule eventually_mono) (rule regularly_varying_pos[OF rv])
  have sb: "\<And>x. prob {\<omega> \<in> space M. x < Max ((\<lambda>i. X i \<omega>) ` {0..<Suc 0})} = prob {\<omega> \<in> space M. x < X 0 \<omega>}"
    by simp
  have "((\<lambda>x. 1 :: real) \<longlongrightarrow> 1) at_top" by simp
  moreover have "\<forall>\<^sub>F x in at_top. 1 = prob {\<omega> \<in> space M. x < Max ((\<lambda>i. X i \<omega>) ` {0..<Suc 0})}
      / prob {\<omega> \<in> space M. x < X 0 \<omega>}"
    using pos
  proof eventually_elim
    case (elim x)
    hence ne: "prob {\<omega> \<in> space M. x < X 0 \<omega>} \<noteq> 0" by simp
    show ?case by (simp only: sb) (simp add: ne)
  qed
  ultimately have "((\<lambda>x. prob {\<omega> \<in> space M. x < Max ((\<lambda>i. X i \<omega>) ` {0..<Suc 0})}
      / prob {\<omega> \<in> space M. x < X 0 \<omega>}) \<longlongrightarrow> 1) at_top"
    by (rule Lim_transform_eventually)
  thus ?case by simp
next
  case (Suc k)
  define Mk where "Mk \<omega> = Max ((\<lambda>i. X i \<omega>) ` {0..<Suc k})" for \<omega>
  have indk: "indep_vars (\<lambda>_. borel) X {0..<Suc k}"
    by (rule indep_vars_subset[OF Suc.prems]) auto
  have IH: "((\<lambda>x. prob {\<omega> \<in> space M. x < Mk \<omega>} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
      \<longlongrightarrow> real (Suc k)) at_top"
    unfolding Mk_def by (rule Suc.IH[OF indk])
  have ins: "indep_vars (\<lambda>_. borel) X (insert (Suc k) {0..<Suc k})"
  proof -
    have "insert (Suc k) {0..<Suc k} = {0..<Suc (Suc k)}" by auto
    thus ?thesis using Suc.prems by simp
  qed
  have ind2: "indep_var borel (X (Suc k)) borel Mk"
    unfolding Mk_def by (rule indep_var_Max[OF _ _ ins]) simp_all
  have Mm: "Mk \<in> borel_measurable M"
    unfolding Mk_def by (intro borel_measurable_Max Xm) simp
  have mx: "\<And>\<omega>. Max ((\<lambda>i. X i \<omega>) ` {0..<Suc (Suc k)}) = max (X (Suc k) \<omega>) (Mk \<omega>)"
  proof -
    fix \<omega>
    have "{0..<Suc (Suc k)} = insert (Suc k) {0..<Suc k}" by auto
    hence "Max ((\<lambda>i. X i \<omega>) ` {0..<Suc (Suc k)}) = Max (insert (X (Suc k) \<omega>) ((\<lambda>i. X i \<omega>) ` {0..<Suc k}))"
      by simp
    also have "\<dots> = max (X (Suc k) \<omega>) (Mk \<omega>)"
      unfolding Mk_def by (rule Max_insert) simp_all
    finally show "Max ((\<lambda>i. X i \<omega>) ` {0..<Suc (Suc k)}) = max (X (Suc k) \<omega>) (Mk \<omega>)" .
  qed
  have e1: "\<And>x. prob {\<omega> \<in> space M. x < X (Suc k) \<omega>} = prob {\<omega> \<in> space M. x < X 0 \<omega>}"
    by (rule same)
  have m0: "((\<lambda>x. prob {\<omega> \<in> space M. x < Mk \<omega>}) \<longlongrightarrow> 0) at_top"
    by (rule tail_tendsto_0[OF Mm])
  have pos: "\<forall>\<^sub>F x in at_top. 0 < prob {\<omega> \<in> space M. x < X 0 \<omega>}"
    using eventually_gt_at_top[of "0::real"]
    by (rule eventually_mono) (rule regularly_varying_pos[OF rv])
  have lim: "((\<lambda>x. 1 + prob {\<omega> \<in> space M. x < Mk \<omega>} / prob {\<omega> \<in> space M. x < X 0 \<omega>}
      - prob {\<omega> \<in> space M. x < Mk \<omega>}) \<longlongrightarrow> 1 + real (Suc k) - 0) at_top"
    by (intro tendsto_diff tendsto_add tendsto_const IH m0)
  have "\<forall>\<^sub>F x in at_top. 1 + prob {\<omega> \<in> space M. x < Mk \<omega>} / prob {\<omega> \<in> space M. x < X 0 \<omega>}
      - prob {\<omega> \<in> space M. x < Mk \<omega>}
      = prob {\<omega> \<in> space M. x < Max ((\<lambda>i. X i \<omega>) ` {0..<Suc (Suc k)})} / prob {\<omega> \<in> space M. x < X 0 \<omega>}"
    using pos
  proof eventually_elim
    case (elim x)
    have ne: "prob {\<omega> \<in> space M. x < X 0 \<omega>} \<noteq> 0" using elim by simp
    have "prob {\<omega> \<in> space M. x < Max ((\<lambda>i. X i \<omega>) ` {0..<Suc (Suc k)})}
      = prob {\<omega> \<in> space M. x < X 0 \<omega>} + prob {\<omega> \<in> space M. x < Mk \<omega>}
        - prob {\<omega> \<in> space M. x < X 0 \<omega>} * prob {\<omega> \<in> space M. x < Mk \<omega>}"
      by (simp only: mx prob_max_indep[OF Xm Mm ind2] e1)
    thus ?case using ne by (simp add: field_simps)
  qed
  with lim have "((\<lambda>x. prob {\<omega> \<in> space M. x < Max ((\<lambda>i. X i \<omega>) ` {0..<Suc (Suc k)})}
      / prob {\<omega> \<in> space M. x < X 0 \<omega>}) \<longlongrightarrow> 1 + real (Suc k) - 0) at_top"
    by (rule Lim_transform_eventually)
  thus ?case by simp
qed

text \<open>Theorem E.  For \<open>n \<ge> 1\<close> independent variables with the same regularly varying tail (no sign condition):
  \<open>P(S_n > x) / P(X > x) \<rightarrow> n\<close>, \<open>P(max > x) / P(X > x) \<rightarrow> n\<close>, hence \<open>P(S_n > x) / P(max > x) \<rightarrow> 1\<close>.\<close>

theorem big_jump_principle:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real" and \<alpha> :: real and n :: nat
  assumes Xm: "\<And>i. X i \<in> borel_measurable M" and n: "0 < n"
    and ind: "indep_vars (\<lambda>_. borel) X {0..<n}"
    and same: "\<And>i x. prob {\<omega> \<in> space M. x < X i \<omega>} = prob {\<omega> \<in> space M. x < X 0 \<omega>}"
    and rv: "regularly_varying (\<lambda>x. prob {\<omega> \<in> space M. x < X 0 \<omega>}) (- \<alpha>)"
  shows "((\<lambda>x. prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<n}. X i \<omega>)} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
        \<longlongrightarrow> real n) at_top"
    and "((\<lambda>x. prob {\<omega> \<in> space M. x < Max ((\<lambda>i. X i \<omega>) ` {0..<n})} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
        \<longlongrightarrow> real n) at_top"
    and "((\<lambda>x. prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<n}. X i \<omega>)}
        / prob {\<omega> \<in> space M. x < Max ((\<lambda>i. X i \<omega>) ` {0..<n})}) \<longlongrightarrow> 1) at_top"
proof -
  obtain k where k: "n = Suc k" using n by (cases n) auto
  have s: "((\<lambda>x. prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<n}. X i \<omega>)} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
        \<longlongrightarrow> real n) at_top"
  proof -
    have ind': "indep_vars (\<lambda>_. borel) X {0..<Suc k}" using ind k by simp
    have "((\<lambda>x. prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<Suc k}. X i \<omega>)} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
        \<longlongrightarrow> real (Suc k)) at_top"
      by (rule big_jump_sum_aux[where X=X and \<alpha>=\<alpha> and k=k, OF Xm same rv ind'])
    thus ?thesis using k by simp
  qed
  have m: "((\<lambda>x. prob {\<omega> \<in> space M. x < Max ((\<lambda>i. X i \<omega>) ` {0..<n})} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
        \<longlongrightarrow> real n) at_top"
  proof -
    have ind': "indep_vars (\<lambda>_. borel) X {0..<Suc k}" using ind k by simp
    have "((\<lambda>x. prob {\<omega> \<in> space M. x < Max ((\<lambda>i. X i \<omega>) ` {0..<Suc k})} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
        \<longlongrightarrow> real (Suc k)) at_top"
      by (rule big_jump_max_aux[where X=X and \<alpha>=\<alpha> and k=k, OF Xm same rv ind'])
    thus ?thesis using k by simp
  qed
  show "((\<lambda>x. prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<n}. X i \<omega>)} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
        \<longlongrightarrow> real n) at_top" by (rule s)
  show "((\<lambda>x. prob {\<omega> \<in> space M. x < Max ((\<lambda>i. X i \<omega>) ` {0..<n})} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
        \<longlongrightarrow> real n) at_top" by (rule m)
  have pos: "\<forall>\<^sub>F x in at_top. 0 < prob {\<omega> \<in> space M. x < X 0 \<omega>}"
    using eventually_gt_at_top[of "0::real"]
    by (rule eventually_mono) (rule regularly_varying_pos[OF rv])
  have nn: "real n \<noteq> 0" using n by simp
  have "((\<lambda>x. (prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<n}. X i \<omega>)} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
      / (prob {\<omega> \<in> space M. x < Max ((\<lambda>i. X i \<omega>) ` {0..<n})} / prob {\<omega> \<in> space M. x < X 0 \<omega>}))
      \<longlongrightarrow> real n / real n) at_top"
    by (rule tendsto_divide[OF s m nn])
  moreover have "\<forall>\<^sub>F x in at_top. (prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<n}. X i \<omega>)} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
      / (prob {\<omega> \<in> space M. x < Max ((\<lambda>i. X i \<omega>) ` {0..<n})} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
      = prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<n}. X i \<omega>)} / prob {\<omega> \<in> space M. x < Max ((\<lambda>i. X i \<omega>) ` {0..<n})}"
    using pos
  proof eventually_elim
    case (elim x)
    have ne: "prob {\<omega> \<in> space M. x < X 0 \<omega>} \<noteq> 0" using elim by simp
    show ?case by (cases "prob {\<omega> \<in> space M. x < Max ((\<lambda>i. X i \<omega>) ` {0..<n})} = 0") (simp_all add: field_simps ne)
  qed
  ultimately have "((\<lambda>x. prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<n}. X i \<omega>)}
        / prob {\<omega> \<in> space M. x < Max ((\<lambda>i. X i \<omega>) ` {0..<n})}) \<longlongrightarrow> real n / real n) at_top"
    by (rule Lim_transform_eventually)
  thus "((\<lambda>x. prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<n}. X i \<omega>)}
        / prob {\<omega> \<in> space M. x < Max ((\<lambda>i. X i \<omega>) ` {0..<n})}) \<longlongrightarrow> 1) at_top"
    using nn by simp
qed

end

end
