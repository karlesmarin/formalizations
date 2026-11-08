(*  Title:      Random_Sums.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

theory Random_Sums
  imports Heavy_Tail_Relations
begin

section \<open>Random sums with a regularly varying summand\<close>

text \<open>If the summands \<open>X_i\<close> are i.i.d. with a regularly varying right tail of index \<open>-\<alpha>\<close>, \<open>\<alpha> > 0\<close>, and \<open>N\<close> is a
  natural-number random variable independent of the sequence with \<open>E N^(1+\<alpha>+\<delta>) < \<infinity>\<close> for some \<open>\<delta> > 0\<close>,
  then \<open>P(S_N > x) / P(X_0 > x) \<rightarrow> E N\<close>, where \<open>S_n = X_0 + \<dots> + X_(n-1)\<close> and \<open>S_0 = 0\<close>.  The proof
  conditions on \<open>N\<close>; for each fixed \<open>n\<close> the principle of the single big jump (\<open>big_jump_principle\<close>) gives
  the limit \<open>n\<close>; for the domination, \<open>P(S_n > x) \<le> n P(X_0 > x/n)\<close> (some summand exceeds \<open>x/n\<close>, no sign
  condition needed) and a Potter bound for \<open>P(X_0 > x/n) / P(X_0 > x)\<close> give \<open>K n^(1+\<alpha>+\<delta>)\<close>.\<close>

subsection \<open>A Potter bound for the ratio of the tail at \<open>x/z\<close> and at \<open>x\<close>, \<open>z \<ge> 1\<close>\<close>

lemma tail_ratio_dom:
  fixes U :: "real \<Rightarrow> real" and \<alpha> \<delta> :: real
  assumes rv: "regularly_varying U (- \<alpha>)" and \<alpha>: "0 < \<alpha>" and \<delta>: "0 < \<delta>"
    and U1: "\<And>x. U x \<le> 1"
  shows "\<exists>x0>0. \<exists>K>0. \<forall>x\<ge>x0. \<forall>z\<ge>1. U (x / z) / U x \<le> K * z powr (\<alpha> + \<delta>)"
proof -
  have A2: "(1::real) < 2" by simp
  obtain T where T: "0 < T"
    and P: "\<And>y x. T \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> U y / U x \<le> 2 * (y / x) powr (- \<alpha> - \<delta>)"
    using Potter_bounds2[OF rv A2 \<delta>] by auto
  have UT: "0 < U T" by (rule regularly_varying_pos[OF rv T])
  define K where "K = 2 + 2 / U T"
  have K2: "0 \<le> 2 / U T" using UT by simp
  have K: "0 < K" unfolding K_def using K2 by linarith
  have main: "U (x / z) / U x \<le> K * z powr (\<alpha> + \<delta>)" if x: "T \<le> x" and z: "1 \<le> z" for x z
  proof -
    have xp: "0 < x" using x T by simp
    have zp: "0 < z" using z by simp
    have Ux: "0 < U x" by (rule regularly_varying_pos[OF rv xp])
    have zz: "0 \<le> z powr (\<alpha> + \<delta>)" by simp
    show ?thesis
    proof (cases "T \<le> x / z")
      case True
      have xz: "x \<le> x * z"
      proof -
        have "x * 1 \<le> x * z" by (rule mult_left_mono) (use xp z in simp_all)
        thus ?thesis by simp
      qed
      have le: "x / z \<le> x" using xz by (simp add: pos_divide_le_eq[OF zp] mult.commute)
      have b: "U (x / z) / U x \<le> 2 * ((x / z) / x) powr (- \<alpha> - \<delta>)" by (rule P[OF True le])
      have e: "(x / z) / x = 1 / z" using xp by (simp add: field_simps)
      have e2: "(1 / z) powr (- \<alpha> - \<delta>) = z powr (\<alpha> + \<delta>)"
        using powr_inv_helper[OF zp, of "- \<alpha> - \<delta>"] by (simp add: add.commute)
      have "U (x / z) / U x \<le> 2 * z powr (\<alpha> + \<delta>)" using b e e2 by simp
      also have "\<dots> \<le> K * z powr (\<alpha> + \<delta>)"
        by (rule mult_right_mono) (use zz K2 in \<open>simp_all add: K_def\<close>)
      finally show ?thesis .
    next
      case False
      have U1': "U (x / z) / U x \<le> 1 / U x"
        by (rule divide_right_mono) (use U1[of "x / z"] Ux in simp_all)
      have pt: "U T / U x \<le> 2 * (T / x) powr (- \<alpha> - \<delta>)" by (rule P[OF order_refl x])
      have xT: "0 < x / T" using xp T by simp
      have e: "T / x = 1 / (x / T)" using xp T by (simp add: field_simps)
      have e2: "(1 / (x / T)) powr (- \<alpha> - \<delta>) = (x / T) powr (\<alpha> + \<delta>)"
        using powr_inv_helper[OF xT, of "- \<alpha> - \<delta>"] by (simp add: add.commute)
      have lt0: "x / z < T" using False by (simp add: not_le)
      have lt: "x < T * z" using iffD1[OF pos_divide_less_eq[OF zp] lt0] .
      have xTz: "x / T \<le> z" using lt T by (simp add: pos_divide_le_eq[OF T] mult.commute)
      have pw: "(x / T) powr (\<alpha> + \<delta>) \<le> z powr (\<alpha> + \<delta>)"
        by (rule powr_mono2) (use \<alpha> \<delta> xT xTz in simp_all)
      have "1 / U x = (1 / U T) * (U T / U x)" using UT Ux by (simp add: field_simps)
      also have "\<dots> \<le> (1 / U T) * (2 * (x / T) powr (\<alpha> + \<delta>))"
      proof -
        have pt2: "U T / U x \<le> 2 * (x / T) powr (\<alpha> + \<delta>)" using pt by (simp only: e e2)
        show ?thesis by (rule mult_left_mono[OF pt2]) (use UT in simp)
      qed
      also have "\<dots> \<le> (1 / U T) * (2 * z powr (\<alpha> + \<delta>))"
        by (rule mult_left_mono) (use pw UT in simp_all)
      also have "\<dots> = (2 / U T) * z powr (\<alpha> + \<delta>)" by simp
      also have "\<dots> \<le> K * z powr (\<alpha> + \<delta>)"
        by (rule mult_right_mono) (use zz in \<open>simp_all add: K_def\<close>)
      finally show ?thesis using U1' by linarith
    qed
  qed
  have fin: "\<forall>x\<ge>T. \<forall>z\<ge>1. U (x / z) / U x \<le> K * z powr (\<alpha> + \<delta>)" using main by blast
  show ?thesis using T K fin by blast
qed

subsection \<open>Sums with a random number of terms\<close>

context prob_space
begin

lemma prob_sum_gt_le:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real" and x :: real and n :: nat
  assumes Xm: "\<And>i. X i \<in> borel_measurable M"
    and same: "\<And>i y. prob {\<omega> \<in> space M. y < X i \<omega>} = prob {\<omega> \<in> space M. y < X 0 \<omega>}"
    and n: "0 < n"
  shows "prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<n}. X i \<omega>)} \<le> real n * prob {\<omega> \<in> space M. x / real n < X 0 \<omega>}"
proof -
  define A where "A i = {\<omega> \<in> space M. x / real n < X i \<omega>}" for i
  have Am: "A i \<in> sets M" for i
  proof -
    have [measurable]: "X i \<in> borel_measurable M" by (rule Xm)
    show ?thesis unfolding A_def by measurable
  qed
  have Sm[measurable]: "(\<lambda>\<omega>. \<Sum>i\<in>{0..<n}. X i \<omega>) \<in> borel_measurable M"
    by (intro borel_measurable_sum Xm)
  have nne: "real n \<noteq> 0" using n by simp
  have sub: "{\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<n}. X i \<omega>)} \<subseteq> (\<Union>i\<in>{0..<n}. A i)"
  proof
    fix \<omega> assume \<omega>: "\<omega> \<in> {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<n}. X i \<omega>)}"
    hence om: "\<omega> \<in> space M" and lt: "x < (\<Sum>i\<in>{0..<n}. X i \<omega>)" by auto
    show "\<omega> \<in> (\<Union>i\<in>{0..<n}. A i)"
    proof (rule ccontr)
      assume "\<omega> \<notin> (\<Union>i\<in>{0..<n}. A i)"
      hence all: "\<forall>i\<in>{0..<n}. X i \<omega> \<le> x / real n" using om unfolding A_def by auto
      have "(\<Sum>i\<in>{0..<n}. X i \<omega>) \<le> real (card {0..<n}) * (x / real n)"
        by (rule sum_bounded_above) (use all in simp)
      hence "(\<Sum>i\<in>{0..<n}. X i \<omega>) \<le> x" using nne by simp
      thus False using lt by simp
    qed
  qed
  have U: "(\<Union>i\<in>{0..<n}. A i) \<in> sets M" using Am by (intro sets.finite_UN) auto
  have "prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<n}. X i \<omega>)} \<le> prob (\<Union>i\<in>{0..<n}. A i)"
    by (rule finite_measure_mono[OF sub U])
  also have "\<dots> \<le> (\<Sum>i\<in>{0..<n}. prob (A i))"
    by (rule measure_subadditive_finite) (use Am in auto)
  also have "\<dots> = (\<Sum>i\<in>{0..<n}. prob {\<omega> \<in> space M. x / real n < X 0 \<omega>})"
    unfolding A_def by (rule sum.cong[OF refl]) (rule same)
  also have "\<dots> = real n * prob {\<omega> \<in> space M. x / real n < X 0 \<omega>}" by simp
  finally show ?thesis .
qed

lemma random_sum_prob_eq:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real" and N :: "'a \<Rightarrow> nat" and x :: real
  assumes Nm[measurable]: "N \<in> measurable M (count_space UNIV)"
    and Xm[measurable]: "\<And>i. X i \<in> borel_measurable M"
    and ind: "\<And>n A. A \<in> sets (Pi\<^sub>M UNIV (\<lambda>_. borel)) \<Longrightarrow>
        prob ({\<omega> \<in> space M. N \<omega> = n} \<inter> {\<omega> \<in> space M. (\<lambda>i. X i \<omega>) \<in> A})
        = prob {\<omega> \<in> space M. N \<omega> = n} * prob {\<omega> \<in> space M. (\<lambda>i. X i \<omega>) \<in> A}"
  shows "prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<N \<omega>}. X i \<omega>)}
    = (\<integral>\<omega>. prob {\<omega>' \<in> space M. x < (\<Sum>i\<in>{0..<N \<omega>}. X i \<omega>')} \<partial>M)"
proof -
  define E where "E n = {\<omega> \<in> space M. N \<omega> = n}" for n
  define B where "B n = {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<n}. X i \<omega>)}" for n
  define h where "h n = prob (B n)" for n
  have Em: "E n \<in> sets M" for n unfolding E_def by measurable
  have Bm: "B n \<in> sets M" for n unfolding B_def by measurable
  have h01: "0 \<le> h n" "h n \<le> 1" for n unfolding h_def by (auto simp: measure_nonneg prob_le_1)
  have sn: "(\<lambda>y::nat \<Rightarrow> real. \<Sum>i\<in>{0..<n}. y i) \<in> borel_measurable (Pi\<^sub>M UNIV (\<lambda>_. borel))" for n
    by measurable
  have Aset: "{y \<in> space (Pi\<^sub>M (UNIV::nat set) (\<lambda>_. borel)). x < (\<Sum>i\<in>{0..<n}. y i)} \<in> sets (Pi\<^sub>M (UNIV::nat set) (\<lambda>_. borel))" for n
    using sn[of n] by measurable
  have Beq: "B n = {\<omega> \<in> space M. (\<lambda>i. X i \<omega>) \<in> {y \<in> space (Pi\<^sub>M (UNIV::nat set) (\<lambda>_. borel)). x < (\<Sum>i\<in>{0..<n}. y i)}}" for n
    unfolding B_def by (auto simp: space_PiM)
  have key: "prob (E n \<inter> B n) = prob (E n) * h n" for n
    using ind[OF Aset[of n], of n] unfolding E_def h_def Beq[of n] by simp
  have disj: "disjoint_family (\<lambda>n. E n \<inter> B n)" unfolding disjoint_family_on_def E_def by auto
  have Cm: "range (\<lambda>n. E n \<inter> B n) \<subseteq> sets M" using Em Bm by auto
  have U: "{\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<N \<omega>}. X i \<omega>)} = (\<Union>n. E n \<inter> B n)" unfolding E_def B_def by auto
  have L: "ennreal (prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<N \<omega>}. X i \<omega>)}) = (\<Sum>n. ennreal (prob (E n) * h n))"
  proof -
    have "ennreal (prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<N \<omega>}. X i \<omega>)})
        = emeasure M {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<N \<omega>}. X i \<omega>)}"
      by (rule emeasure_eq_ennreal_measure[symmetric]) simp
    also have "\<dots> = emeasure M (\<Union>n. E n \<inter> B n)" unfolding U ..
    also have "\<dots> = (\<Sum>n. emeasure M (E n \<inter> B n))" by (rule suminf_emeasure[symmetric, OF Cm disj])
    also have "\<dots> = (\<Sum>n. ennreal (prob (E n) * h n))"
    proof (rule suminf_cong)
      fix n
      have "emeasure M (E n \<inter> B n) = ennreal (prob (E n \<inter> B n))"
        by (rule emeasure_eq_ennreal_measure) simp
      thus "emeasure M (E n \<inter> B n) = ennreal (prob (E n) * h n)" using key[of n] by simp
    qed
    finally show ?thesis .
  qed
  have hNm: "(\<lambda>\<omega>. h (N \<omega>)) \<in> borel_measurable M" by measurable
  have hint: "integrable M (\<lambda>\<omega>. h (N \<omega>))"
    by (rule integrable_const_bound[where B=1]) (use h01 hNm in \<open>auto simp: abs_of_nonneg\<close>)
  have R: "ennreal (\<integral>\<omega>. h (N \<omega>) \<partial>M) = (\<Sum>n. ennreal (prob (E n) * h n))"
  proof -
    have "ennreal (\<integral>\<omega>. h (N \<omega>) \<partial>M) = (\<integral>\<^sup>+\<omega>. ennreal (h (N \<omega>)) \<partial>M)"
      by (rule nn_integral_eq_integral[symmetric, OF hint]) (use h01 in auto)
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<Sum>n. ennreal (h n) * indicator (E n) \<omega>) \<partial>M)"
    proof (rule nn_integral_cong)
      fix \<omega> assume \<omega>: "\<omega> \<in> space M"
      have t: "\<And>n. ennreal (h n) * indicator (E n) \<omega> = (if n = N \<omega> then ennreal (h n) else 0)"
        using \<omega> by (simp add: indicator_def E_def)
      have "(\<Sum>n. if n = N \<omega> then ennreal (h n) else 0) = (\<Sum>n\<in>{N \<omega>}. if n = N \<omega> then ennreal (h n) else 0)"
        by (rule suminf_finite) auto
      thus "ennreal (h (N \<omega>)) = (\<Sum>n. ennreal (h n) * indicator (E n) \<omega>)" unfolding t by simp
    qed
    also have "\<dots> = (\<Sum>n. \<integral>\<^sup>+\<omega>. ennreal (h n) * indicator (E n) \<omega> \<partial>M)"
      by (rule nn_integral_suminf) (use Em in measurable)
    also have "\<dots> = (\<Sum>n. ennreal (prob (E n) * h n))"
    proof (rule suminf_cong)
      fix n
      have "(\<integral>\<^sup>+\<omega>. ennreal (h n) * indicator (E n) \<omega> \<partial>M) = ennreal (h n) * emeasure M (E n)"
        by (rule nn_integral_cmult_indicator[OF Em])
      also have "\<dots> = ennreal (prob (E n) * h n)"
      proof -
        have e: "emeasure M (E n) = ennreal (prob (E n))" by (rule emeasure_eq_ennreal_measure) simp
        show ?thesis unfolding e using h01[of n] by (simp add: ennreal_mult[symmetric] mult.commute)
      qed
      finally show "(\<integral>\<^sup>+\<omega>. ennreal (h n) * indicator (E n) \<omega> \<partial>M) = ennreal (prob (E n) * h n)" .
    qed
    finally show ?thesis .
  qed
  have "ennreal (prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<N \<omega>}. X i \<omega>)}) = ennreal (\<integral>\<omega>. h (N \<omega>) \<partial>M)"
    using L R by simp
  moreover have "0 \<le> (\<integral>\<omega>. h (N \<omega>) \<partial>M)" using h01 by (intro integral_nonneg_AE) auto
  ultimately have "prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<N \<omega>}. X i \<omega>)} = (\<integral>\<omega>. h (N \<omega>) \<partial>M)"
    by (simp add: measure_nonneg)
  thus ?thesis unfolding h_def B_def .
qed

subsection \<open>The random-sum theorem\<close>

text \<open>The independence of \<open>N\<close> and the sequence \<open>(X_i)\<close> is stated on the events \<open>{N = n}\<close> against every measurable
  set of the product space \<open>\<real>^\<nat>\<close> of the sequence; since \<open>N\<close> is discrete this is the independence of \<open>N\<close> from the
  sequence.\<close>

theorem random_sum_tail:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real" and N :: "'a \<Rightarrow> nat" and \<alpha> \<delta> :: real
  assumes Xm: "\<And>i. X i \<in> borel_measurable M"
    and indX: "indep_vars (\<lambda>_. borel) X UNIV"
    and same: "\<And>i y. prob {\<omega> \<in> space M. y < X i \<omega>} = prob {\<omega> \<in> space M. y < X 0 \<omega>}"
    and rv: "regularly_varying (\<lambda>y. prob {\<omega> \<in> space M. y < X 0 \<omega>}) (- \<alpha>)" and \<alpha>: "0 < \<alpha>"
    and Nm[measurable]: "N \<in> measurable M (count_space UNIV)"
    and indN: "\<And>n A. A \<in> sets (Pi\<^sub>M UNIV (\<lambda>_. borel)) \<Longrightarrow>
        prob ({\<omega> \<in> space M. N \<omega> = n} \<inter> {\<omega> \<in> space M. (\<lambda>i. X i \<omega>) \<in> A})
        = prob {\<omega> \<in> space M. N \<omega> = n} * prob {\<omega> \<in> space M. (\<lambda>i. X i \<omega>) \<in> A}"
    and \<delta>: "0 < \<delta>"
    and mom: "integrable M (\<lambda>\<omega>. real (N \<omega>) powr (1 + \<alpha> + \<delta>))"
  shows "integrable M (\<lambda>\<omega>. real (N \<omega>))"
    and "((\<lambda>x. prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<N \<omega>}. X i \<omega>)} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
      \<longlongrightarrow> expectation (\<lambda>\<omega>. real (N \<omega>))) at_top"
proof -
  have Xm'[measurable]: "\<And>i. X i \<in> borel_measurable M" by (rule Xm)
  define T where "T y = prob {\<omega> \<in> space M. y < X 0 \<omega>}" for y
  have rvT: "regularly_varying T (- \<alpha>)" using rv unfolding T_def .
  have Tpos: "0 < T y" if "0 < y" for y using regularly_varying_pos[OF rvT that] .
  have T1: "T y \<le> 1" for y unfolding T_def by (rule prob_le_1)
  obtain x0 K where x0: "0 < x0" and K: "0 < K"
    and dom: "\<And>x z. x0 \<le> x \<Longrightarrow> 1 \<le> z \<Longrightarrow> T (x / z) / T x \<le> K * z powr (\<alpha> + \<delta>)"
    using tail_ratio_dom[OF rvT \<alpha> \<delta> T1] by blast
  have Nint: "integrable M (\<lambda>\<omega>. real (N \<omega>))"
  proof (rule Bochner_Integration.integrable_bound[where f="\<lambda>\<omega>. real (N \<omega>) powr (1 + \<alpha> + \<delta>)"])
    show "integrable M (\<lambda>\<omega>. real (N \<omega>) powr (1 + \<alpha> + \<delta>))" by (rule mom)
    show "(\<lambda>\<omega>. real (N \<omega>)) \<in> borel_measurable M" by measurable
    show "AE \<omega> in M. norm (real (N \<omega>)) \<le> norm (real (N \<omega>) powr (1 + \<alpha> + \<delta>))"
    proof (rule AE_I2)
      fix \<omega> assume "\<omega> \<in> space M"
      define n where "n = N \<omega>"
      have "real n \<le> real n powr (1 + \<alpha> + \<delta>)"
      proof (cases "n = 0")
        case True
        thus ?thesis by simp
      next
        case False
        hence n1: "1 \<le> real n" by simp
        have "real n powr 1 \<le> real n powr (1 + \<alpha> + \<delta>)"
          by (rule powr_mono) (use \<alpha> \<delta> n1 in simp_all)
        thus ?thesis by simp
      qed
      thus "norm (real (N \<omega>)) \<le> norm (real (N \<omega>) powr (1 + \<alpha> + \<delta>))" unfolding n_def by simp
    qed
  qed
  show "integrable M (\<lambda>\<omega>. real (N \<omega>))" by (rule Nint)
  define g where "g x n = prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<n}. X i \<omega>)} / T x" for x n
  have g0: "0 \<le> g x n" if "0 < x" for x n
    unfolding g_def using Tpos[OF that] by (auto intro!: divide_nonneg_pos measure_nonneg)
  have gz: "g x 0 = 0" if xp: "0 < x" for x
  proof -
    have e0: "{\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<0}. X i \<omega>)} = {}"
    proof (rule equals0I)
      fix \<omega> assume "\<omega> \<in> {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<0}. X i \<omega>)}"
      hence "x < 0" by simp
      thus False using xp by linarith
    qed
    show ?thesis unfolding g_def e0 by simp
  qed
  have g_bound: "g x n \<le> K * real n powr (1 + \<alpha> + \<delta>)" if x: "x0 \<le> x" for x n
  proof (cases "n = 0")
    case True
    have xp: "0 < x" using x x0 by simp
    show ?thesis using gz[OF xp] True by simp
  next
    case False
    have np: "0 < n" using False by simp
    have n1: "1 \<le> real n" using np by simp
    have Tx: "0 < T x" using Tpos x x0 by simp
    have b1: "prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<n}. X i \<omega>)} \<le> real n * T (x / real n)"
      using prob_sum_gt_le[of X n x, OF Xm same np] unfolding T_def .
    have b2: "T (x / real n) / T x \<le> K * real n powr (\<alpha> + \<delta>)" by (rule dom[OF x n1])
    have pw: "real n powr (1 + \<alpha> + \<delta>) = real n * real n powr (\<alpha> + \<delta>)"
      using powr_add[of "real n" 1 "\<alpha> + \<delta>"] by (simp add: add.assoc)
    have "g x n \<le> (real n * T (x / real n)) / T x"
      unfolding g_def by (rule divide_right_mono) (use b1 Tx in simp_all)
    also have "\<dots> = real n * (T (x / real n) / T x)" by simp
    also have "\<dots> \<le> real n * (K * real n powr (\<alpha> + \<delta>))" by (rule mult_left_mono) (use b2 in simp_all)
    also have "\<dots> = K * real n powr (1 + \<alpha> + \<delta>)" by (simp add: pw mult_ac)
    finally show ?thesis .
  qed
  have lim_g: "((\<lambda>x. g x n) \<longlongrightarrow> real n) at_top" for n
  proof (cases "n = 0")
    case True
    have ev: "\<forall>\<^sub>F x in at_top. (0::real) = g x n"
      using eventually_gt_at_top[of 0] by eventually_elim (simp add: gz True)
    have "((\<lambda>x. g x n) \<longlongrightarrow> 0) at_top" by (rule Lim_transform_eventually[OF tendsto_const ev])
    thus ?thesis using True by simp
  next
    case False
    have np: "0 < n" using False by simp
    have ind': "indep_vars (\<lambda>_. borel) X {0..<n}" by (rule indep_vars_subset[OF indX]) simp
    have "((\<lambda>x. prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<n}. X i \<omega>)} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
        \<longlongrightarrow> real n) at_top"
      by (rule big_jump_principle(1)[OF Xm np ind' same rv])
    thus ?thesis unfolding g_def T_def .
  qed
  define x1 where "x1 = max x0 1"
  have x1: "x0 \<le> x1" "0 < x1" unfolding x1_def using x0 by simp_all
  define w where "w \<omega> = K * real (N \<omega>) powr (1 + \<alpha> + \<delta>)" for \<omega>
  have imr: "integrable M f \<Longrightarrow> integrable M (\<lambda>x. c * f x)" for c and f :: "'a \<Rightarrow> real"
    by (cases "c = 0") (auto intro: integrable_mult_right)
  have wint: "integrable M w" unfolding w_def by (rule imr[OF mom])
  have lim1': "((\<lambda>t. \<integral>\<omega>. g (max t x1) (N \<omega>) \<partial>M) \<longlongrightarrow> \<integral>\<omega>. real (N \<omega>) \<partial>M) at_top"
  proof (rule integral_dominated_convergence_at_top[where w=w])
    show "(\<lambda>\<omega>. real (N \<omega>)) \<in> borel_measurable M" by measurable
    show "\<And>t. (\<lambda>\<omega>. g (max t x1) (N \<omega>)) \<in> borel_measurable M" by measurable
    show "integrable M w" by (rule wint)
    show "AE \<omega> in M. ((\<lambda>t. g (max t x1) (N \<omega>)) \<longlongrightarrow> real (N \<omega>)) at_top"
    proof (rule AE_I2)
      fix \<omega> assume "\<omega> \<in> space M"
      have ev: "\<forall>\<^sub>F t in at_top. g t (N \<omega>) = g (max t x1) (N \<omega>)"
        using eventually_ge_at_top[of x1] by eventually_elim simp
      show "((\<lambda>t. g (max t x1) (N \<omega>)) \<longlongrightarrow> real (N \<omega>)) at_top"
        by (rule Lim_transform_eventually[OF lim_g ev])
    qed
    show "\<forall>\<^sub>F t in at_top. AE \<omega> in M. norm (g (max t x1) (N \<omega>)) \<le> w \<omega>"
    proof (rule always_eventually, rule allI)
      fix t
      have xp: "0 < max t x1" using x1 by simp
      have xx: "x0 \<le> max t x1" using x1 by simp
      show "AE \<omega> in M. norm (g (max t x1) (N \<omega>)) \<le> w \<omega>"
      proof (rule AE_I2)
        fix \<omega> assume "\<omega> \<in> space M"
        show "norm (g (max t x1) (N \<omega>)) \<le> w \<omega>"
          using g0[OF xp, of "N \<omega>"] g_bound[OF xx, of "N \<omega>"] unfolding w_def by simp
      qed
    qed
  qed
  have lim1: "((\<lambda>x. \<integral>\<omega>. g x (N \<omega>) \<partial>M) \<longlongrightarrow> \<integral>\<omega>. real (N \<omega>) \<partial>M) at_top"
  proof (rule Lim_transform_eventually[OF lim1'])
    show "\<forall>\<^sub>F x in at_top. (\<integral>\<omega>. g (max x x1) (N \<omega>) \<partial>M) = (\<integral>\<omega>. g x (N \<omega>) \<partial>M)"
      using eventually_ge_at_top[of x1] by eventually_elim simp
  qed
  have eq: "\<forall>\<^sub>F x in at_top. (\<integral>\<omega>. g x (N \<omega>) \<partial>M)
      = prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<N \<omega>}. X i \<omega>)} / prob {\<omega> \<in> space M. x < X 0 \<omega>}"
    using eventually_ge_at_top[of x1]
  proof eventually_elim
    case (elim x)
    have "(\<integral>\<omega>. g x (N \<omega>) \<partial>M)
        = (\<integral>\<omega>. prob {\<omega>' \<in> space M. x < (\<Sum>i\<in>{0..<N \<omega>}. X i \<omega>')} \<partial>M) / T x"
      unfolding g_def by simp
    also have "(\<integral>\<omega>. prob {\<omega>' \<in> space M. x < (\<Sum>i\<in>{0..<N \<omega>}. X i \<omega>')} \<partial>M)
        = prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<N \<omega>}. X i \<omega>)}"
      by (rule random_sum_prob_eq[symmetric, OF Nm Xm indN])
    finally show ?case unfolding T_def .
  qed
  have "((\<lambda>x. prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<N \<omega>}. X i \<omega>)} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
      \<longlongrightarrow> \<integral>\<omega>. real (N \<omega>) \<partial>M) at_top"
    by (rule Lim_transform_eventually[OF lim1 eq])
  thus "((\<lambda>x. prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<N \<omega>}. X i \<omega>)} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
      \<longlongrightarrow> expectation (\<lambda>\<omega>. real (N \<omega>))) at_top" by simp
qed

end

subsection \<open>A geometric number of terms\<close>

lemma geom_powr_summable:
  fixes r q :: real
  assumes r0: "0 \<le> r" and r1: "r < 1"
  shows "summable (\<lambda>n. r ^ n * real n powr q)"
proof (cases "r = 0")
  case True
  have "(\<lambda>n. r ^ n * real n powr q) = (\<lambda>_. 0)"
  proof (rule ext)
    fix n show "r ^ n * real n powr q = 0" using True by (cases n) simp_all
  qed
  thus ?thesis by simp
next
  case False
  hence rp: "0 < r" using r0 by simp
  define c where "c = (1 + r) / 2"
  have c1: "c < 1" and cr: "r < c" unfolding c_def using r1 rp by simp_all
  define f where "f n = r ^ n * real n powr q" for n
  have lim: "((\<lambda>n. (real (Suc n) / real n) powr q) \<longlongrightarrow> 1) sequentially"
  proof -
    have a: "((\<lambda>n. 1 + inverse (real n)) \<longlongrightarrow> 1 + 0) sequentially"
      by (rule tendsto_add[OF tendsto_const tendsto_inverse_0_at_top[OF filterlim_real_sequentially]])
    have b: "((\<lambda>n. (1 + inverse (real n)) powr q) \<longlongrightarrow> (1 + 0) powr q) sequentially"
      by (rule tendsto_powr[OF a tendsto_const]) simp
    have ev: "\<forall>\<^sub>F n in sequentially. (1 + inverse (real n)) powr q = (real (Suc n) / real n) powr q"
      using eventually_gt_at_top[of 0]
    proof eventually_elim
      case (elim n)
      have "real (Suc n) / real n = 1 + inverse (real n)" using elim by (simp add: field_simps)
      thus ?case by simp
    qed
    have "((\<lambda>n. (real (Suc n) / real n) powr q) \<longlongrightarrow> (1 + 0) powr q) sequentially"
      by (rule Lim_transform_eventually[OF b ev])
    thus ?thesis by simp
  qed
  have cr1: "1 < c / r" using cr rp by (simp add: less_divide_eq_1_pos)
  have ev: "\<forall>\<^sub>F n in sequentially. (real (Suc n) / real n) powr q < c / r"
    using order_tendstoD(2)[OF lim cr1] .
  obtain N where N: "\<And>n. N \<le> n \<Longrightarrow> (real (Suc n) / real n) powr q < c / r"
    using ev unfolding eventually_sequentially by blast
  have fe: "f = (\<lambda>n. r ^ n * real n powr q)" by (rule ext) (simp add: f_def)
  have sf: "summable f"
  proof (rule summable_ratio_test[of c "max N 1" f])
    show "c < 1" by (rule c1)
    fix n assume n: "max N 1 \<le> n"
    have n1: "1 \<le> n" and nN: "N \<le> n" using n by simp_all
    have np: "0 < real n" using n1 by simp
    define \<rho> where "\<rho> = (real (Suc n) / real n) powr q"
    have hr: "\<rho> < c / r" unfolding \<rho>_def by (rule N[OF nN])
    have e: "real (Suc n) powr q = \<rho> * real n powr q"
      unfolding \<rho>_def using np by (simp add: powr_divide)
    have rr: "r * \<rho> \<le> c" using hr rp by (simp add: less_divide_eq mult.commute)
    have fe: "f (Suc n) = (r * \<rho>) * f n" unfolding f_def using e by (simp add: algebra_simps)
    have fn0: "0 \<le> f n" unfolding f_def using rp by simp
    have f0: "0 \<le> f (Suc n)" unfolding f_def using rp by simp
    have "norm (f (Suc n)) = (r * \<rho>) * f n" using fe f0 by simp
    also have "\<dots> \<le> c * f n" by (rule mult_right_mono) (use rr fn0 in simp_all)
    finally show "norm (f (Suc n)) \<le> c * norm (f n)" using fn0 by simp
  qed
  thus ?thesis unfolding fe .
qed

lemma geometric_powr_integrable:
  fixes p q :: real
  assumes p0: "0 < p" and p1: "p < 1"
  shows "integrable (measure_pmf (geometric_pmf p)) (\<lambda>n. real n powr q)"
proof -
  have s0: "summable (\<lambda>n. (1 - p) ^ n * real n powr q)" by (rule geom_powr_summable) (use p0 p1 in simp_all)
  have s1: "summable (\<lambda>n. (1 - p) ^ n * p * real n powr q)"
    using summable_mult[OF s0, of p] by (simp add: mult_ac)
  have nn: "0 \<le> (1 - p) ^ n * p * real n powr q" for n using p0 p1 by simp
  have "integrable (count_space UNIV) (\<lambda>n. pmf (geometric_pmf p) n * real n powr q)"
  proof (subst integrable_count_space_nat_iff)
    show "summable (\<lambda>n. norm (pmf (geometric_pmf p) n * real n powr q))"
      using s1 nn p0 p1 by (simp add: abs_of_nonneg)
  qed
  thus ?thesis
    unfolding measure_pmf_eq_density by (subst integrable_density) simp_all
qed

lemma integral_Ioi_pos:
  fixes U :: "real \<Rightarrow> real"
  assumes pos: "\<And>t. t \<in> {0<..} \<Longrightarrow> 0 < U t" and intU: "set_integrable lborel {0<..} U"
  shows "0 < (\<integral>t\<in>{0<..}. U t \<partial>lborel)"
proof -
  have e1: "0 < emeasure lborel {0<..0+1::real}" by simp
  have e2: "emeasure lborel {0<..0+1::real} \<le> emeasure lborel {0::real<..}" by (rule emeasure_mono) auto
  show ?thesis
    by (intro set_integral_zero_less intU order.strict_trans2[OF e1 e2]) (auto intro!: pos)
qed

context prob_space
begin

theorem random_sum_geometric:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real" and N :: "'a \<Rightarrow> nat" and \<alpha> p :: real
  assumes Xm: "\<And>i. X i \<in> borel_measurable M"
    and indX: "indep_vars (\<lambda>_. borel) X UNIV"
    and same: "\<And>i y. prob {\<omega> \<in> space M. y < X i \<omega>} = prob {\<omega> \<in> space M. y < X 0 \<omega>}"
    and rv: "regularly_varying (\<lambda>y. prob {\<omega> \<in> space M. y < X 0 \<omega>}) (- \<alpha>)" and \<alpha>: "0 < \<alpha>"
    and Nm[measurable]: "N \<in> measurable M (count_space UNIV)"
    and indN: "\<And>n A. A \<in> sets (Pi\<^sub>M UNIV (\<lambda>_. borel)) \<Longrightarrow>
        prob ({\<omega> \<in> space M. N \<omega> = n} \<inter> {\<omega> \<in> space M. (\<lambda>i. X i \<omega>) \<in> A})
        = prob {\<omega> \<in> space M. N \<omega> = n} * prob {\<omega> \<in> space M. (\<lambda>i. X i \<omega>) \<in> A}"
    and p0: "0 < p" and p1: "p < 1"
    and law: "distr M (count_space UNIV) N = measure_pmf (geometric_pmf p)"
  shows "((\<lambda>x. prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<N \<omega>}. X i \<omega>)} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
      \<longlongrightarrow> (1 - p) / p) at_top"
proof -
  have m1: "(\<lambda>n::nat. real n powr (1 + \<alpha> + 1)) \<in> borel_measurable (count_space UNIV)" by simp
  have mom: "integrable M (\<lambda>\<omega>. real (N \<omega>) powr (1 + \<alpha> + 1))"
  proof -
    have "integrable (distr M (count_space UNIV) N) (\<lambda>n. real n powr (1 + \<alpha> + 1))"
      unfolding law by (rule geometric_powr_integrable[OF p0 p1])
    thus ?thesis using integrable_distr_eq[OF Nm m1] by simp
  qed
  have m2: "(\<lambda>n::nat. real n) \<in> borel_measurable (count_space UNIV)" by simp
  have E: "expectation (\<lambda>\<omega>. real (N \<omega>)) = (1 - p) / p"
  proof -
    have "(\<integral>\<omega>. real (N \<omega>) \<partial>M) = (\<integral>n. real n \<partial>distr M (count_space UNIV) N)"
      by (rule integral_distr[symmetric, OF Nm m2])
    also have "\<dots> = measure_pmf.expectation (geometric_pmf p) real" unfolding law by simp
    also have "\<dots> = (1 - p) / p" by (rule expectation_geometric_pmf) (use p0 p1 in simp)
    finally show ?thesis by simp
  qed
  show ?thesis
    using random_sum_tail(2)[OF Xm indX same rv \<alpha> Nm indN zero_less_one mom] E by simp
qed

subsection \<open>A Pollaczek--Khinchine-type corollary, conditional on the representation\<close>

text \<open>The M/G/1 queue is not constructed here.  What is formalised is the following conditional statement:
  if \<open>W\<close> has the law of a geometric sum \<open>X_0 + \<dots> + X_(N-1)\<close> of i.i.d. variables whose tail is the integrated tail
  (residual-lifetime tail) \<open>F_I(x) = (1/m) \<integral>_x^\<infinity> P(B > t) dt\<close> of a variable \<open>B\<close>, with \<open>P(N = n) = (1-\<rho>) \<rho>^n\<close>,
  then \<open>P(W > x) ~ \<rho>/(1-\<rho>) F_I(x)\<close> as soon as \<open>P(B > t)\<close> is regularly varying of index \<open>-\<alpha>\<close>, \<open>\<alpha> > 1\<close> (so
  that \<open>F_I\<close> is regularly varying of index \<open>1-\<alpha>\<close>, by Karamata's theorem in the AFP).  The representation of the
  stationary waiting time of the M/G/1 queue as such a geometric sum (and \<open>m\<close> as the mean of \<open>B\<close>) is a
  hypothesis here, not a result.  Here \<open>m = \<integral>_0^\<infinity> P(B > t) dt\<close>, which is the mean of \<open>B\<close> for \<open>B \<ge> 0\<close>; this
  identity is not proved either.\<close>

definition residual_tail :: "('a \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real" where
  "residual_tail B x = (\<integral>t\<in>{x<..}. prob {\<omega> \<in> space M. t < B \<omega>} \<partial>lborel)
      / (\<integral>t\<in>{0<..}. prob {\<omega> \<in> space M. t < B \<omega>} \<partial>lborel)"

lemma residual_tail_rv:
  fixes B :: "'a \<Rightarrow> real" and \<alpha> :: real
  assumes rvB: "regularly_varying (\<lambda>t. prob {\<omega> \<in> space M. t < B \<omega>}) (- \<alpha>)" and \<alpha>: "1 < \<alpha>"
    and intB: "set_integrable lborel {0<..} (\<lambda>t. prob {\<omega> \<in> space M. t < B \<omega>})"
  shows "regularly_varying (residual_tail B) (- (\<alpha> - 1))"
proof -
  define U where "U t = prob {\<omega> \<in> space M. t < B \<omega>}" for t
  have rvU: "regularly_varying U (- \<alpha>)" using rvB unfolding U_def .
  have intU: "set_integrable lborel {0<..} U" using intB unfolding U_def .
  have rvI: "regularly_varying (\<lambda>x. \<integral>t\<in>{x<..}. U t \<partial>lborel) (- \<alpha> + 1)"
    by (rule regularly_varying_tail_integral[OF rvU _ intU]) (use \<alpha> in simp)
  have m: "0 < (\<integral>t\<in>{0<..}. U t \<partial>lborel)"
    by (rule integral_Ioi_pos[OF _ intU]) (auto intro!: regularly_varying_pos[OF rvU])
  have eq: "residual_tail B = (\<lambda>x. (1 / (\<integral>t\<in>{0<..}. U t \<partial>lborel)) * (\<integral>t\<in>{x<..}. U t \<partial>lborel))"
    unfolding residual_tail_def U_def[symmetric] by (rule ext) simp
  have "regularly_varying (\<lambda>x. (1 / (\<integral>t\<in>{0<..}. U t \<partial>lborel)) * (\<integral>t\<in>{x<..}. U t \<partial>lborel)) (- \<alpha> + 1)"
    by (rule regularly_varying_cmult[OF _ rvI]) (use m in simp)
  thus ?thesis unfolding eq by simp
qed

theorem pollaczek_khinchine_rv:
  fixes B W :: "'a \<Rightarrow> real" and X :: "nat \<Rightarrow> 'a \<Rightarrow> real" and N :: "'a \<Rightarrow> nat" and \<alpha> \<rho> :: real
  assumes rvB: "regularly_varying (\<lambda>t. prob {\<omega> \<in> space M. t < B \<omega>}) (- \<alpha>)" and \<alpha>: "1 < \<alpha>"
    and intB: "set_integrable lborel {0<..} (\<lambda>t. prob {\<omega> \<in> space M. t < B \<omega>})"
    and Xm: "\<And>i. X i \<in> borel_measurable M"
    and indX: "indep_vars (\<lambda>_. borel) X UNIV"
    and same: "\<And>i y. prob {\<omega> \<in> space M. y < X i \<omega>} = prob {\<omega> \<in> space M. y < X 0 \<omega>}"
    and repX: "\<And>x. 0 < x \<Longrightarrow> prob {\<omega> \<in> space M. x < X 0 \<omega>} = residual_tail B x"
    and Nm[measurable]: "N \<in> measurable M (count_space UNIV)"
    and indN: "\<And>n A. A \<in> sets (Pi\<^sub>M UNIV (\<lambda>_. borel)) \<Longrightarrow>
        prob ({\<omega> \<in> space M. N \<omega> = n} \<inter> {\<omega> \<in> space M. (\<lambda>i. X i \<omega>) \<in> A})
        = prob {\<omega> \<in> space M. N \<omega> = n} * prob {\<omega> \<in> space M. (\<lambda>i. X i \<omega>) \<in> A}"
    and \<rho>0: "0 < \<rho>" and \<rho>1: "\<rho> < 1"
    and law: "distr M (count_space UNIV) N = measure_pmf (geometric_pmf (1 - \<rho>))"
    and W: "\<And>x. prob {\<omega> \<in> space M. x < W \<omega>} = prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<N \<omega>}. X i \<omega>)}"
  shows "((\<lambda>x. prob {\<omega> \<in> space M. x < W \<omega>} / residual_tail B x) \<longlongrightarrow> \<rho> / (1 - \<rho>)) at_top"
proof -
  have rvR: "regularly_varying (residual_tail B) (- (\<alpha> - 1))" by (rule residual_tail_rv[OF rvB \<alpha> intB])
  have rvT: "regularly_varying (\<lambda>y. prob {\<omega> \<in> space M. y < X 0 \<omega>}) (- (\<alpha> - 1))"
    using rvR regularly_varying_cong[of "\<lambda>y. prob {\<omega> \<in> space M. y < X 0 \<omega>}" "residual_tail B" "- (\<alpha> - 1)"] repX
    by simp
  have a1: "0 < \<alpha> - 1" using \<alpha> by simp
  have p0: "0 < 1 - \<rho>" and p1: "1 - \<rho> < 1" using \<rho>0 \<rho>1 by simp_all
  have main: "((\<lambda>x. prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<N \<omega>}. X i \<omega>)} / prob {\<omega> \<in> space M. x < X 0 \<omega>})
      \<longlongrightarrow> (1 - (1 - \<rho>)) / (1 - \<rho>)) at_top"
    by (rule random_sum_geometric[OF Xm indX same rvT a1 Nm indN p0 p1 law])
  have ev: "\<forall>\<^sub>F x in at_top. prob {\<omega> \<in> space M. x < (\<Sum>i\<in>{0..<N \<omega>}. X i \<omega>)} / prob {\<omega> \<in> space M. x < X 0 \<omega>}
      = prob {\<omega> \<in> space M. x < W \<omega>} / residual_tail B x"
    using eventually_gt_at_top[of 0] by eventually_elim (simp add: W repX)
  have "((\<lambda>x. prob {\<omega> \<in> space M. x < W \<omega>} / residual_tail B x) \<longlongrightarrow> (1 - (1 - \<rho>)) / (1 - \<rho>)) at_top"
    by (rule Lim_transform_eventually[OF main ev])
  thus ?thesis by simp
qed

end

end
