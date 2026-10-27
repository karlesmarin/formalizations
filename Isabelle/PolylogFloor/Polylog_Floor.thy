(*  Title:      Polylog_Floor.thy
    Author:     Carles Marín

    The antipodal floor of the polylogarithm and of the zeta states

    The Gamma-density measure x^(s-1) e^(-x) / Gamma s with tau = e^(-x) has moments (k+1)^(-s); with the floor of
    Hausdorff_Floor this gives eta s <= |Li_s z| on the unit circle for real s > 0, z /= 1, and the zeta state never
    gets closer to orthogonality than 1 - 2^(1-s).
    Lean counterparts: Formalizations.Analysis.SpecialFunctions.Polylog.HausdorffFloor (gammaMeasure,
    polylog_circle_floor) and Formalizations.Physics.QuantumMechanics.SpeedLimit.ZetaStateFloor.

    Main results:
    * gamma_moment: the moments of the Gamma-density measure.
    * polylog_circle_exists, polylog_circle_floor: eta s <= |Li_s z|.
    * eta_eq: eta s = (1 - 2^(1-s)) zeta s for s > 1.
    * zeta_state_floor.
*)

theory Polylog_Floor
  imports "Hausdorff_Floor.Hausdorff_Floor"
begin

section \<open>The Gamma measure\<close>

text \<open>The unnormalised density \<open>x^(s-1) exp(-a x)\<close> on \<open>(0, \<infinity>)\<close>.\<close>

definition gH :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "gH s a x = (if 0 < x then x powr (s - 1) * exp (- (a * x)) else 0)"

lemma gH_nonneg: "0 \<le> gH s a x"
  unfolding gH_def by simp

lemma gH_meas [measurable]: "gH s a \<in> borel_measurable borel"
  unfolding gH_def by measurable

lemma gH_scale:
  assumes a: "0 < a"
  shows "gH s 1 (a * x) = a powr (s - 1) * gH s a x"
proof (cases "0 < x")
  case True
  then have "0 < a * x" using a by simp
  with True a show ?thesis
    by (simp add: gH_def powr_mult mult.assoc)
next
  case False
  with a show ?thesis by (simp add: gH_def zero_less_mult_iff)
qed

lemma nn_integral_gH:
  assumes s: "0 < s" and a: "0 < a"
  shows "(\<integral>\<^sup>+x. ennreal (gH s a x) \<partial>lborel) = ennreal (Gamma s / a powr s)"
proof -
  have null0: "{0::real} \<in> null_sets lborel"
    by (rule countable_imp_null_set_lborel) simp
  have ae0: "AE x in lborel. x \<noteq> (0::real)"
    by (rule eventually_mono[OF AE_not_in[OF null0]]) simp
  have G1: "(\<integral>\<^sup>+x. ennreal (gH s 1 x) \<partial>lborel) = ennreal (Gamma s)"
  proof -
    have "(\<integral>\<^sup>+x. ennreal (gH s 1 x) \<partial>lborel)
        = (\<integral>\<^sup>+x. ennreal (indicator {0..} x * x powr (s - 1) / exp x) \<partial>lborel)"
    proof (rule nn_integral_cong_AE)
      show "AE x in lborel. ennreal (gH s 1 x) = ennreal (indicator {0..} x * x powr (s - 1) / exp x)"
        using ae0
      proof eventually_elim
        case (elim x)
        show ?case
          by (cases "0 < x") (use elim in \<open>auto simp: gH_def indicator_def exp_minus divide_inverse\<close>)
      qed
    qed
    also have "\<dots> = ennreal (Gamma s)"
      by (rule Gamma_conv_nn_integral_real[OF s, symmetric])
    finally show ?thesis .
  qed
  define I where "I = (\<integral>\<^sup>+x. ennreal (gH s a x) \<partial>lborel)"
  have meas1: "(\<lambda>y. ennreal (gH s 1 y)) \<in> borel_measurable borel" by measurable
  have aff: "(\<integral>\<^sup>+x. ennreal (gH s 1 x) \<partial>lborel)
      = ennreal \<bar>a\<bar> * (\<integral>\<^sup>+x. ennreal (gH s 1 (0 + a * x)) \<partial>lborel)"
    by (rule nn_integral_real_affine[OF meas1]) (use a in simp)
  have inner: "(\<integral>\<^sup>+x. ennreal (gH s 1 (0 + a * x)) \<partial>lborel) = ennreal (a powr (s - 1)) * I"
  proof -
    have "\<And>x. ennreal (gH s 1 (0 + a * x)) = ennreal (a powr (s - 1)) * ennreal (gH s a x)"
      using gH_scale[OF a, of s] by (simp add: ennreal_mult')
    then show ?thesis
      unfolding I_def by (simp add: nn_integral_cmult)
  qed
  have apow: "ennreal a * ennreal (a powr (s - 1)) = ennreal (a powr s)"
  proof -
    have "a * a powr (s - 1) = a powr s" using a by (simp add: powr_mult_base)
    then show ?thesis using a by (simp flip: ennreal_mult')
  qed
  have key0: "ennreal (Gamma s) = ennreal a * (ennreal (a powr (s - 1)) * I)"
    using G1 aff inner a by simp
  have key: "ennreal (a powr s) * I = ennreal (Gamma s)"
    unfolding key0 apow[symmetric] by (rule mult.assoc)
  have cpos: "0 < a powr s" using a by simp
  have Ifin: "I \<noteq> top"
  proof
    assume "I = top"
    then have "ennreal (a powr s) * I = top" using cpos by (simp add: ennreal_mult_eq_top_iff)
    with key show False by simp
  qed
  then have Ilt: "I < top" by (simp add: less_top)
  define r where "r = enn2real I"
  have r0: "0 \<le> r" unfolding r_def by simp
  have Ir: "I = ennreal r" unfolding r_def using Ilt by simp
  have "ennreal (a powr s * r) = ennreal (Gamma s)"
    using key Ir cpos by (simp add: ennreal_mult')
  then have "a powr s * r = Gamma s"
    using cpos r0 s by (subst (asm) ennreal_inj) auto
  then have "r = Gamma s / a powr s" using cpos by (simp add: eq_divide_eq mult.commute)
  then show ?thesis unfolding I_def[symmetric] using Ir by simp
qed

definition gD :: "real \<Rightarrow> real \<Rightarrow> real" where
  "gD s x = gH s 1 x / Gamma s"

definition gmeas :: "real \<Rightarrow> real measure" where
  "gmeas s = density lborel (\<lambda>x. ennreal (gD s x))"

lemma gD_nonneg: "0 < s \<Longrightarrow> 0 \<le> gD s x"
  unfolding gD_def by (simp add: gH_nonneg)

lemma gD_meas [measurable]: "gD s \<in> borel_measurable borel"
  unfolding gD_def by measurable

lemma nn_integral_gD:
  assumes s: "0 < s" and a: "0 < a"
  shows "(\<integral>\<^sup>+x. ennreal (gH s a x / Gamma s) \<partial>lborel) = ennreal (1 / a powr s)"
proof -
  have g: "0 < Gamma s" using s by simp
  have pt: "\<And>x. ennreal (gH s a x / Gamma s) = ennreal (1 / Gamma s) * ennreal (gH s a x)"
  proof -
    fix x
    have eq: "gH s a x / Gamma s = (1 / Gamma s) * gH s a x" by simp
    show "ennreal (gH s a x / Gamma s) = ennreal (1 / Gamma s) * ennreal (gH s a x)"
      by (subst eq) (rule ennreal_mult', use g in simp)
  qed
  have cpos: "0 < a powr s" using a by simp
  have "(\<integral>\<^sup>+x. ennreal (gH s a x / Gamma s) \<partial>lborel)
      = ennreal (1 / Gamma s) * ennreal (Gamma s / a powr s)"
    by (simp add: pt nn_integral_cmult nn_integral_gH[OF s a])
  also have "\<dots> = ennreal (1 / Gamma s * (Gamma s / a powr s))"
    by (rule ennreal_mult'[symmetric]) (use g in simp)
  also have "1 / Gamma s * (Gamma s / a powr s) = 1 / a powr s"
    using g by simp
  finally show ?thesis .
qed

lemma gmeas_total:
  assumes s: "0 < s"
  shows "emeasure (gmeas s) (space (gmeas s)) = 1"
  unfolding gmeas_def gD_def
  using nn_integral_gD[OF s zero_less_one] by (simp add: emeasure_density)

lemma gmeas_prob:
  assumes s: "0 < s"
  shows "finite_measure (gmeas s)"
  by (rule finite_measureI) (simp add: gmeas_total[OF s])

lemma gmeas_ae_pos:
  assumes s: "0 < s"
  shows "AE x in gmeas s. 0 < x"
  unfolding gmeas_def
proof (subst AE_density)
  show "(\<lambda>x. ennreal (gD s x)) \<in> borel_measurable lborel" by measurable
  show "AE x in lborel. 0 < ennreal (gD s x) \<longrightarrow> 0 < x"
  proof (rule AE_I2, intro impI)
    fix x :: real
    assume "0 < ennreal (gD s x)"
    then show "0 < x" by (cases "0 < x") (simp_all add: gD_def gH_def)
  qed
qed

theorem gamma_moment:
  assumes s: "0 < s"
  shows "finite_measure.moment (gmeas s) (\<lambda>x. exp (- x)) k = real (Suc k) powr (- s)"
proof -
  interpret P: finite_measure "gmeas s" using gmeas_prob[OF s] .
  have pt: "gD s x * exp (- x) ^ k = gH s (real (Suc k)) x / Gamma s" for x
  proof (cases "0 < x")
    case True
    have "exp (- (real (Suc k) * x)) = exp (- x) ^ Suc k"
    proof -
      have "- (real (Suc k) * x) = of_nat (Suc k) * (- x)" by simp
      then show ?thesis by (simp only: exp_of_nat_mult)
    qed
    with True show ?thesis by (simp add: gD_def gH_def field_simps)
  next
    case False
    then show ?thesis by (simp add: gD_def gH_def)
  qed
  have "P.moment (\<lambda>x. exp (- x)) k = (\<integral>x. exp (- x) ^ k \<partial>gmeas s)"
    unfolding P.moment_def by simp
  also have "\<dots> = (\<integral>x. gD s x * exp (- x) ^ k \<partial>lborel)"
    unfolding gmeas_def
    by (subst integral_density) (use gD_nonneg[OF s] in \<open>auto intro!: AE_I2\<close>)
  also have "\<dots> = (\<integral>x. gH s (real (Suc k)) x / Gamma s \<partial>lborel)"
    by (simp add: pt)
  also have "\<dots> = enn2real (\<integral>\<^sup>+x. ennreal (gH s (real (Suc k)) x / Gamma s) \<partial>lborel)"
  proof (rule integral_eq_nn_integral)
    show "(\<lambda>x. gH s (real (Suc k)) x / Gamma s) \<in> borel_measurable lborel" by measurable
    show "AE x in lborel. 0 \<le> gH s (real (Suc k)) x / Gamma s"
      using s by (intro AE_I2) (simp add: gH_nonneg)
  qed
  also have "\<dots> = 1 / real (Suc k) powr s"
    using nn_integral_gD[OF s, of "real (Suc k)"] by simp
  also have "\<dots> = real (Suc k) powr (- s)"
    by (simp add: powr_minus inverse_eq_divide)
  finally show ?thesis .
qed

section \<open>The floor of the polylogarithm on the unit circle\<close>

theorem polylog_circle_exists:
  fixes z :: complex
  assumes s: "0 < s" and z: "norm z = 1" and z1: "z \<noteq> 1"
  obtains L \<eta> where
    "(\<lambda>N. \<Sum>k<N. z ^ Suc k * of_real (real (Suc k) powr (- s))) \<longlonglongrightarrow> L"
    and "(\<lambda>N. \<Sum>k<N. (- 1) ^ k * real (Suc k) powr (- s)) \<longlonglongrightarrow> \<eta>"
    and "\<eta> \<le> norm L"
proof -
  interpret P: finite_measure "gmeas s" using gmeas_prob[OF s] .
  have \<tau>m: "(\<lambda>x::real. exp (- x)) \<in> borel_measurable (gmeas s)"
    unfolding gmeas_def by measurable
  have \<tau>01: "AE x in gmeas s. 0 \<le> exp (- x) \<and> exp (- x) < 1"
    using gmeas_ae_pos[OF s] by eventually_elim simp
  have mom: "P.moment (\<lambda>x. exp (- x)) k = real (Suc k) powr (- s)" for k
    using gamma_moment[OF s] by simp
  have c1: "(\<lambda>N. \<Sum>k<N. of_real (P.moment (\<lambda>x. exp (- x)) k) * z ^ k)
      \<longlonglongrightarrow> (\<integral>x. 1 / (1 - of_real (exp (- x)) * z) \<partial>gmeas s)"
    by (rule P.moment_series_floor(1)[OF \<tau>m \<tau>01 z z1])
  have c2: "(\<integral>x. 1 / (1 + exp (- x)) \<partial>gmeas s)
      \<le> norm (\<integral>x. 1 / (1 - of_real (exp (- x)) * z) \<partial>gmeas s)"
    by (rule P.moment_series_floor(2)[OF \<tau>m \<tau>01 z z1])
  have zm: "norm (- 1 :: complex) = 1" by simp
  have zm1: "(- 1 :: complex) \<noteq> 1" by simp
  have c3: "(\<lambda>N. \<Sum>k<N. of_real (P.moment (\<lambda>x. exp (- x)) k) * (- 1 :: complex) ^ k)
      \<longlonglongrightarrow> (\<integral>x. 1 / (1 - of_real (exp (- x)) * (- 1 :: complex)) \<partial>gmeas s)"
    by (rule P.moment_series_floor(1)[OF \<tau>m \<tau>01 zm zm1])
  define \<eta> where "\<eta> = (\<integral>x. 1 / (1 + exp (- x)) \<partial>gmeas s)"
  define F where "F = (\<integral>x. 1 / (1 - of_real (exp (- x)) * z) \<partial>gmeas s)"
  have Fm: "(\<integral>x. 1 / (1 - of_real (exp (- x)) * (- 1 :: complex)) \<partial>gmeas s) = of_real \<eta>"
  proof -
    have "(\<lambda>x. 1 / (1 - of_real (exp (- x)) * (- 1 :: complex)))
        = (\<lambda>x. of_real (1 / (1 + exp (- x))))"
      by (rule ext) simp
    then show ?thesis unfolding \<eta>_def by (subst \<open>(\<lambda>x. 1 / (1 - of_real (exp (- x)) * (- 1 :: complex))) = (\<lambda>x. of_real (1 / (1 + exp (- x))))\<close>) (rule integral_complex_of_real)
  qed
  have alt: "(\<lambda>N. \<Sum>k<N. (- 1) ^ k * real (Suc k) powr (- s)) \<longlonglongrightarrow> \<eta>"
  proof -
    have "(\<lambda>N. (of_real (\<Sum>k<N. (- 1) ^ k * real (Suc k) powr (- s)) :: complex)) \<longlonglongrightarrow> of_real \<eta>"
      using c3 unfolding Fm mom by (simp add: mult.commute)
    then show ?thesis by (simp only: tendsto_of_real_iff)
  qed
  have pol: "(\<lambda>N. \<Sum>k<N. z ^ Suc k * of_real (real (Suc k) powr (- s))) \<longlonglongrightarrow> z * F"
  proof -
    have "(\<lambda>N. z * (\<Sum>k<N. of_real (real (Suc k) powr (- s)) * z ^ k)) \<longlonglongrightarrow> z * F"
      by (rule tendsto_mult_left) (use c1 in \<open>simp add: mom F_def\<close>)
    moreover have "(\<lambda>N. \<Sum>k<N. z ^ Suc k * of_real (real (Suc k) powr (- s)))
        = (\<lambda>N. z * (\<Sum>k<N. of_real (real (Suc k) powr (- s)) * z ^ k))"
      by (rule ext) (simp add: sum_distrib_left power_Suc mult_ac)
    ultimately show ?thesis by simp
  qed
  show ?thesis
  proof (rule that[OF pol alt])
    show "\<eta> \<le> norm (z * F)"
      using c2 unfolding \<eta>_def F_def by (simp add: norm_mult z)
  qed
qed

theorem polylog_circle_floor:
  fixes z :: complex
  assumes s: "0 < s" and z: "norm z = 1" and z1: "z \<noteq> 1"
    and L: "(\<lambda>N. \<Sum>k<N. z ^ Suc k * of_real (real (Suc k) powr (- s))) \<longlonglongrightarrow> L"
    and \<eta>: "(\<lambda>N. \<Sum>k<N. (- 1) ^ k * real (Suc k) powr (- s)) \<longlonglongrightarrow> \<eta>"
  shows "\<eta> \<le> norm L"
proof -
  obtain L' \<eta>' where L': "(\<lambda>N. \<Sum>k<N. z ^ Suc k * of_real (real (Suc k) powr (- s))) \<longlonglongrightarrow> L'"
    and \<eta>': "(\<lambda>N. \<Sum>k<N. (- 1) ^ k * real (Suc k) powr (- s)) \<longlonglongrightarrow> \<eta>'"
    and le: "\<eta>' \<le> norm L'"
    by (rule polylog_circle_exists[OF s z z1])
  from LIMSEQ_unique[OF L L'] LIMSEQ_unique[OF \<eta> \<eta>'] le show ?thesis by simp
qed

section \<open>The identity \<open>\<eta>(s) = (1 - 2^(1-s)) \<zeta>(s)\<close>\<close>

definition zeta :: "real \<Rightarrow> real" where
  "zeta s = (\<Sum>n. real (Suc n) powr (- s))"

lemma summable_zeta:
  assumes s: "1 < s"
  shows "summable (\<lambda>n. real (Suc n) powr (- s))"
proof -
  have "summable (\<lambda>n. (of_nat n :: real) powr (- s))"
    using s by (simp add: summable_real_powr_iff)
  then show ?thesis
    using iffD2[OF summable_Suc_iff[where f = "\<lambda>n. (of_nat n :: real) powr (- s)"]] by simp
qed

lemma sum_pair:
  fixes f :: "nat \<Rightarrow> 'b::comm_monoid_add" and j :: nat
  shows "(\<Sum>i\<in>{j * 2..<j * 2 + 2}. f i) = f (j * 2) + f (j * 2 + 1)"
  by (simp add: numeral_2_eq_2 sum.atLeastLessThan_Suc)

theorem eta_eq:
  assumes s: "1 < s"
  shows "(\<lambda>N. \<Sum>k<N. (- 1) ^ k * real (Suc k) powr (- s)) \<longlonglongrightarrow> (1 - 2 powr (1 - s)) * zeta s"
proof -
  define a where "a n = real (Suc n) powr (- s)" for n
  define c where "c = (2::real) powr (- s)"
  define b where "b k = (- 1) ^ k * a k" for k
  have a0: "\<And>n. 0 \<le> a n" unfolding a_def by simp
  have sa: "summable a" unfolding a_def by (rule summable_zeta[OF s])
  have hA: "a sums zeta s" using sa unfolding zeta_def a_def[symmetric] by (rule summable_sums)
  have sb: "summable b"
  proof (rule summable_norm_cancel)
    have "(\<lambda>n. norm (b n)) = a"
      by (rule ext) (simp add: b_def norm_mult abs_mult a0)
    then show "summable (\<lambda>n. norm (b n))" using sa by simp
  qed
  have hB: "b sums suminf b" using sb by (rule summable_sums)
  have odd: "\<And>j. a (j * 2 + 1) = c * a j"
  proof -
    fix j
    have e1: "real (Suc (j * 2 + 1)) = 2 * real (Suc j)" by (simp add: algebra_simps)
    have "a (j * 2 + 1) = (2 * real (Suc j)) powr (- s)" unfolding a_def e1 ..
    also have "\<dots> = c * a j" unfolding c_def a_def by (rule powr_mult)
    finally show "a (j * 2 + 1) = c * a j" .
  qed
  have gA: "(\<lambda>j. a (j * 2) + a (j * 2 + 1)) sums zeta s"
    using sums_group[OF hA, of 2] by (simp add: sum_pair)
  have gB: "(\<lambda>j. b (j * 2) + b (j * 2 + 1)) sums suminf b"
    using sums_group[OF hB, of 2] by (simp add: sum_pair)
  have pb: "\<And>j. b (j * 2) + b (j * 2 + 1) = (a (j * 2) + a (j * 2 + 1)) - (2 * c) * a j"
    unfolding b_def using odd by (simp add: neg_one_even_power neg_one_odd_power)
  have gC: "(\<lambda>j. (a (j * 2) + a (j * 2 + 1)) - (2 * c) * a j) sums (zeta s - (2 * c) * zeta s)"
    by (rule sums_diff[OF gA sums_mult[OF hA]])
  have "suminf b = zeta s - (2 * c) * zeta s"
    using gB gC unfolding pb by (rule sums_unique2)
  moreover have "2 powr (1 - s) = 2 * c"
    unfolding c_def by (simp add: powr_diff powr_minus field_simps)
  ultimately have "suminf b = (1 - 2 powr (1 - s)) * zeta s" by (simp add: algebra_simps)
  moreover have "(\<lambda>N. \<Sum>k<N. b k) \<longlonglongrightarrow> suminf b" using sb by (rule summable_LIMSEQ)
  ultimately show ?thesis unfolding b_def a_def by simp
qed

section \<open>The floor of the zeta states\<close>

theorem zeta_state_floor:
  assumes s: "1 < s"
  shows "1 - 2 powr (1 - s)
      \<le> norm (\<Sum>n. of_real (real (Suc n) powr (- s) / zeta s)
                 * exp (- (of_real (real (Suc n) * \<theta>) * \<i>)))"
proof -
  define a where "a n = real (Suc n) powr (- s)" for n
  have sa: "summable a" unfolding a_def by (rule summable_zeta[OF s])
  have zpos: "0 < zeta s"
    unfolding zeta_def a_def[symmetric] by (rule suminf_pos[OF sa]) (simp add: a_def)
  define z :: complex where "z = exp (- (of_real \<theta> * \<i>))"
  have nz: "norm z = 1" unfolding z_def by (simp add: norm_exp_eq_Re)
  define T where "T n = z ^ Suc n * of_real (a n)" for n
  have tmeq: "\<And>n. of_real (a n / zeta s) * exp (- (of_real (real (Suc n) * \<theta>) * \<i>))
      = T n / of_real (zeta s)"
  proof -
    fix n
    have "exp (- (of_real (real (Suc n) * \<theta>) * \<i>)) = z ^ Suc n"
    proof -
      have "- (of_real (real (Suc n) * \<theta>) * \<i>) = of_nat (Suc n) * (- (of_real \<theta> * \<i>))"
        by simp
      then show ?thesis unfolding z_def by (simp only: exp_of_nat_mult)
    qed
    then show "of_real (a n / zeta s) * exp (- (of_real (real (Suc n) * \<theta>) * \<i>)) = T n / of_real (zeta s)"
      unfolding T_def by (simp add: field_simps)
  qed
  have sT: "summable T"
  proof (rule summable_norm_cancel)
    have "(\<lambda>n. norm (T n)) = a"
      by (rule ext) (simp add: T_def norm_mult nz norm_power a_def)
    then show "summable (\<lambda>n. norm (T n))" using sa by simp
  qed
  define L where "L = suminf T"
  have TL: "(\<lambda>N. \<Sum>k<N. T k) \<longlonglongrightarrow> L" unfolding L_def using sT by (rule summable_LIMSEQ)
  have eq: "(\<Sum>n. of_real (a n / zeta s) * exp (- (of_real (real (Suc n) * \<theta>) * \<i>)))
      = L / of_real (zeta s)"
    unfolding tmeq L_def using sT by (simp add: suminf_divide)
  have eta: "(1 - 2 powr (1 - s)) * zeta s \<le> norm L"
  proof (cases "z = 1")
    case True
    have Teq: "T = (\<lambda>n. of_real (a n))" unfolding T_def True by simp
    have hA: "a sums zeta s" unfolding zeta_def a_def[symmetric] by (rule summable_sums[OF sa])
    have "L = of_real (zeta s)"
      unfolding L_def Teq by (rule sums_unique[OF sums_of_real[OF hA], symmetric])
    moreover have "0 < (2::real) powr (1 - s)" by simp
    ultimately show ?thesis using zpos by (simp add: algebra_simps)
  next
    case False
    have eE: "(\<lambda>N. \<Sum>k<N. (- 1) ^ k * real (Suc k) powr (- s)) \<longlonglongrightarrow> (1 - 2 powr (1 - s)) * zeta s"
      by (rule eta_eq[OF s])
    have s0: "0 < s" using s by simp
    have TL': "(\<lambda>N. \<Sum>k<N. z ^ Suc k * of_real (real (Suc k) powr (- s))) \<longlonglongrightarrow> L"
      using TL unfolding T_def a_def by simp
    show ?thesis by (rule polylog_circle_floor[OF s0 nz False TL' eE])
  qed
  show ?thesis
    unfolding a_def[symmetric] eq using eta zpos
    by (simp add: norm_divide pos_le_divide_eq)
qed

end
