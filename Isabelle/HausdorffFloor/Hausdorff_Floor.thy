(*  Title:      Hausdorff_Floor.thy
    Author:     Carles Marín

    The antipodal floor of moment power series on the unit circle

    For a finite measure and tau in [0, 1) almost everywhere, the moment series converges at every z /= 1 of the unit
    circle to the integral of 1/(1 - tau z), and its modulus is at least the integral of 1/(1 + tau). The proof avoids
    Abel's theorem: the partial sums are integrals of geometric sums and converge by dominated convergence.
    Lean counterpart: Formalizations.Analysis.SpecialFunctions.Polylog.HausdorffFloor.

    Main results:
    * moment_series_floor.

    References:
    * L. Fejér, Acta Sci. Math. (Szeged) 8 (1937) 89--115, p. 104.
    * Boyer--Parry, arXiv:2111.12226, Appendix A, Lemma 8 (for Li_2).
*)

theory Hausdorff_Floor
  imports "HOL-Analysis.Analysis"
begin

section \<open>The per-term bound\<close>

text \<open>For \<open>x \<in> [0, 1)\<close> and \<open>z\<close> on the unit circle,
  \<open>1 / (1 + x) \<le> Re (1 / (1 - x z))\<close>: the gap is
  \<open>x (1 - x) (1 + Re z) / ((1 + x) |1 - x z|\<^sup>2)\<close>.\<close>

lemma one_div_one_add_le_Re:
  fixes x :: real and z :: complex
  assumes x0: "0 \<le> x" and x1: "x < 1" and z: "norm z = 1"
  shows "1 / (1 + x) \<le> Re (1 / (1 - of_real x * z))"
proof -
  define r where "r = Re z"
  define i where "i = Im z"
  have nrm: "r\<^sup>2 + i\<^sup>2 = 1"
    using z cmod_power2[of z] unfolding r_def i_def by simp
  have r1: "r \<le> 1"
    using complex_Re_le_cmod[of z] z unfolding r_def by simp
  have rm1: "-1 \<le> r"
    using abs_Re_le_cmod[of z] z unfolding r_def by (simp add: abs_le_iff)
  define w where "w = 1 - of_real x * z"
  have Rew: "Re w = 1 - x * r" and Imw: "Im w = - (x * i)"
    unfolding w_def r_def i_def by simp_all
  define D where "D = (Re w)\<^sup>2 + (Im w)\<^sup>2"
  have D_eq: "D = 1 - 2 * x * r + x\<^sup>2"
  proof -
    have "D = 1 - 2 * x * r + x\<^sup>2 * (r\<^sup>2 + i\<^sup>2)"
      unfolding D_def Rew Imw by (simp add: power2_eq_square algebra_simps)
    then show ?thesis using nrm by simp
  qed
  have rx: "r * x \<le> x"
    using mult_right_mono[OF r1 x0] by simp
  have Dpos: "0 < D"
  proof -
    have "(1 - x)\<^sup>2 \<le> D"
      unfolding D_eq power2_eq_square using rx
      by (simp add: algebra_simps)
    moreover have "0 < (1 - x)\<^sup>2" using x1 by simp
    ultimately show ?thesis by linarith
  qed
  have Re_eq: "Re (1 / w) = (1 - x * r) / D"
    unfolding D_def by (simp add: Re_divide Rew)
  have gap: "(1 - x * r) * (1 + x) - D = x * (1 + r) * (1 - x)"
    unfolding D_eq by (simp add: power2_eq_square algebra_simps)
  have gap0: "0 \<le> x * (1 + r) * (1 - x)"
    using x0 x1 rm1 by simp
  have key: "D \<le> (1 - x * r) * (1 + x)"
    using gap gap0 by linarith
  have "1 / (1 + x) \<le> (1 - x * r) / D"
    using key Dpos x0 by (simp add: field_simps)
  then show ?thesis
    using Re_eq unfolding w_def by simp
qed

section \<open>A uniform lower bound for \<open>|1 - t z|\<close>\<close>

text \<open>For \<open>z \<noteq> 1\<close> on the unit circle there is \<open>c > 0\<close> with \<open>c \<le> |1 - t z|\<close> for all
  \<open>t \<in> [0, 1]\<close>: \<open>|1 - t z|\<^sup>2 = 1 - 2 t Re z + t\<^sup>2\<close> is at least \<open>1\<close> if \<open>Re z \<le> 0\<close> and at least
  \<open>(Im z)\<^sup>2 > 0\<close> otherwise.\<close>

lemma uniform_gap:
  fixes z :: complex
  assumes z: "norm z = 1" and z1: "z \<noteq> 1"
  obtains c where "0 < c" "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> 1 \<Longrightarrow> c \<le> norm (1 - of_real t * z)"
proof -
  define r where "r = Re z"
  define i where "i = Im z"
  have nrm: "r\<^sup>2 + i\<^sup>2 = 1"
    using z cmod_power2[of z] unfolding r_def i_def by simp
  define c2 where "c2 = (if r \<le> 0 then 1 else i\<^sup>2)"
  have c2pos: "0 < c2"
  proof (cases "r \<le> 0")
    case True then show ?thesis unfolding c2_def by simp
  next
    case False
    have "i \<noteq> 0"
    proof
      assume i0: "i = 0"
      then have "r\<^sup>2 = 1" using nrm by simp
      then have "r = 1" using False by (simp add: power2_eq_1_iff)
      then have "z = 1" using i0 unfolding r_def i_def by (simp add: complex_eq_iff)
      then show False using z1 by simp
    qed
    then show ?thesis using False unfolding c2_def by simp
  qed
  have bound: "c2 \<le> (norm (1 - of_real t * z))\<^sup>2" if t0: "0 \<le> t" and t1: "t \<le> 1" for t
  proof -
    have sq: "(norm (1 - of_real t * z))\<^sup>2 = 1 - 2 * t * r + t\<^sup>2 * (r\<^sup>2 + i\<^sup>2)"
      unfolding cmod_power2 r_def i_def by (simp add: power2_eq_square algebra_simps)
    show ?thesis
    proof (cases "r \<le> 0")
      case True
      have "0 \<le> - 2 * t * r" using t0 True by (simp add: mult_nonneg_nonpos)
      then have "1 \<le> 1 - 2 * t * r + t\<^sup>2" using zero_le_power2[of t] by linarith
      then show ?thesis unfolding c2_def using True sq nrm by simp
    next
      case False
      have "i\<^sup>2 \<le> 1 - 2 * t * r + t\<^sup>2"
      proof -
        have eq: "1 - 2 * t * r + t\<^sup>2 - i\<^sup>2 = (t - r)\<^sup>2"
          using nrm by (simp add: power2_eq_square algebra_simps)
        have "0 \<le> (t - r)\<^sup>2" by simp
        then show ?thesis using eq by linarith
      qed
      then show ?thesis unfolding c2_def using False sq nrm by simp
    qed
  qed
  show ?thesis
  proof (rule that[of "sqrt c2"])
    show "0 < sqrt c2" using c2pos by simp
    fix t :: real assume "0 \<le> t" "t \<le> 1"
    then have "c2 \<le> (norm (1 - of_real t * z))\<^sup>2" by (rule bound)
    then have "sqrt c2 \<le> sqrt ((norm (1 - of_real t * z))\<^sup>2)" by (rule real_sqrt_le_mono)
    then show "sqrt c2 \<le> norm (1 - of_real t * z)" by simp
  qed
qed

section \<open>The floor for moment series\<close>

context finite_measure
begin

text \<open>The moments of \<open>\<tau>\<close> and the partial sums of their power series at \<open>z\<close>.\<close>

definition moment :: "('a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "moment \<tau> k = (\<integral>x. \<tau> x ^ k \<partial>M)"

theorem moment_series_floor:
  fixes \<tau> :: "'a \<Rightarrow> real" and z :: complex
  assumes \<tau>m: "\<tau> \<in> borel_measurable M"
    and \<tau>01: "AE x in M. 0 \<le> \<tau> x \<and> \<tau> x < 1"
    and z: "norm z = 1" and z1: "z \<noteq> 1"
  defines "F \<equiv> (\<integral>x. 1 / (1 - of_real (\<tau> x) * z) \<partial>M)"
  shows "(\<lambda>N. \<Sum>k<N. of_real (moment \<tau> k) * z ^ k) \<longlonglongrightarrow> F"
    and "(\<integral>x. 1 / (1 + \<tau> x) \<partial>M) \<le> norm F"
proof -
  obtain c where c0: "0 < c" and cb: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> 1 \<Longrightarrow> c \<le> norm (1 - of_real t * z)"
    using uniform_gap[OF z z1] by blast
  define g where "g N x = (\<Sum>k<N. (of_real (\<tau> x) * z) ^ k)" for N x
  define f where "f x = 1 / (1 - of_real (\<tau> x) * z)" for x
  have gm: "g N \<in> borel_measurable M" for N
    unfolding g_def using \<tau>m by measurable
  have fm: "f \<in> borel_measurable M"
    unfolding f_def using \<tau>m by measurable
  \<comment> \<open>each power of \<open>\<tau>\<close> is integrable: bounded by 1 almost everywhere\<close>
  have int_pow: "integrable M (\<lambda>x. \<tau> x ^ k)" for k
  proof (rule integrable_const_bound[where B = 1])
    show "AE x in M. norm (\<tau> x ^ k) \<le> 1"
      using \<tau>01 by eventually_elim (simp add: power_le_one power_abs)
    show "(\<lambda>x. \<tau> x ^ k) \<in> borel_measurable M" using \<tau>m by measurable
  qed
  \<comment> \<open>the partial sums of the moment series are integrals of geometric sums\<close>
  have ps: "(\<Sum>k<N. of_real (moment \<tau> k) * z ^ k) = (\<integral>x. g N x \<partial>M)" for N
  proof -
    have tm: "(of_real (\<tau> x) * z) ^ k = of_real (\<tau> x ^ k) * z ^ k" for x k
      by (simp add: power_mult_distrib)
    have intk: "integrable M (\<lambda>x. of_real (\<tau> x ^ k) * z ^ k :: complex)" for k
      using int_pow[of k] by (intro integrable_mult_left integrable_of_real)
    have intk': "integrable M (\<lambda>x. (of_real (\<tau> x) :: complex) ^ k * z ^ k)" for k
      using intk[of k] by simp
    have "(\<integral>x. g N x \<partial>M) = (\<Sum>k<N. \<integral>x. of_real (\<tau> x ^ k) * z ^ k \<partial>M)"
      unfolding g_def tm by (subst Bochner_Integration.integral_sum) (auto intro: intk intk')
    also have "\<dots> = (\<Sum>k<N. of_real (moment \<tau> k) * z ^ k)"
      unfolding moment_def
      by (simp add: integral_mult_left_zero integral_complex_of_real flip: of_real_power)
    finally show ?thesis by simp
  qed
  \<comment> \<open>pointwise convergence of the geometric sums, almost everywhere\<close>
  have lim: "AE x in M. (\<lambda>N. g N x) \<longlonglongrightarrow> f x"
    using \<tau>01
  proof eventually_elim
    case (elim x)
    have "norm (of_real (\<tau> x) * z) < 1" using elim z by (simp add: norm_mult)
    then have "(\<lambda>k. (of_real (\<tau> x) * z) ^ k) sums (1 / (1 - of_real (\<tau> x) * z))"
      by (rule geometric_sums)
    then show ?case unfolding g_def f_def sums_def by simp
  qed
  \<comment> \<open>a uniform bound for the geometric sums\<close>
  have bnd: "AE x in M. norm (g N x) \<le> 2 / c" for N
    using \<tau>01
  proof eventually_elim
    case (elim x)
    define w where "w = of_real (\<tau> x) * z"
    have nw: "norm w < 1" using elim z unfolding w_def by (simp add: norm_mult)
    have gapw: "c \<le> norm (1 - w)" unfolding w_def using cb elim by simp
    have w1: "w \<noteq> 1" using nw by auto
    have gs: "(\<Sum>k<N. w ^ k) = (w ^ N - 1) / (w - 1)" by (rule geometric_sum[OF w1])
    have sg: "(w ^ N - 1) / (w - 1) = (1 - w ^ N) / (1 - w)"
    proof -
      have "(w ^ N - 1) / (w - 1) = (- (1 - w ^ N)) / (- (1 - w))" by simp
      also have "\<dots> = (1 - w ^ N) / (1 - w)" by (rule minus_divide_divide)
      finally show ?thesis .
    qed
    have "g N x = (1 - w ^ N) / (1 - w)"
      unfolding g_def w_def[symmetric] using gs sg by simp
    also have "norm \<dots> \<le> 2 / c"
    proof -
      have pw: "norm w ^ N \<le> 1"
        using nw by (intro power_le_one) simp_all
      have "norm (1 - w ^ N) \<le> 2"
        using norm_triangle_ineq4[of 1 "w ^ N"] pw by (simp add: norm_power)
      then show ?thesis
        using gapw c0 by (simp add: norm_divide frac_le)
    qed
    finally show ?case .
  qed
  show conv: "(\<lambda>N. \<Sum>k<N. of_real (moment \<tau> k) * z ^ k) \<longlonglongrightarrow> F"
    unfolding ps F_def f_def[symmetric]
    by (rule integral_dominated_convergence[where w = "\<lambda>_. 2 / c"]) (use fm gm lim bnd in auto)
  \<comment> \<open>the floor: the real part of the integrand is at least \<open>1 / (1 + \<tau>)\<close>\<close>
  have intf: "integrable M f"
  proof (rule integrable_const_bound[where B = "1 / c"])
    show "AE x in M. norm (f x) \<le> 1 / c"
      using \<tau>01
    proof eventually_elim
      case (elim x)
      have "c \<le> norm (1 - of_real (\<tau> x) * z)" using cb elim by simp
      then show ?case unfolding f_def using c0 by (simp add: norm_divide frac_le)
    qed
    show "f \<in> borel_measurable M" by (rule fm)
  qed
  have int1: "integrable M (\<lambda>x. 1 / (1 + \<tau> x))"
  proof (rule integrable_const_bound[where B = 1])
    show "AE x in M. norm (1 / (1 + \<tau> x)) \<le> 1"
      using \<tau>01 by eventually_elim simp
    show "(\<lambda>x. 1 / (1 + \<tau> x)) \<in> borel_measurable M" using \<tau>m by measurable
  qed
  have "(\<integral>x. 1 / (1 + \<tau> x) \<partial>M) \<le> (\<integral>x. Re (f x) \<partial>M)"
  proof (rule integral_mono_AE)
    show "integrable M (\<lambda>x. 1 / (1 + \<tau> x))" by (rule int1)
    show "integrable M (\<lambda>x. Re (f x))" using intf by (rule integrable_Re)
    show "AE x in M. 1 / (1 + \<tau> x) \<le> Re (f x)"
      using \<tau>01 by eventually_elim (use one_div_one_add_le_Re z in \<open>auto simp: f_def\<close>)
  qed
  also have "\<dots> = Re F"
    unfolding F_def f_def[symmetric] using intf by (rule integral_Re)
  also have "\<dots> \<le> norm F" by (rule complex_Re_le_cmod)
  finally show "(\<integral>x. 1 / (1 + \<tau> x) \<partial>M) \<le> norm F" .
qed

end

end
