(* Title: Decay of the cosine integral along the positive imaginary axis
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Ci_Tail
  imports TAF_Ci_Foundation
begin

definition quarter_arc where
  "quarter_arc r t = of_real r * exp (\<i> * of_real t)"

lemma quarter_arc_outside_cut:
  assumes r: "0<r" and t: "t\<in>{0..pi/2}"
  shows "quarter_arc r t\<notin>\<real>\<^sub>\<le>\<^sub>0"
proof (cases "t=pi/2")
  case True
  have st: "sin t = 1" by (simp only: True sin_pi_half)
  have ct: "cos t = 0" by (simp only: True cos_pi_half)
  have arc: "quarter_arc r t = \<i> * of_real r"
    by (simp add: quarter_arc_def exp_Euler cos_of_real sin_of_real st ct)
  show ?thesis using r arc
    by (simp add: complex_nonpos_Reals_iff)
next
  case False
  have co: "0<cos t" using t False pi_gt_zero by (intro cos_gt_zero_pi) auto
  have "0<Re (quarter_arc r t)" using mult_pos_pos[OF r co]
    by (simp add: quarter_arc_def Re_exp cos_of_real sin_of_real)
  then show ?thesis by (auto simp: complex_nonpos_Reals_iff)
qed

lemma quarter_arc_gamma_derivative:
  assumes r: "0<r" and t: "t\<in>{0..pi/2}"
  shows "((\<lambda>t. Gamma_incu 0 (quarter_arc r t)) has_vector_derivative
    (-\<i>*exp (-quarter_arc r t))) (at t within A)"
proof -
  let ?z="quarter_arc r t"
  have nz: "?z\<noteq>0" using r by (simp add: quarter_arc_def)
  have outside: "?z\<notin>\<real>\<^sub>\<le>\<^sub>0"
    by (rule quarter_arc_outside_cut[OF r t])
  have od: "(0::complex) \<in> \<int>-\<int>\<^sub>\<le>\<^sub>0 \<or> ?z \<notin> \<real>\<^sub>\<le>\<^sub>0"
    using outside by simp
  have outer: "(Gamma_incu 0 has_field_derivative (-inverse ?z*exp (-?z))) (at ?z)"
    using has_field_derivative_Gamma_incu_complex[where s=0 and z="?z" and A=UNIV, OF od]
    by (simp add: powr'_def)
  have inner: "((\<lambda>z::complex. of_real r*exp (\<i>*z)) has_field_derivative (?z*\<i>)) (at (of_real t))"
    by (auto intro!: derivative_eq_intros simp: quarter_arc_def algebra_simps)
  have d: "((\<lambda>z::complex. Gamma_incu 0 (of_real r*exp (\<i>*z))) has_field_derivative
      ((-inverse ?z*exp (-?z))*(?z*\<i>))) (at (of_real t))"
    using DERIV_chain[OF outer[unfolded quarter_arc_def] inner]
    by (simp add: o_def quarter_arc_def)
  have alg: "(-inverse ?z*exp (-?z))*(?z*\<i>)= -\<i>*exp (-?z)"
    using nz by (simp add: field_simps)
  have vd: "((\<lambda>u. Gamma_incu 0 (quarter_arc r u)) has_vector_derivative
      ((-inverse ?z*exp (-?z))*(?z*\<i>))) (at t within A)"
    using has_vector_derivative_real_field[OF d, where s=A]
    by (simp add: quarter_arc_def)
  show ?thesis using vd by (simp only: alg)
qed

lemma quarter_arc_gamma_bound:
  assumes r: "0<r"
  shows "norm (Gamma_incu 0 (\<i>* of_real r)-Gamma_incu 0 (of_real r))\<le>
    integral {0..pi/2} (\<lambda>t. exp (-r*cos t))"
proof -
  have ftc: "((\<lambda>t. -\<i>*exp (-quarter_arc r t)) has_integral
      (Gamma_incu 0 (quarter_arc r (pi/2))-Gamma_incu 0 (quarter_arc r 0))) {0..pi/2}"
    by (rule fundamental_theorem_of_calculus; use quarter_arc_gamma_derivative[OF r] pi_gt_zero in auto)
  have ehalf: "exp (\<i> * of_real (pi/2)) = \<i>"
    by (subst exp_Euler; simp add: cos_of_real sin_of_real)
  have endh: "quarter_arc r (pi/2) = \<i> * of_real r"
    unfolding quarter_arc_def by (subst ehalf; simp add: mult.commute)
  have end0: "quarter_arc r 0 = of_real r"
    by (simp add: quarter_arc_def)
  have norm: "norm (-\<i>*exp (-quarter_arc r t))=exp (-r*cos t)" for t
    by (simp add: norm_mult norm_exp_eq_Re quarter_arc_def Re_exp cos_of_real sin_of_real)
  have integrable: "(\<lambda>t. exp (-r*cos t)) integrable_on {0..pi/2}"
    by (intro integrable_continuous_real continuous_intros)
  have point: "norm (-\<i>*exp (-quarter_arc r t))\<le>exp (-r*cos t)" for t
    by (simp only: norm)
  have bound: "norm (integral {0..pi/2} (\<lambda>t. -\<i>*exp (-quarter_arc r t)))\<le>
      integral {0..pi/2} (\<lambda>t. exp (-r*cos t))"
    by (rule integral_norm_bound_integral[OF has_integral_integrable[OF ftc] integrable point])
  have value_eq: "integral {0..pi/2} (\<lambda>t. -\<i>*exp (-quarter_arc r t)) =
      Gamma_incu 0 (\<i>* of_real r)-Gamma_incu 0 (of_real r)"
    using integral_unique[OF ftc] by (simp only: endh end0)
  show ?thesis using bound by (simp only: value_eq)
qed

lemma quarter_arc_dominating_limit:
  "((\<lambda>n. integral {0..pi/2} (\<lambda>t. exp (-real n*cos t))) \<longlongrightarrow> 0) sequentially"
proof -
  let ?S="{0..pi/2}"
  let ?f="\<lambda>n::nat. \<lambda>t::real. if t=pi/2 then 0 else exp (-real n*cos t)"
  have ints: "?f n integrable_on ?S" for n
  proof (rule integrable_spike_finite[where S="{pi/2}" and f="\<lambda>t. exp (-real n*cos t)"])
    show "finite {pi/2::real}" by simp
    show "?f n t=exp (-real n*cos t)" if "t\<in>?S-{pi/2}" for t using that by simp
    show "(\<lambda>t. exp (-real n*cos t)) integrable_on ?S"
      by (intro integrable_continuous_real continuous_intros)
  qed
  have bound: "norm (?f n t)\<le>(1::real)" if t: "t\<in>?S" for n t
  proof (cases "t=pi/2")
    case True then show ?thesis by simp
  next
    case False
    have co: "0\<le>cos t" using t pi_gt_zero by (intro cos_ge_zero) auto
    have "0\<le>real n*cos t" by (intro mult_nonneg_nonneg co) auto
    then show ?thesis using False by simp
  qed
  have point: "((\<lambda>n. ?f n t) \<longlongrightarrow> 0) sequentially" if t: "t\<in>?S" for t
  proof (cases "t=pi/2")
    case True then show ?thesis by simp
  next
    case False
    have co: "0<cos t" using t False pi_gt_zero by (intro cos_gt_zero_pi) auto
    have bot: "filterlim (\<lambda>n::nat. (-cos t)*real n) at_bot sequentially"
      by (rule filterlim_tendsto_neg_mult_at_bot[OF tendsto_const _ filterlim_real_sequentially];
          use co in auto)
    have "((\<lambda>n::nat. exp ((-cos t)*real n)) \<longlongrightarrow> 0) sequentially"
      by (rule filterlim_compose[OF exp_at_bot bot])
    then show ?thesis using False by (simp add: mult.commute)
  qed
  have int1: "(\<lambda>_. 1::real) integrable_on ?S"
    by (rule integrable_const_ivl)
  have lim: "((\<lambda>n. integral ?S (?f n)) \<longlongrightarrow> integral ?S (\<lambda>_. 0::real)) sequentially"
    by (rule dominated_convergence(2)[OF ints int1 bound point])
  have eq: "integral ?S (?f n)=integral ?S (\<lambda>t. exp (-real n*cos t))" for n
    by (rule Henstock_Kurzweil_Integration.integral_spike[where S="{pi/2}"];
        auto intro: negligible_finite)
  show ?thesis using lim by (simp only: eq integral_0)
qed

lemma cosine_integral_nat_limit:
  "((\<lambda>n::nat. cosine_integral (real n)) \<longlongrightarrow> 0) sequentially"
proof -
  have ev: "\<forall>\<^sub>F n::nat in sequentially.
      norm (Gamma_incu 0 (\<i>* of_real (real n))-Gamma_incu 0 (of_real (real n)))\<le>
      integral {0..pi/2} (\<lambda>t. exp (-real n*cos t))"
    by (rule eventually_sequentiallyI[where c=1];
        intro quarter_arc_gamma_bound; simp)
  have diff: "((\<lambda>n::nat. Gamma_incu 0 (\<i>* of_real (real n))-
      Gamma_incu 0 (of_real (real n))) \<longlongrightarrow> 0) sequentially"
    by (rule Lim_null_comparison[OF ev quarter_arc_dominating_limit])
  have real_axis: "((\<lambda>n::nat. Gamma_incu 0 (of_real (real n)::complex)) \<longlongrightarrow> 0) sequentially"
    using filterlim_compose[OF Gamma_incu_at_top_complex[where s=0]
      filterlim_real_sequentially] by (simp add: o_def of_real_of_nat_eq)
  have imaginary: "((\<lambda>n::nat. Gamma_incu 0 (\<i>* of_real (real n))) \<longlongrightarrow> 0) sequentially"
    using tendsto_add[OF diff real_axis] by simp
  have re: "((\<lambda>n::nat. -Re (Gamma_incu 0 (\<i>* of_real (real n)))) \<longlongrightarrow> 0) sequentially"
    using tendsto_minus[OF tendsto_Re[OF imaginary]] by simp
  have eq: "\<forall>\<^sub>F n::nat in sequentially.
      cosine_integral (real n)= -Re (Gamma_incu 0 (\<i>* of_real (real n)))"
    by (rule eventually_sequentiallyI[where c=1];
        intro cosine_integral_gamma_bridge; simp)
  show ?thesis by (subst tendsto_cong[OF eq]; rule re)
qed

lemma cosine_integral_parts_derivative:
  assumes xp: "0<x"
  shows "((\<lambda>x. cosine_integral x-sin x/x) has_real_derivative (sin x/x^2)) (at x)"
proof -
  have ds: "(sin has_real_derivative cos x) (at x)"
    by (rule DERIV_sin)
  have di: "((\<lambda>t::real. t) has_real_derivative 1) (at x)"
    by (rule DERIV_ident)
  have q: "((\<lambda>t. sin t/t) has_real_derivative
      (cos x*x-sin x)/x^2) (at x)"
    using DERIV_quotient[OF ds di] xp by (simp add: power2_eq_square)
  have c: "(cosine_integral has_real_derivative cos x/x) (at x)"
    by (rule cosine_integral_derivative[OF xp])
  have d: "((\<lambda>x. cosine_integral x-sin x/x) has_real_derivative
      (cos x/x-(cos x*x-sin x)/x^2)) (at x)"
    by (rule DERIV_diff[OF c q])
  have alg: "cos x/x-(cos x*x-sin x)/x^2=sin x/x^2"
    using xp by (simp add: field_simps power2_eq_square)
  show ?thesis using d by (simp only: alg)
qed

lemma cosine_integral_parts_interval:
  assumes d: "0<d" and dn: "d\<le>n"
  shows "abs ((cosine_integral n-sin n/n)-(cosine_integral d-sin d/d))\<le>1/d-1/n"
proof -
  have xp: "0<x" if "x\<in>{d..n}" for x using d that by auto
  have deriv: "((\<lambda>u. cosine_integral u-sin u/u) has_vector_derivative
      (sin x/x^2)) (at x within {d..n})" if xi: "x\<in>{d..n}" for x
  proof -
    have base: "((\<lambda>u. cosine_integral u-sin u/u) has_vector_derivative
        (sin x/x^2)) (at x)"
      using cosine_integral_parts_derivative[OF xp[OF xi]]
      by (simp only: has_real_derivative_iff_has_vector_derivative)
    show ?thesis by (rule has_vector_derivative_at_within[OF base])
  qed
  have ftc: "((\<lambda>x. sin x/x^2) has_integral
      ((cosine_integral n-sin n/n)-(cosine_integral d-sin d/d))) {d..n}"
    by (rule fundamental_theorem_of_calculus[OF dn]; rule deriv; assumption)
  have inverse_derivative: "((\<lambda>x::real. -1/x) has_vector_derivative (1/x^2)) (at x within {d..n})"
    if "x\<in>{d..n}" for x
  proof -
    have inv: "((\<lambda>u::real. inverse u) has_real_derivative
        (- ((inverse x) ^ 2))) (at x within {d..n})"
      using DERIV_inverse[where x=x and s="{d..n}"] xp[OF that]
      by (simp add: power2_eq_square)
    have neg: "((\<lambda>u::real. -inverse u) has_real_derivative
        (inverse x^2)) (at x within {d..n})"
      using DERIV_minus[OF inv] by simp
    show ?thesis using neg
      by (simp add: has_real_derivative_iff_has_vector_derivative
        inverse_eq_divide power_divide)
  qed
  have int_inv: "((\<lambda>x::real. 1/x^2) has_integral (1/d-1/n)) {d..n}"
    using fundamental_theorem_of_calculus[OF dn inverse_derivative] by simp
  have point: "norm (sin x/x^2)\<le>1/x^2" if "x\<in>{d..n}" for x
    by (simp add: abs_divide; intro divide_right_mono abs_sin_le_one; simp)
  have bound: "norm (integral {d..n} (\<lambda>x. sin x/x^2))\<le>integral {d..n} (\<lambda>x. 1/x^2)"
    by (rule integral_norm_bound_integral[OF has_integral_integrable[OF ftc]
          has_integral_integrable[OF int_inv] point])
  show ?thesis using bound integral_unique[OF ftc] integral_unique[OF int_inv] by simp
qed

lemma sine_over_nat_limit:
  "((\<lambda>n::nat. sin (real n)/real n) \<longlongrightarrow> 0) sequentially"
proof -
  have point: "norm (sin (real n)/real n)\<le>1/real n" for n::nat
    by (simp add: abs_divide; intro divide_right_mono abs_sin_le_one; simp)
  have ev: "\<forall>\<^sub>F n::nat in sequentially.
      norm (sin (real n)/real n)\<le>1/real n"
    by (rule eventually_sequentiallyI[where c=0]; rule point)
  have lim: "((\<lambda>n::nat. 1/real n) \<longlongrightarrow> 0) sequentially"
    using lim_inverse_n by (simp add: inverse_eq_divide)
  show ?thesis by (rule Lim_null_comparison[OF ev lim])
qed

lemma cosine_integral_tail_remainder:
  assumes d: "0<d"
  shows "abs (cosine_integral d-sin d/d)\<le>1/d"
proof -
  let ?H="\<lambda>x. cosine_integral x-sin x/x"
  have hlim: "((\<lambda>n::nat. ?H (real n)) \<longlongrightarrow> 0) sequentially"
    using tendsto_diff[OF cosine_integral_nat_limit sine_over_nat_limit] by simp
  have lim: "((\<lambda>n::nat. ?H (real n)-?H d) \<longlongrightarrow> -?H d) sequentially"
    using tendsto_diff[OF hlim tendsto_const[of "?H d"]] by simp
  have evd: "\<forall>\<^sub>F n::nat in sequentially. d\<le>real n"
    by (rule eventually_compose_filterlim[OF eventually_ge_at_top filterlim_real_sequentially])
  have bound: "norm (?H (real n)-?H d)\<le>1/d" if dn: "d\<le>real n" for n::nat
  proof -
    have "abs (?H (real n)-?H d)\<le>1/d-1/real n"
      by (rule cosine_integral_parts_interval[OF d dn])
    also have "...\<le>1/d" by simp
    finally show ?thesis by simp
  qed
  have evbound: "\<forall>\<^sub>F n::nat in sequentially.
      norm (?H (real n)-?H d)\<le>1/d"
    by (rule eventually_mono[OF evd]; rule bound)
  have "norm (-?H d)\<le>1/d"
    by (rule Lim_norm_ubound[OF _ lim evbound]; simp)
  then show ?thesis by simp
qed

lemma cosine_integral_large_bound:
  assumes d: "0<d"
  shows "abs (cosine_integral d)\<le>2/d"
proof -
  have sd: "abs (sin d/d)\<le>1/d"
    using divide_right_mono[OF abs_sin_le_one less_imp_le[OF d]]
    by (simp add: abs_divide abs_of_pos[OF d])
  have "abs (cosine_integral d)\<le>abs (cosine_integral d-sin d/d)+abs (sin d/d)"
    using abs_triangle_ineq[of "cosine_integral d-sin d/d" "sin d/d"] by simp
  also have "...\<le>1/d+1/d" using cosine_integral_tail_remainder[OF d] sd by linarith
  finally show ?thesis by simp
qed

lemma cosine_integral_at_top:
  "(cosine_integral \<longlongrightarrow> 0) at_top"
proof -
  have pos: "\<forall>\<^sub>F x::real in at_top. 0<x"
    by (rule eventually_gt_at_top)
  have ev: "\<forall>\<^sub>F x::real in at_top. norm (cosine_integral x)\<le>2/x"
    by (rule eventually_mono[OF pos]; simp add: cosine_integral_large_bound)
  have lim: "((\<lambda>x::real. 2/x) \<longlongrightarrow> 0) at_top"
    using tendsto_mult[OF tendsto_const[of "2::real"]
      tendsto_inverse_0_at_top[OF filterlim_ident]]
    by (simp add: divide_inverse)
  show ?thesis by (rule Lim_null_comparison[OF ev lim])
qed

lemma cosine_integral_improper_integral:
  assumes dp: "0<d"
  shows "((\<lambda>R::real. integral {d..R} (\<lambda>x. cos x/x))
      \<longlongrightarrow> -cosine_integral d) at_top"
proof -
  have finite_eq: "integral {d..R} (\<lambda>x. cos x/x) =
      cosine_integral R-cosine_integral d" if dr: "d\<le>R" for R
  proof -
    have der: "(cosine_integral has_vector_derivative cos x/x)
        (at x within {d..R})" if xi: "x\<in>{d..R}" for x
    proof -
      have xp: "0<x" using dp xi by auto
      have base: "(cosine_integral has_vector_derivative cos x/x) (at x)"
        using cosine_integral_derivative[OF xp]
        by (simp only: has_real_derivative_iff_has_vector_derivative)
      show ?thesis by (rule has_vector_derivative_at_within[OF base])
    qed
    have ftc: "((\<lambda>x. cos x/x) has_integral
        (cosine_integral R-cosine_integral d)) {d..R}"
      by (rule fundamental_theorem_of_calculus[OF dr der])
    show ?thesis by (rule integral_unique[OF ftc])
  qed
  have evd: "\<forall>\<^sub>F R::real in at_top. d\<le>R"
    by (rule eventually_ge_at_top)
  have ev_eq: "\<forall>\<^sub>F R::real in at_top.
      integral {d..R} (\<lambda>x. cos x/x) = cosine_integral R-cosine_integral d"
    by (rule eventually_mono[OF evd]; rule finite_eq)
  have lim: "((\<lambda>R::real. cosine_integral R-cosine_integral d)
      \<longlongrightarrow> -cosine_integral d) at_top"
    using tendsto_diff[OF cosine_integral_at_top tendsto_const[of "cosine_integral d"]]
    by simp
  show ?thesis by (subst tendsto_cong[OF ev_eq]; rule lim)
qed

end
