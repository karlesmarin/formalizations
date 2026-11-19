(* Title: Cosine-integral representation and explicit logarithmic remainder
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_RoPE_Ci
  imports TAF_Ci_Tail
begin

lemma cosine_integral_logarithmic_derivative:
  assumes d: "0<d" and L: "L\<noteq>0"
  shows "((\<lambda>t. (-1/L)*cosine_integral (d*exp (-L*t))) has_real_derivative
    (cos (d*exp (-L*t)))) (at t)"
proof -
  let ?z="d*exp (-L*t)"
  have zp: "0<?z" by (intro mult_pos_pos d exp_gt_zero)
  have inner: "((\<lambda>t. d*exp (-L*t)) has_real_derivative (-L*?z)) (at t)"
    by (auto intro!: derivative_eq_intros simp: algebra_simps)
  have comp: "((\<lambda>t. cosine_integral (d*exp (-L*t))) has_real_derivative
      ((cos ?z/?z)*(-L*?z))) (at t)"
    by (rule DERIV_chain2[OF cosine_integral_derivative[OF zp] inner])
  have rate: "(cos ?z/?z)*(-L*?z)= -L*cos ?z"
    using d by (simp add: divide_inverse mult_ac)
  have dcomp: "((\<lambda>t. cosine_integral (d*exp (-L*t))) has_real_derivative
      (-L*cos ?z)) (at t)" using comp by (simp only: rate)
  show ?thesis using DERIV_cmult[OF dcomp, where c="-1/L"] L by simp
qed

lemma rope_cosine_integral_ci:
  assumes theta: "1<theta" and d: "0<d"
  shows "rope_cosine_integral m theta d=real m/ln theta*
    (cosine_integral d-cosine_integral (d/theta))"
proof -
  have th: "0<theta" using theta by linarith
  have L: "ln theta\<noteq>0" using theta by simp
  have der: "((\<lambda>t. (-1/ln theta)*cosine_integral (d*exp (-ln theta*t)))
      has_vector_derivative cos (d*exp (-ln theta*x))) (at x within {0..1})" for x
  proof -
    have base: "((\<lambda>t. (-1/ln theta)*cosine_integral (d*exp (-ln theta*t)))
        has_vector_derivative cos (d*exp (-ln theta*x))) (at x)"
      using cosine_integral_logarithmic_derivative[OF d L, of x]
      by (simp only: has_real_derivative_iff_has_vector_derivative)
    show ?thesis by (rule has_vector_derivative_at_within[OF base])
  qed
  have der_normal: "((\<lambda>t. -(cosine_integral (d*exp (-ln theta*t))/ln theta))
      has_vector_derivative cos (d*exp (-ln theta*x))) (at x within {0..1})" for x
    using der[of x] by (simp add: divide_inverse algebra_simps)
  have ftc: "((\<lambda>t. cos (d*exp (-ln theta*t))) has_integral
      ((-1/ln theta)*cosine_integral (d*exp (-ln theta*1))-
       (-1/ln theta)*cosine_integral (d*exp (-ln theta*0)))) {0..1}"
    by (rule fundamental_theorem_of_calculus
        [where f="\<lambda>t. (-1/ln theta)*cosine_integral (d*exp (-ln theta*t))"];
        (rule der | simp))
  have int: "integral {0..1} (\<lambda>t. cos (d*exp (-ln theta*t)))=
      (cosine_integral d-cosine_integral (d/theta))/ln theta"
    using integral_unique[OF ftc] th
    by (simp add: exp_minus' diff_divide_distrib algebra_simps)
  have scaled: "real m * integral {0..1} (\<lambda>t. cos (d*exp (-ln theta*t))) =
      real m * (cosine_integral d-cosine_integral (d/theta))/ln theta"
    using arg_cong[where f="\<lambda>x. real m*x", OF int]
    by (simp add: divide_inverse mult_ac)
  show ?thesis unfolding rope_cosine_integral_def using scaled by simp
qed

definition rope_logarithmic_error_bound where
  "rope_logarithmic_error_bound m theta d=d*(1-1/theta)+
    real m/ln theta*(2/d+d^2/(4*theta^2))"

lemma rope_cosine_logarithmic_remainder:
  assumes m: "0<m" and theta: "1<theta" and d: "0<d"
  shows "abs (rope_cosine_sum m theta d-real m/ln theta*(ln theta-euler_mascheroni-ln d))
    \<le>rope_logarithmic_error_bound m theta d"
proof -
  let ?L="ln theta"
  let ?c="real m/?L"
  let ?R="cosine_integral (d/theta)-euler_mascheroni-ln (d/theta)"
  let ?A="?c*(?L-euler_mascheroni-ln d)"
  have th: "0<theta" using theta by linarith
  have L: "0<?L" using theta by simp
  have cp: "0\<le>?c" by (intro divide_nonneg_nonneg; use L in auto)
  have yp: "0<d/theta" by (rule divide_pos_pos[OF d th])
  have small: "abs ?R\<le>(d/theta)^2/4" by (rule cosine_integral_small_remainder[OF yp])
  have large: "abs (cosine_integral d)\<le>2/d" by (rule cosine_integral_large_bound[OF d])
  have log: "ln (d/theta)=ln d-?L" using d th by (simp add: ln_div)
  have rem: "rope_cosine_integral m theta d-?A=?c*(cosine_integral d-?R)"
    by (simp add: rope_cosine_integral_ci[OF theta d] log
      add_divide_distrib algebra_simps)
  have triangle: "abs (cosine_integral d-?R)\<le>abs (cosine_integral d)+abs ?R"
    by (rule abs_triangle_ineq4)
  have local: "abs (rope_cosine_integral m theta d-?A)\<le>?c*(2/d+(d/theta)^2/4)"
  proof -
    have "abs (rope_cosine_integral m theta d-?A)=?c*abs (cosine_integral d-?R)"
      by (simp only: rem abs_mult abs_of_nonneg[OF cp])
    also have "...\<le>?c*(2/d+(d/theta)^2/4)"
      by (rule mult_left_mono; use triangle small large cp in linarith)
    finally show ?thesis .
  qed
  have sum_triangle: "abs (rope_cosine_sum m theta d-?A)\<le>
      abs (rope_cosine_sum m theta d-rope_cosine_integral m theta d)+
      abs (rope_cosine_integral m theta d-?A)"
    using abs_triangle_ineq[of "rope_cosine_sum m theta d-rope_cosine_integral m theta d"
      "rope_cosine_integral m theta d-?A"] by simp
  have grid: "abs (rope_cosine_sum m theta d-rope_cosine_integral m theta d)
      \<le>d*(1-1/theta)"
    by (rule rope_grid_error[OF m theta less_imp_le[OF d]])
  have "abs (rope_cosine_sum m theta d-?A)\<le>
      abs (rope_cosine_sum m theta d-rope_cosine_integral m theta d)+
      abs (rope_cosine_integral m theta d-?A)"
    by (rule sum_triangle)
  also have "...\<le>d*(1-1/theta)+?c*(2/d+(d/theta)^2/4)"
    by (rule add_mono[OF grid local])
  finally have combined: "abs (rope_cosine_sum m theta d-?A)
      \<le>d*(1-1/theta)+?c*(2/d+(d/theta)^2/4)" .
  have fraction: "(d/theta)^2/4 = d^2/(4*theta^2)"
    by (simp add: power_divide mult.commute)
  show ?thesis using combined
    by (simp only: rope_logarithmic_error_bound_def fraction)
qed

end
