(* Title: Logarithmic RoPE grid with explicit finite quadrature error
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_RoPE_Grid
  imports TAF_Cosine_Riemann
begin

definition rope_cosine_sum :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "rope_cosine_sum m theta d=(\<Sum>i<m. cos (d*exp (-ln theta*(real i/real m))))"

definition rope_cosine_integral :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "rope_cosine_integral m theta d=real m*integral {0..1} (\<lambda>t. cos (d*exp (-ln theta*t)))"

lemma exponential_phase_antimono:
  fixes d L :: real
  assumes d: "0\<le>d" and L: "0\<le>L"
  shows "antimono (\<lambda>t. d*exp (-L*t))"
proof (rule antimonoI)
  fix x y :: real assume xy: "x\<le>y"
  have "L*x\<le>L*y" by (rule mult_left_mono[OF xy L])
  then have ex: "exp (-L*y)\<le>exp (-L*x)" by simp
  show "d*exp (-L*y)\<le>d*exp (-L*x)" by (rule mult_left_mono[OF ex d])
qed

lemma rope_grid_error:
  assumes m: "0<m" and theta: "1<theta" and d: "0\<le>d"
  shows "abs (rope_cosine_sum m theta d-rope_cosine_integral m theta d)\<le>d*(1-1/theta)"
proof -
  have th: "0<theta" using theta by linarith
  have L: "0\<le>ln theta" using theta by simp
  have mono: "antimono (\<lambda>t. d*exp (-ln theta*t))"
    by (rule exponential_phase_antimono[OF d L])
  have cont: "continuous_on UNIV (\<lambda>t. cos (d*exp (-ln theta*t)))"
    by (rule logarithmic_cosine_continuous)
  have error: "abs ((\<Sum>i<m. cos (d*exp (-ln theta*(real i/real m))))-
    real m*integral {0..1} (\<lambda>t. cos (d*exp (-ln theta*t))))\<le>
      d*exp (-ln theta*0)-d*exp (-ln theta*1)"
    by (rule monotone_cosine_riemann_error[OF m mono cont])
  show ?thesis using error th
    by (simp add: rope_cosine_sum_def rope_cosine_integral_def exp_minus' algebra_simps)
qed

lemma normalized_rope_grid_error:
  assumes m: "0<m" and theta: "1<theta" and d: "0\<le>d"
  shows "abs (rope_cosine_sum m theta d/real m-
    integral {0..1} (\<lambda>t. cos (d*exp (-ln theta*t))))\<le>d*(1-1/theta)/real m"
proof -
  have mp: "0<real m" using m by simp
  have err: "abs (rope_cosine_sum m theta d-rope_cosine_integral m theta d)/real m\<le>d*(1-1/theta)/real m"
    by (rule divide_right_mono[OF rope_grid_error[OF m theta d]]; use mp in linarith)
  have id: "rope_cosine_sum m theta d/real m-
    integral {0..1} (\<lambda>t. cos (d*exp (-ln theta*t))) =
    (rope_cosine_sum m theta d-rope_cosine_integral m theta d)/real m"
    using mp by (simp add: rope_cosine_integral_def diff_divide_distrib)
  show ?thesis using err mp by (simp only: id abs_divide abs_of_pos[OF mp])
qed

lemma normalized_rope_grid_limit:
  assumes theta: "1<theta" and d: "0\<le>d"
  shows "((\<lambda>m. rope_cosine_sum m theta d/real m) \<longlongrightarrow>
    integral {0..1} (\<lambda>t. cos (d*exp (-ln theta*t)))) sequentially"
proof -
  let ?I = "integral {0..1} (\<lambda>t. cos (d*exp (-ln theta*t)))"
  let ?B = "d*(1-1/theta)"
  have lim: "((\<lambda>m. ?B/real m) \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF tendsto_const[of ?B] lim_inverse_n]
    by (simp add: divide_inverse)
  have ev: "\<forall>\<^sub>F m in sequentially. norm (rope_cosine_sum m theta d/real m-?I)\<le>?B/real m"
    by (rule eventually_sequentiallyI[where c=1];
        use normalized_rope_grid_error[OF _ theta d] in auto)
  have zero: "((\<lambda>m. rope_cosine_sum m theta d/real m-?I) \<longlongrightarrow> 0) sequentially"
    by (rule Lim_null_comparison[OF ev lim])
  show ?thesis using tendsto_add[OF zero tendsto_const[of ?I]] by simp
qed

end
