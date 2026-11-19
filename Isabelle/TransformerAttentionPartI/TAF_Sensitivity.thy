(* Title: Oscillation sensitivity of a finite exponential family
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Sensitivity
  imports TAF_KL_Bound TAF_Softmax
begin

lemma tanh_below_identity:
  fixes x :: real
  assumes x: "0\<le>x"
  shows "tanh x\<le>x"
proof -
  have d: "((\<lambda>t::real. t-tanh t) has_real_derivative (tanh t)^2) (at t)" for t
    by (auto intro!: derivative_eq_intros simp: algebra_simps)
  have "(0-tanh 0)\<le>x-tanh x"
    by (rule deriv_nonneg_imp_mono[where g'="\<lambda>t. (tanh t)^2"]; auto intro: d simp: x)
  then show ?thesis by simp
qed

lemma scalar_interval_bounds:
  fixes c z L :: real
  assumes "0\<le>z" "z\<le>L"
  shows "min 0 (c*L)\<le>c*z" "c*z\<le>max 0 (c*L)"
proof -
  have both: "min 0 (c*L)\<le>c*z \<and> c*z\<le>max 0 (c*L)"
  proof (cases "0\<le>c")
    case True
    have lo: "0\<le>c*z" by (rule mult_nonneg_nonneg[OF True assms(1)])
    have hi: "c*z\<le>c*L" by (rule mult_left_mono[OF assms(2) True])
    show ?thesis using lo hi by auto
  next
    case False
    have cn: "c\<le>0" using False by simp
    have lo: "c*L\<le>c*z" by (rule mult_left_mono_neg[OF assms(2) cn])
    have hi: "c*z\<le>0" using cn assms(1) by (rule mult_nonpos_nonneg)
    show ?thesis using lo hi by auto
  qed
  show "min 0 (c*L)\<le>c*z" using both by blast
  show "c*z\<le>max 0 (c*L)" using both by blast
qed

lemma scalar_range_width:
  fixes c L :: real
  assumes "0\<le>L"
  shows "max 0 (c*L)-min 0 (c*L)=abs c*L"
proof -
  have "max 0 (c*L)-min 0 (c*L)=abs (c*L)"
    by (auto simp: max_def min_def abs_if)
  then show ?thesis using assms by (simp add: abs_mult abs_of_nonneg)
qed

context finite_exp_family
begin

lemma probability_as_softmax:
  assumes i: "i\<in>S"
  shows "finite_softmax S (\<lambda>i. ln (a i)-t*E i) i=ep t i"
proof -
  have pt: "exp (ln (a j)-t*E j)=ew t j" if j: "j\<in>S" for j
    using a_pos[OF j] by (simp add: ew_def exp_diff exp_minus')
  have den: "(\<Sum>j\<in>S. exp (ln (a j)-t*E j))=mom 0 t"
    unfolding mom0_as_sum by (rule sum.cong[OF refl]; rule pt)
  show ?thesis by (simp only: finite_softmax_def den pt[OF i] ep_def)
qed

lemma family_tv_oscillation:
  assumes L: "0\<le>L" and lo: "\<And>i. i\<in>S \<Longrightarrow> 0\<le>E i"
    and hi: "\<And>i. i\<in>S \<Longrightarrow> E i\<le>L"
  shows "tv_distance S (ep g) (ep h)\<le>tanh (abs (h-g)*L/4)"
proof -
  let ?s = "\<lambda>i. ln (a i)-g*E i"
  let ?r = "\<lambda>i. (g-h)*E i"
  have rlo: "min 0 ((g-h)*L)\<le>?r i" if "i\<in>S" for i
    by (rule scalar_interval_bounds(1)[OF lo[OF that] hi[OF that]])
  have rhi: "?r i\<le>max 0 ((g-h)*L)" if "i\<in>S" for i
    by (rule scalar_interval_bounds(2)[OF lo[OF that] hi[OF that]])
  have sm: "(\<lambda>i. ?s i+?r i)=(\<lambda>i. ln (a i)-h*E i)"
    by (rule ext; simp add: algebra_simps)
  have tv: "tv_distance S (ep g) (ep h)=
    tv_distance S (finite_softmax S ?s) (finite_softmax S (\<lambda>i. ?s i+?r i))"
    unfolding tv_distance_def sm
    by (rule arg_cong[where f="\<lambda>x::real. x/2"]; rule sum.cong[OF refl]; simp only: probability_as_softmax)
  have b: "tv_distance S (finite_softmax S ?s) (finite_softmax S (\<lambda>i. ?s i+?r i))\<le>
      tanh ((max 0 ((g-h)*L)-min 0 ((g-h)*L))/4)"
    by (rule softmax_oscillation_bound[OF finite_S nonempty_S rlo rhi])
  show ?thesis using b by (simp only: tv scalar_range_width[OF L] abs_minus_commute)
qed

lemma family_tv_linear_bound:
  assumes L: "0\<le>L" and lo: "\<And>i. i\<in>S \<Longrightarrow> 0\<le>E i"
    and hi: "\<And>i. i\<in>S \<Longrightarrow> E i\<le>L"
  shows "tv_distance S (ep g) (ep h)\<le>min 1 (abs (h-g)*L/4)"
proof -
  have b: "tv_distance S (ep g) (ep h)\<le>tanh (abs (h-g)*L/4)"
    by (rule family_tv_oscillation[OF L lo hi])
  have nn: "0\<le>abs (h-g)*L/4" using L by (intro divide_nonneg_nonneg mult_nonneg_nonneg) auto
  have lin: "tanh (abs (h-g)*L/4)\<le>abs (h-g)*L/4" by (rule tanh_below_identity[OF nn])
  have one: "tanh (abs (h-g)*L/4)<1" by (rule tanh_real_lt_1)
  show ?thesis using b lin one by simp
qed

end
end
