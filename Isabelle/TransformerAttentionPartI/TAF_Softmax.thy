(* Title: Oscillation bound for the finite softmax
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Softmax
  imports TAF_Tilt TAF_Exponential_Family
begin

definition finite_softmax :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real" where
  "finite_softmax S s i = exp (s i)/(\<Sum>j\<in>S. exp (s j))"

lemma exponential_sum_positive:
  fixes s :: "'a \<Rightarrow> real"
  assumes "finite S" "S\<noteq>{}"
  shows "0 < (\<Sum>i\<in>S. exp (s i))"
  using sum_strict_mono[OF assms, where f="\<lambda>_. 0" and g="\<lambda>i. exp (s i)"] by simp

lemma softmax_probability:
  assumes "finite S" "S\<noteq>{}"
  shows "finite_probability S (finite_softmax S s)"
proof
  show "finite S" by (rule assms(1))
  show "0 \<le> finite_softmax S s i" if "i\<in>S" for i
    using exponential_sum_positive[OF assms, where s=s]
    by (simp add: finite_softmax_def)
  show "sum (finite_softmax S s) S = 1"
    using exponential_sum_positive[OF assms, where s=s]
    by (simp add: finite_softmax_def sum_divide_distrib[symmetric])
qed

lemma softmax_shift:
  "finite_softmax S (\<lambda>i. s i+c) = finite_softmax S s"
  by (rule ext; simp add: finite_softmax_def exp_add sum_distrib_right[symmetric])

lemma softmax_as_tilt:
  assumes fin: "finite S" and ne: "S\<noteq>{}"
  shows "finite_softmax S (\<lambda>i. s i+r i) =
    finite_tilt S (finite_softmax S s) (\<lambda>i. exp (r i-l))"
proof -
  let ?Z = "\<Sum>i\<in>S. exp (s i)"
  let ?Zr = "\<Sum>i\<in>S. exp (s i+r i)"
  have Z: "?Z\<noteq>0"
    using exponential_sum_positive[OF fin ne, where s=s] by linarith
  have Zr: "?Zr\<noteq>0"
    using exponential_sum_positive[OF fin ne, where s="\<lambda>i. s i+r i"] by linarith
  have point_eq: "finite_softmax S s i*exp (r i-l) = exp (s i+r i)/(exp l*?Z)" for i
    by (simp add: finite_softmax_def exp_add exp_diff algebra_simps)
  have m: "fw_mean S (finite_softmax S s) (\<lambda>i. exp (r i-l)) = ?Zr/(exp l*?Z)"
    by (simp add: fw_mean_def point_eq sum_divide_distrib[symmetric])
  have tiltpoint: "finite_tilt S (finite_softmax S s) (\<lambda>i. exp (r i-l)) i =
    exp (s i+r i)/?Zr" for i
    unfolding finite_tilt_def
    by (simp only: m point_eq; use Z Zr in simp)
  show ?thesis by (rule ext; simp only: tiltpoint finite_softmax_def)
qed

lemma tanh_half_exp:
  fixes x :: real
  shows "tanh (x/2) = (exp x-1)/(exp x+1)"
proof -
  have e: "exp x\<noteq>0" by simp
  have dp: "0<exp x+1" by (rule add_pos_pos; simp)
  have den: "exp x+1\<noteq>0" using dp by linarith
  have exponent: "-2*(x/2)=-x" by simp
  have ei: "exp (-2*(x/2))=1/exp x" by (simp only: exponent exp_minus')
  have num: "1-1/exp x=(exp x-1)/exp x" using e by (simp add: diff_divide_distrib)
  have denom: "1+1/exp x=(exp x+1)/exp x" using e by (simp add: add_divide_distrib)
  show ?thesis
    by (simp only: tanh_real_altdef ei num denom; simp)
qed

lemma softmax_oscillation_bound:
  assumes fin: "finite S" and ne: "S\<noteq>{}"
    and lo: "\<And>i. i\<in>S \<Longrightarrow> l \<le> r i"
    and hi: "\<And>i. i\<in>S \<Longrightarrow> r i \<le> u"
  shows "tv_distance S (finite_softmax S s) (finite_softmax S (\<lambda>i. s i+r i))
    \<le> tanh ((u-l)/4)"
proof -
  interpret p: finite_probability S "finite_softmax S s"
    by (rule softmax_probability[OF fin ne])
  obtain i where "i\<in>S" using ne by blast
  then have lu: "l\<le>u" using lo hi by force
  show ?thesis
  proof (cases "l=u")
    case True
    have pt: "finite_softmax S (\<lambda>i. s i+r i) j = finite_softmax S s j" if "j\<in>S" for j
    proof -
      have eq: "r i=l" if "i\<in>S" for i using lo[OF that] hi[OF that] True by linarith
      have denom: "(\<Sum>i\<in>S. exp (s i+r i)) = (\<Sum>i\<in>S. exp (s i+l))"
        by (rule sum.cong[OF refl]; simp add: eq)
      show ?thesis using eq[OF that]
        by (simp only: finite_softmax_def denom; simp add: exp_add sum_distrib_right[symmetric])
    qed
    show ?thesis using True by (simp add: tv_distance_def pt)
  next
    case False
    have lt: "l<u" using lu False by auto
    have ul: "0 < (u-l)/2" using lt by simp
    let ?t = "exp ((u-l)/2)"
    have t: "1 < ?t" using ul by simp
    have square: "?t^2 = exp (u-l)"
      by (simp add: power2_eq_square exp_add[symmetric])
    have yl: "1 \<le> exp (r i-l)" if "i\<in>S" for i using lo[OF that] by simp
    have yh: "exp (r i-l) \<le> ?t^2" if "i\<in>S" for i using hi[OF that] by (simp add: square)
    have bound: "tv_distance S (finite_softmax S s)
      (finite_tilt S (finite_softmax S s) (\<lambda>i. exp (r i-l))) \<le> (?t-1)/(?t+1)"
      by (rule p.tilt_tv_bound[where t="?t" and Y="\<lambda>i. exp (r i-l)", OF t yl yh])
    have eq: "(?t-1)/(?t+1) = tanh ((u-l)/4)"
      using tanh_half_exp[where x="(u-l)/2"] by simp
    show ?thesis using bound eq softmax_as_tilt[OF fin ne, where s=s and r=r and l=l] by simp
  qed
qed

end
