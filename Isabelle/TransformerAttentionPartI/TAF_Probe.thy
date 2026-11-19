(* Title: Exact logarithmic calibration of finite attention probes
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Probe
  imports TAF_Finite_Weights
begin

definition probe_null :: "'r set \<Rightarrow> ('k \<Rightarrow> 'r \<Rightarrow> real) \<Rightarrow>
    ('k \<Rightarrow> 'r \<Rightarrow> nat) \<Rightarrow> 'k \<Rightarrow> real" where
  "probe_null R a n k = (\<Sum>r\<in>R. a k r / real (n k r))"

definition log_slope :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow>
    ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real" where
  "log_slope S w x A =
    - (\<Sum>i\<in>S. w i*(x i-fw_mean S w x)*ln (A i)) / fw_var S w x"

lemma probe_uniform_average:
  assumes "\<And>r. r\<in>R \<Longrightarrow> A k r = 1 / real (n k r)"
  shows "(\<Sum>r\<in>R. a k r * A k r) = probe_null R a n k"
  using assms by (simp add: probe_null_def)

lemma fixed_probe_null:
  assumes a: "\<And>k r. k\<in>K \<Longrightarrow> r\<in>R \<Longrightarrow> a k r = b r"
    and n: "\<And>k r. k\<in>K \<Longrightarrow> r\<in>R \<Longrightarrow> n k r = m r"
    and k: "k\<in>K"
  shows "probe_null R a n k = (\<Sum>r\<in>R. b r / real (m r))"
  unfolding probe_null_def using a n k by (intro sum.cong) auto

lemma log_slope_ratio:
  assumes pos: "\<And>i. i\<in>S \<Longrightarrow> 0 < A i"
    and pos0: "\<And>i. i\<in>S \<Longrightarrow> 0 < A0 i"
  shows "log_slope S w x (\<lambda>i. A i/A0 i) =
      log_slope S w x A - log_slope S w x A0"
proof -
  have logs: "ln (A i/A0 i) = ln (A i)-ln (A0 i)" if "i\<in>S" for i
    using pos[OF that] pos0[OF that] by (simp add: ln_div)
  have sums: "(\<Sum>i\<in>S. w i*(x i-fw_mean S w x)*ln (A i/A0 i)) =
      (\<Sum>i\<in>S. w i*(x i-fw_mean S w x)*ln (A i)) -
      (\<Sum>i\<in>S. w i*(x i-fw_mean S w x)*ln (A0 i))"
  proof -
    have point_eq: "w i*(x i-fw_mean S w x)*ln (A i/A0 i) =
        w i*(x i-fw_mean S w x)*ln (A i) -
        w i*(x i-fw_mean S w x)*ln (A0 i)" if "i\<in>S" for i
      by (simp only: logs[OF that] right_diff_distrib)
    show ?thesis using sum.cong[OF refl point_eq]
      by (simp only: sum_subtractf)
  qed
  show ?thesis unfolding log_slope_def sums
    by (simp add: diff_divide_distrib; linarith)
qed

context finite_probability
begin

lemma centered_mean_zero:
  "(\<Sum>i\<in>S. p i*(x i-fw_mean S p x)) = 0"
  by (simp add: fw_mean_def algebra_simps sum_subtractf
      sum_distrib_right[symmetric] p_sum)

lemma constant_log_slope: "log_slope S p x (\<lambda>_. c) = 0"
proof -
  have "(\<Sum>i\<in>S. p i*(x i-fw_mean S p x)*ln c) = 0"
    using centered_mean_zero[of x] by (simp add: sum_distrib_right[symmetric])
  then show ?thesis by (simp add: log_slope_def)
qed

lemma constant_profile_log_slope:
  assumes "\<And>i. i\<in>S \<Longrightarrow> A i = c"
  shows "log_slope S p x A = 0"
  using assms constant_log_slope[of x c]
  by (simp add: log_slope_def)

lemma fixed_query_zero_null:
  assumes a: "\<And>k r. k\<in>S \<Longrightarrow> r\<in>R \<Longrightarrow> a k r = b r"
    and n: "\<And>k r. k\<in>S \<Longrightarrow> r\<in>R \<Longrightarrow> n k r = m r"
  shows "log_slope S p x (probe_null R a n) = 0"
  by (rule constant_profile_log_slope[where c="\<Sum>r\<in>R. b r / real (m r)"])
     (rule fixed_probe_null[OF a n])

lemma covariance_centered:
  "fw_cov S p x y = (\<Sum>i\<in>S. p i*(x i-fw_mean S p x)*y i)"
  unfolding fw_cov_def fw_mean_def
  by (simp add: algebra_simps sum_subtractf sum_distrib_left)

lemma slope_covariance:
  "log_slope S p x A = -fw_cov S p x (\<lambda>i. ln (A i)) / fw_var S p x"
  by (simp add: log_slope_def covariance_centered)

end

lemma variable_query_flat_counterexample:
  "(1/6::real) = ((1/4)+(1/12))/2"
  by simp

end
