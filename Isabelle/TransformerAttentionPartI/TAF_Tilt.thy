(* Title: Sharp finite total-variation bound for exponential tilting
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Tilt
  imports TAF_Finite_Weights
begin

definition tv_distance :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real" where
  "tv_distance S p q = (\<Sum>i\<in>S. abs (p i-q i))/2"

definition finite_tilt :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real" where
  "finite_tilt S p Y i = p i*Y i/fw_mean S p Y"

lemma absolute_chord:
  fixes M m y :: real
  assumes "1 < M" "1 \<le> m" "m \<le> M" "1 \<le> y" "y \<le> M"
  shows "abs (y-m) \<le> ((M-y)*(m-1)+(y-1)*(M-m))/(M-1)"
proof -
  let ?N = "(M-y)*(m-1)+(y-1)*(M-m)"
  have d: "0 < M-1" using assms by linarith
  have lo: "?N-(m-y)*(M-1) = 2*(y-1)*(M-m)"
    by (simp add: algebra_simps)
  have hi: "?N-(y-m)*(M-1) = 2*(M-y)*(m-1)"
    by (simp add: algebra_simps)
  have nl: "0 \<le> 2*(y-1)*(M-m)"
    using assms by (intro mult_nonneg_nonneg; linarith)
  have nh: "0 \<le> 2*(M-y)*(m-1)"
    using assms by (intro mult_nonneg_nonneg; linarith)
  have l: "m-y \<le> ?N/(M-1)" using lo nl d by (simp add: le_divide_eq; linarith)
  have h: "y-m \<le> ?N/(M-1)" using hi nh d by (simp add: le_divide_eq; linarith)
  show ?thesis using l h by (auto simp: abs_le_iff; linarith)
qed

lemma sharp_tilt_rational_bound:
  fixes t m :: real
  assumes t: "1 < t" and m: "0 < m"
  shows "(m-1)*(t^2-m)/(m*(t^2-1)) \<le> (t-1)/(t+1)"
proof -
  have tp: "0 < t+1" and tm: "0 < t-1" using t by linarith+
  have square_id: "(t-1)*(t+1)=t^2-1" by (simp add: algebra_simps power2_eq_square)
  have ts: "0 < t^2-1" using mult_pos_pos[OF tm tp] square_id by simp
  have den: "0 < m*(t^2-1)" by (rule mult_pos_pos[OF m ts])
  have id: "(t-1)*(m*(t^2-1))-(m-1)*(t^2-m)*(t+1) = (t+1)*(m-t)^2"
    by (simp add: algebra_simps power2_eq_square)
  have nn: "0 \<le> (t+1)*(m-t)^2"
    using tp by (intro mult_nonneg_nonneg) auto
  have cross: "(m-1)*(t^2-m)*(t+1) \<le> (t-1)*(m*(t^2-1))"
    using id nn by linarith
  show ?thesis using cross
    by (simp only: pos_divide_le_eq[OF den] times_divide_eq_left pos_le_divide_eq[OF tp])
qed

context finite_probability
begin

lemma tilt_is_probability:
  assumes Y: "\<And>i. i\<in>S \<Longrightarrow> 0 < Y i"
    and m: "0 < fw_mean S p Y"
  shows "finite_probability S (finite_tilt S p Y)"
proof
  show "finite S" by (rule finite_S)
  show "0 \<le> finite_tilt S p Y i" if "i\<in>S" for i
    unfolding finite_tilt_def using p_nonneg[OF that] Y[OF that] m
    by (intro divide_nonneg_nonneg mult_nonneg_nonneg; auto)
  show "sum (finite_tilt S p Y) S = 1"
    using m by (simp add: finite_tilt_def fw_mean_def sum_divide_distrib[symmetric])
qed

lemma tilt_tv_identity:
  assumes m: "0 < fw_mean S p Y"
  shows "tv_distance S p (finite_tilt S p Y) =
    fw_mean S p (\<lambda>i. abs (Y i-fw_mean S p Y))/(2*fw_mean S p Y)"
proof -
  let ?m = "fw_mean S p Y"
  have point_eq: "abs (p i-finite_tilt S p Y i) = p i*abs (Y i-?m)/?m"
    if "i\<in>S" for i
  proof -
    have id: "p i-finite_tilt S p Y i = p i*(?m-Y i)/?m"
      unfolding finite_tilt_def using m by (simp add: divide_simps algebra_simps)
    show ?thesis using p_nonneg[OF that] m
      by (simp add: id abs_mult abs_divide abs_of_nonneg abs_of_pos abs_minus_commute)
  qed
  have sum_eq: "(\<Sum>i\<in>S. abs (p i-finite_tilt S p Y i)) =
      (\<Sum>i\<in>S. p i*abs (Y i-?m))/?m"
    using sum.cong[OF refl point_eq] by (simp only: sum_divide_distrib)
  show ?thesis unfolding tv_distance_def fw_mean_def[symmetric]
    using sum_eq by (simp add: fw_mean_def divide_divide_eq_left)
qed

lemma tilt_tv_bound:
  assumes t: "1 < t"
    and Ylo: "\<And>i. i\<in>S \<Longrightarrow> 1 \<le> Y i"
    and Yhi: "\<And>i. i\<in>S \<Longrightarrow> Y i \<le> t^2"
  shows "tv_distance S p (finite_tilt S p Y) \<le> (t-1)/(t+1)"
proof -
  let ?m = "fw_mean S p Y"
  let ?M = "t^2"
  have t0: "0 < t" using t by linarith
  have ts: "1 < ?M"
  proof -
    have "0 < (t-1)*(t+1)" using t by (intro mult_pos_pos; linarith)
    then show ?thesis by (simp add: algebra_simps power2_eq_square)
  qed
  have ml: "1 \<le> ?m" and mh: "?m \<le> ?M" using mean_bounds[OF Ylo Yhi] by auto
  have mp: "0 < ?m" using ml by linarith
  have chord: "abs (Y i-?m) \<le>
      ((?M-Y i)*(?m-1)+(Y i-1)*(?M-?m))/(?M-1)" if "i\<in>S" for i
    by (rule absolute_chord[OF ts ml mh Ylo[OF that] Yhi[OF that]])
  have aff: "((?M-y)*(?m-1)+(y-1)*(?M-?m))/(?M-1) =
      (?m*(?M+1)-2*?M)/(?M-1)+((?M+1-2*?m)/(?M-1))*y" for y
    by (simp only: times_divide_eq_left add_divide_distrib[symmetric];
        simp add: algebra_simps)
  have avg: "fw_mean S p (\<lambda>i. ((?M-Y i)*(?m-1)+(Y i-1)*(?M-?m))/(?M-1)) =
      2*(?m-1)*(?M-?m)/(?M-1)"
  proof -
    have fun_eq: "(\<lambda>i. ((?M-Y i)*(?m-1)+(Y i-1)*(?M-?m))/(?M-1)) =
      (\<lambda>i. (?m*(?M+1)-2*?M)/(?M-1)+((?M+1-2*?m)/(?M-1))*Y i)"
      by (rule ext; rule aff)
    have linear: "fw_mean S p (\<lambda>i. (?m*(?M+1)-2*?M)/(?M-1)+((?M+1-2*?m)/(?M-1))*Y i) =
      (?m*(?M+1)-2*?M)/(?M-1)+((?M+1-2*?m)/(?M-1))*?m"
      using mean_add[where x="\<lambda>_. (?m*(?M+1)-2*?M)/(?M-1)" and y="\<lambda>i. ((?M+1-2*?m)/(?M-1))*Y i"]
        mean_const[where c="(?m*(?M+1)-2*?M)/(?M-1)"]
        mean_scale[where c="(?M+1-2*?m)/(?M-1)" and x=Y]
      by simp
    have eq: "(?m*(?M+1)-2*?M)/(?M-1)+((?M+1-2*?m)/(?M-1))*?m =
      2*(?m-1)*(?M-?m)/(?M-1)"
      by (simp only: times_divide_eq_left add_divide_distrib[symmetric]; simp add: algebra_simps)
    show ?thesis using arg_cong[OF fun_eq, of "fw_mean S p"] linear eq by argo
  qed
  have ea: "fw_mean S p (\<lambda>i. abs (Y i-?m)) \<le> 2*(?m-1)*(?M-?m)/(?M-1)"
  proof -
    have "fw_mean S p (\<lambda>i. abs (Y i-?m)) \<le>
      fw_mean S p (\<lambda>i. ((?M-Y i)*(?m-1)+(Y i-1)*(?M-?m))/(?M-1))"
      by (rule mean_mono; rule chord)
    then show ?thesis using avg by simp
  qed
  have divided: "fw_mean S p (\<lambda>i. abs (Y i-?m))/(2*?m) \<le>
      (2*(?m-1)*(?M-?m)/(?M-1))/(2*?m)"
    by (intro divide_right_mono[OF ea]) (use mp in linarith)
  have cancel: "(2*(?m-1)*(?M-?m)/(?M-1))/(2*?m) =
      (?m-1)*(?M-?m)/(?m*(?M-1))"
    using mp ts by (simp add: field_simps algebra_simps)
  have b: "tv_distance S p (finite_tilt S p Y) \<le> (?m-1)*(?M-?m)/(?m*(?M-1))"
    using divided cancel tilt_tv_identity[OF mp] by simp
  show ?thesis using b sharp_tilt_rational_bound[OF t mp] by linarith
qed

end
end
