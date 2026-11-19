(* Title: Conditional transfer from the cosine grid to a finite power row
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_RoPE_Scores
  imports TAF_RoPE_Ci TAF_Log_Scores
begin

lemma rope_score_point_remainder:
  fixes a c e B rho h :: real
  assumes m: "0<m" and theta: "1<theta" and d: "0<d" and h: "0<h"
    and B: "rope_logarithmic_error_bound m theta d\<le>B" and e: "abs e\<le>rho"
  defines "g \<equiv> a*real m/(sqrt h*ln theta)"
  shows "abs ((c+a*rope_cosine_sum m theta d/sqrt h+e)-
      ((c+g*(ln theta-euler_mascheroni))-g*ln d))\<le>abs a*B/sqrt h+rho"
proof -
  let ?R="rope_cosine_sum m theta d-real m/ln theta*(ln theta-euler_mascheroni-ln d)"
  have shp: "0<sqrt h" using h by simp
  have geq: "g=(a/sqrt h)*(real m/ln theta)"
    by (simp add: g_def divide_inverse algebra_simps)
  have algebra: "(c+a*rope_cosine_sum m theta d/sqrt h+e)-
      ((c+g*(ln theta-euler_mascheroni))-g*ln d)=(a/sqrt h)*?R+e"
    by (simp add: geq divide_inverse algebra_simps)
  have err: "abs ?R\<le>B" using rope_cosine_logarithmic_remainder[OF m theta d] B by linarith
  have coeff: "0\<le>abs a/sqrt h" by (intro divide_nonneg_nonneg; use shp in auto)
  have product: "(abs a/sqrt h)*abs ?R\<le>(abs a/sqrt h)*B"
    by (rule mult_left_mono[OF err coeff])
  have "abs ((a/sqrt h)*?R+e)\<le>abs ((a/sqrt h)*?R)+abs e"
    by (rule abs_triangle_ineq)
  also have "...\<le>(abs a/sqrt h)*B+rho"
    using product e shp by (simp only: abs_mult abs_divide abs_of_pos[OF shp]; linarith)
  finally have bound2: "abs ((a/sqrt h)*?R+e)\<le>(abs a/sqrt h)*B+rho" .
  have left_eq: "abs ((c+a*rope_cosine_sum m theta d/sqrt h+e)-
      ((c+g*(ln theta-euler_mascheroni))-g*ln d)) = abs ((a/sqrt h)*?R+e)"
    by (simp only: algebra)
  have right_eq: "(abs a/sqrt h)*B+rho = abs a*B/sqrt h+rho"
    by (simp add: divide_inverse mult_ac)
  show ?thesis using bound2 by (simp only: left_eq right_eq)
qed

lemma conditional_rope_power_row:
  fixes a c :: real
  assumes fin: "finite S" and ne: "S\<noteq>{}"
    and m: "0<m" and theta: "1<theta" and h: "0<h"
    and d: "\<And>i. i\<in>S \<Longrightarrow> 0<d i"
    and B: "\<And>i. i\<in>S \<Longrightarrow> rope_logarithmic_error_bound m theta (d i)\<le>B"
    and e: "\<And>i. i\<in>S \<Longrightarrow> abs (e i)\<le>rho"
  defines "g \<equiv> a*real m/(sqrt h*ln theta)"
    and "eta \<equiv> abs a*B/sqrt h+rho"
  shows "tv_distance S (finite_power_profile S d g)
      (finite_softmax S (\<lambda>i. c+a*rope_cosine_sum m theta (d i)/sqrt h+e i))\<le>tanh (eta/2)"
proof -
  let ?b="c+g*(ln theta-euler_mascheroni)"
  let ?s="\<lambda>i. c+a*rope_cosine_sum m theta (d i)/sqrt h+e i"
  let ?r="\<lambda>i. ?s i-(?b-g*ln (d i))"
  have bound: "abs (?r i)\<le>eta" if i: "i\<in>S" for i
    using rope_score_point_remainder[OF m theta d[OF i] h B[OF i] e[OF i], where a=a and c=c]
    by (simp only: g_def eta_def)
  have lo: "-eta\<le>?r i" if "i\<in>S" for i using bound[OF that] by (auto simp: abs_le_iff)
  have hi: "?r i\<le>eta" if "i\<in>S" for i using bound[OF that] by (auto simp: abs_le_iff)
  have stability: "tv_distance S (finite_power_profile S d g)
      (finite_softmax S (\<lambda>i. ?b-g*ln (d i)+?r i))\<le>tanh ((eta-(-eta))/4)"
    by (rule logarithmic_score_stability[OF fin ne d lo hi])
  have eq: "(\<lambda>i. ?b-g*ln (d i)+?r i)=?s" by (rule ext; simp)
  show ?thesis using stability by (simp only: eq; simp)
qed

lemma finite_rope_max_bound:
  assumes "finite S" "i\<in>S"
  shows "rope_logarithmic_error_bound m theta (d i)\<le>
      Max ((\<lambda>i. rope_logarithmic_error_bound m theta (d i)) ` S)"
  by (rule Max_ge; use assms in auto)

end
