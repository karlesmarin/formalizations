(* Title: Strict instrumental bias of the causal diagonal average
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_All_Null
  imports TAF_Uniform_Null TAF_Affine_Bounds
begin

definition diagonal_null :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "diagonal_null T d=(\<Sum>i\<in>{d..<T}. 1/(real i+1))/real (T-d)"

lemma diagonal_null_positive:
  assumes d: "d<T"
  shows "0<diagonal_null T d"
proof -
  have terms: "0<1/(real i+1)" for i::nat by simp
  have sum: "0<(\<Sum>i\<in>{d..<T}. 1/(real i+1))"
    by (rule sum_pos; use d terms in auto)
  show ?thesis unfolding diagonal_null_def
    by (rule divide_pos_pos[OF sum]; use d in simp)
qed

lemma diagonal_null_strict_step:
  assumes d: "Suc d<T"
  shows "diagonal_null T (Suc d)<diagonal_null T d"
proof -
  let ?R="{Suc d..<T}"
  let ?s="\<Sum>i\<in>?R. 1/(real i+1)"
  let ?m="real (T-Suc d)"
  let ?h="1/(real d+1)"
  have mp: "0<?m" using d by simp
  have lower: "1/(real i+1)<?h" if "i\<in>?R" for i
    using that by (simp add: pos_divide_less_eq pos_less_divide_eq; linarith)
  have strict: "?s<(\<Sum>i\<in>?R. ?h)"
    by (rule sum_strict_mono; use d lower in auto)
  have sm: "?s<?m*?h" using strict by simp
  have set_eq: "{d..<T}=insert d ?R" using d by auto
  have sum_eq: "(\<Sum>i\<in>{d..<T}. 1/(real i+1))=?h+?s"
    by (simp add: set_eq)
  have count_eq: "T-d=Suc (T-Suc d)" using d by arith
  have denominator: "real (T-d)=?m+1" by (simp only: count_eq of_nat_Suc)
  have frac: "?s/?m<(?h+?s)/(?m+1)"
    using sm mp by (simp add: pos_divide_less_eq pos_less_divide_eq algebra_simps)
  show ?thesis unfolding diagonal_null_def using frac by (simp only: sum_eq denominator)
qed

lemma diagonal_null_strict_decrease:
  assumes de: "d<e" and e: "e<T"
  shows "diagonal_null T e<diagonal_null T d"
  using de e
proof (induction e)
  case 0 then show ?case by simp
next
  case (Suc e)
  have step: "diagonal_null T (Suc e)<diagonal_null T e"
    by (rule diagonal_null_strict_step[OF Suc.prems(2)])
  show ?case
  proof (cases "d=e")
    case True then show ?thesis using step by simp
  next
    case False
    have de: "d<e" using False Suc.prems(1) by arith
    have eT: "e<T" using Suc.prems(2) by arith
    have "diagonal_null T e<diagonal_null T d" by (rule Suc.IH[OF de eT])
    then show ?thesis using step by linarith
  qed
qed

context finite_probability
begin

lemma diagonal_null_positive_slope:
  assumes var: "0<fw_var S p (\<lambda>i. ln (real (d i)))"
    and range: "\<And>i. i\<in>S \<Longrightarrow> 0<d i" "\<And>i. i\<in>S \<Longrightarrow> d i<T"
  shows "0<log_slope S p (\<lambda>i. ln (real (d i))) (\<lambda>i. diagonal_null T (d i))"
proof -
  let ?x="\<lambda>i. ln (real (d i))"
  let ?y="\<lambda>i. -ln (diagonal_null T (d i))"
  have order: "?y i<?y j" if ij: "i\<in>S" "j\<in>S" "?x i<?x j" for i j
  proof -
    have rp: "0<real (d i)" "0<real (d j)" using range(1)[OF ij(1)] range(1)[OF ij(2)] by auto
    have dj: "d i<d j" using ij(3) rp by simp
    have decay: "diagonal_null T (d j)<diagonal_null T (d i)"
      by (rule diagonal_null_strict_decrease[OF dj range(2)[OF ij(2)]])
    have pos: "0<diagonal_null T (d i)" "0<diagonal_null T (d j)"
      using diagonal_null_positive range(2)[OF ij(1)] range(2)[OF ij(2)] by auto
    have "ln (diagonal_null T (d j))<ln (diagonal_null T (d i))" using decay pos by simp
    then show ?thesis by linarith
  qed
  have cv: "0<fw_cov S p ?x ?y" by (rule ordered_covariance_positive[OF var order])
  have eq: "fw_cov S p ?x ?y= -fw_cov S p ?x (\<lambda>i. ln (diagonal_null T (d i)))"
    using covariance_scale_y[where x="?x" and y="\<lambda>i. ln (diagonal_null T (d i))" and c="-1"] by simp
  have neg: "0< -fw_cov S p ?x (\<lambda>i. ln (diagonal_null T (d i)))"
    using cv eq by linarith
  have quotient: "0<(-fw_cov S p ?x (\<lambda>i. ln (diagonal_null T (d i))))/fw_var S p ?x"
    by (rule divide_pos_pos[OF neg var])
  show ?thesis using quotient by (simp only: slope_covariance)
qed

end
end
