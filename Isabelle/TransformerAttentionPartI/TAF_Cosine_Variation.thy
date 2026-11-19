(* Title: Quadrature error controlled by a primitive of absolute sine
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Cosine_Variation
  imports TAF_RoPE_Grid
begin

lemma variation_riemann_error:
  fixes f V :: "real \<Rightarrow> real"
  assumes m: "0<m"
    and cont: "continuous_on UNIV f"
    and cap: "\<And>a b t. a\<le>b \<Longrightarrow> t\<in>{a..b} \<Longrightarrow> abs (f a-f t)\<le>V a-V b"
  shows "abs ((\<Sum>i<m. f (real i/real m))-real m*integral {0..1} (\<lambda>t. f t))
    \<le>V 0-V 1"
proof -
  let ?f = "f"
  let ?h = "1/real m"
  let ?e = "\<lambda>i. ?f (real i/real m)-real m*integral {real i/real m..real (Suc i)/real m} ?f"
  have mp: "0<real m" using m by simp
  have hp: "0\<le>?h" using mp by simp
  have mn: "real m\<noteq>0" using mp by simp
  have cell: "abs (?e i)\<le>V (real i/real m)-V (real (Suc i)/real m)" for i
  proof -
    let ?a = "real i/real m"
    let ?b = "real (Suc i)/real m"
    have ab: "?a\<le>?b" using mp by (simp add: divide_right_mono)
    have ci: "continuous_on {?a..?b} ?f" by (rule continuous_on_subset[OF cont]) auto
    have ii: "?f integrable_on {?a..?b}" by (rule integrable_continuous_real[OF ci])
    have ce: "abs ((?b-?a)*?f ?a-integral {?a..?b} ?f)\<le>(?b-?a)*(V ?a-V ?b)"
      by (rule cell_integral_error[OF ab ii]; rule cap[OF ab]; assumption)
    have width: "?b-?a=1/real m" using mn by (simp add: diff_divide_distrib[symmetric])
    have scaled: "real m*abs ((?b-?a)*?f ?a-integral {?a..?b} ?f)\<le>
      real m*((?b-?a)*(V ?a-V ?b))"
      by (intro mult_left_mono[OF ce]; use mp in linarith)
    have scalar: "real m*((?b-?a)*?f ?a-integral {?a..?b} ?f)=?e i"
      using mn by (simp add: width field_simps algebra_simps)
    have left: "real m*abs ((?b-?a)*?f ?a-integral {?a..?b} ?f)=abs (?e i)"
      using arg_cong[OF scalar, of abs]
      by (simp only: abs_mult abs_of_pos[OF mp])
    have right: "real m*((?b-?a)*(V ?a-V ?b))=V ?a-V ?b"
      using mn by (simp only: width; simp add: field_simps algebra_simps)
    show ?thesis using scaled left right by argo
  qed
  have parts: "(\<Sum>i<m. integral {real i/real m..real (Suc i)/real m} ?f)=integral {0..1} ?f"
    using uniform_integral_partition[OF hp cont, where n=m] mn by simp
  have total: "sum ?e {..<m}=(\<Sum>i<m. ?f (real i/real m))-real m*integral {0..1} ?f"
    by (simp only: sum_subtractf sum_distrib_left[symmetric] parts)
  have norm: "abs (sum ?e {..<m})\<le>(\<Sum>i<m. abs (?e i))"
    using norm_sum[of ?e "{..<m}"] by simp
  have bound: "(\<Sum>i<m. abs (?e i))\<le>(\<Sum>i<m. V (real i/real m)-V (real (Suc i)/real m))"
    by (intro sum_mono cell)
  have telescope: "(\<Sum>i<m. V (real i/real m)-V (real (Suc i)/real m))=V 0-V 1"
    using phase_telescope[where P=V and h="?h" and n=m] mn by simp
  show ?thesis using norm bound total telescope by argo
qed

end
