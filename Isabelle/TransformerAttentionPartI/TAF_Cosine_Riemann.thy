(* Title: Explicit finite Riemann error for a monotone cosine phase
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Cosine_Riemann
  imports TAF_Cosine_Foundation
begin

lemma uniform_integral_partition:
  fixes f :: "real \<Rightarrow> real"
  assumes h: "0\<le>h" and cont: "continuous_on UNIV f"
  shows "(\<Sum>i<n. integral {real i*h..real (Suc i)*h} f)=integral {0..real n*h} f"
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc n)
  have a0: "0\<le>real n*h" using h by (intro mult_nonneg_nonneg) auto
  have an: "real n*h\<le>real (Suc n)*h" using h by (simp add: algebra_simps)
  have ci: "continuous_on {0..real (Suc n)*h} f"
    by (rule continuous_on_subset[OF cont]) auto
  have ii: "f integrable_on {0..real (Suc n)*h}" by (rule integrable_continuous_real[OF ci])
  have combine: "integral {0..real n*h} f+integral {real n*h..real (Suc n)*h} f =
    integral {0..real (Suc n)*h} f"
    by (rule Henstock_Kurzweil_Integration.integral_combine[OF a0 an ii])
  show ?case using Suc.IH combine by simp
qed

lemma phase_telescope:
  fixes P :: "real \<Rightarrow> real" and h :: real
  shows "(\<Sum>i<n. P (real i*h)-P (real (Suc i)*h))=P 0-P (real n*h)"
  by (induction n) auto

lemma monotone_cosine_cell:
  fixes P :: "real \<Rightarrow> real"
  assumes mono: "antimono P" and ab: "a\<le>b"
    and int: "(\<lambda>t. cos (P t)) integrable_on {a..b}"
  shows "abs ((b-a)*cos (P a)-integral {a..b} (\<lambda>t. cos (P t)))\<le>(b-a)*(P a-P b)"
proof (rule cell_integral_error[OF ab int])
  fix t assume t: "t\<in>{a..b}"
  have pa: "P t\<le>P a" and pb: "P b\<le>P t" using mono t by (auto simp: antimono_def)
  have "abs (cos (P a)-cos (P t))\<le>abs (P a-P t)" by (rule cosine_lipschitz)
  also have "...\<le>P a-P b" using pa pb by simp
  finally show "abs (cos (P a)-cos (P t))\<le>P a-P b" .
qed

lemma monotone_cosine_riemann_error:
  fixes P :: "real \<Rightarrow> real"
  assumes m: "0<m" and mono: "antimono P"
    and cont: "continuous_on UNIV (\<lambda>t. cos (P t))"
  shows "abs ((\<Sum>i<m. cos (P (real i/real m)))-real m*integral {0..1} (\<lambda>t. cos (P t)))
    \<le>P 0-P 1"
proof -
  let ?f = "\<lambda>t. cos (P t)"
  let ?h = "1/real m"
  let ?e = "\<lambda>i. ?f (real i/real m)-real m*integral {real i/real m..real (Suc i)/real m} ?f"
  have mp: "0<real m" using m by simp
  have hp: "0\<le>?h" using mp by simp
  have mn: "real m\<noteq>0" using mp by simp
  have cell: "abs (?e i)\<le>P (real i/real m)-P (real (Suc i)/real m)" for i
  proof -
    let ?a = "real i/real m"
    let ?b = "real (Suc i)/real m"
    have ab: "?a\<le>?b" using mp by (simp add: divide_right_mono)
    have ci: "continuous_on {?a..?b} ?f" by (rule continuous_on_subset[OF cont]) auto
    have ii: "?f integrable_on {?a..?b}" by (rule integrable_continuous_real[OF ci])
    have ce: "abs ((?b-?a)*?f ?a-integral {?a..?b} ?f)\<le>(?b-?a)*(P ?a-P ?b)"
      by (rule monotone_cosine_cell[OF mono ab ii])
    have width: "?b-?a=1/real m" using mn by (simp add: diff_divide_distrib[symmetric])
    have scaled: "real m*abs ((?b-?a)*?f ?a-integral {?a..?b} ?f)\<le>
      real m*((?b-?a)*(P ?a-P ?b))"
      by (intro mult_left_mono[OF ce]; use mp in linarith)
    have scalar: "real m*((?b-?a)*?f ?a-integral {?a..?b} ?f)=?e i"
      using mn by (simp add: width field_simps algebra_simps)
    have left: "real m*abs ((?b-?a)*?f ?a-integral {?a..?b} ?f)=abs (?e i)"
      using arg_cong[OF scalar, of abs]
      by (simp only: abs_mult abs_of_pos[OF mp])
    have right: "real m*((?b-?a)*(P ?a-P ?b))=P ?a-P ?b"
      using mn by (simp only: width; simp add: field_simps algebra_simps)
    show ?thesis using scaled left right by argo
  qed
  have parts: "(\<Sum>i<m. integral {real i/real m..real (Suc i)/real m} ?f)=integral {0..1} ?f"
    using uniform_integral_partition[OF hp cont, where n=m] mn by simp
  have total: "sum ?e {..<m}=(\<Sum>i<m. ?f (real i/real m))-real m*integral {0..1} ?f"
    by (simp only: sum_subtractf sum_distrib_left[symmetric] parts)
  have norm: "abs (sum ?e {..<m})\<le>(\<Sum>i<m. abs (?e i))"
    using norm_sum[of ?e "{..<m}"] by simp
  have bound: "(\<Sum>i<m. abs (?e i))\<le>(\<Sum>i<m. P (real i/real m)-P (real (Suc i)/real m))"
    by (intro sum_mono cell)
  have telescope: "(\<Sum>i<m. P (real i/real m)-P (real (Suc i)/real m))=P 0-P 1"
    using phase_telescope[where P=P and h="?h" and n=m] mn by simp
  show ?thesis using norm bound total telescope by argo
qed

end
