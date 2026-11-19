(* Title: Strict sign of a nondegenerate weighted covariance
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Strict_Covariance
  imports TAF_Secants
begin

context finite_probability
begin

lemma nondegenerate_positive_pair:
  assumes "0<fw_var S p x"
  shows "\<exists>i\<in>S. \<exists>j\<in>S. 0<p i*p j \<and> x i\<noteq>x j"
proof -
  have total: "0<(\<Sum>i\<in>S. \<Sum>j\<in>S. p i*p j*(x i-x j)^2)"
    using pair_variance[of x] assms by linarith
  obtain i where i: "i\<in>S" "0<(\<Sum>j\<in>S. p i*p j*(x i-x j)^2)"
    using positive_sum_has_positive_term[OF total] by blast
  obtain j where j: "j\<in>S" "0<p i*p j*(x i-x j)^2"
    using positive_sum_has_positive_term[OF i(2)] by blast
  have weight: "0<p i*p j"
  proof -
    have nn: "0\<le>p i*p j" using p_nonneg[OF i(1)] p_nonneg[OF j(1)]
      by (rule mult_nonneg_nonneg)
    have nz: "p i*p j\<noteq>0" using j(2) by auto
    show ?thesis using nn nz by (auto simp only: le_less)
  qed
  have diff: "x i\<noteq>x j" using j(2) by auto
  show ?thesis using i(1) j(1) weight diff by blast
qed

lemma strictly_comonotone_covariance:
  assumes var: "0<fw_var S p x"
    and order: "\<And>i j. i\<in>S \<Longrightarrow> j\<in>S \<Longrightarrow> x i\<noteq>x j \<Longrightarrow>
      0<(x i-x j)*(y i-y j)"
  shows "0<fw_cov S p x y"
proof -
  obtain i j where ij: "i\<in>S" "j\<in>S" "0<p i*p j" "x i\<noteq>x j"
    using nondegenerate_positive_pair[OF var] by blast
  have nn: "0\<le>p i*p j*(x i-x j)*(y i-y j)" if "i\<in>S" "j\<in>S" for i j
  proof (cases "x i=x j")
    case True then show ?thesis by simp
  next
    case False
    have w: "0\<le>p i*p j" using p_nonneg[OF that(1)] p_nonneg[OF that(2)]
      by (rule mult_nonneg_nonneg)
    show ?thesis using mult_nonneg_nonneg[OF w less_imp_le[OF order[OF that False]]]
      by (simp add: mult.assoc)
  qed
  have positive: "0<p i*p j*(x i-x j)*(y i-y j)"
    using mult_pos_pos[OF ij(3) order[OF ij(1,2,4)]] by (simp add: mult.assoc)
  have inn: "0<(\<Sum>k\<in>S. p i*p k*(x i-x k)*(y i-y k))"
    by (rule positive_sum; use nn ij positive in auto)
  have inner_nn: "0\<le>(\<Sum>k\<in>S. p l*p k*(x l-x k)*(y l-y k))" if "l\<in>S" for l
    by (intro sum_nonneg nn that)
  have tot: "0<(\<Sum>l\<in>S. \<Sum>k\<in>S. p l*p k*(x l-x k)*(y l-y k))"
    by (rule positive_sum; use inner_nn inn ij in auto)
  show ?thesis using tot covariance_pairwise[of x y] by linarith
qed

end
end
