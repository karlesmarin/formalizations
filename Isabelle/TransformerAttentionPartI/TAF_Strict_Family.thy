(* Title: Strict entropy maximum and impossibility of an exact mixed power
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_Strict_Family
  imports TAF_Sensitivity
begin

context finite_exp_family
begin

lemma entropy_unique_maximum:
  assumes i: "i\<in>S" and j: "j\<in>S" and diff: "E i\<noteq>E j" and g: "g\<noteq>0"
  shows "canonical_entropy g<canonical_entropy 0"
proof (cases "0<g")
  case True
  obtain z where z: "0<z" "z<g" "canonical_entropy g-canonical_entropy 0=(g-0)*(-z*evar z)"
    using MVT2[OF True, where f=canonical_entropy and f'="\<lambda>t. -t*evar t"] entropy_derivative by blast
  have vp: "0<evar z" by (rule strict_variance[OF i j diff])
  have neg: "-z*evar z<0" using z(1) vp by (intro mult_neg_pos; linarith)
  have pn: "g*(-z*evar z)<0" by (rule mult_pos_neg[OF True neg])
  have delta: "canonical_entropy g-canonical_entropy 0<0"
    by (simp only: z(3) diff_zero; rule pn)
  show ?thesis using delta by linarith
next
  case False
  have gn: "g<0" using False g by auto
  obtain z where z: "g<z" "z<0" "canonical_entropy 0-canonical_entropy g=(0-g)*(-z*evar z)"
    using MVT2[OF gn, where f=canonical_entropy and f'="\<lambda>t. -t*evar t"] entropy_derivative by blast
  have vp: "0<evar z" by (rule strict_variance[OF i j diff])
  have zp: "0 < -z" using z(2) by linarith
  have gp: "0<0-g" using gn by linarith
  have pp: "0<(0-g)*(-z*evar z)" by (intro mult_pos_pos gp zp vp)
  have delta: "0<canonical_entropy 0-canonical_entropy g"
    by (simp only: z(3); rule pp)
  show ?thesis using delta by linarith
qed

lemma non_affine_log_partition:
  assumes i: "i\<in>S" and j: "j\<in>S" and diff: "E i\<noteq>E j" and ab: "l<u"
  shows "\<not> (\<forall>x\<in>{l<..<u}. ln (mom 0 x)=c-k*x)"
proof
  assume lin: "\<forall>x\<in>{l<..<u}. ln (mom 0 x)=c-k*x"
  have same_mean: "emean x=k" if x: "x\<in>{l<..<u}" for x
  proof -
    have dc: "((\<lambda>x. c-k*x) has_real_derivative (-k)) (at x)"
      by (auto intro!: derivative_eq_intros)
    have dl: "((\<lambda>x. ln (mom 0 x)) has_real_derivative (-k)) (at x)"
      by (rule has_field_derivative_transform_within_open[where f="\<lambda>x. c-k*x" and S="{l<..<u}",
          OF dc _ x]; use lin in auto)
    have "-k=-emean x" by (rule DERIV_unique[OF dl log_partition_derivative])
    then show ?thesis by simp
  qed
  let ?u = "(2*l+u)/3"
  let ?v = "(l+2*u)/3"
  have u: "?u\<in>{l<..<u}" using ab by (auto; linarith)
  have v: "?v\<in>{l<..<u}" using ab by (auto; linarith)
  have numerators: "2*l+u<l+2*u" using ab by linarith
  have uv: "?u<?v" by (rule divide_strict_right_mono[OF numerators]) simp
  have dec: "emean ?v<emean ?u" by (rule strict_mean_decrease[OF i j diff uv])
  show False using dec same_mean[OF u] same_mean[OF v] by simp
qed

end
end
