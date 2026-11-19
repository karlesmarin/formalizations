(* Title: Exact integral remainder for finite-family relative entropy
   Author: Carles Marín (with Codex as formalization assistant)
   Copyright (c) 2026 Carles Marín. License: Apache-2.0 *)
theory TAF_KL_Remainder
  imports TAF_Mixture_Entropy
begin

context finite_exp_family
begin

lemma kl_integral_remainder:
  "finite_kl S (ep g) (ep h) = ereal ((h-g)^2 *
    integral {0..1} (\<lambda>t. (1-t)*evar (g+t*(h-g))))"
proof -
  let ?d = "h-g"
  let ?H = "\<lambda>t. ln (mom 0 (g+t*?d))-ln (mom 0 g)+t*?d*emean g"
  let ?H' = "\<lambda>t. ?d*(emean g-emean (g+t*?d))"
  let ?H'' = "\<lambda>t. ?d^2*evar (g+t*?d)"
  have path: "((\<lambda>t. g+t*?d) has_real_derivative ?d) (at t)" for t
    by (auto intro!: derivative_eq_intros)
  have lp: "((\<lambda>t. ln (mom 0 (g+t*?d))) has_real_derivative
    (-emean (g+t*?d)*?d)) (at t)" for t
    by (rule DERIV_chain2[OF log_partition_derivative path])
  have mp: "((\<lambda>t. emean (g+t*?d)) has_real_derivative
    (-evar (g+t*?d)*?d)) (at t)" for t
    by (rule DERIV_chain2[OF mean_derivative path])
  have first: "(?H has_real_derivative ?H' t) (at t)" for t
  proof -
    have rest: "((\<lambda>t. -ln (mom 0 g)+t*?d*emean g) has_real_derivative (?d*emean g)) (at t)"
      by (auto intro!: derivative_eq_intros simp: algebra_simps)
    show ?thesis using DERIV_add[OF lp[of t] rest]
      by (simp add: algebra_simps)
  qed
  have second: "(?H' has_real_derivative ?H'' t) (at t)" for t
  proof -
    have minus: "((\<lambda>t. -emean (g+t*?d)) has_real_derivative
      (-(-evar (g+t*?d)*?d))) (at t)" by (rule DERIV_minus[OF mp])
    have sum: "((\<lambda>t. emean g-emean (g+t*?d)) has_real_derivative
      (evar (g+t*?d)*?d)) (at t)"
      using DERIV_add[OF DERIV_const minus] by simp
    show ?thesis using DERIV_cmult[OF sum, where c="?d"]
      by (simp add: algebra_simps power2_eq_square)
  qed
  let ?Df = "\<lambda>(n::nat). if n=0 then ?H else if n=1 then ?H' else ?H''"
  have derivs: "(?Df m has_vector_derivative ?Df (Suc m) t) (at t within {0..1})"
    if "m<(2::nat)" "0\<le>t" "t\<le>1" for m t
  proof -
    have "m=0 \<or> m=1" using that by auto
    then show ?thesis
      using first[of t] second[of t]
      by (auto simp: has_real_derivative_iff_has_vector_derivative
          intro: has_vector_derivative_at_within)
  qed
  have tay: "?H 1 = (\<Sum>i<(2::nat). ((1-0)^i/fact i) *\<^sub>R ?Df i 0) +
      integral {0..1} (\<lambda>x. ((1-x)^((2::nat)-1)/fact ((2::nat)-1)) *\<^sub>R ?Df 2 x)"
    by (rule Taylor_integral[where p=2 and Df="?Df" and f="?H" and a=0 and b=1,
        OF _ _ derivs]; simp)
  have eq: "?H 1 = integral {0..1} (\<lambda>t. ?d^2*((1-t)*evar (g+t*?d)))"
    using tay by (simp add: lessThan_Suc numeral_2_eq_2 algebra_simps)
  have "?H 1 = ?d^2*integral {0..1} (\<lambda>t. (1-t)*evar (g+t*?d))"
    using eq by (simp add: integral_mult_left)
  then show ?thesis using kl_partition_identity[of g h] by simp
qed

end
end
