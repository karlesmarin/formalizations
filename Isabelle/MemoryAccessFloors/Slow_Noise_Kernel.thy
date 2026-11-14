(*  Title:      Slow_Noise_Kernel.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Three numerical inequalities about pi, sine and cosine used in the analysis of the second-order error of a
    quantum-memory write under slow noise: the minimum-time robust pulse is worse than the square pulse, the
    square pulse is between 1.81 and 1.82 times the floor, and a bang--bang pulse beats the square pulse at
    rho = 1/10. They are proved from rational bounds on pi (Complex_Transcendental.pi_approx) and the
    Maclaurin bound of the sine, with no use of numerical approximation oracles.
*)

theory Slow_Noise_Kernel
  imports "HOL-Analysis.Analysis"
begin

section \<open>Rational bounds on pi\<close>

lemma pi_lo: "157 / 50 < pi" using pi_approx(1) by simp

lemma pi_hi: "pi < 3927 / 1250" using pi_approx(2) by simp

section \<open>The minimum-time robust pulse against the square pulse\<close>

lemma robust_worse_than_square_kernel: "(pi - 1)\<^sup>2 / 24 > (8 + pi\<^sup>2) / 96"
proof -
  have p0: "0 < pi" by simp
  have m: "157 / 50 * pi < pi\<^sup>2" unfolding power2_eq_square
    using pi_lo p0 by (intro mult_strict_right_mono) simp_all
  have key: "0 < 3 * pi\<^sup>2 - 8 * pi - 4" using m pi_lo by linarith
  have id: "(pi - 1)\<^sup>2 / 24 - (8 + pi\<^sup>2) / 96 = (3 * pi\<^sup>2 - 8 * pi - 4) / 96"
    by (simp add: power2_eq_square field_simps)
  have "0 < (pi - 1)\<^sup>2 / 24 - (8 + pi\<^sup>2) / 96" by (subst id) (use key in simp)
  thus ?thesis by simp
qed

section \<open>The square pulse against the floor\<close>

lemma square_vs_floor_kernel: "(8 + pi\<^sup>2) / pi\<^sup>2 > 1.81" and "(8 + pi\<^sup>2) / pi\<^sup>2 < 1.82"
proof -
  have p0: "0 < pi" by simp
  have pp: "0 < pi\<^sup>2" using p0 by simp
  have m1: "157 / 50 * pi < pi\<^sup>2" unfolding power2_eq_square
    using pi_lo p0 by (intro mult_strict_right_mono) simp_all
  have m2: "pi\<^sup>2 < 3927 / 1250 * pi" unfolding power2_eq_square
    using pi_hi p0 by (intro mult_strict_right_mono) simp_all
  have lo: "49 / 5 < pi\<^sup>2" using m1 pi_lo by linarith
  have hi: "pi\<^sup>2 < 987 / 100" using m2 pi_hi by linarith
  have e1: "(1.81 :: real) = 181 / 100" by simp
  have e2: "(1.82 :: real) = 91 / 50" by simp
  show "(8 + pi\<^sup>2) / pi\<^sup>2 > 1.81" unfolding e1
    by (subst pos_less_divide_eq[OF pp]) (use hi in linarith)
  show "(8 + pi\<^sup>2) / pi\<^sup>2 < 1.82" unfolding e2
    by (subst pos_divide_less_eq[OF pp]) (use lo in linarith)
qed

section \<open>The sine at 106/125 from its Maclaurin bound\<close>

lemma sin_d_lower: "749 / 1000 \<le> sin (106 / 125 :: real)"
proof -
  have b: "\<bar>sin (106 / 125 :: real) - (\<Sum>m<6. sin_coeff m * (106 / 125) ^ m)\<bar>
           \<le> inverse (fact 6) * \<bar>106 / 125 :: real\<bar> ^ 6"
    by (rule Maclaurin_sin_bound)
  have s: "(\<Sum>m<6. sin_coeff m * (106 / 125 :: real) ^ m)
           = 343332313222 / 457763671875"
    by (simp add: eval_nat_numeral lessThan_Suc sin_coeff_Suc cos_coeff_Suc)
  have e: "inverse (fact 6) * \<bar>106 / 125 :: real\<bar> ^ 6 < 6 / 10000"
    by (simp add: eval_nat_numeral fact_Suc)
  have b2: "\<bar>sin (106 / 125 :: real) - 343332313222 / 457763671875\<bar> \<le> 6 / 10000"
    using order_trans[OF b less_imp_le[OF e]] unfolding s .
  show ?thesis using b2 unfolding abs_le_iff by linarith
qed

section \<open>The bang--bang pulse beats the square pulse\<close>

lemma key_linear:
  fixes p w s t :: real
  assumes "p < 3927 / 1250" and "1209 / 500 * (749 / 1000) \<le> w / 2 + 106 / 125 * s"
    and "561001 / 1000000 \<le> t"
  shows "11 / 10 * (106 / 125 * p + 11236 / 15625) < 9 / 5 * (w / 2 + 106 / 125 * s) + 11 / 10 * t"
  using assms by argo

definition F_cost_k :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "F_cost_k \<rho> z A B = 2 * (1 + \<rho>) * z\<^sup>2 + A\<^sup>2 + \<rho> * B\<^sup>2"

lemma bang_bang_beats_square_kernel:
  "F_cost_k (1 / 10) (cos (106 / 125)) (pi / 2 + 106 / 125 - sin (106 / 125))
            (pi / 2 + 106 / 125 + sin (106 / 125))
   < F_cost_k (1 / 10) 1 (pi / 2) (pi / 2)"
proof -
  define s where "s = sin (106 / 125 :: real)"
  have hs: "749 / 1000 \<le> s" unfolding s_def using sin_d_lower .
  have c2: "(cos (106 / 125 :: real))\<^sup>2 = 1 - s\<^sup>2"
    unfolding s_def using sin_cos_squared_add[of "106 / 125 :: real"] by linarith
  have hm: "1209 / 500 \<le> pi / 2 + 106 / 125" using pi_lo by linarith
  have hms0: "1209 / 500 * (749 / 1000) \<le> (pi / 2 + 106 / 125) * s"
    by (rule mult_mono[OF hm hs]) (use pi_lo in \<open>(linarith)+\<close>)
  have hms: "1209 / 500 * (749 / 1000) \<le> pi * s / 2 + 106 / 125 * s"
    by (rule order_trans[OF hms0]) (simp add: algebra_simps)
  have hs2: "561001 / 1000000 \<le> s\<^sup>2"
  proof -
    have "(749 / 1000) ^ 2 \<le> s\<^sup>2" using hs by (intro power_mono) simp_all
    moreover have "(749 / 1000 :: real) ^ 2 = 561001 / 1000000" by (simp add: power2_eq_square)
    ultimately show ?thesis by simp
  qed
  have key: "11 / 10 * (106 / 125 * pi + 11236 / 15625)
             < 9 / 5 * (pi * s / 2 + 106 / 125 * s) + 11 / 10 * s\<^sup>2"
    by (rule key_linear[OF pi_hi _ hs2]) (use hms in simp)
  have hF: "(2 * (1 + 1 / 10) * 1\<^sup>2 + (pi / 2)\<^sup>2 + 1 / 10 * (pi / 2)\<^sup>2)
            - (2 * (1 + 1 / 10) * (1 - s\<^sup>2) + (pi / 2 + 106 / 125 - s)\<^sup>2
               + 1 / 10 * (pi / 2 + 106 / 125 + s)\<^sup>2)
            = 9 / 5 * (pi * s / 2 + 106 / 125 * s) + 11 / 10 * s\<^sup>2
              - 11 / 10 * (106 / 125 * pi + 11236 / 15625)"
    by (simp add: power2_eq_square field_simps)
  show ?thesis
    unfolding F_cost_k_def c2 s_def[symmetric] using key hF by linarith
qed

end
