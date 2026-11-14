(*  Title:      Slow_Noise_Second_Order.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    From "Exact limits for writing a quantum memory" (C. Marín, draft, November 2026): the algebra of the second-order error of
    every pulse under static offsets, the value of the square pulse, the floor pi^2 sigma^2/(96 G^2) for noise
    on the qubit, the comparison with the minimum-time robust pulse, and a bang-bang pulse that beats the
    square one at rho = 1/10.
*)

theory Slow_Noise_Second_Order
  imports "HOL-Analysis.Analysis" "HOL-Decision_Procs.Approximation"
begin

text \<open>Notation throughout: @{text "G > 0"}, @{text "A\<^sub>0 = \<pi>/(4G)"}, @{text "z\<^sub>0 = 1/(2G)"}.
  Everything is stated over the reals; the dynamics is not formalised, only the elementary
  algebra and the numerical inequalities used in the proof of the proposition.\<close>

section \<open>A. Second-order algebra\<close>

text \<open>With @{text "e = \<xi>\<^sub>q - \<xi>\<^sub>m"}, @{text "f = \<xi>\<^sub>q A + \<xi>\<^sub>m B"}, @{text "z = |\<zeta>|"} and
  @{text "w = Re (\<Xi>\<^sub>2)\<^sub>aa"}: unitarity to second order reads @{text "1 - 2w + f\<^sup>2 = 1 - e\<^sup>2 z\<^sup>2"}.\<close>

lemma second_order_algebra:
  fixes e f z w :: real
  assumes "0 \<le> z" and "1 - 2 * w + f\<^sup>2 = 1 - e\<^sup>2 * z\<^sup>2"
  shows "2 * w = e\<^sup>2 * z\<^sup>2 + f\<^sup>2"
  using assms(2) by linarith

lemma second_order_combination:
  fixes Ee2 Ef2 z P C p c :: real
  assumes "P = Ee2 * z\<^sup>2" and "C = Ee2 * z\<^sup>2 + Ef2" and "p = 1 - P" and "c = 1 - C / 2"
  shows "(3 - p - 2 * c) / 6 = (2 * (Ee2 * z\<^sup>2) + Ef2) / 6"
  using assms by (simp add: field_simps)

section \<open>B. The square pulse\<close>

lemma square_value:
  fixes sq2 sm2 G z0 A0 :: real
  assumes "G > 0" and "sq2 \<ge> 0" and "sm2 \<ge> 0" and "z0 = 1 / (2 * G)" and "A0 = pi / (4 * G)"
  shows "(2 * (sq2 + sm2) * z0\<^sup>2 + sq2 * A0\<^sup>2 + sm2 * A0\<^sup>2) / 6
         = (8 + pi\<^sup>2) * (sq2 + sm2) / (96 * G\<^sup>2)"
  using assms(1) unfolding assms(4,5) by (simp add: field_simps power2_eq_square)

section \<open>C. Qubit-only floor\<close>

lemma qubit_only_floor:
  fixes sigma2 z A G :: real
  assumes "G > 0" and "sigma2 \<ge> 0" and "A \<ge> pi / (4 * G)"
  shows "(2 * sigma2 * z\<^sup>2 + sigma2 * A\<^sup>2) / 6 \<ge> pi\<^sup>2 * sigma2 / (96 * G\<^sup>2)"
proof -
  have a0: "0 \<le> pi / (4 * G)" using assms(1) pi_gt_zero by simp
  have sq: "(pi / (4 * G))\<^sup>2 \<le> A\<^sup>2" using assms(3) a0 by (intro power_mono) auto
  have e: "pi\<^sup>2 * sigma2 / (96 * G\<^sup>2) = sigma2 * (pi / (4 * G))\<^sup>2 / 6"
    using assms(1) by (simp add: field_simps power2_eq_square)
  have h1: "sigma2 * (pi / (4 * G))\<^sup>2 \<le> sigma2 * A\<^sup>2" using sq assms(2) by (rule mult_left_mono)
  have h2: "0 \<le> 2 * sigma2 * z\<^sup>2" using assms(2) by simp
  show ?thesis unfolding e
    by (intro divide_right_mono) (use h1 h2 in \<open>auto simp: algebra_simps\<close>)
qed

section \<open>D. Minimum-time robust pulse\<close>

lemma min_time_robust_value:
  fixes sigma2 G A :: real
  assumes "G > 0" and "A = (pi - 1) / (2 * G)"
  shows "(2 * sigma2 * 0\<^sup>2 + sigma2 * A\<^sup>2) / 6 = (pi - 1)\<^sup>2 * sigma2 / (24 * G\<^sup>2)"
  using assms(1) unfolding assms(2) by (simp add: field_simps power2_eq_square)

lemma robust_worse_than_square: "(pi - 1)\<^sup>2 / 24 > (8 + pi\<^sup>2) / 96"
  by (approximation 20)

section \<open>E. The square pulse against the floor\<close>

lemma square_vs_floor: "(8 + pi\<^sup>2) / pi\<^sup>2 > 1.81" and "(8 + pi\<^sup>2) / pi\<^sup>2 < 1.82"
  by (approximation 20)+

section \<open>F. Excess of the zero-leakage pulses\<close>

text \<open>With @{text "u > 2"} and @{text "r = \<surd>(u\<^sup>2 - 4)"} the excess @{text "A - A\<^sub>0"} (units @{text "R = 1"})
  is @{text "arctan (2/r) + (r - u)/2"}. We prove @{text "0 \<le> \<dots> \<le> 2/(u + r) \<le> 2/u"}, hence also @{text "\<le> 2/r"};
  the excess tends to @{text 0}. (The expression is taken as given, not derived from the dynamics.)\<close>

lemma csc_A_excess:
  fixes u r :: real
  assumes "u > 2" and "r = sqrt (u\<^sup>2 - 4)"
  shows "0 \<le> arctan (2 / r) + (r - u) / 2"
    and "arctan (2 / r) + (r - u) / 2 \<le> 2 / (u + r)"
    and "2 / (u + r) \<le> 2 / u"
    and "arctan (2 / r) + (r - u) / 2 \<le> 2 / u"
proof -
  have u0: "0 < u" using assms(1) by simp
  have u4: "4 < u\<^sup>2" using assms(1) power_strict_mono[of 2 u 2] by simp
  have r2: "r\<^sup>2 = u\<^sup>2 - 4" using assms(2) u4 by simp
  have r0: "0 < r" using assms(2) u4 by simp
  have ur: "0 < u + r" using u0 r0 by simp
  define s where "s = 2 / (u + r)"
  have s0: "0 < s" using ur by (simp add: s_def)
  have us: "u - r = 4 / (u + r)"
  proof -
    have "(u - r) * (u + r) = u\<^sup>2 - r\<^sup>2" by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> = 4" using r2 by simp
    finally show ?thesis using ur by (simp add: field_simps)
  qed
  have rus: "(r - u) / 2 = - s" using us by (simp add: s_def)
  have s1: "s < 1"
  proof -
    have "2 < u + r" using assms(1) r0 by linarith
    thus ?thesis by (simp add: s_def divide_less_eq)
  qed
  have ss: "s * s < 1"
  proof -
    have "s * s < s * 1" using mult_strict_left_mono[OF s1 s0] by simp
    thus ?thesis using s1 by linarith
  qed
  have ne1: "u + r \<noteq> 0" using ur by simp
  have ne2: "r \<noteq> 0" using r0 by simp
  have q4: "(u + r) * (u + r) - 4 = 2 * r * (u + r)"
    using r2 by (simp add: power2_eq_square algebra_simps)
  have e1: "1 - s * s = 2 * r / (u + r)"
  proof -
    have ss4: "s * s = 4 / ((u + r) * (u + r))" by (simp add: s_def)
    have "1 - s * s = ((u + r) * (u + r) - 4) / ((u + r) * (u + r))"
      using ne1 unfolding ss4 by (simp add: diff_divide_distrib)
    also have "\<dots> = 2 * r * (u + r) / ((u + r) * (u + r))" using q4 by simp
    also have "\<dots> = 2 * r / (u + r)" 
    proof -
      have ne3: "(u + r) * (u + r) \<noteq> 0" using ne1 by simp
      show ?thesis by (subst frac_eq_eq[OF ne3 ne1]) (simp add: algebra_simps)
    qed
    finally show ?thesis .
  qed
  have dbl: "2 * s / (1 - s * s) = 2 / r"
  proof -
    have ne4: "2 * r / (u + r) \<noteq> 0" using ne1 ne2 by simp
    show ?thesis unfolding e1
      by (subst frac_eq_eq[OF ne4 ne2]) (use ne1 in \<open>simp add: s_def field_simps\<close>)
  qed
  have atw: "arctan (2 / r) = 2 * arctan s"
  proof -
    have "arctan s + arctan s = arctan ((s + s) / (1 - s * s))"
      using s0 s1 by (intro arctan_add) auto
    also have "(s + s) / (1 - s * s) = 2 / r" using dbl by simp
    finally show ?thesis by simp
  qed
  have up: "arctan s \<le> s" using s0 arctan_le_self[of s] by simp
  have lo: "s / 2 \<le> arctan s"
  proof -
    define a where "a = arctan s"
    have a0: "0 < a" using arctan_monotone[OF s0] by (simp add: a_def)
    have a1: "a < pi / 4" using arctan_monotone[OF s1] by (simp add: a_def arctan_one)
    have ta: "tan a = s" unfolding a_def by (rule tan_arctan)
    have c4: "1 / 2 \<le> cos (pi / 4)" by (approximation 20)
    have c: "1 / 2 \<le> cos a"
    proof -
      have "cos (pi / 4) \<le> cos a"
        using a0 a1 pi_gt_zero by (intro cos_monotone_0_pi_le) auto
      thus ?thesis using c4 by linarith
    qed
    have ca: "0 < cos a" using c by simp
    have sn: "sin a \<le> a" using sin_x_le_x[of a] a0 by simp
    have "s * cos a = sin a" using ta ca by (simp add: tan_def field_simps)
    hence "s * cos a \<le> a" using sn by simp
    moreover have "s * (1 / 2) \<le> s * cos a" using c s0 by (intro mult_left_mono) auto
    ultimately show ?thesis unfolding a_def[symmetric] by linarith
  qed
  show c1: "0 \<le> arctan (2 / r) + (r - u) / 2" using atw rus lo by linarith
  show c2: "arctan (2 / r) + (r - u) / 2 \<le> 2 / (u + r)" using atw rus up by (simp add: s_def[symmetric])
  show c3: "2 / (u + r) \<le> 2 / u" using u0 r0 by (intro divide_left_mono) auto
  show "arctan (2 / r) + (r - u) / 2 \<le> 2 / u" using c2 c3 by linarith
qed

section \<open>G. The bang--bang pulse beats the square pulse\<close>

text \<open>Units @{text "G = 1/2"}: @{text "A\<^sub>0 = \<pi>/2"}, @{text "z\<^sub>0 = 1"}.\<close>

definition F_cost :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "F_cost \<rho> z A B = 2 * (1 + \<rho>) * z\<^sup>2 + A\<^sup>2 + \<rho> * B\<^sup>2"

lemma bang_bang_beats_square:
  "F_cost (1 / 10) (cos (106 / 125)) (pi / 2 + 106 / 125 - sin (106 / 125))
          (pi / 2 + 106 / 125 + sin (106 / 125))
   < F_cost (1 / 10) 1 (pi / 2) (pi / 2)"
  unfolding F_cost_def by (approximation 30)

end
