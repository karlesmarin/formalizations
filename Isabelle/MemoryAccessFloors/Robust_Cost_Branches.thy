(*  Title:      Robust_Cost_Branches.thy
    Author:     Carles Marin
    Copyright:  Carles Marin
    License:    BSD-3-Clause

    Two short steps of the memory-floor notes.
    (1) The cost of cancelling the leakage (corollary on the robust cost of the robust-offset paper): with the
        excess exposures x = A - A0 and y = B - A0, the disk x y >= 1/(4 G^2) gives the branch sqrt(gq gm)/G
        (Memory_Robust.robust_cost_amgm) and the duration x + y >= pi/(2 G) gives the branch (pi/2) min(gq, gm)/G;
        together, gq x + gm y >= max of the two.  The disk and the duration bound are hypotheses here (they are
        Theorem 1 of that paper, formalised in Robust_Disk and Robust_Core).
    (2) The envelopes at a fixed duration (corollary of the fixed-duration theorem of the memory-floors paper):
        if shifting the relaxation rates by mu multiplies every population by exp (mu t), the bound of the shifted
        system, exp (mu T) p(T) <= max_{s <= T} exp (mu s) p_res(s), is the envelope
        p(T) <= exp (-mu T) max_{s <= T} exp (mu s) p_res(s).  The shifted bound is a hypothesis (the fixed-duration
        theorem; its algebraic core is in Fixed_Duration_Core).
*)

theory Robust_Cost_Branches
  imports Memory_Robust
begin

theorem robust_cost_min_branch:
  fixes G gq gm x y :: real
  assumes "0 < G" "0 \<le> gq" "0 \<le> gm" "0 \<le> x" "0 \<le> y" "pi / (2 * G) \<le> x + y"
  shows "pi / 2 * min gq gm / G \<le> gq * x + gm * y"
proof -
  have m0: "0 \<le> min gq gm" using assms(2,3) by simp
  have "min gq gm * x \<le> gq * x" by (rule mult_right_mono) (use assms(4) in auto)
  moreover have "min gq gm * y \<le> gm * y" by (rule mult_right_mono) (use assms(5) in auto)
  ultimately have a: "min gq gm * (x + y) \<le> gq * x + gm * y" by (simp add: distrib_left)
  have "min gq gm * (pi / (2 * G)) \<le> min gq gm * (x + y)"
    by (rule mult_left_mono[OF assms(6) m0])
  moreover have "pi / 2 * min gq gm / G = min gq gm * (pi / (2 * G))"
    using assms(1) by (simp add: field_simps)
  ultimately show ?thesis using a by linarith
qed

theorem robust_cost_both_branches:
  fixes G gq gm x y :: real
  assumes "0 < G" "0 \<le> gq" "0 \<le> gm" "0 \<le> x" "0 \<le> y"
    and "1 / (4 * G\<^sup>2) \<le> x * y" and "pi / (2 * G) \<le> x + y"
  shows "max (sqrt (gq * gm)) (pi / 2 * min gq gm) / G \<le> gq * x + gm * y"
proof -
  have a: "sqrt (gq * gm) / G \<le> gq * x + gm * y"
    by (rule robust_cost_amgm[OF assms(1-6)])
  have b: "pi / 2 * min gq gm / G \<le> gq * x + gm * y"
    by (rule robust_cost_min_branch[OF assms(1-5) assms(7)])
  have "max (sqrt (gq * gm)) (pi / 2 * min gq gm) / G
        = max (sqrt (gq * gm) / G) (pi / 2 * min gq gm / G)"
    using assms(1) by (simp add: max_divide_distrib_right)
  then show ?thesis using a b by simp
qed

text \<open>Equal rates: the two branches agree with the value pi gamma / (2 G) attained by the bang-bang pulse.\<close>

theorem robust_cost_equal_rates:
  fixes G g :: real
  assumes "0 < G" "0 \<le> g"
  shows "max (sqrt (g * g)) (pi / 2 * min g g) / G = pi * g / (2 * G)"
proof -
  have s: "sqrt (g * g) = g" using assms(2) by simp
  have "1 * g \<le> pi / 2 * g" by (rule mult_right_mono) (use assms(2) pi_gt3 in auto)
  then have "max g (pi / 2 * g) = pi / 2 * g" by (simp add: max_absorb2)
  then have "max (sqrt (g * g)) (pi / 2 * min g g) = pi / 2 * g" using s by simp
  then show ?thesis using assms(1) by (simp add: field_simps)
qed

theorem fixed_duration_envelope:
  fixes mu T M p :: real
  assumes "exp (mu * T) * p \<le> M"
  shows "p \<le> exp (- (mu * T)) * M"
proof -
  have e: "0 < exp (mu * T)" by simp
  have "p \<le> M / exp (mu * T)" using assms e by (simp add: pos_le_divide_eq mult.commute)
  moreover have "M / exp (mu * T) = exp (- (mu * T)) * M" by (simp add: exp_minus field_simps)
  ultimately show ?thesis by simp
qed

text \<open>The envelope is never below the plain resonant pulse at the same duration (take s = T).\<close>

theorem envelope_ge_resonant:
  fixes mu T :: real and pres :: "real \<Rightarrow> real"
  assumes "0 \<le> T" "\<forall>s \<in> {0..T}. exp (mu * s) * pres s \<le> Mx"
  shows "pres T \<le> exp (- (mu * T)) * Mx"
  using fixed_duration_envelope assms by auto

end
