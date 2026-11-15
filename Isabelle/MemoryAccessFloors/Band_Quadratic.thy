(*  Title:      Band_Quadratic.thy
    Author:     Carles Marin
    Copyright:  Carles Marin
    License:    BSD-3-Clause

    The band with correlated offsets is an interval between two certified values (paper B, Remark rem:corr):
    for g(s) = Qx + b s + Qy s^2 with b >= 0 and 0 <= sa <= s <= 1, if g(sa) >= 0 and g(1) >= 0 then g(s) >= 0.
    Case Qy >= 0: g(s) - g(sa) = (s - sa) (b + Qy (s + sa)).  Case Qy < 0: g is concave and
    (1 - sa) g(s) - (1 - s) g(sa) - (s - sa) g(1) = - Qy (1 - sa) (1 - s) (s - sa) >= 0.
*)

theory Band_Quadratic
  imports "HOL-Analysis.Analysis"
begin

lemma chord_identity:
  fixes Qx b Qy sa s :: real
  shows "(1 - sa) * (Qx + b * s + Qy * s^2) - (1 - s) * (Qx + b * sa + Qy * sa^2)
           - (s - sa) * (Qx + b + Qy) = - Qy * ((1 - sa) * (1 - s) * (s - sa))"
  by (simp add: algebra_simps power2_eq_square)

lemma convex_case:
  fixes Qx b Qy sa s :: real
  assumes "0 \<le> sa" "sa \<le> s" "0 \<le> b" "0 \<le> Qy" "0 \<le> Qx + b * sa + Qy * sa^2"
  shows "0 \<le> Qx + b * s + Qy * s^2"
proof -
  have "(Qx + b * s + Qy * s^2) - (Qx + b * sa + Qy * sa^2) = (s - sa) * (b + Qy * (s + sa))"
    by (simp add: algebra_simps power2_eq_square)
  moreover have "0 \<le> (s - sa) * (b + Qy * (s + sa))"
    by (rule mult_nonneg_nonneg) (use assms in \<open>auto intro!: add_nonneg_nonneg mult_nonneg_nonneg\<close>)
  ultimately show ?thesis using assms(5) by linarith
qed

lemma concave_case:
  fixes Qx b Qy sa s :: real
  assumes "0 \<le> sa" "sa \<le> s" "s \<le> 1" "Qy < 0" "0 \<le> Qx + b * sa + Qy * sa^2" "0 \<le> Qx + b + Qy"
  shows "0 \<le> Qx + b * s + Qy * s^2"
proof (cases "sa = 1")
  case True
  then have "s = 1" using assms(2,3) by simp
  then show ?thesis using True assms(6) by simp
next
  case False
  then have sa1: "0 < 1 - sa" using assms(1,2,3) by linarith
  have t: "0 \<le> (1 - sa) * (1 - s) * (s - sa)"
    using assms(2,3) sa1 by (intro mult_nonneg_nonneg) auto
  have e: "0 \<le> - Qy * ((1 - sa) * (1 - s) * (s - sa))"
    by (rule mult_nonneg_nonneg) (use assms(4) t in auto)
  have a1: "0 \<le> (1 - s) * (Qx + b * sa + Qy * sa^2)" using assms(3,5) by (intro mult_nonneg_nonneg) auto
  have a2: "0 \<le> (s - sa) * (Qx + b + Qy)" using assms(2,6) by (intro mult_nonneg_nonneg) auto
  have "0 \<le> (1 - sa) * (Qx + b * s + Qy * s^2)"
    using chord_identity[where Qx = Qx and b = b and Qy = Qy and sa = sa and s = s] e a1 a2 by linarith
  with sa1 show ?thesis by (simp add: zero_le_mult_iff)
qed

theorem band_between:
  fixes Qx b Qy sa s :: real
  assumes "0 \<le> sa" "sa \<le> s" "s \<le> 1" "0 \<le> b" "0 \<le> Qx + b * sa + Qy * sa^2" "0 \<le> Qx + b + Qy"
  shows "0 \<le> Qx + b * s + Qy * s^2"
proof (cases "0 \<le> Qy")
  case True
  then show ?thesis using convex_case assms by blast
next
  case False
  then show ?thesis using concave_case assms by auto
qed

end
