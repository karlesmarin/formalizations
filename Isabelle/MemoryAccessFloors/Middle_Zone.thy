(*  Title:      Middle_Zone.thy
    Author:     Carles Marin
    Copyright:  Carles Marin
    License:    BSD-3-Clause

    Case 4 of the argument "the optimum over Lambda_c lies in the turn-wait-turn family" (paper B,
    Proposition prop:noiseloss (iii)).  With J(x, y) = Lam (2 z^2 + (A0 + x)^2) / 12 + (A0 + y) / 3 and
    Lam > 2 / A0, the minimum of J on {x >= x0, y >= x0, x + y >= 2 d} is at (x0, 2 d - x0).
    The proof is one identity,
        J(x, y) - J(x0, 2 d - x0) = (x - x0) (Lam (2 A0 + x + x0) - 4) / 12 + (x + y - 2 d) / 3,
    both terms being >= 0.  The hypotheses x0 <= d and x0 <= y of the statement are not used.
*)

theory Middle_Zone
  imports "HOL-Analysis.Analysis"
begin

lemma lam_key:
  fixes Lam A0 t :: real
  assumes "0 < A0" "2 / A0 < Lam" "0 \<le> t"
  shows "4 \<le> Lam * (2 * A0 + t)"
proof -
  have "2 < Lam * A0" using assms(1,2) by (simp add: divide_less_eq)
  moreover have "0 < Lam" using assms(1,2) by (meson divide_pos_pos less_trans zero_less_numeral)
  ultimately have "0 \<le> Lam * t" using assms(3) by simp
  then show ?thesis using \<open>2 < Lam * A0\<close> by (simp add: algebra_simps)
qed

lemma J_difference:
  fixes Lam A0 z x y x0 d :: real
  shows "(Lam * (2 * z^2 + (A0 + x)^2) / 12 + (A0 + y) / 3)
           - (Lam * (2 * z^2 + (A0 + x0)^2) / 12 + (A0 + (2 * d - x0)) / 3)
         = (x - x0) * (Lam * (2 * A0 + x + x0) - 4) / 12 + (x + y - 2 * d) / 3"
  by (simp add: field_simps power2_eq_square)

theorem middle_zone_min:
  fixes Lam A0 z x y x0 d :: real
  assumes "0 < A0" "2 / A0 < Lam" "0 \<le> x0" "x0 \<le> d" "x0 \<le> x" "x0 \<le> y" "2 * d \<le> x + y"
  shows "Lam * (2 * z^2 + (A0 + x0)^2) / 12 + (A0 + (2 * d - x0)) / 3
           \<le> Lam * (2 * z^2 + (A0 + x)^2) / 12 + (A0 + y) / 3"
proof -
  have k: "4 \<le> Lam * (2 * A0 + (x + x0))" using lam_key[OF assms(1,2)] assms(3,5) by simp
  have p: "0 \<le> (x - x0) * (Lam * (2 * A0 + x + x0) - 4)"
    by (rule mult_nonneg_nonneg) (use assms(5) k in \<open>auto simp: add.assoc\<close>)
  have "0 \<le> (x - x0) * (Lam * (2 * A0 + x + x0) - 4) / 12 + (x + y - 2 * d) / 3"
    using p assms(7) by (simp add: add_nonneg_nonneg)
  moreover have "(Lam * (2 * z^2 + (A0 + x)^2) / 12 + (A0 + y) / 3)
           - (Lam * (2 * z^2 + (A0 + x0)^2) / 12 + (A0 + (2 * d - x0)) / 3)
         = (x - x0) * (Lam * (2 * A0 + x + x0) - 4) / 12 + (x + y - 2 * d) / 3"
    by (rule J_difference)
  ultimately show ?thesis by linarith
qed

end
