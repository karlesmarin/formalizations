(*  Title:      Dubins_Family_Identity.thy
    Author:     Carles Marin
    Copyright:  Carles Marin
    License:    BSD-3-Clause

    Elementary identities and signs for the Dubins family x, y, z.
*)

theory Dubins_Family_Identity
  imports "HOL-Analysis.Analysis"
begin

definition dub_x :: "real \<Rightarrow> real \<Rightarrow> real"
  where "dub_x \<phi> w = \<phi> - sin \<phi> + (w / 2) * (1 - cos \<phi>)"

definition dub_y :: "real \<Rightarrow> real \<Rightarrow> real"
  where "dub_y \<phi> w = \<phi> + sin \<phi> + (w / 2) * (1 + cos \<phi>)"

definition dub_z :: "real \<Rightarrow> real \<Rightarrow> real"
  where "dub_z \<phi> w = cos \<phi> - (w / 2) * sin \<phi>"

lemma dubins_polynomial_identity:
  fixes p s c w :: real
  shows "(p - s + (w / 2) * (1 - c)) * (p + s + (w / 2) * (1 + c)) - (1 - (c - (w / 2) * s))\<^sup>2
         - (p\<^sup>2 - 2 * (1 - c) + w * (p - s)) = (w\<^sup>2 / 4 + 1) * (1 - (s * s + c * c))"
  by (simp add: field_simps power2_eq_square)

text \<open>(1a) exact identity\<close>
lemma dubins_identity:
  "dub_x \<phi> w * dub_y \<phi> w - (1 - dub_z \<phi> w)\<^sup>2
     = \<phi>\<^sup>2 - 2 * (1 - cos \<phi>) + w * (\<phi> - sin \<phi>)"
proof -
  have h: "sin \<phi> * sin \<phi> + cos \<phi> * cos \<phi> = 1"
    using sin_cos_squared_add[of \<phi>] by (simp add: power2_eq_square)
  have "dub_x \<phi> w * dub_y \<phi> w - (1 - dub_z \<phi> w)\<^sup>2
        - (\<phi>\<^sup>2 - 2 * (1 - cos \<phi>) + w * (\<phi> - sin \<phi>))
        = (w\<^sup>2 / 4 + 1) * (1 - (sin \<phi> * sin \<phi> + cos \<phi> * cos \<phi>))"
    unfolding dub_x_def dub_y_def dub_z_def by (rule dubins_polynomial_identity)
  also have "\<dots> = 0" using h by simp
  finally show ?thesis by linarith
qed

lemma one_minus_cos_le:
  fixes t :: real
  shows "1 - cos t \<le> t\<^sup>2 / 2"
proof -
  have "1 - cos t = 2 * (sin (t / 2))\<^sup>2"
    using cos_double_sin[of "t / 2"] by simp
  moreover have "(sin (t / 2))\<^sup>2 \<le> (t / 2)\<^sup>2"
    using abs_sin_x_le_abs_x[of "t / 2"] abs_le_square_iff[of "sin (t / 2)" "t / 2"] by blast
  ultimately show ?thesis by (simp add: power2_eq_square)
qed

text \<open>(1b) nonnegativity\<close>
lemma dubins_quantity_nonneg:
  assumes "0 \<le> \<phi>" "0 \<le> w"
  shows "0 \<le> dub_x \<phi> w * dub_y \<phi> w - (1 - dub_z \<phi> w)\<^sup>2"
proof -
  have "0 \<le> w * (\<phi> - sin \<phi>)"
    using assms sin_x_le_x[of \<phi>] by (simp add: mult_nonneg_nonneg)
  moreover have "0 \<le> \<phi>\<^sup>2 - 2 * (1 - cos \<phi>)"
    using one_minus_cos_le[of \<phi>] by simp
  ultimately show ?thesis by (simp add: dubins_identity)
qed

text \<open>(1c)\<close>
lemma dubins_D_bound:
  fixes a D :: real
  assumes "a = 1 - dub_z \<phi> w" "D = 2 * (1 - (dub_z \<phi> w)\<^sup>2) - pi * dub_x \<phi> w - (dub_x \<phi> w)\<^sup>2"
    "0 \<le> dub_x \<phi> w"
  shows "D \<le> 4 * a * (1 - a / 2)"
proof -
  have "0 \<le> pi * dub_x \<phi> w" using assms(3) by (simp add: mult_nonneg_nonneg)
  moreover have "0 \<le> (dub_x \<phi> w)\<^sup>2" by simp
  moreover have "4 * a * (1 - a / 2) = 2 * (1 - (dub_z \<phi> w)\<^sup>2)"
  proof -
    have zz: "dub_z \<phi> w = 1 - a" using assms(1) by simp
    then show ?thesis unfolding zz by (simp add: field_simps power2_eq_square)
  qed
  ultimately show ?thesis using assms(2) by linarith
qed

end
