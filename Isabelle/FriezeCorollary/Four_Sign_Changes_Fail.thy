(*  Title:      Four_Sign_Changes_Fail.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD
*)

(* encaje: integer-frieze-sign-changes, Corollary cor:all: Theorems A (Integer_Frieze_Rows) and B (Odd_Frieze_Rows)
   together, for every n >= 14 *)
theory Four_Sign_Changes_Fail
  imports Odd_Frieze_Rows.Odd_Frieze_Rows
begin

text \<open>Corollary \<open>cor:all\<close> of ``Integer frieze patterns and sign changes'': four sign changes fail for every
  $n\ge14$. For even $n=14+2t$ (Theorem A, \<open>strictly_ordered_middle_rows\<close>) the middle rows of two frieze patterns
  are strictly ordered, so their difference has no zero and no sign change; for odd $n=15+2t$ (Theorem B,
  \<open>two_sign_changes\<close>) the rows $\lfloor w/2\rfloor$ differ with no zero and exactly two sign changes, inside the
  printed range of the question. In both cases fewer than four sign changes, whichever way zeros are counted (there
  are none).\<close>

corollary four_sign_changes_fail_even:
  assumes "14 \<le> n" "even n"
  shows "\<exists>t. n = 14 + 2 * t \<and> frieze (FA t) \<and> frieze (FB t) \<and> length (FA t) = n \<and> length (FB t) = n \<and>
           (\<forall>i < n div 2. dia (FA t) i < dia (FB t) i)"
proof -
  obtain k where k: "n = 2 * k" using assms(2) by (auto elim: evenE)
  define t where "t = k - 7"
  have t: "n = 14 + 2 * t" using k assms(1) unfolding t_def by linarith
  have "n div 2 = 7 + t" using t by simp
  then show ?thesis using strictly_ordered_middle_rows[of t] t by auto
qed

corollary four_sign_changes_fail_odd:
  assumes "15 \<le> n" "odd n"
  shows "\<exists>t. n = 15 + 2 * t \<and> frieze (VA t) \<and> frieze (VB t) \<and> length (VA t) = n \<and> length (VB t) = n \<and>
           (\<forall>i < n. dd t i \<noteq> 0) \<and> sign_changes (dd t) n = 2"
proof -
  obtain t where t: "n = 15 + 2 * t"
  proof
    show "n = 15 + 2 * ((n - 15) div 2)" using assms by (auto elim!: oddE)
  qed
  then show ?thesis using two_sign_changes[of t] by auto
qed

end
