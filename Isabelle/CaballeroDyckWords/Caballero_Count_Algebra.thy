(*  Title:      Caballero_Count_Algebra.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín
*)

section \<open>Final arithmetic of Theorem A: \<open>(5b+4)(b+1)/2 - (3b-1) - \<Sum>(b-2d) = \<lfloor>(9b\<^sup>2+8b+12)/4\<rfloor>\<close>\<close>

theory Caballero_Count_Algebra
  imports Main
begin

text \<open>
  Scope: this theory proves ONLY the closing arithmetic of Theorem A (task 292, final count). It does
  NOT formalise the cell lemmas: the value \<open>R(1,b) = (5b+4)(b+1)/2\<close> and the excesses \<open>3b-1\<close> and
  \<open>b-2d\<close> are taken as given numbers; the triple lemmas and the families O and Q are not covered.
  The sum is over the integers, the floors are natural-number divisions.
\<close>

lemma sum_b_minus_2d:
  "(\<Sum>d\<in>{1..k}. (int b - 2 * int d)) = int k * int b - int k * (int k + 1)"
  by (induction k) (auto simp: algebra_simps)

text \<open>Even \<open>b = 2(i+1)\<close> and odd \<open>b = 2j+1\<close> (\<open>j \<ge> 1\<close>), all three claims at once.\<close>

definition claims :: "nat \<Rightarrow> bool" where
  "claims b \<longleftrightarrow>
     int ((5 * b + 4) * (b + 1) div 2) - (3 * int b - 1)
       - (\<Sum>d\<in>{1..(b - 1) div 2}. (int b - 2 * int d)) = int ((9 * b\<^sup>2 + 8 * b + 12) div 4)
   \<and> int ((9 * b\<^sup>2 + 8 * b + 12) div 4)
       = 3 + (9 * int b * (int b + 1) - 2 * int ((b + 1) div 2)) div 4
   \<and> 4 dvd (9 * int b * (int b + 1) - 2 * int ((b + 1) div 2))"

lemma claims_even: "claims (2 * (i + 1))"
proof -
  define b where "b = 2 * (i + 1)"
  have X2: "(5 * b + 4) * (b + 1) div 2 = (5 * (i + 1) + 2) * (2 * (i + 1) + 1)"
    by (simp add: b_def algebra_simps)
  have Y4: "(9 * b\<^sup>2 + 8 * b + 12) div 4 = 9 * (i + 1)\<^sup>2 + 4 * (i + 1) + 3"
    by (simp add: b_def algebra_simps power2_eq_square)
  have k: "(b - 1) div 2 = i" and k2: "(b + 1) div 2 = i + 1" unfolding b_def by arith+
  have w: "9 * int b * (int b + 1) - 2 * int (i + 1) = 4 * (int (i + 1) * (9 * int i + 13))"
    by (simp add: b_def algebra_simps)
  show ?thesis unfolding claims_def b_def[symmetric]
    apply (simp only: X2 Y4 k k2 sum_b_minus_2d w)
    apply (simp add: b_def algebra_simps power2_eq_square)
    done
qed

lemma claims_odd: "claims (2 * j + 1)"
proof -
  define b where "b = 2 * j + 1"
  have X2: "(5 * b + 4) * (b + 1) div 2 = (10 * j + 9) * (j + 1)"
    by (simp add: b_def algebra_simps)
  have c: "9 * b\<^sup>2 + 8 * b + 12 = 4 * (9 * j\<^sup>2 + 13 * j + 7) + 1"
    by (simp add: b_def algebra_simps power2_eq_square)
  have d: "(4 * (9 * j\<^sup>2 + 13 * j + 7) + 1) div 4 = 9 * j\<^sup>2 + 13 * j + 7" by simp
  have Y4: "(9 * b\<^sup>2 + 8 * b + 12) div 4 = 9 * j\<^sup>2 + 13 * j + 7" by (simp only: c d)
  have k: "(b - 1) div 2 = j" and k2: "(b + 1) div 2 = j + 1" unfolding b_def by arith+
  have w: "9 * int b * (int b + 1) - 2 * int (j + 1) = 4 * (int (j + 1) * (9 * int j + 4))"
    by (simp add: b_def algebra_simps)
  show ?thesis unfolding claims_def b_def[symmetric]
    apply (simp only: X2 Y4 k k2 sum_b_minus_2d w)
    apply (simp add: b_def algebra_simps power2_eq_square)
    done
qed

theorem theorem_A_algebra:
  fixes b :: nat
  assumes "b \<ge> 2"
  shows "int ((5 * b + 4) * (b + 1) div 2) - (3 * int b - 1)
           - (\<Sum>d\<in>{1..(b - 1) div 2}. (int b - 2 * int d)) = int ((9 * b\<^sup>2 + 8 * b + 12) div 4)"
    and "int ((9 * b\<^sup>2 + 8 * b + 12) div 4)
           = 3 + (9 * int b * (int b + 1) - 2 * int ((b + 1) div 2)) div 4"
    and "4 dvd (9 * int b * (int b + 1) - 2 * int ((b + 1) div 2))"
proof -
  have "claims b"
  proof (cases "even b")
    case True
    then obtain j where j: "b = 2 * j" by auto
    with assms obtain i where "j = i + 1" by (cases j) auto
    with j claims_even show ?thesis by simp
  next
    case False
    then obtain j where "b = 2 * j + 1" by (auto elim: oddE)
    with claims_odd show ?thesis by simp
  qed
  thus "int ((5 * b + 4) * (b + 1) div 2) - (3 * int b - 1)
           - (\<Sum>d\<in>{1..(b - 1) div 2}. (int b - 2 * int d)) = int ((9 * b\<^sup>2 + 8 * b + 12) div 4)"
    and "int ((9 * b\<^sup>2 + 8 * b + 12) div 4)
           = 3 + (9 * int b * (int b + 1) - 2 * int ((b + 1) div 2)) div 4"
    and "4 dvd (9 * int b * (int b + 1) - 2 * int ((b + 1) div 2))"
    unfolding claims_def by simp_all
qed

text \<open>With \<open>b = q - 1\<close>, \<open>q\<close> odd: the cardinality \<open>(9q\<^sup>2 - 10q + 13)/4\<close> of the case \<open>L\<^sub>2\<^sub>q\<close>.\<close>

theorem theorem_A_q:
  fixes q :: nat
  assumes "odd q" "q \<ge> 3"
  shows "int ((9 * (q - 1)\<^sup>2 + 8 * (q - 1) + 12) div 4) = (9 * int q ^ 2 - 10 * int q + 13) div 4"
    and "4 dvd (9 * int q ^ 2 - 10 * int q + 13)"
proof -
  obtain j where q: "q = 2 * j + 1" using assms(1) by (auto elim: oddE)
  have jp: "j \<ge> 1" using assms(2) q by simp
  have n: "(9 * (q - 1)\<^sup>2 + 8 * (q - 1) + 12) = 4 * (9 * j\<^sup>2 + 4 * j + 3)"
    using q by (simp add: algebra_simps power2_eq_square)
  have z: "9 * int q ^ 2 - 10 * int q + 13 = 4 * (9 * int j ^ 2 + 4 * int j + 3)"
    using q by (simp add: algebra_simps power2_eq_square)
  show "int ((9 * (q - 1)\<^sup>2 + 8 * (q - 1) + 12) div 4) = (9 * int q ^ 2 - 10 * int q + 13) div 4"
  proof -
    have n2: "(9 * (q - 1)\<^sup>2 + 8 * (q - 1) + 12) div 4 = 9 * j\<^sup>2 + 4 * j + 3"
      unfolding n by simp
    show ?thesis unfolding n2 z by simp
  qed
  show "4 dvd (9 * int q ^ 2 - 10 * int q + 13)" by (simp add: z)
qed

end
