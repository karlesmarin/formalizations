(*  Title:      BSR_m4_Cor5.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Arithmetic of Corollary cor:five of the paper "Every m x 4 biquadratic sum of squares is a sum of 3m-1 squares (5 <= m <= 16)" (2026, in preparation): BSR(m,5) <= 4m-1 for every m >= 2.
    (a) for m >= 12, every r with C(r+1,2) <= 15*C(m+1,2) satisfies r <= 4m-1;
    (b) for 5 <= m <= 16, m + (3m-1) = 4m-1;
    (c) the cases m = 2, 3, 4 (6 <= 7, 10 <= 11, 14 <= 15);
    (d) a combination: from the cited inputs (BSR(m,5) <= m + BSR(m,4), BSR(m,4) <= 3m-1 for 5 <= m <= 16,
        the bound Lambda of Choi-Lam-Reznick, and the values for m = 2, 3, 4) to BSR(m,5) <= 4m-1 for all m >= 2.
    The cited inputs are hypotheses of (d), not proved here.  BSR itself is not defined in this theory.
*)

theory BSR_m4_Cor5
  imports Complex_Main
begin

subsection \<open>(a) The bound of Choi--Lam--Reznick for m >= 12\<close>

lemma clr_bound:
  fixes m r :: nat
  assumes m: "12 \<le> m" and r: "r * (r + 1) \<le> 15 * m * (m + 1)"
  shows "r \<le> 4 * m - 1"
proof (rule ccontr)
  assume "\<not> r \<le> 4 * m - 1"
  then have h: "4 * m \<le> r" using m by simp
  have "4 * m * (4 * m + 1) \<le> r * (r + 1)" using h by (intro mult_mono) simp_all
  then have "4 * m * (4 * m + 1) \<le> 15 * m * (m + 1)" using r by (rule order_trans)
  moreover have "12 * m \<le> m * m" using m by (rule mult_right_mono) simp
  ultimately show False using m by (simp add: algebra_simps)
qed

lemma two_choose: "2 * ((n + 1) choose 2) = (n + 1) * n"
proof -
  have "even ((n + 1) * n)" by (cases "even n") (simp_all add: even_mult_iff)
  then obtain k where k: "(n + 1) * n = 2 * k" by (rule evenE)
  have a: "(n + 1) choose 2 = (n + 1) * n div 2" by (simp add: choose_two)
  have b: "(n + 1) * n div 2 = k" using k by simp
  show ?thesis using a b k by simp
qed

text \<open>Same statement with binomial coefficients: C(r+1,2) <= 15 C(m+1,2).\<close>

lemma clr_bound_choose:
  fixes m r :: nat
  assumes m: "12 \<le> m" and r: "(r + 1) choose 2 \<le> 15 * ((m + 1) choose 2)"
  shows "r \<le> 4 * m - 1"
proof -
  have e1: "2 * ((r + 1) choose 2) = (r + 1) * r" by (rule two_choose)
  have e2: "2 * ((m + 1) choose 2) = (m + 1) * m" by (rule two_choose)
  have "2 * ((r + 1) choose 2) \<le> 2 * (15 * ((m + 1) choose 2))" using r by simp
  then have "(r + 1) * r \<le> 15 * ((m + 1) * m)" using e1 e2 by simp
  then have "r * (r + 1) \<le> 15 * m * (m + 1)" by (simp add: algebra_simps)
  with m show ?thesis by (rule clr_bound)
qed

text \<open>Sharpness: r = 4m passes the bound exactly when m <= 11, so the hypothesis m >= 12 is needed.\<close>

lemma clr_bound_sharp:
  "(44::nat) * (44 + 1) \<le> 15 * 11 * (11 + 1) \<and> \<not> (44::nat) \<le> 4 * 11 - 1"
  by simp

lemma four_m_passes_iff:
  fixes m :: nat
  shows "4 * m * (4 * m + 1) \<le> 15 * m * (m + 1) \<longleftrightarrow> m \<le> 11"
proof
  assume h: "4 * m * (4 * m + 1) \<le> 15 * m * (m + 1)"
  show "m \<le> 11"
  proof (rule ccontr)
    assume "\<not> m \<le> 11"
    then have "12 \<le> m" by simp
    from clr_bound[OF this h] \<open>12 \<le> m\<close> show False by simp
  qed
next
  assume "m \<le> 11"
  then show "4 * m * (4 * m + 1) \<le> 15 * m * (m + 1)" proof -
    have "m * m \<le> 11 * m" using \<open>m \<le> 11\<close> by (rule mult_right_mono) simp
    then show ?thesis by (simp add: algebra_simps)
  qed
qed

subsection \<open>(b) Adding one column, and (c) the cases m = 2, 3, 4\<close>

lemma add_column_arith:
  fixes m :: nat
  assumes "5 \<le> m" "m \<le> 16"
  shows "m + (3 * m - 1) = 4 * m - 1"
  using assms by simp

lemma small_cases: "(6::nat) \<le> 4 * 2 - 1" "(10::nat) \<le> 4 * 3 - 1" "(14::nat) \<le> 4 * 4 - 1"
  by simp_all

subsection \<open>(d) Combination of the cited inputs\<close>

theorem cor_five:
  fixes bsr :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  assumes add_col: "\<And>m. 5 \<le> m \<Longrightarrow> m \<le> 16 \<Longrightarrow> bsr m 5 \<le> m + bsr m 4"
    and main: "\<And>m. 5 \<le> m \<Longrightarrow> m \<le> 16 \<Longrightarrow> bsr m 4 \<le> 3 * m - 1"
    and clr: "\<And>m. 12 \<le> m \<Longrightarrow> \<exists>L. bsr m 5 \<le> L \<and> L * (L + 1) \<le> 15 * m * (m + 1)"
    and v2: "bsr 2 5 \<le> 6" and v3: "bsr 3 5 \<le> 10" and v4: "bsr 4 5 \<le> 14"
    and m2: "2 \<le> m"
  shows "bsr m 5 \<le> 4 * m - 1"
proof (cases "m \<le> 4")
  case True
  with m2 have "m = 2 \<or> m = 3 \<or> m = 4" by auto
  then show ?thesis using v2 v3 v4 by auto
next
  case False
  then have m5: "5 \<le> m" by simp
  show ?thesis
  proof (cases "m \<le> 16")
    case True
    then show ?thesis using add_col[OF m5 True] main[OF m5 True] m5 by simp
  next
    case False
    obtain L where L: "bsr m 5 \<le> L" "L * (L + 1) \<le> 15 * m * (m + 1)"
      using clr[of m] False by auto
    from clr_bound[of m L] False L(2) have "L \<le> 4 * m - 1" by simp
    with L(1) show ?thesis by simp
  qed
qed

end
