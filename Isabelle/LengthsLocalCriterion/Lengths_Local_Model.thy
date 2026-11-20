(*  Title:      Lengths_Local_Model.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Non-vacuity of the locales lengths_data and lengths_local of Lengths_Local_Criterion: two concrete models
   satisfy all their assumptions, and the corollary and the theorem sharp are instantiated in each of them.

   In both models the places are the natural numbers, the single place v = 2 splits, every element is a square in
   Q_2 and the nonnegative rationals are the squares elsewhere, the Hilbert symbol is constantly 1, m = 4 and
   D = delta = 1. The excess and the defect are DEFINED by the criterion itself (so that Theorem finite holds by
   definition), and the two bounds of Theorem one are proved for them. In model 1 the Hasse invariant of q is -1 at
   the place 2, and the theorem sharp then gives excess 7 with defect 4; in model 2 it is +1 everywhere, and the same
   theorem gives excess at most 6. Neither model is the real Hilbert symbol of Q: the locale does not force that.
*)
theory Lengths_Local_Model
  imports Lengths_Local_Criterion
begin

lemma nonneg_scale:
  fixes x c :: rat
  assumes "c \<noteq> 0"
  shows "(0 \<le> x * c\<^sup>2) = (0 \<le> x)"
proof -
  have cp: "0 < c\<^sup>2" using assms by simp
  show ?thesis using mult_le_cancel_right_pos[OF cp, where a = 0 and b = x] by simp
qed

section \<open>Model 1: the Hasse invariant of q is -1 at the split place 2\<close>

interpretation A: lengths_data
  "\<lambda>(v::nat) (x::rat). v = 2 \<or> 0 \<le> x" "\<lambda>(v::nat) (a::rat) (b::rat). (1::int)" "\<lambda>v::nat. v = 2"
  1 1 4 "\<lambda>v::nat. if v = 2 then (-1::int) else 1" "\<lambda>d::nat. {2::nat}"
proof unfold_locales
  show "(0::rat) < 1" by simp
  show "(1::rat) \<noteq> 0" by simp
  show "\<And>(v::nat) (a::rat) (b::rat). a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> (1::int) = 1 \<or> (1::int) = -1" by simp
  show "\<And>v::nat. (if v = 2 then (-1::int) else 1) = 1 \<or> (if v = 2 then (-1::int) else 1) = -1" by simp
  show "\<And>(d::nat) (v::nat). v \<notin> {2} \<Longrightarrow> (if v = 2 then (-1::int) else 1) = 1" by simp
  show "\<And>(v::nat) (a::rat) (b::rat). a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> (1::int) = 1" by simp
  show "\<And>(v::nat) (a::rat). a \<noteq> 0 \<Longrightarrow> (1::int) = 1" by simp
  show "\<And>(v::nat) (a::rat) (b::rat) (c::rat). a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> (1::int) = 1" by simp
  show "\<And>(v::nat) (a::rat) (b::rat). a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> (v = 2 \<or> 0 \<le> a) \<Longrightarrow> (1::int) = 1" by simp
  show "\<And>(v::nat) (x::rat) (c::rat). c \<noteq> 0 \<Longrightarrow> (v = 2 \<or> 0 \<le> x * c\<^sup>2) = (v = 2 \<or> 0 \<le> x)"
    using nonneg_scale by auto
  show "\<And>v::nat. v = 2 \<or> (0::rat) \<le> 1" by simp
  show "\<And>(v::nat) (x::rat) (y::rat). (v = 2 \<or> 0 \<le> x) \<Longrightarrow> (v = 2 \<or> 0 \<le> y) \<Longrightarrow> (v = 2 \<or> 0 \<le> x * y)"
    by (auto intro: mult_nonneg_nonneg)
  show "\<And>v::nat. v = 2 \<Longrightarrow> v = 2 \<or> (0::rat) \<le> - 1" by simp
qed

definition mexcA :: "nat \<Rightarrow> bool" where
  "mexcA h \<longleftrightarrow> (\<exists>h'. h' \<le> h \<and> h' \<le> 4 + 3 \<and> (\<exists>d. d mod 2 = 4 mod 2 \<and> d \<le> h' \<and> A.crit h' d))"

definition mdefA :: "nat \<Rightarrow> bool" where
  "mdefA e \<longleftrightarrow> (\<exists>d. d \<le> e \<and> d \<le> 4 \<and> d mod 2 = 4 mod 2 \<and> A.crit0 d)"

lemma A_crit0_4: "A.crit0 4"
  unfolding A.crit0_def
proof
  fix v :: nat
  assume "v \<in> {2}"
  have "A.sgn2 4 v \<in> A.R v 4 (A.Dd 4)" using A.R_ge3[where t = 4] A.sgn2_pm by simp
  then show "\<exists>e. e \<in> A.R v 4 (A.Dd 4) \<and> (v = 2 \<longrightarrow> e = A.sgn2 4 v)" by blast
qed

interpretation AL: lengths_local
  "\<lambda>(v::nat) (x::rat). v = 2 \<or> 0 \<le> x" "\<lambda>(v::nat) (a::rat) (b::rat). (1::int)" "\<lambda>v::nat. v = 2"
  1 1 4 "\<lambda>v::nat. if v = 2 then (-1::int) else 1" "\<lambda>d::nat. {2::nat}" mexcA mdefA
proof unfold_locales
  show "\<And>h. mexcA h = (\<exists>h'. h' \<le> h \<and> h' \<le> 4 + 3 \<and> (\<exists>d. d mod 2 = 4 mod 2 \<and> d \<le> h' \<and> A.crit h' d))"
    by (simp add: mexcA_def)
  show "\<And>e. mdefA e = (\<exists>d. d \<le> e \<and> d \<le> 4 \<and> d mod 2 = 4 mod 2 \<and> A.crit0 d)"
    by (simp add: mdefA_def)
  show "mdefA 4" unfolding mdefA_def using A_crit0_4 by blast
  show "mexcA (4 + 3)"
    unfolding mexcA_def using A.crit0_crit3[OF A_crit0_4] by (intro exI[where x = 7] conjI exI[where x = 4]) auto
qed

text \<open>The corollary bounded in model 1: defect at most 4 and excess at most 7.\<close>

lemma model1_cor: "mdefA 4 \<and> mexcA 7"
  using AL.cor_bounded by (simp add: cm_def)

lemma mdefA_not3: "\<not> mdefA 3"
proof
  assume "mdefA 3"
  then obtain d where d: "d \<le> 3" "d mod 2 = 4 mod 2" "A.crit0 d" unfolding mdefA_def by blast
  have "d = 0 \<or> d = 2" using d(1,2) by arith
  then show False
  proof (elim disjE)
    assume "d = 0"
    with d(3) have "A.crit0 0" by simp
    then show False by (simp add: A.crit0_def A.R_def A.sgn2_def A.Dd_def)
  next
    assume "d = 2"
    with d(3) have "A.crit0 2" by simp
    then show False by (simp add: A.crit0_def A.R_def A.sgn2_def A.Dd_def)
  qed
qed

text \<open>The theorem sharp in model 1: the place 2 splits, -D = -1 is a square in Q_2, and the Hasse invariant of q
  is -1 there; the defect is 4, hence the excess is 7.\<close>

theorem model1_excess7: "mexcA 7 \<and> \<not> mexcA 6"
proof -
  have "mdefA 4 \<and> \<not> mdefA 3 \<and> (\<exists>v::nat. v = 2 \<and> (v = 2 \<or> (0::rat) \<le> - 1) \<and> (if v = 2 then (-1::int) else 1) = -1)"
    using model1_cor mdefA_not3 by auto
  then show ?thesis using AL.sharp by simp
qed

section \<open>Model 2: the Hasse invariant of q is +1 everywhere\<close>

interpretation B: lengths_data
  "\<lambda>(v::nat) (x::rat). v = 2 \<or> 0 \<le> x" "\<lambda>(v::nat) (a::rat) (b::rat). (1::int)" "\<lambda>v::nat. v = 2"
  1 1 4 "\<lambda>v::nat. (1::int)" "\<lambda>d::nat. {2::nat}"
proof unfold_locales
  show "(0::rat) < 1" by simp
  show "(1::rat) \<noteq> 0" by simp
  show "\<And>(v::nat) (a::rat) (b::rat). a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> (1::int) = 1 \<or> (1::int) = -1" by simp
  show "\<And>v::nat. (1::int) = 1 \<or> (1::int) = -1" by simp
  show "\<And>(d::nat) (v::nat). v \<notin> {2} \<Longrightarrow> (1::int) = 1" by simp
  show "\<And>(v::nat) (a::rat) (b::rat). a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> (1::int) = 1" by simp
  show "\<And>(v::nat) (a::rat). a \<noteq> 0 \<Longrightarrow> (1::int) = 1" by simp
  show "\<And>(v::nat) (a::rat) (b::rat) (c::rat). a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> (1::int) = 1" by simp
  show "\<And>(v::nat) (a::rat) (b::rat). a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> (v = 2 \<or> 0 \<le> a) \<Longrightarrow> (1::int) = 1" by simp
  show "\<And>(v::nat) (x::rat) (c::rat). c \<noteq> 0 \<Longrightarrow> (v = 2 \<or> 0 \<le> x * c\<^sup>2) = (v = 2 \<or> 0 \<le> x)"
    using nonneg_scale by auto
  show "\<And>v::nat. v = 2 \<or> (0::rat) \<le> 1" by simp
  show "\<And>(v::nat) (x::rat) (y::rat). (v = 2 \<or> 0 \<le> x) \<Longrightarrow> (v = 2 \<or> 0 \<le> y) \<Longrightarrow> (v = 2 \<or> 0 \<le> x * y)"
    by (auto intro: mult_nonneg_nonneg)
  show "\<And>v::nat. v = 2 \<Longrightarrow> v = 2 \<or> (0::rat) \<le> - 1" by simp
qed

definition mexcB :: "nat \<Rightarrow> bool" where
  "mexcB h \<longleftrightarrow> (\<exists>h'. h' \<le> h \<and> h' \<le> 4 + 3 \<and> (\<exists>d. d mod 2 = 4 mod 2 \<and> d \<le> h' \<and> B.crit h' d))"

definition mdefB :: "nat \<Rightarrow> bool" where
  "mdefB e \<longleftrightarrow> (\<exists>d. d \<le> e \<and> d \<le> 4 \<and> d mod 2 = 4 mod 2 \<and> B.crit0 d)"

lemma B_crit0_4: "B.crit0 4"
  unfolding B.crit0_def
proof
  fix v :: nat
  assume "v \<in> {2}"
  have "B.sgn2 4 v \<in> B.R v 4 (B.Dd 4)" using B.R_ge3[where t = 4] B.sgn2_pm by simp
  then show "\<exists>e. e \<in> B.R v 4 (B.Dd 4) \<and> (v = 2 \<longrightarrow> e = B.sgn2 4 v)" by blast
qed

interpretation BL: lengths_local
  "\<lambda>(v::nat) (x::rat). v = 2 \<or> 0 \<le> x" "\<lambda>(v::nat) (a::rat) (b::rat). (1::int)" "\<lambda>v::nat. v = 2"
  1 1 4 "\<lambda>v::nat. (1::int)" "\<lambda>d::nat. {2::nat}" mexcB mdefB
proof unfold_locales
  show "\<And>h. mexcB h = (\<exists>h'. h' \<le> h \<and> h' \<le> 4 + 3 \<and> (\<exists>d. d mod 2 = 4 mod 2 \<and> d \<le> h' \<and> B.crit h' d))"
    by (simp add: mexcB_def)
  show "\<And>e. mdefB e = (\<exists>d. d \<le> e \<and> d \<le> 4 \<and> d mod 2 = 4 mod 2 \<and> B.crit0 d)"
    by (simp add: mdefB_def)
  show "mdefB 4" unfolding mdefB_def using B_crit0_4 by blast
  show "mexcB (4 + 3)"
    unfolding mexcB_def using B.crit0_crit3[OF B_crit0_4] by (intro exI[where x = 7] conjI exI[where x = 4]) auto
qed

text \<open>In model 2 no place has Hasse invariant -1, so the theorem sharp says that the excess 7 is not attained:
  the excess is at most 6.\<close>

theorem model2_excess_le6: "mexcB 6"
proof -
  have c: "mdefB 4 \<and> mexcB 7" using BL.cor_bounded by (simp add: cm_def)
  have "\<not> (\<exists>v::nat. v = 2 \<and> (v = 2 \<or> (0::rat) \<le> - 1) \<and> (1::int) = -1)" by simp
  then have "\<not> (mexcB 7 \<and> \<not> mexcB 6)" using BL.sharp by auto
  then show ?thesis using c by blast
qed

end
