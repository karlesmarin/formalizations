(*  Title:      Vertex_Configurations.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    The sorted lists of regular polygons that fit around a vertex: sum of (n_i - 2)/n_i = 2 exactly for the 17 configurations
*)

theory Vertex_Configurations
  imports Complex_Main
begin

section \<open>Vertex configurations of regular polygons\<close>

text \<open>
A vertex configuration is a list of k >= 3 regular polygons with n_i >= 3 sides whose interior angles
(n_i - 2) * 180 / n_i add up to 360, i.e. sum (n_i - 2)/n_i = 2, equivalently sum 1/n_i = k/2 - 1.
We prove: k lies between 3 and 6, every n_i <= 42, and the sorted solutions are exactly the 17
classical ones. (NOT formalized: which 11 of the 21 cyclic orders extend to a tiling of the plane;
that is geometry.)
\<close>

subsection \<open>A pruned search and its correctness\<close>

fun gen :: "nat \<Rightarrow> nat \<Rightarrow> rat \<Rightarrow> nat list list" where
  "gen 0 m S = (if S = 0 then [[]] else [])"
| "gen (Suc r) m S =
    (if S \<le> 0 then []
     else concat (map (\<lambda>n. map (Cons n) (gen r n (S - 1 / of_nat n)))
                      [m ..< Suc (nat \<lfloor>of_nat (Suc r) / S\<rfloor>)]))"

lemma sum_inv_le:
  assumes "\<forall>y\<in>set ys. n \<le> y" "1 \<le> n"
  shows "(\<Sum>y\<leftarrow>ys. 1 / of_nat y :: rat) \<le> of_nat (length ys) / of_nat n"
  using assms
proof (induction ys)
  case Nil then show ?case by simp
next
  case (Cons y ys)
  have n0: "(0::rat) < of_nat n" using Cons.prems(2) by simp
  have "(1::rat) / of_nat y \<le> 1 / of_nat n"
    using Cons.prems n0 by (intro frac_le) simp_all
  moreover have "(\<Sum>z\<leftarrow>ys. 1 / of_nat z :: rat) \<le> of_nat (length ys) / of_nat n"
    using Cons by simp
  moreover have "(1 + of_nat (length ys) :: rat) / of_nat n = 1 / of_nat n + of_nat (length ys) / of_nat n"
    by (simp add: add_divide_distrib)
  ultimately show ?case by simp
qed

lemma sum_inv_nonneg: "(0::rat) \<le> (\<Sum>y\<leftarrow>ys. 1 / of_nat y)"
  by (induction ys) (simp_all add: add_nonneg_nonneg)

lemma sum_inv_pos:
  assumes "ys \<noteq> []" "\<forall>y\<in>set ys. 1 \<le> y"
  shows "(0::rat) < (\<Sum>y\<leftarrow>ys. 1 / of_nat y)"
proof (cases ys)
  case Nil then show ?thesis using assms by simp
next
  case (Cons a zs)
  have "(0::rat) < 1 / of_nat a" using assms(2) Cons by simp
  moreover have "(0::rat) \<le> (\<Sum>y\<leftarrow>zs. 1 / of_nat y)" by (rule sum_inv_nonneg)
  ultimately have "(0::rat) < 1 / of_nat a + (\<Sum>y\<leftarrow>zs. 1 / of_nat y)" by linarith
  then show ?thesis using Cons by simp
qed

lemma gen_iff:
  assumes "1 \<le> m"
  shows "xs \<in> set (gen r m S) \<longleftrightarrow>
         (length xs = r \<and> sorted xs \<and> (\<forall>x\<in>set xs. m \<le> x) \<and> (\<Sum>x\<leftarrow>xs. 1 / of_nat x) = S)"
  using assms
proof (induction r arbitrary: m S xs)
  case 0
  show ?case by (cases xs) auto
next
  case (Suc r)
  show ?case
  proof
    assume h: "xs \<in> set (gen (Suc r) m S)"
    then have Spos: "\<not> S \<le> 0" by (auto split: if_splits)
    from h Spos obtain n ys where
      xs: "xs = n # ys" and nr: "n \<in> set [m ..< Suc (nat \<lfloor>of_nat (Suc r) / S\<rfloor>)]"
      and ys: "ys \<in> set (gen r n (S - 1 / of_nat n))"
      by auto
    have mn: "m \<le> n" using nr unfolding set_upt atLeastLessThan_iff by blast
    have n1: "1 \<le> n" using mn Suc.prems by simp
    from Suc.IH[OF n1, where S = "S - 1 / of_nat n" and xs = ys] ys
    have ih: "length ys = r" "sorted ys" "\<forall>x\<in>set ys. n \<le> x"
      "(\<Sum>x\<leftarrow>ys. 1 / of_nat x) = S - 1 / of_nat n" by simp_all
    show "length xs = Suc r \<and> sorted xs \<and> (\<forall>x\<in>set xs. m \<le> x) \<and>
          (\<Sum>x\<leftarrow>xs. 1 / of_nat x) = S"
      using xs ih mn by (auto simp: sorted_simps)
  next
    assume h: "length xs = Suc r \<and> sorted xs \<and> (\<forall>x\<in>set xs. m \<le> x) \<and>
               (\<Sum>x\<leftarrow>xs. 1 / of_nat x) = S"
    then obtain n ys where xs: "xs = n # ys" by (cases xs) auto
    have len: "length ys = r" and srt: "sorted ys" and ge: "\<forall>y\<in>set ys. n \<le> y"
      and mn: "m \<le> n" and sm: "1 / of_nat n + (\<Sum>x\<leftarrow>ys. 1 / of_nat x) = S"
      using h xs by (auto simp: sorted_simps)
    have n1: "1 \<le> n" using mn Suc.prems by simp
    have n0: "(0::rat) < of_nat n" using n1 by simp
    have Spos: "(0::rat) < S"
    proof -
      have "(0::rat) < 1 / of_nat n" using n0 by simp
      moreover have "(0::rat) \<le> (\<Sum>x\<leftarrow>ys. 1 / of_nat x)" by (rule sum_inv_nonneg)
      ultimately show ?thesis using sm by linarith
    qed
    have "(\<Sum>x\<leftarrow>ys. 1 / of_nat x :: rat) \<le> of_nat r / of_nat n"
      using sum_inv_le[OF ge n1] len by simp
    then have "S \<le> of_nat (Suc r) / of_nat n"
      using sm by (simp add: add_divide_distrib)
    then have "of_nat n \<le> of_nat (Suc r) / S"
      using n0 Spos by (simp add: field_simps)
    then have nb: "n \<le> nat \<lfloor>of_nat (Suc r) / S\<rfloor>"
      by (simp add: le_nat_iff le_floor_iff)
    have yin: "ys \<in> set (gen r n (S - 1 / of_nat n))"
      using Suc.IH[OF n1, where S = "S - 1 / of_nat n" and xs = ys] len srt ge sm by simp
    have nin: "n \<in> set [m ..< Suc (nat \<lfloor>of_nat (Suc r) / S\<rfloor>)]"
      using mn nb by (auto simp: less_Suc_eq_le)
    have nS: "\<not> S \<le> 0" using Spos by simp
    show "xs \<in> set (gen (Suc r) m S)"
      unfolding gen.simps if_not_P[OF nS] set_concat set_map
      using nin yin xs by force
  qed
qed

subsection \<open>The statement\<close>

definition configs :: "nat list list" where
  "configs = [[3,7,42],[3,8,24],[3,9,18],[3,10,15],[3,12,12],[4,5,20],[4,6,12],[4,8,8],[5,5,10],[6,6,6],
              [3,3,4,12],[3,3,6,6],[3,4,4,6],[4,4,4,4],
              [3,3,3,3,6],[3,3,3,4,4],
              [3,3,3,3,3,3]]"

definition search :: "nat list list" where
  "search = concat (map (\<lambda>k. gen k 3 ((of_nat k - 2) / 2)) [3 ..< 7])"

text \<open>The finite search closes by computation.\<close>

lemma search_eq_configs: "search = configs"
  unfolding search_def configs_def by eval

lemma configs_card: "length configs = 17" and configs_distinct: "distinct configs"
  unfolding configs_def by eval+

lemma configs_bounds:
  "\<forall>xs\<in>set configs. 3 \<le> length xs \<and> length xs \<le> 6 \<and> (\<forall>x\<in>set xs. 3 \<le> x \<and> x \<le> 42)"
  unfolding configs_def by eval

lemma angle_sum:
  assumes "\<forall>x\<in>set xs. 1 \<le> x"
  shows "(\<Sum>x\<leftarrow>xs. (of_nat x - 2) / of_nat x :: rat) =
         of_nat (length xs) - 2 * (\<Sum>x\<leftarrow>xs. 1 / of_nat x)"
  using assms
proof (induction xs)
  case Nil then show ?case by simp
next
  case (Cons a xs)
  have a0: "(of_nat a :: rat) \<noteq> 0" using Cons.prems by simp
  have "(of_nat a - 2) / (of_nat a :: rat) = 1 - 2 * (1 / of_nat a)" using a0 by (simp add: field_simps)
  then show ?case using Cons by (simp add: algebra_simps)
qed

text \<open>Hand proof of the bound on the number of polygons: 3 <= k <= 6.\<close>

lemma length_bounds:
  assumes "\<forall>x\<in>set xs. 3 \<le> x" "(\<Sum>x\<leftarrow>xs. (of_nat x - 2) / of_nat x :: rat) = 2"
  shows "3 \<le> length xs" "length xs \<le> 6"
proof -
  have ge1: "\<forall>x\<in>set xs. 1 \<le> x" using assms(1) by auto
  have eq: "of_nat (length xs) - 2 * (\<Sum>x\<leftarrow>xs. 1 / of_nat x) = (2::rat)"
    using assms(2) angle_sum[OF ge1] by simp
  have ne: "xs \<noteq> []" using assms(2) by auto
  have pos: "(0::rat) < (\<Sum>x\<leftarrow>xs. 1 / of_nat x)" by (rule sum_inv_pos[OF ne ge1])
  have up: "(\<Sum>x\<leftarrow>xs. 1 / of_nat x :: rat) \<le> of_nat (length xs) / of_nat 3"
    by (rule sum_inv_le[OF assms(1)]) simp
  have "(of_nat (length xs) :: rat) > 2" using eq pos by linarith
  then show "3 \<le> length xs" by (simp add: less_eq_Suc_le)
  have "(of_nat (length xs) :: rat) \<le> 6" using eq up by simp
  then show "length xs \<le> 6" by simp
qed

theorem classification:
  assumes "\<forall>x\<in>set xs. 3 \<le> x" "sorted xs"
  shows "(\<Sum>x\<leftarrow>xs. (of_nat x - 2) / of_nat x :: rat) = 2 \<longleftrightarrow> xs \<in> set configs"
proof
  have ge1: "\<forall>x\<in>set xs. 1 \<le> x" using assms(1) by auto
  assume h: "(\<Sum>x\<leftarrow>xs. (of_nat x - 2) / of_nat x :: rat) = 2"
  have lb: "3 \<le> length xs" "length xs \<le> 6" using length_bounds[OF assms(1) h] by simp_all
  have eq: "(\<Sum>x\<leftarrow>xs. 1 / of_nat x :: rat) = (of_nat (length xs) - 2) / 2"
    using h angle_sum[OF ge1] by simp
  have hg: "xs \<in> set (gen (length xs) 3 ((of_nat (length xs) - 2) / 2))"
    using gen_iff[where m = 3 and r = "length xs" and S = "(of_nat (length xs) - 2) / 2" and xs = xs]
      assms eq by simp
  have hk: "length xs \<in> set [3 ..< 7]" using lb
    by (simp only: set_upt atLeastLessThan_iff; arith)
  have "xs \<in> set search" unfolding search_def set_concat set_map using hk hg by blast
  then show "xs \<in> set configs" using search_eq_configs by simp
next
  have ge1: "\<forall>x\<in>set xs. 1 \<le> x" using assms(1) by auto
  assume "xs \<in> set configs"
  then have "xs \<in> set search" using search_eq_configs by simp
  then have "\<exists>k\<in>set [3 ..< 7]. xs \<in> set (gen k 3 ((of_nat k - 2) / 2))"
    unfolding search_def set_concat set_map by blast
  then obtain k where g: "xs \<in> set (gen k 3 ((of_nat k - 2) / 2))" by blast
  from gen_iff[where m = 3 and r = k and S = "(of_nat k - 2) / 2" and xs = xs] g
  have "length xs = k" "(\<Sum>x\<leftarrow>xs. 1 / of_nat x :: rat) = (of_nat k - 2) / 2" by simp_all
  then show "(\<Sum>x\<leftarrow>xs. (of_nat x - 2) / of_nat x :: rat) = 2"
    using angle_sum[OF ge1] by simp
qed

corollary max_polygon_bound:
  assumes "\<forall>x\<in>set xs. 3 \<le> x" "sorted xs" "(\<Sum>x\<leftarrow>xs. (of_nat x - 2) / of_nat x :: rat) = 2"
  shows "3 \<le> length xs" "length xs \<le> 6" "\<forall>x\<in>set xs. x \<le> 42"
proof -
  have "xs \<in> set configs" using classification[OF assms(1,2)] assms(3) by simp
  then show "3 \<le> length xs" "length xs \<le> 6" "\<forall>x\<in>set xs. x \<le> 42"
    using configs_bounds by auto
qed

text \<open>The extreme case: 1/3 + 1/7 + 1/42 = 1/2, i.e. the angles of 3, 7, 42-gons add up to 360 degrees.\<close>

lemma extreme_case: "(\<Sum>x\<leftarrow>[3,7,42]. (of_nat x - 2) / of_nat x :: rat) = 2"
  by eval

end
