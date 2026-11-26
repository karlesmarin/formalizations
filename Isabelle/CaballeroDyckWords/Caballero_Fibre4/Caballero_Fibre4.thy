(*  Title:      Caballero_Fibre4.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Marín, paper II on Rodríguez Caballero's parenthesis problem (in preparation), Corollary 9.5 (cor:fibre4):
   a fibre of size four for a = 3.

   For a = 3, a vector c = (c_{-3}, ..., c_3) and b >= 1 let f(v) = min(b+1, max(0, v+1)),
   H_i(j) = sum_{l=0}^{3} f(c_{i-l} + j) (0 <= i <= 3, 0 <= j <= b) and Z(c) the multiset of the
   4(b+1) values H_i(j). The word of n is determined by Z(c) and conversely ([I, Section 6]; the paper's setting),
   so "same word" is "same Z".

   Proved here, for b >= 5: the four vectors (b-4,b-1,B^5), (b-3,b-2,B^5), (b-2,b-2,b-1,B^4), (b-2,b-1,b-1,b-1,B^3)
   (B = b) are pairwise distinct and have the same Z, namely
   {4b-1, 4b+1, 4b+2, 4b+3, 4b+3} + (4b-1) copies of T = 4b+4: the displayed formula of Theorem S1 at
   sigma = 4b-1.

   Not formalized: the second sentence of the corollary (among the pairs of Theorem S1, an m = 2 pair and an
   m = 3 pair have the same word only for (n,rho) = (1,0) and (1,1)); it needs Z for the whole family
   (x, y, B^5), x = b - 4n + rho, and Theorem S1 itself (Z(c) = Z(G) with G the partner of [I]).
*)
theory Caballero_Fibre4
  imports Complex_Main "HOL-Library.Multiset"
begin

section \<open>Definitions, as in the paper (a = 3)\<close>

definition fcl :: "int \<Rightarrow> int \<Rightarrow> int" where
  "fcl b v = min (b + 1) (max 0 (v + 1))"

definition Hval :: "int \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "Hval b c i j = (\<Sum>l \<in> {0..3}. fcl b (c (i - l) + j))"

text \<open>Z(c): the multiset of the 4(b+1) values H_i(j), 0 <= i <= 3, 0 <= j <= b.\<close>
definition Zms :: "int \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int multiset" where
  "Zms b c = mset (concat (map (\<lambda>i. map (\<lambda>j. Hval b c i j) [0..b]) [0..3]))"

text \<open>A vector (c_{-3}, ..., c_3) given as a list of seven entries.\<close>
definition vec7 :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "vec7 l h = (if -3 \<le> h \<and> h \<le> 3 then l ! nat (h + 3) else 0)"

section \<open>Evaluation for vectors with all coordinates in [b-4, b]\<close>

lemma Hval_expand: "Hval b c i j = fcl b (c i + j) + fcl b (c (i - 1) + j) + fcl b (c (i - 2) + j) + fcl b (c (i - 3) + j)"
proof -
  have "{0..3 :: int} = {0, 1, 2, 3}" by auto
  then show ?thesis by (simp add: Hval_def)
qed

lemma Hval_top:
  assumes "5 \<le> b" "4 \<le> j" and c: "\<And>h. - 3 \<le> h \<Longrightarrow> h \<le> 3 \<Longrightarrow> b - 4 \<le> c h \<and> c h \<le> b"
    and i: "0 \<le> i" "i \<le> 3"
  shows "Hval b c i j = 4 * (b + 1)"
proof -
  have "\<And>k. 0 \<le> k \<Longrightarrow> k \<le> 3 \<Longrightarrow> fcl b (c (i - k) + j) = b + 1"
  proof -
    fix k :: int assume k: "0 \<le> k" "k \<le> 3"
    have "b - 4 \<le> c (i - k)" using c[of "i - k"] i k by simp
    then show "fcl b (c (i - k) + j) = b + 1" using assms(2) by (simp add: fcl_def)
  qed
  from this[of 0] this[of 1] this[of 2] this[of 3] show ?thesis by (simp add: Hval_expand)
qed

lemma rep4: "replicate_mset (4 * n) x = replicate_mset n x + replicate_mset n x + replicate_mset n x + replicate_mset n x"
  by (auto simp: multiset_eq_iff)

lemma Zms_near:
  assumes b: "5 \<le> b" and c: "\<And>h. - 3 \<le> h \<Longrightarrow> h \<le> 3 \<Longrightarrow> b - 4 \<le> c h \<and> c h \<le> b"
  shows "Zms b c = replicate_mset (4 * nat (b - 3)) (4 * (b + 1))
      + mset (concat (map (\<lambda>i. map (\<lambda>j. Hval b c i j) [0..3]) [0..3]))"
proof -
  have row: "\<And>i. 0 \<le> i \<Longrightarrow> i \<le> 3 \<Longrightarrow> map (\<lambda>j. Hval b c i j) [0..b]
      = map (\<lambda>j. Hval b c i j) [0..3] @ replicate (nat (b - 3)) (4 * (b + 1))"
  proof -
    fix i :: int assume i: "0 \<le> i" "i \<le> 3"
    have sp: "[0..b] = [0..3] @ [4..b]" using upto_split1[of 0 4 b] b by simp
    have "map (\<lambda>j. Hval b c i j) [4..b] = map (\<lambda>j. 4 * (b + 1)) [4..b]"
      by (rule map_cong[OF refl]) (use Hval_top[OF b _ c i] in \<open>simp add: set_upto\<close>)
    also have "\<dots> = replicate (length [4..b]) (4 * (b + 1))" by (simp add: map_replicate_const)
    also have "length [4..b] = nat (b - 3)" using b by (simp add: length_upto)
    finally show "map (\<lambda>j. Hval b c i j) [0..b]
      = map (\<lambda>j. Hval b c i j) [0..3] @ replicate (nat (b - 3)) (4 * (b + 1))" by (simp add: sp)
  qed
  have l03: "[0..3 :: int] = [0, 1, 2, 3]" by eval
  show ?thesis
    unfolding Zms_def
    apply (simp only: l03)
    apply (simp only: list.map concat.simps row[of 0, simplified] row[of 1, simplified] row[of 2, simplified]
      row[of 3, simplified])
    apply (simp add: mset_append rep4 ac_simps l03)
    done
qed

section \<open>The four vectors\<close>

definition v1 :: "int \<Rightarrow> int \<Rightarrow> int" where "v1 b = vec7 [b - 4, b - 1, b, b, b, b, b]"
definition v2 :: "int \<Rightarrow> int \<Rightarrow> int" where "v2 b = vec7 [b - 3, b - 2, b, b, b, b, b]"
definition v3 :: "int \<Rightarrow> int \<Rightarrow> int" where "v3 b = vec7 [b - 2, b - 2, b - 1, b, b, b, b]"
definition v4 :: "int \<Rightarrow> int \<Rightarrow> int" where "v4 b = vec7 [b - 2, b - 1, b - 1, b - 1, b, b, b]"

definition Zfibre :: "int \<Rightarrow> int multiset" where
  "Zfibre b = replicate_mset (nat (4 * b - 1)) (4 * b + 4) + {#4 * b - 1, 4 * b + 1, 4 * b + 2, 4 * b + 3, 4 * b + 3#}"

lemma near_v:
  assumes "5 \<le> b" and "c = v1 b \<or> c = v2 b \<or> c = v3 b \<or> c = v4 b"
  shows "\<And>h. - 3 \<le> h \<Longrightarrow> h \<le> 3 \<Longrightarrow> b - 4 \<le> c h \<and> c h \<le> b"
proof -
  fix h :: int assume h: "- 3 \<le> h" "h \<le> 3"
  then have "h = -3 \<or> h = -2 \<or> h = -1 \<or> h = 0 \<or> h = 1 \<or> h = 2 \<or> h = 3" by auto
  with assms show "b - 4 \<le> c h \<and> c h \<le> b"
    by (elim disjE) (auto simp: v1_def v2_def v3_def v4_def vec7_def)
qed

lemma upto03: "[0..3 :: int] = [0, 1, 2, 3]" by eval

lemma list_v1:
  assumes "5 \<le> b"
  shows "concat (map (\<lambda>i. map (\<lambda>j. Hval b (v1 b) i j) [0..3]) [0..3]) = [4 * b + 4 - 5, 4 * b + 4 - 3, 4 * b + 4 - 2, 4 * b + 4 - 1, 4 * b + 4 - 1, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0]"
  using assms by (simp add: upto03 Hval_expand v1_def vec7_def fcl_def min_def max_def)

lemma Zms_v1:
  assumes b: "5 \<le> b"
  shows "Zms b (v1 b) = Zfibre b"
proof -
  have n: "\<And>h. - 3 \<le> h \<Longrightarrow> h \<le> 3 \<Longrightarrow> b - 4 \<le> v1 b h \<and> v1 b h \<le> b"
    by (rule near_v[OF b]) simp
  have nb: "nat (4 * b - 1) = 4 * nat (b - 3) + 11" using b by arith
  show ?thesis
    by (simp add: Zms_near[OF b n] list_v1[OF b] Zfibre_def nb multiset_eq_iff count_replicate_mset split: if_splits)
qed

lemma list_v2:
  assumes "5 \<le> b"
  shows "concat (map (\<lambda>i. map (\<lambda>j. Hval b (v2 b) i j) [0..3]) [0..3]) = [4 * b + 4 - 5, 4 * b + 4 - 3, 4 * b + 4 - 1, 4 * b + 4 - 0, 4 * b + 4 - 2, 4 * b + 4 - 1, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0]"
  using assms by (simp add: upto03 Hval_expand v2_def vec7_def fcl_def min_def max_def)

lemma Zms_v2:
  assumes b: "5 \<le> b"
  shows "Zms b (v2 b) = Zfibre b"
proof -
  have n: "\<And>h. - 3 \<le> h \<Longrightarrow> h \<le> 3 \<Longrightarrow> b - 4 \<le> v2 b h \<and> v2 b h \<le> b"
    by (rule near_v[OF b]) simp
  have nb: "nat (4 * b - 1) = 4 * nat (b - 3) + 11" using b by arith
  show ?thesis
    by (simp add: Zms_near[OF b n] list_v2[OF b] Zfibre_def nb multiset_eq_iff count_replicate_mset split: if_splits)
qed

lemma list_v3:
  assumes "5 \<le> b"
  shows "concat (map (\<lambda>i. map (\<lambda>j. Hval b (v3 b) i j) [0..3]) [0..3]) = [4 * b + 4 - 5, 4 * b + 4 - 2, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 3, 4 * b + 4 - 1, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 1, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0]"
  using assms by (simp add: upto03 Hval_expand v3_def vec7_def fcl_def min_def max_def)

lemma Zms_v3:
  assumes b: "5 \<le> b"
  shows "Zms b (v3 b) = Zfibre b"
proof -
  have n: "\<And>h. - 3 \<le> h \<Longrightarrow> h \<le> 3 \<Longrightarrow> b - 4 \<le> v3 b h \<and> v3 b h \<le> b"
    by (rule near_v[OF b]) simp
  have nb: "nat (4 * b - 1) = 4 * nat (b - 3) + 11" using b by arith
  show ?thesis
    by (simp add: Zms_near[OF b n] list_v3[OF b] Zfibre_def nb multiset_eq_iff count_replicate_mset split: if_splits)
qed

lemma list_v4:
  assumes "5 \<le> b"
  shows "concat (map (\<lambda>i. map (\<lambda>j. Hval b (v4 b) i j) [0..3]) [0..3]) = [4 * b + 4 - 5, 4 * b + 4 - 1, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 3, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 2, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 1, 4 * b + 4 - 0, 4 * b + 4 - 0, 4 * b + 4 - 0]"
  using assms by (simp add: upto03 Hval_expand v4_def vec7_def fcl_def min_def max_def)

lemma Zms_v4:
  assumes b: "5 \<le> b"
  shows "Zms b (v4 b) = Zfibre b"
proof -
  have n: "\<And>h. - 3 \<le> h \<Longrightarrow> h \<le> 3 \<Longrightarrow> b - 4 \<le> v4 b h \<and> v4 b h \<le> b"
    by (rule near_v[OF b]) simp
  have nb: "nat (4 * b - 1) = 4 * nat (b - 3) + 11" using b by arith
  show ?thesis
    by (simp add: Zms_near[OF b n] list_v4[OF b] Zfibre_def nb multiset_eq_iff count_replicate_mset split: if_splits)
qed

section \<open>Corollary 9.5, first sentence\<close>

lemma neq_at: "f h \<noteq> g h \<Longrightarrow> f \<noteq> g" by auto

lemma v_at_m3: "v1 b (-3) = b - 4" "v2 b (-3) = b - 3" "v3 b (-3) = b - 2" "v4 b (-3) = b - 2"
  and v_at_m2: "v3 b (-2) = b - 2" "v4 b (-2) = b - 1"
  by (simp_all add: v1_def v2_def v3_def v4_def vec7_def)

text \<open>For b >= 5 the four vectors (b-4,b-1,B^5), (b-3,b-2,B^5), (b-2,b-2,b-1,B^4), (b-2,b-1,b-1,b-1,B^3)
  (B = b) are pairwise distinct and have the same Z(c) (hence the same word), equal to the multiset
  {4b-1, 4b+1, 4b+2, 4b+3, 4b+3} + (4b-1) copies of T = 4b+4.\<close>
theorem cor_fibre4:
  assumes b: "5 \<le> b"
  shows "v1 b \<noteq> v2 b" "v1 b \<noteq> v3 b" "v1 b \<noteq> v4 b" "v2 b \<noteq> v3 b" "v2 b \<noteq> v4 b" "v3 b \<noteq> v4 b"
    and "Zms b (v1 b) = Zfibre b" "Zms b (v2 b) = Zfibre b" "Zms b (v3 b) = Zfibre b" "Zms b (v4 b) = Zfibre b"
proof -
  show "v1 b \<noteq> v2 b" by (rule neq_at[of _ "-3"]) (simp add: v_at_m3)
  show "v1 b \<noteq> v3 b" by (rule neq_at[of _ "-3"]) (simp add: v_at_m3)
  show "v1 b \<noteq> v4 b" by (rule neq_at[of _ "-3"]) (simp add: v_at_m3)
  show "v2 b \<noteq> v3 b" by (rule neq_at[of _ "-3"]) (simp add: v_at_m3)
  show "v2 b \<noteq> v4 b" by (rule neq_at[of _ "-3"]) (simp add: v_at_m3)
  show "v3 b \<noteq> v4 b" by (rule neq_at[of _ "-2"]) (simp add: v_at_m2)
  show "Zms b (v1 b) = Zfibre b" by (rule Zms_v1[OF b])
  show "Zms b (v2 b) = Zfibre b" by (rule Zms_v2[OF b])
  show "Zms b (v3 b) = Zfibre b" by (rule Zms_v3[OF b])
  show "Zms b (v4 b) = Zfibre b" by (rule Zms_v4[OF b])
qed

end
