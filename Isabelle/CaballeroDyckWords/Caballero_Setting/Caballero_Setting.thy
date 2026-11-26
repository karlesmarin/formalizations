(*  Title:      Caballero_Setting.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

   Marín, paper II on Rodríguez Caballero's parenthesis problem (in preparation): Section "Setting" (Lemma M,
   Lemma P), Section "Walls" (Proposition wall (a),(c); Corollary antichain (ii),(iii); Lemma amb;
   Proposition burnside; the counting part of Theorem a3-families) and Proposition tau.

   For a, b integers, a vector c : int => int (only the coordinates -a <= h <= a count), put
     f(v)   = min(b+1, max(0, v+1)),
     H_i(j) = sum_{l=0}^{a} f(c_{i-l} + j)           (0 <= i <= a, 0 <= j <= b),
     Z(c)   = the multiset of the (a+1)(b+1) values H_i(j),
     Sigma(c) = sum of the elements of Z(c),
     F(v)   = sum_{j=0}^{b} f(v+j).
   The word of n is determined by Z(c) and conversely ([I, Section 6]; the paper's setting), so "same word" is
   "same Z".  Realisable vectors are those of the open quadrant; here "realisable" is replaced where needed by the
   property the proofs use (non-decreasing in h, coordinates in [-b-1, b]); the theorems are therefore stated
   for a larger class of vectors.  The geometric facts (cells, walls, the involution sigma) enter as hypotheses
   in the abstract statements (amb, burnside, a3-families).
*)
theory Caballero_Setting
  imports Complex_Main "HOL-Library.Multiset"
begin

section \<open>Definitions, as in the paper\<close>

definition fcl :: "int \<Rightarrow> int \<Rightarrow> int" where
  "fcl b v = min (b + 1) (max 0 (v + 1))"

definition Hval :: "int \<Rightarrow> int \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "Hval a b c i j = (\<Sum>l \<in> {0..a}. fcl b (c (i - l) + j))"

text \<open>Z(c): the multiset of the (a+1)(b+1) values H_i(j), 0 <= i <= a, 0 <= j <= b.\<close>
definition Zms :: "int \<Rightarrow> int \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int multiset" where
  "Zms a b c = image_mset (\<lambda>p. Hval a b c (fst p) (snd p)) (mset_set ({0..a} \<times> {0..b}))"

definition Sig :: "int \<Rightarrow> int \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int" where
  "Sig a b c = sum_mset (Zms a b c)"

definition Fsum :: "int \<Rightarrow> int \<Rightarrow> int" where
  "Fsum b v = (\<Sum>j \<in> {0..b}. fcl b (v + j))"

section \<open>The step of f and Lemma M (elementary move)\<close>

lemma fcl_step:
  "fcl b (v + 1) = fcl b v + (if -1 \<le> v \<and> v \<le> b - 1 then 1 else 0)"
  unfolding fcl_def by (auto simp: min_def max_def)

text \<open>The change of f(v+j) when v moves by sigma = +1 or -1, as a function of j.\<close>
definition mvd :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "mvd b s v j = (if s = 1 then (if 0 \<le> v + 1 + j \<and> v + 1 + j \<le> b then 1 else 0)
                  else (if 0 \<le> v + j \<and> v + j \<le> b then -1 else 0))"

lemma fcl_move:
  assumes "s = 1 \<or> s = -1"
  shows "fcl b (v + s + j) = fcl b (v + j) + mvd b s v j"
proof (cases "s = 1")
  case True
  have "fcl b (v + j + 1) = fcl b (v + j) + (if -1 \<le> v + j \<and> v + j \<le> b - 1 then 1 else 0)"
    by (rule fcl_step)
  then show ?thesis using True by (auto simp: mvd_def add.commute add.left_commute)
next
  case False
  then have s: "s = -1" using assms by simp
  have e: "v + s + j = v + j - 1" using s by simp
  have "fcl b ((v + j - 1) + 1) = fcl b (v + j - 1) + (if -1 \<le> v + j - 1 \<and> v + j - 1 \<le> b - 1 then 1 else 0)"
    by (rule fcl_step)
  then show ?thesis unfolding e using s by (auto simp: mvd_def)
qed

definition Jset :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int set" where
  "Jset b s v = {j \<in> {0..b}. if s = 1 then 0 \<le> v + 1 + j \<and> v + 1 + j \<le> b else 0 \<le> v + j \<and> v + j \<le> b}"

lemma mvd_Jset:
  assumes "0 \<le> j" "j \<le> b" "s = 1 \<or> s = -1"
  shows "mvd b s v j = (if j \<in> Jset b s v then s else 0)"
  using assms by (auto simp: mvd_def Jset_def)

lemma sum_reindex_rev:
  fixes G :: "int \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>l \<in> {0..a}. G (i - l)) = (\<Sum>h \<in> {i - a..i}. G h)"
  by (rule sum.reindex_bij_witness[where i = "\<lambda>h. i - h" and j = "\<lambda>l. i - l"]) auto

text \<open>Lemma M, general form: several coordinates move; the changes of one row add, computed on the original
  vector.  M is the finite set of moved coordinates, s h = +-1 the move of coordinate h.\<close>
theorem lem_M_multi:
  assumes fin: "finite M" and s: "\<And>h. h \<in> M \<Longrightarrow> s h = 1 \<or> s h = -1"
    and cc: "\<And>h. c' h = c h + (if h \<in> M then s h else 0)"
    and j: "0 \<le> j" "j \<le> b"
  shows "Hval a b c' i j = Hval a b c i j
           + (\<Sum>h \<in> M. if 0 \<le> i - h \<and> i - h \<le> a \<and> j \<in> Jset b (s h) (c h) then s h else 0)"
proof -
  let ?g = "\<lambda>h. if h \<in> M \<and> j \<in> Jset b (s h) (c h) then s h else 0"
  have step: "\<And>l. fcl b (c' (i - l) + j) = fcl b (c (i - l) + j) + ?g (i - l)"
  proof -
    fix l
    show "fcl b (c' (i - l) + j) = fcl b (c (i - l) + j) + ?g (i - l)"
    proof (cases "i - l \<in> M")
      case True
      have "c' (i - l) = c (i - l) + s (i - l)" using cc True by simp
      then have "fcl b (c' (i - l) + j) = fcl b (c (i - l) + s (i - l) + j)" by (simp add: add.assoc)
      also have "\<dots> = fcl b (c (i - l) + j) + mvd b (s (i - l)) (c (i - l)) j"
        using fcl_move[OF s[OF True]] by blast
      also have "\<dots> = fcl b (c (i - l) + j) + ?g (i - l)"
        using mvd_Jset[OF j s[OF True]] True by simp
      finally show ?thesis .
    next
      case False
      then show ?thesis using cc by simp
    qed
  qed
  have "Hval a b c' i j = (\<Sum>l \<in> {0..a}. fcl b (c (i - l) + j) + ?g (i - l))"
    unfolding Hval_def using step by simp
  also have "\<dots> = Hval a b c i j + (\<Sum>l \<in> {0..a}. ?g (i - l))"
    by (simp add: Hval_def sum.distrib)
  finally have e1: "Hval a b c' i j = Hval a b c i j + (\<Sum>l \<in> {0..a}. ?g (i - l))" .
  have "(\<Sum>l \<in> {0..a}. ?g (i - l)) = (\<Sum>h \<in> {i - a..i}. ?g h)" by (rule sum_reindex_rev)
  also have "\<dots> = (\<Sum>h \<in> {i - a..i} \<inter> M. if j \<in> Jset b (s h) (c h) then s h else 0)"
  proof -
    have "(\<Sum>h \<in> {i - a..i}. ?g h) = (\<Sum>h \<in> {i - a..i}. if h \<in> M then (if j \<in> Jset b (s h) (c h) then s h else 0) else 0)"
      by (rule sum.cong) auto
    also have "\<dots> = (\<Sum>h \<in> {i - a..i} \<inter> M. if j \<in> Jset b (s h) (c h) then s h else 0)"
      by (rule sum.inter_restrict[symmetric]) simp
    finally show ?thesis .
  qed
  also have "\<dots> = (\<Sum>h \<in> M. if 0 \<le> i - h \<and> i - h \<le> a \<and> j \<in> Jset b (s h) (c h) then s h else 0)"
  proof -
    have "(\<Sum>h \<in> M. if 0 \<le> i - h \<and> i - h \<le> a \<and> j \<in> Jset b (s h) (c h) then s h else 0)
        = (\<Sum>h \<in> M. if h \<in> {i - a..i} then (if j \<in> Jset b (s h) (c h) then s h else 0) else 0)"
      by (rule sum.cong) auto
    also have "\<dots> = (\<Sum>h \<in> M \<inter> {i - a..i}. if j \<in> Jset b (s h) (c h) then s h else 0)"
      by (rule sum.inter_restrict[symmetric]) fact
    finally show ?thesis by (simp add: Int_commute)
  qed
  finally show ?thesis using e1 by simp
qed

text \<open>Lemma M as stated in the paper: one coordinate h moves by sigma = +1 or -1.
  J = {j in [0,b] : 0 <= c_h + 1 + j <= b} if sigma = 1, J = {j in [0,b] : 0 <= c_h + j <= b} if sigma = -1.
  (The hypothesis c'_h in [-b-1, b] of the paper is not needed.)\<close>
theorem lem_M:
  assumes "sg = 1 \<or> sg = -1" and "c' = c(h := c h + sg)" and "0 \<le> j" "j \<le> b"
  shows "Hval a b c' i j
         = Hval a b c i j + (if 0 \<le> i - h \<and> i - h \<le> a \<and> j \<in> Jset b sg (c h) then sg else 0)"
proof -
  have "Hval a b c' i j = Hval a b c i j
           + (\<Sum>k \<in> {h}. if 0 \<le> i - k \<and> i - k \<le> a \<and> j \<in> Jset b ((\<lambda>_. sg) k) (c k) then (\<lambda>_. sg) k else 0)"
    by (rule lem_M_multi[where M = "{h}" and s = "\<lambda>_. sg"]) (use assms in \<open>auto simp: fun_upd_def\<close>)
  then show ?thesis by simp
qed

section \<open>Walls: Sigma(c) = sum_h (a+1-|h|) F(c_h), the step formula, the weights\<close>

lemma conv_count:
  assumes "-a \<le> h" "h \<le> a"
  shows "card {i \<in> {0..a}. i - a \<le> h \<and> h \<le> i} = nat (a + 1 - \<bar>h\<bar>)"
proof (cases "0 \<le> h")
  case True
  have "{i \<in> {0..a}. i - a \<le> h \<and> h \<le> i} = {h..a}" using True assms by auto
  then show ?thesis using True assms by simp
next
  case False
  have "{i \<in> {0..a}. i - a \<le> h \<and> h \<le> i} = {0..a + h}" using False assms by auto
  then show ?thesis using False assms by simp
qed

text \<open>Rows and shifts: the coordinate h enters row i exactly when 0 <= i-h <= a, i.e. in a+1-|h| rows.\<close>
lemma conv_sum:
  fixes g :: "int \<Rightarrow> int"
  shows "(\<Sum>i \<in> {0..a}. \<Sum>l \<in> {0..a}. g (i - l)) = (\<Sum>h \<in> {-a..a}. (a + 1 - \<bar>h\<bar>) * g h)"
proof (cases "0 \<le> a")
  case False
  then show ?thesis by simp
next
  case True
  have inner: "\<And>i. i \<in> {0..a} \<Longrightarrow> (\<Sum>l \<in> {0..a}. g (i - l))
        = (\<Sum>h \<in> {-a..a}. if i - a \<le> h \<and> h \<le> i then g h else 0)"
  proof -
    fix i assume i: "i \<in> {0..a}"
    have "(\<Sum>l \<in> {0..a}. g (i - l)) = (\<Sum>h \<in> {i - a..i}. g h)" by (rule sum_reindex_rev)
    also have "\<dots> = (\<Sum>h \<in> {i - a..i} \<inter> {-a..a}. g h)"
      by (rule sum.cong) (use i in auto)
    also have "\<dots> = (\<Sum>h \<in> {-a..a}. if h \<in> {i - a..i} then g h else 0)"
      by (subst Int_commute) (rule sum.inter_restrict, simp)
    finally show "(\<Sum>l \<in> {0..a}. g (i - l)) = (\<Sum>h \<in> {-a..a}. if i - a \<le> h \<and> h \<le> i then g h else 0)"
      by (simp add: atLeastAtMost_iff conj_commute)
  qed
  have "(\<Sum>i \<in> {0..a}. \<Sum>l \<in> {0..a}. g (i - l))
      = (\<Sum>i \<in> {0..a}. \<Sum>h \<in> {-a..a}. if i - a \<le> h \<and> h \<le> i then g h else 0)"
    by (rule sum.cong) (use inner in auto)
  also have "\<dots> = (\<Sum>h \<in> {-a..a}. \<Sum>i \<in> {0..a}. if i - a \<le> h \<and> h \<le> i then g h else 0)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>h \<in> {-a..a}. (a + 1 - \<bar>h\<bar>) * g h)"
  proof (rule sum.cong[OF refl])
    fix h assume h: "h \<in> {-a..a}"
    have "(\<Sum>i \<in> {0..a}. if i - a \<le> h \<and> h \<le> i then g h else 0)
        = (\<Sum>i \<in> {i \<in> {0..a}. i - a \<le> h \<and> h \<le> i}. g h)"
      by (rule sum.inter_filter[symmetric]) simp
    also have "\<dots> = int (card {i \<in> {0..a}. i - a \<le> h \<and> h \<le> i}) * g h" by simp
    also have "\<dots> = (a + 1 - \<bar>h\<bar>) * g h"
    proof -
      have hh: "-a \<le> h" "h \<le> a" using h by simp_all
      have ha: "\<bar>h\<bar> \<le> a" using hh by (simp add: abs_le_iff)
      show ?thesis using conv_count[OF hh] ha by simp
    qed
    finally show "(\<Sum>i \<in> {0..a}. if i - a \<le> h \<and> h \<le> i then g h else 0) = (a + 1 - \<bar>h\<bar>) * g h" .
  qed
  finally show ?thesis .
qed

lemma Sig_decomp:
  "Sig a b c = (\<Sum>h \<in> {-a..a}. (a + 1 - \<bar>h\<bar>) * Fsum b (c h))"
proof -
  have "Sig a b c = (\<Sum>p \<in> {0..a} \<times> {0..b}. Hval a b c (fst p) (snd p))"
    by (simp add: Sig_def Zms_def sum_unfold_sum_mset)
  also have "\<dots> = (\<Sum>i \<in> {0..a}. \<Sum>j \<in> {0..b}. Hval a b c i j)"
    by (simp add: sum.cartesian_product case_prod_unfold)
  also have "\<dots> = (\<Sum>i \<in> {0..a}. \<Sum>l \<in> {0..a}. Fsum b (c (i - l)))"
    unfolding Hval_def Fsum_def by (simp add: sum.swap[of _ "{0..b}"])
  also have "\<dots> = (\<Sum>h \<in> {-a..a}. (a + 1 - \<bar>h\<bar>) * Fsum b (c h))" by (rule conv_sum)
  finally show ?thesis .
qed

lemma Fsum_step:
  assumes "-b - 1 \<le> v" "v \<le> b - 1"
  shows "Fsum b (v + 1) = Fsum b v + (b + 1 - \<bar>v + 1\<bar>)"
proof -
  have "Fsum b (v + 1) = (\<Sum>j \<in> {0..b}. fcl b (v + j) + (if -1 \<le> v + j \<and> v + j \<le> b - 1 then 1 else 0))"
    unfolding Fsum_def
  proof (rule sum.cong[OF refl])
    fix j :: int
    have e1: "fcl b (v + 1 + j) = fcl b ((v + j) + 1)" by (rule arg_cong[where f = "fcl b"]) simp
    show "fcl b (v + 1 + j) = fcl b (v + j) + (if -1 \<le> v + j \<and> v + j \<le> b - 1 then 1 else 0)"
      by (simp only: e1 fcl_step)
  qed
  also have "\<dots> = Fsum b v + (\<Sum>j \<in> {0..b}. if -1 \<le> v + j \<and> v + j \<le> b - 1 then 1 else 0)"
    by (simp add: Fsum_def sum.distrib)
  also have "(\<Sum>j \<in> {0..b}. if -1 \<le> v + j \<and> v + j \<le> b - 1 then (1::int) else 0)
           = int (card {j \<in> {0..b}. -1 \<le> v + j \<and> v + j \<le> b - 1})"
    by (subst sum.inter_filter[symmetric]) simp_all
  also have "card {j \<in> {0..b}. -1 \<le> v + j \<and> v + j \<le> b - 1} = nat (b + 1 - \<bar>v + 1\<bar>)"
  proof (cases "-1 \<le> v")
    case True
    have "{j \<in> {0..b}. -1 \<le> v + j \<and> v + j \<le> b - 1} = {0..b - 1 - v}" using True assms by auto
    then show ?thesis using True assms by simp
  next
    case False
    have "{j \<in> {0..b}. -1 \<le> v + j \<and> v + j \<le> b - 1} = {-1 - v..b}" using False assms by auto
    then show ?thesis using False assms by simp
  qed
  finally show ?thesis using assms by simp
qed

text \<open>Proposition wall (a): Sigma(c + e_h) - Sigma(c) = (a+1-|h|)(b+1-|c_h+1|), for c in [-b-1,b], |h| <= a,
  c_h <= b-1.\<close>
theorem prop_wall_a:
  assumes "-a \<le> h" "h \<le> a" "-b - 1 \<le> c h" "c h \<le> b - 1"
  shows "Sig a b (c(h := c h + 1)) - Sig a b c = (a + 1 - \<bar>h\<bar>) * (b + 1 - \<bar>c h + 1\<bar>)"
proof -
  let ?w = "\<lambda>k. (a + 1 - \<bar>k\<bar>) * Fsum b (c k)"
  let ?w' = "\<lambda>k. (a + 1 - \<bar>k\<bar>) * Fsum b ((c(h := c h + 1)) k)"
  have hin: "h \<in> {-a..a}" using assms by simp
  have "(\<Sum>k \<in> {-a..a} - {h}. ?w' k) = (\<Sum>k \<in> {-a..a} - {h}. ?w k)" by (rule sum.cong) auto
  moreover have "?w' h = (a + 1 - \<bar>h\<bar>) * Fsum b (c h + 1)" by simp
  ultimately have "Sig a b (c(h := c h + 1)) - Sig a b c = ?w' h - ?w h"
    unfolding Sig_decomp by (simp add: sum.remove[OF _ hin])
  also have "\<dots> = (a + 1 - \<bar>h\<bar>) * (Fsum b (c h + 1) - Fsum b (c h))" by (simp add: algebra_simps)
  also have "\<dots> = (a + 1 - \<bar>h\<bar>) * (b + 1 - \<bar>c h + 1\<bar>)" using Fsum_step[OF assms(3,4)] by simp
  finally show ?thesis .
qed

text \<open>Proposition wall (c), first formula, for any two vectors.\<close>
theorem prop_wall_c:
  "Sig a b d - Sig a b c = (\<Sum>h \<in> {-a..a}. (a + 1 - \<bar>h\<bar>) * (Fsum b (d h) - Fsum b (c h)))"
proof -
  have "(\<Sum>h \<in> {-a..a}. (a + 1 - \<bar>h\<bar>) * (Fsum b (d h) - Fsum b (c h)))
      = (\<Sum>h \<in> {-a..a}. (a + 1 - \<bar>h\<bar>) * Fsum b (d h) - (a + 1 - \<bar>h\<bar>) * Fsum b (c h))"
    by (rule sum.cong) (auto simp: algebra_simps)
  then show ?thesis by (simp add: Sig_decomp sum_subtractf)
qed

text \<open>Proposition wall (c), second formula: F(v) - F(u) = sum_{rho=u+1}^{v} (b+1-|rho|), -b-1 <= u <= v <= b.\<close>
theorem prop_wall_F:
  assumes "-b - 1 \<le> u" "u \<le> v" "v \<le> b"
  shows "Fsum b v - Fsum b u = (\<Sum>\<rho> \<in> {u + 1..v}. b + 1 - \<bar>\<rho>\<bar>)"
proof -
  have aux: "v \<le> b \<Longrightarrow> Fsum b v - Fsum b u = (\<Sum>\<rho> \<in> {u + 1..v}. b + 1 - \<bar>\<rho>\<bar>)"
    using assms(2)
  proof (induct v rule: int_ge_induct)
    case base
    then show ?case by simp
  next
    case (step k)
    have k: "-b - 1 \<le> k" "k \<le> b - 1" using step assms(1) by auto
    have "{u + 1..k + 1} = insert (k + 1) {u + 1..k}" using step by auto
    then have "(\<Sum>\<rho> \<in> {u + 1..k + 1}. b + 1 - \<bar>\<rho>\<bar>) = (b + 1 - \<bar>k + 1\<bar>) + (\<Sum>\<rho> \<in> {u + 1..k}. b + 1 - \<bar>\<rho>\<bar>)"
      by simp
    moreover have "Fsum b k - Fsum b u = (\<Sum>\<rho> \<in> {u + 1..k}. b + 1 - \<bar>\<rho>\<bar>)" using step k by simp
    moreover have "Fsum b (k + 1) = Fsum b k + (b + 1 - \<bar>k + 1\<bar>)" by (rule Fsum_step[OF k])
    ultimately show ?case by simp
  qed
  show ?thesis using aux assms(3) by simp
qed

text \<open>The weight of a wall: omega(h, rho) = (a+1-|h|)(b+1-|rho|) >= 1 for |h| <= a, |rho| <= b
  (Proposition wall (b), the weight part; the geometric part is not formalised).\<close>
theorem wall_omega_pos:
  fixes a b h \<rho> :: int
  assumes "\<bar>h\<bar> \<le> a" "\<bar>\<rho>\<bar> \<le> b"
  shows "1 \<le> (a + 1 - \<bar>h\<bar>) * (b + 1 - \<bar>\<rho>\<bar>)"
proof -
  have h1: "1 \<le> a + 1 - \<bar>h\<bar>" using assms(1) by linarith
  have h2: "1 \<le> b + 1 - \<bar>\<rho>\<bar>" using assms(2) by linarith
  have "1 * 1 \<le> (a + 1 - \<bar>h\<bar>) * (b + 1 - \<bar>\<rho>\<bar>)" by (rule mult_mono[OF h1 h2]) (use h1 in linarith, simp)
  then show ?thesis by simp
qed

section \<open>Corollary antichain (ii), (iii)\<close>

lemma Fsum_strict_mono:
  assumes "-b - 1 \<le> u" "u < v" "v \<le> b"
  shows "Fsum b u < Fsum b v"
proof -
  have "Fsum b v - Fsum b u = (\<Sum>\<rho> \<in> {u + 1..v}. b + 1 - \<bar>\<rho>\<bar>)" using prop_wall_F assms by simp
  also have "\<dots> > 0"
  proof (rule sum_pos)
    show "finite {u + 1..v}" by simp
    show "{u + 1..v} \<noteq> {}" using assms by simp
    fix \<rho> assume "\<rho> \<in> {u + 1..v}"
    then have "-b \<le> \<rho>" "\<rho> \<le> b" using assms by auto
    then show "0 < b + 1 - \<bar>\<rho>\<bar>" by simp
  qed
  finally show ?thesis by simp
qed

text \<open>(ii): if c <= d coordinatewise (on [-a,a]), c /= d, coordinates in [-b-1, b], then Sigma(c) < Sigma(d).\<close>
theorem cor_antichain_ii:
  assumes rng: "\<And>h. -a \<le> h \<Longrightarrow> h \<le> a \<Longrightarrow> -b - 1 \<le> c h \<and> c h \<le> b \<and> -b - 1 \<le> d h \<and> d h \<le> b"
    and le: "\<And>h. -a \<le> h \<Longrightarrow> h \<le> a \<Longrightarrow> c h \<le> d h"
    and ne: "\<exists>h. -a \<le> h \<and> h \<le> a \<and> c h \<noteq> d h"
  shows "Sig a b c < Sig a b d"
proof -
  obtain h0 where h0: "-a \<le> h0" "h0 \<le> a" "c h0 \<noteq> d h0" using ne by blast
  have pos: "\<And>h. h \<in> {-a..a} \<Longrightarrow> 0 \<le> (a + 1 - \<bar>h\<bar>) * (Fsum b (d h) - Fsum b (c h))"
  proof -
    fix h assume h: "h \<in> {-a..a}"
    then have hh: "-a \<le> h" "h \<le> a" by simp_all
    have "Fsum b (c h) \<le> Fsum b (d h)"
    proof (cases "c h = d h")
      case True then show ?thesis by simp
    next
      case False
      then have "c h < d h" using le hh by (meson antisym_conv1)
      then show ?thesis using Fsum_strict_mono rng hh by fastforce
    qed
    moreover have "0 \<le> a + 1 - \<bar>h\<bar>" using hh by simp
    ultimately show "0 \<le> (a + 1 - \<bar>h\<bar>) * (Fsum b (d h) - Fsum b (c h))" by simp
  qed
  have "0 < (a + 1 - \<bar>h0\<bar>) * (Fsum b (d h0) - Fsum b (c h0))"
  proof -
    have "c h0 < d h0" using le h0 by (meson antisym_conv1)
    then have "Fsum b (c h0) < Fsum b (d h0)" using Fsum_strict_mono rng h0 by fastforce
    moreover have "0 < a + 1 - \<bar>h0\<bar>" using h0 by simp
    ultimately show ?thesis by simp
  qed
  then have "0 < (\<Sum>h \<in> {-a..a}. (a + 1 - \<bar>h\<bar>) * (Fsum b (d h) - Fsum b (c h)))"
    using sum_pos2[of "{-a..a}" h0 "\<lambda>h. (a + 1 - \<bar>h\<bar>) * (Fsum b (d h) - Fsum b (c h))"] h0 pos by simp
  then show ?thesis using prop_wall_c[of a b d c] by linarith
qed

text \<open>In particular every fibre is an antichain: equal Z excludes c <= d, c /= d.\<close>
corollary cor_antichain_fibre:
  assumes "Zms a b c = Zms a b d"
    and "\<And>h. -a \<le> h \<Longrightarrow> h \<le> a \<Longrightarrow> -b - 1 \<le> c h \<and> c h \<le> b \<and> -b - 1 \<le> d h \<and> d h \<le> b"
    and "\<And>h. -a \<le> h \<Longrightarrow> h \<le> a \<Longrightarrow> c h \<le> d h"
  shows "\<forall>h. -a \<le> h \<and> h \<le> a \<longrightarrow> c h = d h"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "\<exists>h. -a \<le> h \<and> h \<le> a \<and> c h \<noteq> d h" by blast
  from cor_antichain_ii[OF assms(2,3) this] have "Sig a b c < Sig a b d" .
  moreover have "Sig a b c = Sig a b d" using assms(1) by (simp add: Sig_def)
  ultimately show False by simp
qed

text \<open>(iii): if Z(c) = Z(d), the signed sum of the wall weights vanishes.\<close>
corollary cor_antichain_iii:
  assumes "Zms a b c = Zms a b d"
  shows "(\<Sum>h \<in> {-a..a}. (a + 1 - \<bar>h\<bar>) * (Fsum b (d h) - Fsum b (c h))) = 0"
proof -
  have "Sig a b c = Sig a b d" using assms by (simp add: Sig_def)
  then show ?thesis using prop_wall_c[of a b d c] by simp
qed

section \<open>Proposition tau: the smallest element of Z(c)\<close>

definition clipb :: "int \<Rightarrow> int \<Rightarrow> int" where
  "clipb b v = min b (max (-b - 1) v)"

text \<open>g(n,m,eps) = (clip(n + h m + eps_h))_h; S_-(eps) = sum_{h=-a}^{0} eps_h.\<close>
definition gvec :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int" where
  "gvec b n m e h = clipb b (n + h * m + e h)"

definition Sminus :: "int \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int" where
  "Sminus a e = (\<Sum>h \<in> {-a..0}. e h)"

lemma fcl_mono: "u \<le> v \<Longrightarrow> fcl b u \<le> fcl b v"
  unfolding fcl_def by (intro min.mono max.mono order_refl) simp

lemma sum_reindex_neg:
  fixes G :: "int \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>l \<in> {0..a}. G (- l)) = (\<Sum>h \<in> {-a..0}. G h)"
  by (rule sum.reindex_bij_witness[where i = "\<lambda>h. - h" and j = "\<lambda>l. - l"]) auto

lemma tau_sum: "Hval a b c 0 0 = (\<Sum>h \<in> {-a..0}. fcl b (c h))"
proof -
  have "Hval a b c 0 0 = (\<Sum>l \<in> {0..a}. fcl b (c (- l)))" by (simp add: Hval_def)
  also have "\<dots> = (\<Sum>h \<in> {-a..0}. fcl b (c h))" by (rule sum_reindex_neg[of "\<lambda>h. fcl b (c h)"])
  finally show ?thesis .
qed

lemma Hval_ge:
  assumes mono: "\<And>h h'. -a \<le> h \<Longrightarrow> h \<le> h' \<Longrightarrow> h' \<le> a \<Longrightarrow> c h \<le> c h'"
    and "0 \<le> i" "i \<le> a" "0 \<le> j"
  shows "Hval a b c 0 0 \<le> Hval a b c i j"
  unfolding Hval_def
proof (rule sum_mono)
  fix l assume l: "l \<in> {0..a}"
  have "c (0 - l) \<le> c (i - l)" using mono[of "0 - l" "i - l"] l assms by simp
  then show "fcl b (c (0 - l) + 0) \<le> fcl b (c (i - l) + j)" using assms(4) by (intro fcl_mono) simp
qed

text \<open>Proposition tau, first part: for a non-decreasing c (every realisable vector is), the smallest element
  of Z(c) is tau(c) = H_0(0) = sum_{h=-a}^{0} f(c_h).\<close>
theorem prop_tau_min:
  assumes mono: "\<And>h h'. -a \<le> h \<Longrightarrow> h \<le> h' \<Longrightarrow> h' \<le> a \<Longrightarrow> c h \<le> c h'"
    and "0 \<le> a" "0 \<le> b"
  shows "Hval a b c 0 0 \<in># Zms a b c" and "\<forall>x \<in># Zms a b c. Hval a b c 0 0 \<le> x"
    and "Hval a b c 0 0 = (\<Sum>h \<in> {-a..0}. fcl b (c h))"
proof -
  show "Hval a b c 0 0 \<in># Zms a b c" using assms(2,3)
    by (simp add: Zms_def) (rule rev_image_eqI[of "(0::int, 0::int)"]; simp)
  show "\<forall>x \<in># Zms a b c. Hval a b c 0 0 \<le> x"
  proof
    fix x assume "x \<in># Zms a b c"
    then obtain i j where "x = Hval a b c i j" "0 \<le> i" "i \<le> a" "0 \<le> j" by (auto simp: Zms_def)
    then show "Hval a b c 0 0 \<le> x"
      using Hval_ge[where a = a and b = b and c = c and i = i and j = j, OF mono] by blast
  qed
  show "Hval a b c 0 0 = (\<Sum>h \<in> {-a..0}. fcl b (c h))" by (rule tau_sum)
qed

lemma sum_nonpos_int:
  fixes a :: int
  assumes "0 \<le> a"
  shows "2 * (\<Sum>h \<in> {-a..0}. h) = - (a * (a + 1))"
  using assms
proof (induct a rule: int_ge_induct)
  case base
  then show ?case by simp
next
  case (step k)
  have "{-(k + 1)..0} = insert (-(k + 1)) {-k..0}" using step by auto
  then have "(\<Sum>h \<in> {-(k + 1)..0}. h) = -(k + 1) + (\<Sum>h \<in> {-k..0}. h)" by simp
  then show ?case using step by (simp add: algebra_simps)
qed

text \<open>Proposition tau, formula: if -1 <= n + h m + eps_h <= b for -a <= h <= 0 then
  tau = (a+1)(n+1) - a(a+1)/2 m + S_-(eps); written with the factor 2 to stay in the integers.\<close>
theorem prop_tau_formula:
  assumes "0 \<le> a" "0 \<le> b" and cond: "\<And>h. -a \<le> h \<Longrightarrow> h \<le> 0 \<Longrightarrow> -1 \<le> n + h * m + e h \<and> n + h * m + e h \<le> b"
  shows "2 * (\<Sum>h \<in> {-a..0}. fcl b (gvec b n m e h)) = 2 * (a + 1) * (n + 1) - a * (a + 1) * m + 2 * Sminus a e"
proof -
  have e1: "\<And>h. h \<in> {-a..0} \<Longrightarrow> fcl b (gvec b n m e h) = (n + 1) + m * h + e h"
  proof -
    fix h assume h: "h \<in> {-a..0}"
    then have "-1 \<le> n + h * m + e h" "n + h * m + e h \<le> b" using cond by auto
    with assms(2) show "fcl b (gvec b n m e h) = (n + 1) + m * h + e h"
      unfolding fcl_def gvec_def clipb_def by (auto simp: min_def max_def algebra_simps)
  qed
  have "(\<Sum>h \<in> {-a..0}. fcl b (gvec b n m e h)) = (\<Sum>h \<in> {-a..0}. (n + 1) + m * h + e h)"
    by (rule sum.cong[OF refl]) (use e1 in auto)
  also have "\<dots> = (a + 1) * (n + 1) + m * (\<Sum>h \<in> {-a..0}. h) + Sminus a e"
    using assms(1) by (simp add: sum.distrib sum_distrib_left Sminus_def)
  finally have "2 * (\<Sum>h \<in> {-a..0}. fcl b (gvec b n m e h))
      = 2 * ((a + 1) * (n + 1)) + m * (2 * (\<Sum>h \<in> {-a..0}. h)) + 2 * Sminus a e" by (simp add: algebra_simps)
  then show ?thesis using sum_nonpos_int[OF assms(1)] by (simp add: algebra_simps)
qed

text \<open>The real form, as in the paper: tau = (a+1)(n+1) - a(a+1)/2 m + S_-(eps).\<close>
corollary prop_tau_formula_real:
  assumes "0 \<le> a" "0 \<le> b" and "\<And>h. -a \<le> h \<Longrightarrow> h \<le> 0 \<Longrightarrow> -1 \<le> n + h * m + e h \<and> n + h * m + e h \<le> b"
  shows "real_of_int (\<Sum>h \<in> {-a..0}. fcl b (gvec b n m e h))
         = (real_of_int a + 1) * (real_of_int n + 1) - real_of_int a * (real_of_int a + 1) / 2 * real_of_int m
           + real_of_int (Sminus a e)"
proof -
  have h: "2 * real_of_int (\<Sum>h \<in> {-a..0}. fcl b (gvec b n m e h))
       = 2 * (real_of_int a + 1) * (real_of_int n + 1) - real_of_int a * (real_of_int a + 1) * real_of_int m
         + 2 * real_of_int (Sminus a e)"
    using arg_cong[where f = real_of_int, OF prop_tau_formula[OF assms]] by simp
  have "real_of_int (\<Sum>h \<in> {-a..0}. fcl b (gvec b n m e h))
      = (2 * (real_of_int a + 1) * (real_of_int n + 1) - real_of_int a * (real_of_int a + 1) * real_of_int m
         + 2 * real_of_int (Sminus a e)) / 2"
    by (rule eq_divide_imp) (simp, use h in \<open>simp add: mult.commute\<close>)
  then show ?thesis by (simp add: field_simps)
qed

text \<open>Proposition tau, consequence: c = g(n,m,eps), d = g(n',m,eps') both satisfying the condition and
  Z(c) = Z(d) (both non-decreasing, as realisable vectors are) give (a+1)(n'-n) = S_-(eps) - S_-(eps') and
  S_-(eps) = S_-(eps') mod (a+1).\<close>
theorem prop_tau_cons:
  assumes "0 \<le> a" "0 \<le> b"
    and mc: "\<And>h h'. -a \<le> h \<Longrightarrow> h \<le> h' \<Longrightarrow> h' \<le> a \<Longrightarrow> gvec b n m e h \<le> gvec b n m e h'"
    and md: "\<And>h h'. -a \<le> h \<Longrightarrow> h \<le> h' \<Longrightarrow> h' \<le> a \<Longrightarrow> gvec b n' m e' h \<le> gvec b n' m e' h'"
    and cc: "\<And>h. -a \<le> h \<Longrightarrow> h \<le> 0 \<Longrightarrow> -1 \<le> n + h * m + e h \<and> n + h * m + e h \<le> b"
    and cd: "\<And>h. -a \<le> h \<Longrightarrow> h \<le> 0 \<Longrightarrow> -1 \<le> n' + h * m + e' h \<and> n' + h * m + e' h \<le> b"
    and Z: "Zms a b (gvec b n m e) = Zms a b (gvec b n' m e')"
  shows "(a + 1) * (n' - n) = Sminus a e - Sminus a e'"
    and "(Sminus a e) mod (a + 1) = (Sminus a e') mod (a + 1)"
proof -
  note T1 = prop_tau_min[where c = "gvec b n m e", OF mc assms(1,2)]
  note T2 = prop_tau_min[where c = "gvec b n' m e'", OF md assms(1,2)]
  have tc: "Hval a b (gvec b n m e) 0 0 \<in># Zms a b (gvec b n m e)" "\<forall>x \<in># Zms a b (gvec b n m e). Hval a b (gvec b n m e) 0 0 \<le> x"
    using T1(1,2) by blast+
  have td: "Hval a b (gvec b n' m e') 0 0 \<in># Zms a b (gvec b n' m e')" "\<forall>x \<in># Zms a b (gvec b n' m e'). Hval a b (gvec b n' m e') 0 0 \<le> x"
    using T2(1,2) by blast+
  have "Hval a b (gvec b n m e) 0 0 = Hval a b (gvec b n' m e') 0 0"
  proof -
    have a1: "Hval a b (gvec b n m e) 0 0 \<le> Hval a b (gvec b n' m e') 0 0"
      using tc(2) td(1) Z by simp
    have a2: "Hval a b (gvec b n' m e') 0 0 \<le> Hval a b (gvec b n m e) 0 0"
      using td(2) tc(1) Z by simp
    show ?thesis using a1 a2 by simp
  qed
  then have "(\<Sum>h \<in> {-a..0}. fcl b (gvec b n m e h)) = (\<Sum>h \<in> {-a..0}. fcl b (gvec b n' m e' h))"
    by (simp add: tau_sum)
  then have "2 * (a + 1) * (n + 1) - a * (a + 1) * m + 2 * Sminus a e
           = 2 * (a + 1) * (n' + 1) - a * (a + 1) * m + 2 * Sminus a e'"
    using prop_tau_formula[OF assms(1,2) cc] prop_tau_formula[OF assms(1,2) cd] by simp
  then show eq: "(a + 1) * (n' - n) = Sminus a e - Sminus a e'" by (simp add: algebra_simps)
  have "(a + 1) dvd (Sminus a e - Sminus a e')" using eq by (metis dvd_triv_left)
  then show "(Sminus a e) mod (a + 1) = (Sminus a e') mod (a + 1)" by (metis mod_eq_dvd_iff)
qed

section \<open>Lemma P: the vector of a point counts positions\<close>

text \<open>The vector of a point (Lambda, theta): c_h = clip(floor(Lambda + h theta)), and the multiset P of the positions
  i theta + j (0 <= i <= a, 0 <= j <= b).\<close>
definition cpt :: "int \<Rightarrow> real \<Rightarrow> real \<Rightarrow> int \<Rightarrow> int" where
  "cpt b Lam th h = clipb b \<lfloor>Lam + real_of_int h * th\<rfloor>"

definition Pms :: "int \<Rightarrow> int \<Rightarrow> real \<Rightarrow> real multiset" where
  "Pms a b th = image_mset (\<lambda>p. real_of_int (fst p) * th + real_of_int (snd p)) (mset_set ({0..a} \<times> {0..b}))"

text \<open>The vector of a point is non-decreasing and has its coordinates in [-b-1, b]: the two properties of
  realisable vectors used above.\<close>
lemma cpt_mono:
  assumes "0 \<le> th" "h \<le> h'"
  shows "cpt b Lam th h \<le> cpt b Lam th h'"
proof -
  have "Lam + real_of_int h * th \<le> Lam + real_of_int h' * th" using assms by (simp add: mult_right_mono)
  then have "\<lfloor>Lam + real_of_int h * th\<rfloor> \<le> \<lfloor>Lam + real_of_int h' * th\<rfloor>" by (rule floor_mono)
  then show ?thesis unfolding cpt_def clipb_def by (simp add: min.mono max.mono)
qed

lemma cpt_range: "0 \<le> b \<Longrightarrow> -b - 1 \<le> cpt b Lam th h \<and> cpt b Lam th h \<le> b"
  unfolding cpt_def clipb_def by (simp add: min_def max_def)

lemma fcl_clip:
  assumes "0 \<le> j'" "j' \<le> b"
  shows "fcl b (clipb b k + j') = max 0 (min b (k + j') + 1)"
  using assms unfolding fcl_def clipb_def by (auto simp: min_def max_def)

lemma count_floor:
  fixes x :: real
  assumes x: "x \<notin> \<int>" and j': "0 \<le> j'" "j' \<le> b"
  shows "int (card {j \<in> {0..b}. real_of_int j < x + real_of_int j'}) = fcl b (clipb b \<lfloor>x\<rfloor> + j')"
proof -
  have key: "\<And>j. real_of_int j < x + real_of_int j' \<longleftrightarrow> j \<le> \<lfloor>x\<rfloor> + j'"
  proof -
    fix j :: int
    have a1: "j - j' \<le> \<lfloor>x\<rfloor> \<longleftrightarrow> real_of_int (j - j') \<le> x" by (rule le_floor_iff)
    have a2: "real_of_int (j - j') \<noteq> x" using x by (metis Ints_of_int)
    show "real_of_int j < x + real_of_int j' \<longleftrightarrow> j \<le> \<lfloor>x\<rfloor> + j'"
    proof
      assume h: "real_of_int j < x + real_of_int j'"
      then have "real_of_int (j - j') \<le> x" by simp
      then have "j - j' \<le> \<lfloor>x\<rfloor>" using a1 by simp
      then show "j \<le> \<lfloor>x\<rfloor> + j'" by simp
    next
      assume h: "j \<le> \<lfloor>x\<rfloor> + j'"
      then have "j - j' \<le> \<lfloor>x\<rfloor>" by simp
      then have "real_of_int (j - j') \<le> x" using a1 by simp
      then have "real_of_int (j - j') < x" using a2 by simp
      then show "real_of_int j < x + real_of_int j'" by simp
    qed
  qed
  have S: "{j \<in> {0..b}. real_of_int j < x + real_of_int j'} = {0..min b (\<lfloor>x\<rfloor> + j')}"
    by (rule set_eqI) (simp add: key)
  have "int (card {0..min b (\<lfloor>x\<rfloor> + j')}) = max 0 (min b (\<lfloor>x\<rfloor> + j') + 1)" by simp
  then show ?thesis using S fcl_clip[OF j'] by simp
qed

text \<open>Lemma P: if Lambda + h theta is not an integer for |h| <= a, then
  H_{i'}(j') = #{p in P : p < Lambda + i' theta + j'}.\<close>
theorem lem_P_count:
  fixes Lam th :: real
  assumes noint: "\<And>h. -a \<le> h \<Longrightarrow> h \<le> a \<Longrightarrow> Lam + real_of_int h * th \<notin> \<int>"
    and i': "0 \<le> i'" "i' \<le> a" and j': "0 \<le> j'" "j' \<le> b"
  shows "Hval a b (cpt b Lam th) i' j'
         = int (size (filter_mset (\<lambda>p. p < Lam + real_of_int i' * th + real_of_int j') (Pms a b th)))"
proof -
  let ?Q = "\<lambda>p::int \<times> int. real_of_int (fst p) * th + real_of_int (snd p) < Lam + real_of_int i' * th + real_of_int j'"
  have "size (filter_mset (\<lambda>p. p < Lam + real_of_int i' * th + real_of_int j') (Pms a b th))
        = card {p \<in> {0..a} \<times> {0..b}. ?Q p}"
    by (simp add: Pms_def filter_mset_image_mset filter_mset_mset_set o_def)
  moreover have "int (card {p \<in> {0..a} \<times> {0..b}. ?Q p}) = (\<Sum>p \<in> {0..a} \<times> {0..b}. if ?Q p then (1::int) else 0)"
    by (subst sum.inter_filter[symmetric]) simp_all
  ultimately have "int (size (filter_mset (\<lambda>p. p < Lam + real_of_int i' * th + real_of_int j') (Pms a b th)))
        = (\<Sum>p \<in> {0..a} \<times> {0..b}. if ?Q p then 1 else 0)"
    by simp
  also have "\<dots> = (\<Sum>l \<in> {0..a}. \<Sum>j \<in> {0..b}. if ?Q (l, j) then (1::int) else 0)"
    by (simp add: sum.cartesian_product case_prod_unfold)
  also have "\<dots> = (\<Sum>l \<in> {0..a}. fcl b (cpt b Lam th (i' - l) + j'))"
  proof (rule sum.cong[OF refl])
    fix l assume l: "l \<in> {0..a}"
    let ?x = "Lam + real_of_int (i' - l) * th"
    have nx: "?x \<notin> \<int>" using noint[of "i' - l"] l i' by simp
    have "(\<Sum>j \<in> {0..b}. if ?Q (l, j) then (1::int) else 0)
        = int (card {j \<in> {0..b}. real_of_int j < ?x + real_of_int j'})"
    proof -
      have "{j \<in> {0..b}. ?Q (l, j)} = {j \<in> {0..b}. real_of_int j < ?x + real_of_int j'}"
        by (rule set_eqI) (simp add: algebra_simps)
      moreover have "(\<Sum>j \<in> {0..b}. if ?Q (l, j) then (1::int) else 0) = int (card {j \<in> {0..b}. ?Q (l, j)})"
        by (subst sum.inter_filter[symmetric]) simp_all
      ultimately show ?thesis by simp
    qed
    also have "\<dots> = fcl b (clipb b \<lfloor>?x\<rfloor> + j')" by (rule count_floor[OF nx j'])
    finally show "(\<Sum>j \<in> {0..b}. if ?Q (l, j) then (1::int) else 0) = fcl b (cpt b Lam th (i' - l) + j')"
      by (simp add: cpt_def)
  qed
  finally show ?thesis by (simp add: Hval_def)
qed

text \<open>The multiset form: Z(c) is the multiset of the counts #{p in P : p < p0 + Lambda}, p0 in P.\<close>
theorem lem_P:
  fixes Lam th :: real
  assumes noint: "\<And>h. -a \<le> h \<Longrightarrow> h \<le> a \<Longrightarrow> Lam + real_of_int h * th \<notin> \<int>"
  shows "Zms a b (cpt b Lam th)
         = image_mset (\<lambda>p0. int (size (filter_mset (\<lambda>p. p < p0 + Lam) (Pms a b th)))) (Pms a b th)"
proof -
  have "Zms a b (cpt b Lam th)
      = image_mset (\<lambda>p. int (size (filter_mset (\<lambda>q. q < Lam + real_of_int (fst p) * th + real_of_int (snd p)) (Pms a b th))))
                   (mset_set ({0..a} \<times> {0..b}))"
    unfolding Zms_def
    by (rule image_mset_cong) (use lem_P_count[OF noint] in auto)
  also have "\<dots> = image_mset (\<lambda>p0. int (size (filter_mset (\<lambda>p. p < p0 + Lam) (Pms a b th)))) (Pms a b th)"
    by (simp add: Pms_def image_mset.compositionality o_def add.commute add.left_commute)
  finally show ?thesis .
qed

section \<open>The counting part of Lemma amb, Proposition burnside and Theorem a3-families\<close>

text \<open>X is the finite set of realisable vectors (cells), w : X -> words (the word of a cell, i.e. Z(c)).
  R = |X|, W = |w X|, E = R - W, and Amb = number of cells whose word is shared.\<close>
definition Ecount :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> int" where
  "Ecount X w = int (card X) - int (card (w ` X))"

definition Amb :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat" where
  "Amb X w = card {x \<in> X. \<exists>y \<in> X. y \<noteq> x \<and> w y = w x}"

lemma fibre_card_pos:
  assumes "finite X" "y \<in> w ` X"
  shows "1 \<le> card {x \<in> X. w x = y}"
proof -
  obtain x where "x \<in> X" "w x = y" using assms(2) by auto
  then have "{x \<in> X. w x = y} \<noteq> {}" by auto
  moreover have "finite {x \<in> X. w x = y}" using assms(1) by simp
  ultimately have "0 < card {x \<in> X. w x = y}" by (simp add: card_gt_0_iff)
  then show ?thesis by simp
qed

text \<open>Lemma amb: E <= Amb <= 2E.\<close>
theorem lem_amb:
  assumes "finite X"
  shows "Ecount X w \<le> int (Amb X w)" and "int (Amb X w) \<le> 2 * Ecount X w"
proof -
  let ?fb = "\<lambda>y. {x \<in> X. w x = y}"
  let ?Sh = "{x \<in> X. \<exists>y \<in> X. y \<noteq> x \<and> w y = w x}"
  have fin: "finite (w ` X)" using assms by simp
  have c1: "int (card X) = (\<Sum>y \<in> w ` X. int (card (?fb y)))"
  proof -
    have "card X = (\<Sum>y \<in> w ` X. card (?fb y))"
    proof -
      have "(\<Sum>y \<in> w ` X. \<Sum>x \<in> {x \<in> X. w x = y}. (1::nat)) = (\<Sum>x \<in> X. (1::nat))"
        by (rule sum.group[OF assms fin order_refl])
      then show ?thesis by simp
    qed
    then show ?thesis by simp
  qed
  have c2: "int (card (w ` X)) = (\<Sum>y \<in> w ` X. (1::int))" by simp
  have c3: "int (Amb X w) = (\<Sum>y \<in> w ` X. int (card {x \<in> ?Sh. w x = y}))"
  proof -
    have fSh: "finite ?Sh" using assms by simp
    have "card ?Sh = (\<Sum>y \<in> w ` X. card {x \<in> ?Sh. w x = y})"
    proof -
      have sub: "w ` ?Sh \<subseteq> w ` X" by auto
      have "(\<Sum>y \<in> w ` X. \<Sum>x \<in> {x \<in> ?Sh. w x = y}. (1::nat)) = (\<Sum>x \<in> ?Sh. (1::nat))"
        by (rule sum.group[OF fSh fin sub])
      then show ?thesis by simp
    qed
    then show ?thesis by (simp add: Amb_def)
  qed
  have shared: "\<And>y. y \<in> w ` X \<Longrightarrow> card {x \<in> ?Sh. w x = y} = (if 2 \<le> card (?fb y) then card (?fb y) else 0)"
  proof -
    fix y assume y: "y \<in> w ` X"
    have fin_fb: "finite (?fb y)" using assms by simp
    show "card {x \<in> ?Sh. w x = y} = (if 2 \<le> card (?fb y) then card (?fb y) else 0)"
    proof (cases "2 \<le> card (?fb y)")
      case True
      have "{x \<in> ?Sh. w x = y} = ?fb y"
      proof (rule set_eqI)
        fix x
        show "x \<in> {x \<in> ?Sh. w x = y} \<longleftrightarrow> x \<in> ?fb y"
        proof
          assume "x \<in> {x \<in> ?Sh. w x = y}" then show "x \<in> ?fb y" by simp
        next
          assume xin: "x \<in> ?fb y"
          have "card (?fb y - {x}) = card (?fb y) - 1" using xin fin_fb by (simp add: card_Diff_singleton)
          then have "0 < card (?fb y - {x})" using True by simp
          then have "?fb y - {x} \<noteq> {}" by (auto simp: card_gt_0_iff)
          then obtain z where z: "z \<in> ?fb y - {x}" by blast
          then show "x \<in> {x \<in> ?Sh. w x = y}" using xin by auto
        qed
      qed
      then show ?thesis using True by simp
    next
      case False
      have "{x \<in> ?Sh. w x = y} = {}"
      proof (rule equals0I)
        fix x assume xs: "x \<in> {x \<in> ?Sh. w x = y}"
        then obtain z where z: "z \<in> X" "z \<noteq> x" "w z = w x" "x \<in> X" "w x = y" by auto
        have "{x, z} \<subseteq> ?fb y" using z by auto
        then have "card {x, z} \<le> card (?fb y)" by (rule card_mono[OF fin_fb])
        moreover have "card {x, z} = 2" using z by simp
        ultimately show False using False by simp
      qed
      then have "card {x \<in> ?Sh. w x = y} = 0" by (rule arg_cong[where f = card, THEN trans]) simp
      then show ?thesis using False by simp
    qed
  qed
  have Ec: "Ecount X w = (\<Sum>y \<in> w ` X. int (card (?fb y)) - 1)"
    unfolding Ecount_def using c1 by (simp add: sum_subtractf)
  have Ac: "int (Amb X w) = (\<Sum>y \<in> w ` X. if 2 \<le> card (?fb y) then int (card (?fb y)) else 0)"
  proof -
    have "(\<Sum>y \<in> w ` X. int (card {x \<in> ?Sh. w x = y}))
        = (\<Sum>y \<in> w ` X. if 2 \<le> card (?fb y) then int (card (?fb y)) else 0)"
    proof (rule sum.cong[OF refl])
      fix y assume y: "y \<in> w ` X"
      have s: "card {x \<in> ?Sh. w x = y} = (if 2 \<le> card (?fb y) then card (?fb y) else 0)" by (rule shared[OF y])
      show "int (card {x \<in> ?Sh. w x = y}) = (if 2 \<le> card (?fb y) then int (card (?fb y)) else 0)"
        by (subst s) (cases "2 \<le> card (?fb y)"; simp)
    qed
    then show ?thesis using c3 by simp
  qed
  have pt: "\<And>y. y \<in> w ` X \<Longrightarrow>
      int (card (?fb y)) - 1 \<le> (if 2 \<le> card (?fb y) then int (card (?fb y)) else 0)
      \<and> (if 2 \<le> card (?fb y) then int (card (?fb y)) else 0) \<le> 2 * (int (card (?fb y)) - 1)"
  proof -
    fix y assume y: "y \<in> w ` X"
    have p: "1 \<le> card (?fb y)" by (rule fibre_card_pos[OF assms y])
    show "int (card (?fb y)) - 1 \<le> (if 2 \<le> card (?fb y) then int (card (?fb y)) else 0)
      \<and> (if 2 \<le> card (?fb y) then int (card (?fb y)) else 0) \<le> 2 * (int (card (?fb y)) - 1)"
    proof (cases "2 \<le> card (?fb y)")
      case True then show ?thesis by simp
    next
      case False
      then have "card (?fb y) = 1" using p by arith
      then show ?thesis by simp
    qed
  qed
  show "Ecount X w \<le> int (Amb X w)"
    unfolding Ec Ac by (rule sum_mono) (use pt in blast)
  show "int (Amb X w) \<le> 2 * Ecount X w"
    unfolding Ec Ac sum_distrib_left by (rule sum_mono) (use pt in blast)
qed

text \<open>Proposition burnside, the counting part: sigma permutes X (an involution), preserves words, and has
  exactly f fixed points; then 2 W <= R + f.  For a = b the paper has f = 2a+1 and
  W(a,a) <= (R(a,a) + 2a + 1)/2.  (That sigma permutes the cells, preserves words and fixes exactly
  2a+1 cells is the geometric part of the proof and is taken as hypothesis here.)\<close>
theorem prop_burnside:
  assumes fin: "finite X" and sig: "\<And>x. x \<in> X \<Longrightarrow> sg x \<in> X" and inv: "\<And>x. x \<in> X \<Longrightarrow> sg (sg x) = x"
    and pres: "\<And>x. x \<in> X \<Longrightarrow> w (sg x) = w x" and nfix: "card {x \<in> X. sg x = x} = f"
  shows "2 * card (w ` X) \<le> card X + f"
proof -
  let ?fb = "\<lambda>y. {x \<in> X. w x = y}"
  let ?F = "{x \<in> X. sg x = x}"
  have finw: "finite (w ` X)" using fin by simp
  have finF: "finite ?F" using fin by simp
  have e1: "card X = (\<Sum>y \<in> w ` X. card (?fb y))"
  proof -
    have "(\<Sum>y \<in> w ` X. \<Sum>x \<in> {x \<in> X. w x = y}. (1::nat)) = (\<Sum>x \<in> X. (1::nat))"
      by (rule sum.group[OF fin finw order_refl])
    then show ?thesis by simp
  qed
  have e2: "card ?F = (\<Sum>y \<in> w ` X. card {x \<in> ?F. w x = y})"
  proof -
    have sub: "w ` ?F \<subseteq> w ` X" by auto
    have "(\<Sum>y \<in> w ` X. \<Sum>x \<in> {x \<in> ?F. w x = y}. (1::nat)) = (\<Sum>x \<in> ?F. (1::nat))"
      by (rule sum.group[OF finF finw sub])
    then show ?thesis by simp
  qed
  have pt: "\<And>y. y \<in> w ` X \<Longrightarrow> 2 \<le> card (?fb y) + card {x \<in> ?F. w x = y}"
  proof -
    fix y assume y: "y \<in> w ` X"
    have fin_fb: "finite (?fb y)" using fin by simp
    show "2 \<le> card (?fb y) + card {x \<in> ?F. w x = y}"
    proof (cases "2 \<le> card (?fb y)")
      case True then show ?thesis by simp
    next
      case False
      have pos: "1 \<le> card (?fb y)" by (rule fibre_card_pos[OF fin y])
      then have one: "card (?fb y) = 1" using False by simp
      then obtain x where fb: "?fb y = {x}" by (auto simp: card_1_singleton_iff)
      then have xin: "x \<in> X" "w x = y" by auto
      have "sg x \<in> ?fb y" using sig[OF xin(1)] pres[OF xin(1)] xin(2) by simp
      then have "sg x = x" using fb by simp
      then have "x \<in> {x \<in> ?F. w x = y}" using xin by simp
      then have ne: "{x \<in> ?F. w x = y} \<noteq> {}" by auto
      have "finite {x \<in> ?F. w x = y}" by (rule finite_subset[OF _ fin]) auto
      with ne have "0 < card {x \<in> ?F. w x = y}" by (simp add: card_gt_0_iff)
      then show ?thesis using one by simp
    qed
  qed
  have "2 * card (w ` X) = (\<Sum>y \<in> w ` X. 2)" by simp
  also have "\<dots> \<le> (\<Sum>y \<in> w ` X. card (?fb y) + card {x \<in> ?F. w x = y})" by (rule sum_mono) (use pt in auto)
  also have "\<dots> = card X + card ?F" by (simp add: sum.distrib e1 e2)
  finally show ?thesis using nfix by simp
qed

text \<open>Theorem a3-families, the counting part: if each listed set has one word, then
  E >= |U| - |pi_0(G)|, where U is the union of the listed sets and pi_0(G) the set of connected
  components of the graph on U with an edge between two vectors whenever they lie in a common listed set.\<close>
definition Edge :: "'a set set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "Edge L x y = (\<exists>S \<in> L. x \<in> S \<and> y \<in> S)"

definition Comps :: "'a set set \<Rightarrow> 'a set set" where
  "Comps L = (\<Union>x \<in> \<Union>L. {{y. (Edge L)\<^sup>*\<^sup>* x y}})"

theorem thm_a3_families:
  assumes fin: "finite X" and sub: "\<And>S. S \<in> L \<Longrightarrow> S \<subseteq> X"
    and one: "\<And>S x y. S \<in> L \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> w x = w y"
  shows "int (card (\<Union>L)) - int (card (Comps L)) \<le> Ecount X w"
proof -
  let ?U = "\<Union>L"
  have UX: "?U \<subseteq> X" using sub by auto
  have finU: "finite ?U" by (rule finite_subset[OF UX fin])
  have wcomp: "\<And>x y. (Edge L)\<^sup>*\<^sup>* x y \<Longrightarrow> w x = w y"
  proof -
    fix x y assume "(Edge L)\<^sup>*\<^sup>* x y"
    then show "w x = w y"
    proof (induction rule: rtranclp_induct)
      case base then show ?case by simp
    next
      case (step y z)
      then show ?case using one by (auto simp: Edge_def)
    qed
  qed
  have finC: "finite (Comps L)"
  proof -
    have "Comps L \<subseteq> Pow ?U"
    proof
      fix C assume "C \<in> Comps L"
      then obtain x where x: "x \<in> ?U" "C = {y. (Edge L)\<^sup>*\<^sup>* x y}" by (auto simp: Comps_def)
      have "C \<subseteq> ?U"
      proof
        fix y assume "y \<in> C"
        then have "(Edge L)\<^sup>*\<^sup>* x y" using x by simp
        then show "y \<in> ?U"
        proof (cases rule: rtranclp.cases)
          case rtrancl_refl then show ?thesis using x by simp
        next
          case (rtrancl_into_rtrancl b)
          then show ?thesis by (auto simp: Edge_def)
        qed
      qed
      then show "C \<in> Pow ?U" by simp
    qed
    moreover have "finite (Pow ?U)" using finU by simp
    ultimately show ?thesis by (rule finite_subset)
  qed
  text \<open>The word is constant on each component, so the number of words on U is at most the number of components.\<close>
  have wU: "card (w ` ?U) \<le> card (Comps L)"
  proof -
    let ?phi = "\<lambda>C. w (SOME x. x \<in> C)"
    have "w ` ?U \<subseteq> ?phi ` Comps L"
    proof
      fix v assume "v \<in> w ` ?U"
      then obtain x where x: "x \<in> ?U" "v = w x" by auto
      let ?C = "{y. (Edge L)\<^sup>*\<^sup>* x y}"
      have Cin: "?C \<in> Comps L" using x unfolding Comps_def by auto
      have "x \<in> ?C" by simp
      then have "(SOME z. z \<in> ?C) \<in> ?C" by (rule someI)
      then have "w (SOME z. z \<in> ?C) = w x" using wcomp by auto
      then show "v \<in> ?phi ` Comps L" using Cin x(2) by force
    qed
    then have "card (w ` ?U) \<le> card (?phi ` Comps L)" using finC by (intro card_mono) simp_all
    also have "\<dots> \<le> card (Comps L)" by (rule card_image_le[OF finC])
    finally show ?thesis .
  qed
  text \<open>E >= |U| - |w U|: the vectors outside U add at most as many words as vectors.\<close>
  have "card (w ` X) \<le> card (w ` ?U) + card (X - ?U)"
  proof -
    have sub: "w ` X \<subseteq> w ` ?U \<union> w ` (X - ?U)" using UX by auto
    have fin2: "finite (w ` ?U \<union> w ` (X - ?U))" using fin finU by simp
    have "card (w ` X) \<le> card (w ` ?U \<union> w ` (X - ?U))" by (rule card_mono[OF fin2 sub])
    also have "\<dots> \<le> card (w ` ?U) + card (w ` (X - ?U))" by (rule card_Un_le)
    also have "\<dots> \<le> card (w ` ?U) + card (X - ?U)" using fin by (simp add: card_image_le)
    finally show ?thesis .
  qed
  moreover have "card X = card ?U + card (X - ?U)"
    using card_Diff_subset[OF finU UX] card_mono[OF fin UX] by arith
  ultimately show ?thesis using wU unfolding Ecount_def by linarith
qed

end
