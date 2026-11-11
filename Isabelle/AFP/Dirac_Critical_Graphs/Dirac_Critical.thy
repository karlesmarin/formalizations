(*  Title:      Dirac_Critical.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín (the proofs). All rights reserved.
    Statement:  definitions and statement transcribed from google-deepmind/formal-conjectures
                (Apache License 2.0); they are not ours.
    License:    BSD
*)

theory Dirac_Critical
  imports Main
begin

section \<open>Dirac's bound for critical graphs: $f_6(4n+2) \geq 4n^2+8n+3$\<close>

text \<open>Mirrors @{text erdos_917.variants.dirac} of google-deepmind/formal-conjectures (ErdosProblems/917.lean).
  Graphs live on the vertex set @{text "{..<N}"} as adjacency relations.  Colourings, chromatic number,
  vertex-critical and edge-critical follow Mathlib / FormalConjecturesForMathlib: the chromatic number of
  the graph after deleting a vertex (induced subgraph on the remaining vertices) or an edge must be smaller.\<close>

subsection \<open>Definitions\<close>

definition simple :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "simple n G \<longleftrightarrow> (\<forall>i<n. \<forall>j<n. G i j \<longleftrightarrow> G j i) \<and> (\<forall>i<n. \<not> G i i)"

definition irr :: "nat set \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "irr S G \<longleftrightarrow> (\<forall>u\<in>S. \<not> G u u)"

definition col_on :: "nat set \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "col_on S k G \<longleftrightarrow> (\<exists>c. (\<forall>v\<in>S. c v < k) \<and> (\<forall>u\<in>S. \<forall>v\<in>S. G u v \<longrightarrow> c u \<noteq> c v))"

definition chi :: "nat set \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat" where
  "chi S G = (LEAST k. col_on S k G)"

definition del_edge :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "del_edge a b G u v \<longleftrightarrow> G u v \<and> \<not> ((u = a \<and> v = b) \<or> (u = b \<and> v = a))"

definition edges :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat set set" where
  "edges N G = {{i, j} | i j. i < N \<and> j < N \<and> G i j}"

definition crit :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "crit k N G \<longleftrightarrow> simple N G \<and> chi {..<N} G = k \<and>
     (\<forall>v<N. chi ({..<N} - {v}) G < k) \<and>
     (\<forall>a<N. \<forall>b<N. G a b \<longrightarrow> chi {..<N} (del_edge a b G) < k)"

definition f :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "f k N = Sup {m. \<exists>G. crit k N G \<and> card (edges N G) = m}"

subsection \<open>Chromatic number\<close>

lemma col_mono: "col_on S k G \<Longrightarrow> k \<le> k' \<Longrightarrow> col_on S k' G"
  unfolding col_on_def by (metis order_less_le_trans)

lemma col_on_sub: "(\<forall>u\<in>S. \<forall>w\<in>S. G u w \<longrightarrow> G' u w) \<Longrightarrow> col_on S k G' \<Longrightarrow> col_on S k G"
  unfolding col_on_def by blast

lemma col_exists:
  assumes "S \<subseteq> {..<N}" "irr S G"
  shows "col_on S N G"
  unfolding col_on_def
proof (intro exI[of _ "\<lambda>v. v"] conjI ballI impI)
  fix v assume "v \<in> S"
  thus "v < N" using assms(1) by auto
next
  fix u v assume "u \<in> S" "v \<in> S" "G u v"
  thus "u \<noteq> v" using assms(2) unfolding irr_def by auto
qed

lemma chi_le_iff:
  assumes "S \<subseteq> {..<N}" "irr S G"
  shows "chi S G \<le> k \<longleftrightarrow> col_on S k G"
proof
  have ex: "\<exists>k. col_on S k G" using col_exists[OF assms(1) assms(2)] by blast
  assume le: "chi S G \<le> k"
  have "col_on S (chi S G) G" unfolding chi_def by (rule LeastI_ex[OF ex])
  thus "col_on S k G" using le by (rule col_mono)
next
  assume "col_on S k G"
  thus "chi S G \<le> k" unfolding chi_def by (rule Least_le)
qed

lemma chi_lt6:
  assumes "S \<subseteq> {..<N}" "irr S G"
  shows "chi S G < 6 \<longleftrightarrow> col_on S 5 G"
  using chi_le_iff[OF assms(1) assms(2), of 5] by auto

lemma chi_eq6:
  assumes "S \<subseteq> {..<N}" "irr S G" "col_on S 6 G" "\<not> col_on S 5 G"
  shows "chi S G = 6"
  using chi_le_iff[OF assms(1,2), of 6] chi_le_iff[OF assms(1,2), of 5] assms(3,4) by auto

lemma del_edge_irr: "irr S G \<Longrightarrow> irr S (del_edge a b G)"
  unfolding del_edge_def irr_def by blast

lemma del_edge_sym: "del_edge a b G = del_edge b a G"
  unfolding del_edge_def by auto

subsection \<open>Cycles\<close>

definition cyc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "cyc M i j \<longleftrightarrow> i < M \<and> j < M \<and> (j = (i + 1) mod M \<or> i = (j + 1) mod M)"

lemma cyc_sym: "cyc M i j \<Longrightarrow> cyc M j i"
  unfolding cyc_def by auto

lemma mod1: "(i::nat) < M \<Longrightarrow> (i + 1) mod M = (if i + 1 < M then i + 1 else 0)"
proof (cases "i + 1 < M")
  case True
  hence "(i + 1) mod M = i + 1" by (rule mod_less)
  thus "i < M \<Longrightarrow> ?thesis" using True by simp
next
  case False
  assume "i < M"
  with False have "i + 1 = M" by arith
  thus ?thesis by simp
qed

lemma cyc_irrefl:
  assumes "3 \<le> M" shows "\<not> cyc M i i"
proof
  assume c: "cyc M i i"
  hence lt: "i < M" and eq: "i = (i + 1) mod M" unfolding cyc_def by auto
  show False
  proof (cases "i + 1 < M")
    case True
    hence "(i + 1) mod M = i + 1" by (rule mod_less)
    thus False using eq by simp
  next
    case False
    hence "(i + 1) mod M = 0" using mod1[OF lt] by simp
    hence "i = 0" using eq by simp
    thus False using False assms by arith
  qed
qed

lemma cyc_two:
  fixes M i i' :: nat
  assumes "3 \<le> M" "i < M" "i' < M" "i = (i' + 1) mod M" "i' = (i + 1) mod M"
  shows False
proof -
  have a: "i = (if i' + 1 < M then i' + 1 else 0)" using mod1[OF assms(3)] assms(4) by simp
  have b: "i' = (if i + 1 < M then i + 1 else 0)" using mod1[OF assms(2)] assms(5) by simp
  show False
  proof (cases "i' + 1 < M")
    case t1: True
    hence ia: "i = i' + 1" using a by simp
    show False
    proof (cases "i + 1 < M")
      case True
      hence "i' = i + 1" using b by simp
      thus False using ia by arith
    next
      case False
      hence "i' = 0" using b by simp
      thus False using ia False assms(1) by arith
    qed
  next
    case f1: False
    hence ia: "i = 0" using a by simp
    show False
    proof (cases "i + 1 < M")
      case True
      hence "i' = i + 1" using b by simp
      thus False using ia f1 assms(1) by arith
    next
      case False
      thus False using ia assms(1) by arith
    qed
  qed
qed

subsection \<open>Rotations of the cycle\<close>

definition rot :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "rot M s i = (i + s) mod M"

lemma rot_lt: "0 < M \<Longrightarrow> rot M s i < M"
  unfolding rot_def by simp

lemma rot_eq:
  assumes "i < M" "s < M"
  shows "rot M s i = (if i + s < M then i + s else i + s - M)"
proof (cases "i + s < M")
  case True thus ?thesis by (simp add: rot_def mod_less)
next
  case False
  have a: "i + s = (i + s - M) + M" using False by arith
  have b: "i + s - M < M" using assms by arith
  have "(i + s) mod M = (i + s - M) mod M" by (metis a mod_add_self2)
  also have "\<dots> = i + s - M" using b by (simp add: mod_less)
  finally show ?thesis using False by (simp add: rot_def)
qed

lemma rot_inj:
  assumes "i < M" "j < M" "s < M" "rot M s i = rot M s j"
  shows "i = j"
proof -
  have "(if i + s < M then i + s else i + s - M) = (if j + s < M then j + s else j + s - M)"
    using rot_eq[OF assms(1,3)] rot_eq[OF assms(2,3)] assms(4) by metis
  note e = this
  show ?thesis
  proof (cases "i + s < M")
    case t1: True
    show ?thesis
    proof (cases "j + s < M")
      case True with t1 e show ?thesis by simp
    next
      case False
      with t1 e have "i + s = j + s - M" by simp
      thus ?thesis using False assms(1,2) by arith
    qed
  next
    case f1: False
    show ?thesis
    proof (cases "j + s < M")
      case True
      with f1 e have "i + s - M = j + s" by simp
      thus ?thesis using f1 assms(1,2) by arith
    next
      case False
      with f1 e have "i + s - M = j + s - M" by simp
      thus ?thesis using f1 False assms(1,2) by arith
    qed
  qed
qed

lemma rot_cyc:
  assumes "cyc M i j"
  shows "cyc M (rot M s i) (rot M s j)"
proof -
  have M: "0 < M" using assms unfolding cyc_def by auto
  have key: "rot M s y = (rot M s x + 1) mod M" if "y = (x + 1) mod M" for x y
  proof -
    from that have h1: "(y + s) mod M = (x + 1 + s) mod M" by (simp only: mod_add_left_eq)
    have h2: "((x + s) mod M + 1) mod M = (x + s + 1) mod M" by (rule mod_add_left_eq)
    have c: "x + 1 + s = x + s + 1" by arith
    show "rot M s y = (rot M s x + 1) mod M" unfolding rot_def by (metis h1 h2 c)
  qed
  from assms have "j = (i + 1) mod M \<or> i = (j + 1) mod M" unfolding cyc_def by auto
  thus ?thesis unfolding cyc_def using rot_lt[OF M] key by metis
qed

subsection \<open>Colourings of the odd cycle\<close>

definition b3 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "b3 M i = (if i = M - 1 then 2 else i mod 2)"

definition e :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "e M a i = (rot M (M - 1 - a) i) mod 2"

definition h :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "h M p i = b3 M (rot M (M - 1 - p) i)"

locale oddc =
  fixes M :: nat
  assumes hodd: "M mod 2 = 1" and hge3: "3 \<le> M"
begin

lemma M0: "0 < M" using hge3 by arith

lemma b3_lt: "b3 M i < 3"
  unfolding b3_def by auto

lemma b3_step: "i < M \<Longrightarrow> b3 M i \<noteq> b3 M ((i + 1) mod M)"
proof -
  assume i: "i < M"
  show ?thesis
  proof (cases "i + 1 < M")
    case True
    hence m: "(i + 1) mod M = i + 1" by (rule mod_less)
    have n1: "i \<noteq> M - 1" using True by arith
    have bi: "b3 M i = i mod 2" using n1 unfolding b3_def by simp
    show ?thesis
    proof (cases "i + 1 = M - 1")
      case True
      hence "b3 M (i + 1) = 2" unfolding b3_def by simp
      thus ?thesis unfolding m bi by arith
    next
      case False
      hence "b3 M (i + 1) = (i + 1) mod 2" unfolding b3_def by simp
      thus ?thesis unfolding m bi by arith
    qed
  next
    case False
    hence m: "(i + 1) mod M = 0" using mod1[OF i] by simp
    have e1: "i = M - 1" using False i by arith
    have "b3 M i = 2" using e1 unfolding b3_def by simp
    moreover have "b3 M 0 = 0" using hge3 unfolding b3_def by simp
    ultimately show ?thesis unfolding m by simp
  qed
qed

lemma b3_valid: "cyc M i j \<Longrightarrow> b3 M i \<noteq> b3 M j"
  unfolding cyc_def using b3_step by metis

lemma pc_valid:
  assumes "cyc M i j" "\<not> (i = M - 1 \<and> j = 0)" "\<not> (i = 0 \<and> j = M - 1)"
  shows "i mod 2 \<noteq> j mod 2"
proof -
  from assms(1) have lt: "i < M" "j < M" and d: "j = (i + 1) mod M \<or> i = (j + 1) mod M"
    unfolding cyc_def by auto
  from d show ?thesis
  proof
    assume dj: "j = (i + 1) mod M"
    show ?thesis
    proof (cases "i + 1 < M")
      case True
      hence "j = i + 1" using dj by (simp add: mod_less)
      thus ?thesis by arith
    next
      case False
      hence "j = 0" using dj mod1[OF lt(1)] by simp
      moreover have "i = M - 1" using False lt(1) by arith
      ultimately show ?thesis using assms(2) by blast
    qed
  next
    assume di: "i = (j + 1) mod M"
    show ?thesis
    proof (cases "j + 1 < M")
      case True
      hence "i = j + 1" using di by (simp add: mod_less)
      thus ?thesis by arith
    next
      case False
      hence "i = 0" using di mod1[OF lt(2)] by simp
      moreover have "j = M - 1" using False lt(2) by arith
      ultimately show ?thesis using assms(3) by blast
    qed
  qed
qed

lemma rot_a: "a < M \<Longrightarrow> rot M (M - 1 - a) a = M - 1"
proof -
  assume a: "a < M"
  have "a + (M - 1 - a) = M - 1" using a by arith
  thus ?thesis unfolding rot_def using M0 by (simp add: mod_less)
qed

lemma rot_next: "a < M \<Longrightarrow> rot M (M - 1 - a) ((a + 1) mod M) = 0"
proof -
  assume a: "a < M"
  have "((a + 1) mod M + (M - 1 - a)) mod M = (a + 1 + (M - 1 - a)) mod M"
    by (simp add: mod_add_left_eq)
  also have "a + 1 + (M - 1 - a) = M" using a by arith
  finally show ?thesis unfolding rot_def by simp
qed

lemma rot_ne:
  assumes "a < M" "i < M" "i \<noteq> a"
  shows "rot M (M - 1 - a) i \<noteq> M - 1"
proof
  assume "rot M (M - 1 - a) i = M - 1"
  hence "rot M (M - 1 - a) i = rot M (M - 1 - a) a" using rot_a[OF assms(1)] by simp
  thus False using rot_inj[OF assms(2) assms(1), of "M - 1 - a"] assms(1,3) by auto
qed

lemma e_lt: "e M a i < 2"
  unfolding e_def by simp

lemma e_vertex:
  assumes "a < M" "cyc M i j" "i \<noteq> a" "j \<noteq> a"
  shows "e M a i \<noteq> e M a j"
proof -
  from assms(2) have lt: "i < M" "j < M" unfolding cyc_def by auto
  have c: "cyc M (rot M (M - 1 - a) i) (rot M (M - 1 - a) j)" by (rule rot_cyc[OF assms(2)])
  have n1: "rot M (M - 1 - a) i \<noteq> M - 1" by (rule rot_ne[OF assms(1) lt(1) assms(3)])
  have n2: "rot M (M - 1 - a) j \<noteq> M - 1" by (rule rot_ne[OF assms(1) lt(2) assms(4)])
  show ?thesis unfolding e_def using pc_valid[OF c] n1 n2 by blast
qed

lemma e_edge:
  assumes "a < M" "cyc M i j" "\<not> ((i = a \<and> j = (a + 1) mod M) \<or> (i = (a + 1) mod M \<and> j = a))"
  shows "e M a i \<noteq> e M a j"
proof -
  from assms(2) have lt: "i < M" "j < M" unfolding cyc_def by auto
  have a1: "(a + 1) mod M < M" using M0 by simp
  have c: "cyc M (rot M (M - 1 - a) i) (rot M (M - 1 - a) j)" by (rule rot_cyc[OF assms(2)])
  have sM: "M - 1 - a < M" using M0 by arith
  have n1: "\<not> (rot M (M - 1 - a) i = M - 1 \<and> rot M (M - 1 - a) j = 0)"
  proof
    assume "rot M (M - 1 - a) i = M - 1 \<and> rot M (M - 1 - a) j = 0"
    hence r1: "rot M (M - 1 - a) i = rot M (M - 1 - a) a" and r2: "rot M (M - 1 - a) j = rot M (M - 1 - a) ((a + 1) mod M)"
      using rot_a[OF assms(1)] rot_next[OF assms(1)] by auto
    from rot_inj[OF lt(1) assms(1) sM r1] rot_inj[OF lt(2) a1 sM r2] assms(3) show False by blast
  qed
  have n2: "\<not> (rot M (M - 1 - a) i = 0 \<and> rot M (M - 1 - a) j = M - 1)"
  proof
    assume "rot M (M - 1 - a) i = 0 \<and> rot M (M - 1 - a) j = M - 1"
    hence r1: "rot M (M - 1 - a) j = rot M (M - 1 - a) a" and r2: "rot M (M - 1 - a) i = rot M (M - 1 - a) ((a + 1) mod M)"
      using rot_a[OF assms(1)] rot_next[OF assms(1)] by auto
    from rot_inj[OF lt(2) assms(1) sM r1] rot_inj[OF lt(1) a1 sM r2] assms(3) show False by blast
  qed
  show ?thesis unfolding e_def using pc_valid[OF c n1 n2] by blast
qed

lemma h_valid: "cyc M i j \<Longrightarrow> h M p i \<noteq> h M p j"
  unfolding h_def using b3_valid[OF rot_cyc] by blast

lemma h_lt: "h M p i < 3"
  unfolding h_def by (rule b3_lt)

lemma h_two:
  assumes "p < M" "i < M" "h M p i = 2"
  shows "i = p"
proof -
  have "b3 M (rot M (M - 1 - p) i) = 2" using assms(3) unfolding h_def .
  hence "rot M (M - 1 - p) i = M - 1" unfolding b3_def by (auto split: if_splits)
  hence "rot M (M - 1 - p) i = rot M (M - 1 - p) p" using rot_a[OF assms(1)] by simp
  moreover have "M - 1 - p < M" using M0 by arith
  ultimately show ?thesis using rot_inj[OF assms(2) assms(1)] by blast
qed

end

subsection \<open>The join of two copies\<close>

definition jn :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "jn M A B X u w \<longleftrightarrow>
     (u < M \<and> w < M \<and> A u w) \<or>
     (M \<le> u \<and> u < 2 * M \<and> M \<le> w \<and> w < 2 * M \<and> B (u - M) (w - M)) \<or>
     (u < M \<and> M \<le> w \<and> w < 2 * M \<and> X u (w - M)) \<or>
     (M \<le> u \<and> u < 2 * M \<and> w < M \<and> X w (u - M))"

definition dirac :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "dirac M = jn M (cyc M) (cyc M) (\<lambda>_ _. True)"

lemma join_col_on:
  fixes gA gB :: "nat \<Rightarrow> nat"
  assumes sets: "S = {u. u < 2 * M \<and> (u < M \<longrightarrow> u \<in> SA) \<and> (M \<le> u \<longrightarrow> u - M \<in> SB)}"
    and p1: "\<And>i j. A i j \<Longrightarrow> i < M \<Longrightarrow> j < M \<Longrightarrow> i \<in> SA \<Longrightarrow> j \<in> SA \<Longrightarrow> gA i \<noteq> gA j"
    and p2: "\<And>i j. B i j \<Longrightarrow> i < M \<Longrightarrow> j < M \<Longrightarrow> i \<in> SB \<Longrightarrow> j \<in> SB \<Longrightarrow> gB i \<noteq> gB j"
    and p3: "\<And>i j. X i j \<Longrightarrow> i < M \<Longrightarrow> j < M \<Longrightarrow> i \<in> SA \<Longrightarrow> j \<in> SB \<Longrightarrow> oA + gA i \<noteq> oB + gB j"
    and b1: "\<And>i. i < M \<Longrightarrow> i \<in> SA \<Longrightarrow> oA + gA i < k"
    and b2: "\<And>j. j < M \<Longrightarrow> j \<in> SB \<Longrightarrow> oB + gB j < k"
  shows "col_on S k (jn M A B X)"
  unfolding col_on_def
proof (intro exI[of _ "\<lambda>u. if u < M then oA + gA u else oB + gB (u - M)"] conjI ballI impI)
  fix v assume "v \<in> S"
  hence v: "v < 2 * M" "v < M \<longrightarrow> v \<in> SA" "M \<le> v \<longrightarrow> v - M \<in> SB" using sets by auto
  show "(if v < M then oA + gA v else oB + gB (v - M)) < k"
  proof (cases "v < M")
    case True thus ?thesis using b1 v(2) by simp
  next
    case False
    hence "v - M < M" using v(1) by arith
    thus ?thesis using False b2 v(3) by simp
  qed
next
  fix u w assume uS: "u \<in> S" and wS: "w \<in> S" and G: "jn M A B X u w"
  hence u: "u < 2 * M" "u < M \<longrightarrow> u \<in> SA" "M \<le> u \<longrightarrow> u - M \<in> SB"
    and w: "w < 2 * M" "w < M \<longrightarrow> w \<in> SA" "M \<le> w \<longrightarrow> w - M \<in> SB" using sets by auto
  have uM: "M \<le> u \<Longrightarrow> u - M < M" using u(1) by arith
  have wM: "M \<le> w \<Longrightarrow> w - M < M" using w(1) by arith
  from G show "(if u < M then oA + gA u else oB + gB (u - M)) \<noteq> (if w < M then oA + gA w else oB + gB (w - M))"
    unfolding jn_def
  proof (elim disjE conjE)
    assume "u < M" "w < M" "A u w"
    thus ?thesis using p1 u w by auto
  next
    assume "M \<le> u" "u < 2 * M" "M \<le> w" "w < 2 * M" "B (u - M) (w - M)"
    thus ?thesis using p2[of "u - M" "w - M"] u w uM wM by auto
  next
    assume "u < M" "M \<le> w" "w < 2 * M" "X u (w - M)"
    thus ?thesis using p3[of u "w - M"] u w wM by auto
  next
    assume "M \<le> u" "u < 2 * M" "w < M" "X w (u - M)"
    thus ?thesis using p3[of w "u - M"] u w uM by auto
  qed
qed

subsection \<open>The Dirac graph is 6-critical\<close>

context oddc
begin

lemma dirac_simple: "simple (2 * M) (dirac M)"
  unfolding simple_def dirac_def jn_def
  using cyc_sym cyc_irrefl[OF hge3] by auto


text \<open>Irreflexivity on any vertex below 2M.\<close>
lemma dirac_irr': "u < 2 * M \<Longrightarrow> \<not> dirac M u u"
  using dirac_simple unfolding simple_def by blast

lemma col6: "col_on {..<2 * M} 6 (dirac M)"
  unfolding dirac_def
  apply (rule join_col_on[where SA = "{..<M}" and SB = "{..<M}" and gA = "b3 M" and gB = "b3 M" and oA = 0 and oB = 3])
  subgoal by auto
  subgoal for i j using b3_valid by auto
  subgoal for i j using b3_valid by auto
  subgoal for i j using b3_lt[of i] by arith
  subgoal for i using b3_lt[of i] by arith
  subgoal for j using b3_lt[of j] by arith
  done

lemma not_col5: "\<not> col_on {..<2 * M} 5 (dirac M)"
proof
  assume "col_on {..<2 * M} 5 (dirac M)"
  then obtain c :: "nat \<Rightarrow> nat" where cb: "\<And>v. v < 2 * M \<Longrightarrow> c v < 5"
    and cp: "\<And>u v. u < 2 * M \<Longrightarrow> v < 2 * M \<Longrightarrow> dirac M u v \<Longrightarrow> c u \<noteq> c v"
    unfolding col_on_def by auto
  text \<open>Each copy uses at least three colours (odd cycle).\<close>
  have three: "3 \<le> card (c ` {off..<off + M})" if off: "off = 0 \<or> off = M" for off
  proof -
    define d where "d i = c (off + i)" for i
    have dstep: "d i \<noteq> d ((i + 1) mod M)" if i: "i < M" for i
    proof -
      have "(i + 1) mod M < M" using M0 by simp
      hence "cyc M i ((i + 1) mod M)" using i unfolding cyc_def by auto
      have dd: "dirac M (off + i) (off + (i + 1) mod M)" using off i \<open>cyc M i ((i + 1) mod M)\<close>
        unfolding dirac_def jn_def by auto
      have l1: "off + i < 2 * M" and l2: "off + (i + 1) mod M < 2 * M"
        using off i \<open>(i + 1) mod M < M\<close> by arith+
      show "d i \<noteq> d ((i + 1) mod M)" unfolding d_def using cp[OF l1 l2 dd] .
    qed
    have img: "c ` {off..<off + M} = d ` {..<M}"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> c ` {off..<off + M}"
      then obtain k where k: "off \<le> k" "k < off + M" "x = c k" by auto
      have "x = d (k - off)" using k unfolding d_def by simp
      moreover have "k - off \<in> {..<M}" using k by auto
      ultimately show "x \<in> d ` {..<M}" by blast
    next
      fix x assume "x \<in> d ` {..<M}"
      then obtain i where "i < M" "x = c (off + i)" unfolding d_def by auto
      thus "x \<in> c ` {off..<off + M}" by auto
    qed
    show "3 \<le> card (c ` {off..<off + M})"
      unfolding img
    proof (rule ccontr)
      assume "\<not> 3 \<le> card (d ` {..<M})"
      hence card2: "card (d ` {..<M}) \<le> 2" by arith
      have m1: "1 < M" using hge3 by arith
      have e01: "d 0 \<noteq> d 1" using dstep[of 0] mod1[of 0 M] M0 m1 by simp
      have D: "d ` {..<M} = {d 0, d 1}"
      proof (rule sym, rule card_seteq)
        show "finite (d ` {..<M})" by simp
        show "{d 0, d 1} \<subseteq> d ` {..<M}" using M0 m1 by auto
        show "card (d ` {..<M}) \<le> card {d 0, d 1}" using card2 e01 by simp
      qed
      have alt: "d i = (if even i then d 0 else d 1)" if "i < M" for i
        using that
        proof (induction i)
          case 0 thus ?case by simp
        next
          case (Suc i)
          hence i: "i < M" by arith
          have m: "(i + 1) mod M = i + 1" using Suc.prems by (simp add: mod_less)
          have ne: "d i \<noteq> d (i + 1)" using dstep[OF i] m by simp
          have in1: "d (Suc i) \<in> {d 0, d 1}" using D Suc.prems by auto
          have in2: "d i \<in> {d 0, d 1}" using D i by auto
          show ?case
          proof (cases "even i")
            case True
            hence "d i = d 0" using Suc.IH i by simp
            hence "d (Suc i) = d 1" using ne in1 by auto
            thus ?thesis using True by simp
          next
            case False
            hence "d i = d 1" using Suc.IH i by simp
            hence "d (Suc i) = d 0" using ne in1 e01 by auto
            thus ?thesis using False by simp
          qed
        qed
      have ev: "even (M - 1)" using hodd by presburger
      have lt: "M - 1 < M" using M0 by arith
      have "d (M - 1) \<noteq> d ((M - 1 + 1) mod M)" by (rule dstep[OF lt])
      moreover have "(M - 1 + 1) mod M = 0" using M0 by simp
      ultimately show False using alt[OF lt] ev by simp
    qed
  qed
  have disj: "c ` {0..<M} \<inter> c ` {M..<M + M} = {}"
  proof (rule ccontr)
    assume "c ` {0..<M} \<inter> c ` {M..<M + M} \<noteq> {}"
    then obtain i j where "i < M" "M \<le> j" "j < M + M" "c i = c j" by auto
    moreover have "dirac M i j" unfolding dirac_def jn_def using calculation by auto
    ultimately show False using cp[of i j] by auto
  qed
  have sub: "c ` {0..<M} \<union> c ` {M..<M + M} \<subseteq> {..<5}"
    using cb by auto
  have "card (c ` {0..<M} \<union> c ` {M..<M + M}) = card (c ` {0..<M}) + card (c ` {M..<M + M})"
    using disj by (intro card_Un_disjoint) auto
  moreover have "card (c ` {0..<M} \<union> c ` {M..<M + M}) \<le> 5"
    using card_mono[OF _ sub] by simp
  ultimately show False using three[of 0] three[of M] by simp
qed

lemma col5_vertex1:
  assumes "v < M"
  shows "col_on ({..<2 * M} - {v}) 5 (dirac M)"
  unfolding dirac_def
  apply (rule join_col_on[where SA = "{..<M} - {v}" and SB = "{..<M}" and gA = "e M v" and gB = "b3 M" and oA = 0 and oB = 2])
  subgoal using assms by auto
  subgoal for i j using e_vertex[OF assms, of i j] by auto
  subgoal for i j using b3_valid by auto
  subgoal for i j using e_lt[of v i] by arith
  subgoal for i using e_lt[of v i] by arith
  subgoal for j using b3_lt[of j] by arith
  done

lemma col5_vertex2:
  assumes "p < M"
  shows "col_on ({..<2 * M} - {M + p}) 5 (dirac M)"
  unfolding dirac_def
  apply (rule join_col_on[where SA = "{..<M}" and SB = "{..<M} - {p}" and gA = "b3 M" and gB = "e M p" and oA = 0 and oB = 3])
  subgoal using assms by auto
  subgoal for i j using b3_valid by auto
  subgoal for i j using e_vertex[OF assms, of i j] by auto
  subgoal for i j using b3_lt[of i] by arith
  subgoal for i using b3_lt[of i] by arith
  subgoal for j using e_lt[of p j] by arith
  done

lemma col5_edge1:
  assumes "a < M"
  shows "col_on {..<2 * M} 5 (del_edge a ((a + 1) mod M) (dirac M))"
proof -
  have b: "(a + 1) mod M < M" using M0 by simp
  show ?thesis
  proof (rule col_on_sub[where G' = "jn M (\<lambda>i j. cyc M i j \<and> \<not> ((i = a \<and> j = (a + 1) mod M) \<or> (i = (a + 1) mod M \<and> j = a))) (cyc M) (\<lambda>_ _. True)"])
    show "\<forall>u\<in>{..<2 * M}. \<forall>w\<in>{..<2 * M}. del_edge a ((a + 1) mod M) (dirac M) u w \<longrightarrow>
        jn M (\<lambda>i j. cyc M i j \<and> \<not> ((i = a \<and> j = (a + 1) mod M) \<or> (i = (a + 1) mod M \<and> j = a))) (cyc M) (\<lambda>_ _. True) u w"
      using assms b unfolding del_edge_def dirac_def jn_def by auto
  next
    show "col_on {..<2 * M} 5 (jn M (\<lambda>i j. cyc M i j \<and> \<not> ((i = a \<and> j = (a + 1) mod M) \<or> (i = (a + 1) mod M \<and> j = a))) (cyc M) (\<lambda>_ _. True))"
      apply (rule join_col_on[where SA = "{..<M}" and SB = "{..<M}" and gA = "e M a" and gB = "b3 M" and oA = 0 and oB = 2])
      subgoal by auto
      subgoal for i j using e_edge[OF assms] by auto
      subgoal for i j using b3_valid by auto
      subgoal for i j using e_lt[of a i] by arith
      subgoal for i using e_lt[of a i] by arith
      subgoal for j using b3_lt[of j] by arith
      done
  qed
qed

lemma col5_edge2:
  assumes "p < M"
  shows "col_on {..<2 * M} 5 (del_edge (M + p) (M + (p + 1) mod M) (dirac M))"
proof -
  have b: "(p + 1) mod M < M" using M0 by simp
  show ?thesis
  proof (rule col_on_sub[where G' = "jn M (cyc M) (\<lambda>i j. cyc M i j \<and> \<not> ((i = p \<and> j = (p + 1) mod M) \<or> (i = (p + 1) mod M \<and> j = p))) (\<lambda>_ _. True)"])
    show "\<forall>u\<in>{..<2 * M}. \<forall>w\<in>{..<2 * M}. del_edge (M + p) (M + (p + 1) mod M) (dirac M) u w \<longrightarrow>
        jn M (cyc M) (\<lambda>i j. cyc M i j \<and> \<not> ((i = p \<and> j = (p + 1) mod M) \<or> (i = (p + 1) mod M \<and> j = p))) (\<lambda>_ _. True) u w"
      using assms b unfolding del_edge_def dirac_def jn_def by auto
  next
    show "col_on {..<2 * M} 5 (jn M (cyc M) (\<lambda>i j. cyc M i j \<and> \<not> ((i = p \<and> j = (p + 1) mod M) \<or> (i = (p + 1) mod M \<and> j = p))) (\<lambda>_ _. True))"
      apply (rule join_col_on[where SA = "{..<M}" and SB = "{..<M}" and gA = "b3 M" and gB = "e M p" and oA = 0 and oB = 3])
      subgoal by auto
      subgoal for i j using b3_valid by auto
      subgoal for i j using e_edge[OF assms] by auto
      subgoal for i j using b3_lt[of i] by arith
      subgoal for i using b3_lt[of i] by arith
      subgoal for j using e_lt[of p j] by arith
      done
  qed
qed

lemma col5_edge3:
  assumes "a < M" "q < M"
  shows "col_on {..<2 * M} 5 (del_edge a (M + q) (dirac M))"
proof -
  define gB where "gB j = (if h M q j = 2 then 0 else h M q j + 1)" for j
  have gBle: "gB j \<le> 2" for j
  proof -
    have hl: "h M q j < 3" by (rule h_lt)
    show "gB j \<le> 2" unfolding gB_def
    proof (cases "h M q j = 2")
      case True thus "(if h M q j = 2 then 0 else h M q j + 1) \<le> 2" by simp
    next
      case False
      hence "h M q j + 1 \<le> 2" using hl by arith
      thus "(if h M q j = 2 then 0 else h M q j + 1) \<le> 2" using False by simp
    qed
  qed
  have gBz: "\<And>j. gB j = 0 \<Longrightarrow> h M q j = 2" unfolding gB_def by (auto split: if_splits)
  show ?thesis
  proof (rule col_on_sub[where G' = "jn M (cyc M) (cyc M) (\<lambda>i j. \<not> (i = a \<and> j = q))"])
    show "\<forall>u\<in>{..<2 * M}. \<forall>w\<in>{..<2 * M}. del_edge a (M + q) (dirac M) u w \<longrightarrow>
        jn M (cyc M) (cyc M) (\<lambda>i j. \<not> (i = a \<and> j = q)) u w"
      using assms unfolding del_edge_def dirac_def jn_def by auto
  next
    show "col_on {..<2 * M} 5 (jn M (cyc M) (cyc M) (\<lambda>i j. \<not> (i = a \<and> j = q)))"
      apply (rule join_col_on[where SA = "{..<M}" and SB = "{..<M}" and gA = "h M a" and gB = gB and oA = 0 and oB = 2])
      subgoal by auto
      subgoal for i j using h_valid by auto
      subgoal for i j
      proof -
        assume "cyc M i j"
        hence "h M q i \<noteq> h M q j" by (rule h_valid)
        thus ?thesis unfolding gB_def using h_lt[of q i] h_lt[of q j] by (auto split: if_splits)
      qed
      subgoal for i j
      proof -
        assume "\<not> (i = a \<and> j = q)" "i < M" "j < M"
        show ?thesis
        proof
          assume "0 + h M a i = 2 + gB j"
          hence "h M a i = 2" "gB j = 0" using h_lt[of a i] by auto
          hence "i = a" "j = q" using h_two[OF assms(1) \<open>i < M\<close>] h_two[OF assms(2) \<open>j < M\<close>] gBz by auto
          thus False using \<open>\<not> (i = a \<and> j = q)\<close> by simp
        qed
      qed
      subgoal for i using h_lt[of a i] by arith
      subgoal for j using gBle[of j] by arith
      done
  qed
qed

lemma col5_edge:
  assumes "a < 2 * M" "b < 2 * M" "dirac M a b"
  shows "col_on {..<2 * M} 5 (del_edge a b (dirac M))"
proof -
  from assms(3) have "(a < M \<and> b < M \<and> cyc M a b) \<or>
     (M \<le> a \<and> a < 2 * M \<and> M \<le> b \<and> b < 2 * M \<and> cyc M (a - M) (b - M)) \<or>
     (a < M \<and> M \<le> b \<and> b < 2 * M) \<or> (M \<le> a \<and> a < 2 * M \<and> b < M)"
    unfolding dirac_def jn_def by auto
  thus ?thesis
  proof (elim disjE conjE)
    assume "a < M" "b < M" "cyc M a b"
    hence "b = (a + 1) mod M \<or> a = (b + 1) mod M" unfolding cyc_def by auto
    thus ?thesis
    proof
      assume "b = (a + 1) mod M" thus ?thesis using col5_edge1[OF \<open>a < M\<close>] by simp
    next
      assume "a = (b + 1) mod M"
      hence "col_on {..<2 * M} 5 (del_edge b ((b + 1) mod M) (dirac M))" using col5_edge1[OF \<open>b < M\<close>] by simp
      thus ?thesis using \<open>a = (b + 1) mod M\<close> del_edge_sym by metis
    qed
  next
    assume "M \<le> a" "a < 2 * M" "M \<le> b" "b < 2 * M" "cyc M (a - M) (b - M)"
    hence "b - M = (a - M + 1) mod M \<or> a - M = (b - M + 1) mod M" unfolding cyc_def by auto
    thus ?thesis
    proof
      assume "b - M = (a - M + 1) mod M"
      hence "b = M + (a - M + 1) mod M" "a = M + (a - M)" using \<open>M \<le> a\<close> \<open>M \<le> b\<close> by arith+
      thus ?thesis using col5_edge2[of "a - M"] \<open>a < 2 * M\<close> by auto
    next
      assume "a - M = (b - M + 1) mod M"
      hence "a = M + (b - M + 1) mod M" "b = M + (b - M)" using \<open>M \<le> a\<close> \<open>M \<le> b\<close> by arith+
      hence "col_on {..<2 * M} 5 (del_edge b a (dirac M))" using col5_edge2[of "b - M"] \<open>b < 2 * M\<close> by auto
      thus ?thesis using del_edge_sym by metis
    qed
  next
    assume "a < M" "M \<le> b" "b < 2 * M"
    thus ?thesis using col5_edge3[of a "b - M"] by auto
  next
    assume "M \<le> a" "a < 2 * M" "b < M"
    hence "col_on {..<2 * M} 5 (del_edge b a (dirac M))" using col5_edge3[of b "a - M"] by auto
    thus ?thesis using del_edge_sym by metis
  qed
qed

lemma dirac_crit: "crit 6 (2 * M) (dirac M)"
proof -
  have irr: "irr {..<2 * M} (dirac M)" using dirac_simple unfolding simple_def irr_def by auto
  have chi6: "chi {..<2 * M} (dirac M) = 6"
    by (rule chi_eq6[OF subset_refl irr col6 not_col5])
  have vert: "\<forall>v<2 * M. chi ({..<2 * M} - {v}) (dirac M) < 6"
  proof (intro allI impI)
    fix v assume v: "v < 2 * M"
    have sub: "{..<2 * M} - {v} \<subseteq> {..<2 * M}" by auto
    have irr': "irr ({..<2 * M} - {v}) (dirac M)" using irr unfolding irr_def by auto
    show "chi ({..<2 * M} - {v}) (dirac M) < 6"
      unfolding chi_lt6[OF sub irr']
    proof (cases "v < M")
      case True thus "col_on ({..<2 * M} - {v}) 5 (dirac M)" by (rule col5_vertex1)
    next
      case False
      hence "v = M + (v - M)" "v - M < M" using v by arith+
      thus "col_on ({..<2 * M} - {v}) 5 (dirac M)" using col5_vertex2[of "v - M"] by metis
    qed
  qed
  have edg: "\<forall>a<2 * M. \<forall>b<2 * M. dirac M a b \<longrightarrow> chi {..<2 * M} (del_edge a b (dirac M)) < 6"
  proof (intro allI impI)
    fix a b assume "a < 2 * M" "b < 2 * M" "dirac M a b"
    have irr2: "irr {..<2 * M} (del_edge a b (dirac M))" by (rule del_edge_irr[OF irr])
    show "chi {..<2 * M} (del_edge a b (dirac M)) < 6"
      unfolding chi_lt6[OF subset_refl irr2] by (rule col5_edge[OF \<open>a < 2 * M\<close> \<open>b < 2 * M\<close> \<open>dirac M a b\<close>])
  qed
  show ?thesis unfolding crit_def using dirac_simple chi6 vert edg by blast
qed

subsection \<open>Counting the edges\<close>

definition cyc_edges :: "nat \<Rightarrow> nat set set" where
  "cyc_edges off = (\<lambda>i. {off + i, off + (i + 1) mod M}) ` {..<M}"

definition cross_edges :: "nat set set" where
  "cross_edges = (\<lambda>(i, j). {i, M + j}) ` ({..<M} \<times> {..<M})"

lemma card_cyc_edges: "card (cyc_edges off) = M"
proof -
  have "inj_on (\<lambda>i. {off + i, off + (i + 1) mod M}) {..<M}"
  proof (rule inj_onI)
    fix i i' assume i: "i \<in> {..<M}" and i': "i' \<in> {..<M}" and eq: "{off + i, off + (i + 1) mod M} = {off + i', off + (i' + 1) mod M}"
    from i i' have lt: "i < M" "i' < M" by simp_all
    from eq have "(off + i = off + i' \<and> off + (i + 1) mod M = off + (i' + 1) mod M) \<or>
        (off + i = off + (i' + 1) mod M \<and> off + (i + 1) mod M = off + i')"
      by (simp add: doubleton_eq_iff)
    thus "i = i'"
    proof
      assume "off + i = off + i' \<and> off + (i + 1) mod M = off + (i' + 1) mod M"
      thus ?thesis by simp
    next
      assume "off + i = off + (i' + 1) mod M \<and> off + (i + 1) mod M = off + i'"
      hence h1: "i = (i' + 1) mod M" and h2: "i' = (i + 1) mod M" by auto
      from cyc_two[OF hge3 lt h1 h2] show ?thesis by simp
    qed
  qed
  thus ?thesis unfolding cyc_edges_def by (simp add: card_image)
qed

lemma card_cross_edges: "card cross_edges = M * M"
proof -
  have "inj_on (\<lambda>(i, j). {i, M + j}) ({..<M} \<times> {..<M})"
    by (rule inj_onI) (auto simp: doubleton_eq_iff)
  thus ?thesis unfolding cross_edges_def by (simp add: card_image)
qed

lemma edges_dirac: "edges (2 * M) (dirac M) = cyc_edges 0 \<union> cyc_edges M \<union> cross_edges"
proof (rule set_eqI)
  fix x
  have m: "\<And>i. (i + 1) mod M < M" using M0 by simp
  show "x \<in> edges (2 * M) (dirac M) \<longleftrightarrow> x \<in> cyc_edges 0 \<union> cyc_edges M \<union> cross_edges"
  proof
    assume "x \<in> edges (2 * M) (dirac M)"
    then obtain u w where x: "x = {u, w}" and uw: "u < 2 * M" "w < 2 * M" "dirac M u w"
      unfolding edges_def by auto
    from uw(3) have "(u < M \<and> w < M \<and> cyc M u w) \<or>
       (M \<le> u \<and> u < 2 * M \<and> M \<le> w \<and> w < 2 * M \<and> cyc M (u - M) (w - M)) \<or>
       (u < M \<and> M \<le> w \<and> w < 2 * M) \<or> (M \<le> u \<and> u < 2 * M \<and> w < M)"
      unfolding dirac_def jn_def by auto
    thus "x \<in> cyc_edges 0 \<union> cyc_edges M \<union> cross_edges"
    proof (elim disjE conjE)
      assume "u < M" "w < M" "cyc M u w"
      hence "w = (u + 1) mod M \<or> u = (w + 1) mod M" unfolding cyc_def by auto
      thus ?thesis
      proof
        assume "w = (u + 1) mod M"
        with \<open>u < M\<close> show ?thesis unfolding x cyc_edges_def by auto
      next
        assume "u = (w + 1) mod M"
        with \<open>w < M\<close> show ?thesis unfolding x cyc_edges_def by (auto simp: insert_commute)
      qed
    next
      assume "M \<le> u" "u < 2 * M" "M \<le> w" "w < 2 * M" "cyc M (u - M) (w - M)"
      hence "w - M = (u - M + 1) mod M \<or> u - M = (w - M + 1) mod M" unfolding cyc_def by auto
      thus ?thesis
      proof
        assume "w - M = (u - M + 1) mod M"
        hence "u = M + (u - M)" "w = M + (u - M + 1) mod M" using \<open>M \<le> u\<close> \<open>M \<le> w\<close> by arith+
        moreover have "u - M < M" using \<open>u < 2 * M\<close> by arith
        ultimately show ?thesis unfolding x cyc_edges_def by (auto simp: image_iff)
      next
        assume "u - M = (w - M + 1) mod M"
        hence "w = M + (w - M)" "u = M + (w - M + 1) mod M" using \<open>M \<le> u\<close> \<open>M \<le> w\<close> by arith+
        moreover have "w - M < M" using \<open>w < 2 * M\<close> by arith
        ultimately show ?thesis unfolding x cyc_edges_def by (auto simp: image_iff insert_commute)
      qed
    next
      assume "u < M" "M \<le> w" "w < 2 * M"
      hence a1: "w - M < M" and eqw: "M + (w - M) = w" by arith+
      have eq: "{u, w} = (\<lambda>(i, j). {i, M + j}) (u, w - M)" by (simp add: eqw)
      have mem: "(u, w - M) \<in> {..<M} \<times> {..<M}" using a1 \<open>u < M\<close> by simp
      have "{u, w} \<in> cross_edges" unfolding cross_edges_def by (rule image_eqI[where f = "\<lambda>(i, j). {i, M + j}" and A = "{..<M} \<times> {..<M}", OF eq mem])
      thus ?thesis unfolding x by simp
    next
      assume "M \<le> u" "u < 2 * M" "w < M"
      hence a1: "u - M < M" and equ: "M + (u - M) = u" by arith+
      have eq: "{u, w} = (\<lambda>(i, j). {i, M + j}) (w, u - M)" by (simp add: equ insert_commute)
      have mem: "(w, u - M) \<in> {..<M} \<times> {..<M}" using a1 \<open>w < M\<close> by simp
      have "{u, w} \<in> cross_edges" unfolding cross_edges_def by (rule image_eqI[where f = "\<lambda>(i, j). {i, M + j}" and A = "{..<M} \<times> {..<M}", OF eq mem])
      thus ?thesis unfolding x by simp
    qed
  next
    assume "x \<in> cyc_edges 0 \<union> cyc_edges M \<union> cross_edges"
    thus "x \<in> edges (2 * M) (dirac M)"
    proof (elim UnE)
      assume "x \<in> cyc_edges 0"
      then obtain i where i: "i < M" and x: "x = {i, (i + 1) mod M}" unfolding cyc_edges_def by auto
      have "cyc M i ((i + 1) mod M)" using i m unfolding cyc_def by auto
      hence "dirac M i ((i + 1) mod M)" using i m unfolding dirac_def jn_def by auto
      moreover have "i < 2 * M" "(i + 1) mod M < 2 * M" using i m[of i] by arith+
      ultimately show ?thesis unfolding edges_def x by blast
    next
      assume "x \<in> cyc_edges M"
      then obtain i where i: "i < M" and x: "x = {M + i, M + (i + 1) mod M}" unfolding cyc_edges_def by auto
      have "cyc M i ((i + 1) mod M)" using i m unfolding cyc_def by auto
      hence "dirac M (M + i) (M + (i + 1) mod M)" using i m unfolding dirac_def jn_def by auto
      moreover have "M + i < 2 * M" "M + (i + 1) mod M < 2 * M" using i m[of i] by arith+
      ultimately show ?thesis unfolding edges_def x by blast
    next
      assume "x \<in> cross_edges"
      then obtain i j where ij: "i < M" "j < M" and x: "x = {i, M + j}" unfolding cross_edges_def by auto
      hence "dirac M i (M + j)" unfolding dirac_def jn_def by auto
      moreover have "i < 2 * M" "M + j < 2 * M" using ij by arith+
      ultimately show ?thesis unfolding edges_def x by blast
    qed
  qed
qed

lemma card_edges_dirac: "card (edges (2 * M) (dirac M)) = 2 * M + M * M"
proof -
  have m: "\<And>i. (i + 1) mod M < M" using M0 by simp
  have d1: "cyc_edges 0 \<inter> cyc_edges M = {}"
  proof (rule equals0I)
    fix x assume "x \<in> cyc_edges 0 \<inter> cyc_edges M"
    then obtain i i' where "i < M" "x = {i, (i + 1) mod M}" "x = {M + i', M + (i' + 1) mod M}"
      unfolding cyc_edges_def by auto
    hence "i \<in> {M + i', M + (i' + 1) mod M}" by auto
    hence "i = M + i' \<or> i = M + (i' + 1) mod M" by simp
    thus False using \<open>i < M\<close> by arith
  qed
  have d2: "cyc_edges 0 \<inter> cross_edges = {}"
  proof (rule equals0I)
    fix x assume "x \<in> cyc_edges 0 \<inter> cross_edges"
    then obtain i i' j where "i < M" "i' < M" "x = {i, (i + 1) mod M}" "x = {i', M + j}"
      unfolding cyc_edges_def cross_edges_def by auto
    hence "M + j \<in> {i, (i + 1) mod M}" by auto
    hence "M + j = i \<or> M + j = (i + 1) mod M" by simp
    thus False using \<open>i < M\<close> m[of i] by arith
  qed
  have d3: "cyc_edges M \<inter> cross_edges = {}"
  proof (rule equals0I)
    fix x assume "x \<in> cyc_edges M \<inter> cross_edges"
    then obtain i i' j where "i < M" and "i' < M" and hx1: "x = {M + i, M + (i + 1) mod M}" and hx2: "x = {i', M + j}"
      unfolding cyc_edges_def cross_edges_def by auto
    hence "i' \<in> {M + i, M + (i + 1) mod M}" by (metis hx1 hx2 insertI1)
    hence "i' = M + i \<or> i' = M + (i + 1) mod M" by simp
    thus False using \<open>i' < M\<close> by arith
  qed
  have fin: "finite (cyc_edges 0)" "finite (cyc_edges M)" "finite cross_edges"
    unfolding cyc_edges_def cross_edges_def by auto
  have "card (cyc_edges 0 \<union> cyc_edges M \<union> cross_edges) = card (cyc_edges 0) + card (cyc_edges M) + card cross_edges"
    using d1 d2 d3 fin by (simp add: card_Un_disjoint Int_Un_distrib2)
  thus ?thesis unfolding edges_dirac using card_cyc_edges card_cross_edges by simp
qed

end

subsection \<open>Bound on the edge count and the theorem\<close>

lemma edges_le: "card (edges N G) \<le> 2 ^ N"
proof -
  have "edges N G \<subseteq> Pow {..<N}" unfolding edges_def by auto
  hence "card (edges N G) \<le> card (Pow {..<N})" by (intro card_mono) auto
  thus ?thesis by (simp add: card_Pow)
qed

theorem dirac_bound:
  assumes "1 \<le> n"
  shows "4 * n ^ 2 + 8 * n + 3 \<le> f 6 (4 * n + 2)"
proof -
  interpret oddc "2 * n + 1"
    by unfold_locales (use assms in \<open>auto\<close>)
  have eqN: "4 * n + 2 = 2 * (2 * n + 1)" by arith
  have eqE: "2 * (2 * n + 1) + (2 * n + 1) * (2 * n + 1) = 4 * n ^ 2 + 8 * n + 3"
    by (simp add: power2_eq_square algebra_simps)
  let ?S = "{m. \<exists>G. crit 6 (4 * n + 2) G \<and> card (edges (4 * n + 2) G) = m}"
  have c1: "crit 6 (4 * n + 2) (dirac (2 * n + 1))" by (simp only: eqN) (rule dirac_crit)
  have c2: "card (edges (4 * n + 2) (dirac (2 * n + 1))) = 4 * n ^ 2 + 8 * n + 3"
    by (simp only: eqN) (rule trans[OF card_edges_dirac eqE])
  have mem: "4 * n ^ 2 + 8 * n + 3 \<in> ?S"
    by (rule CollectI, rule exI[of _ "dirac (2 * n + 1)"], rule conjI[OF c1 c2])
  have bdd: "bdd_above ?S"
  proof (rule bdd_aboveI[of _ "2 ^ (4 * n + 2)"])
    fix m assume "m \<in> ?S"
    then obtain G where "card (edges (4 * n + 2) G) = m" by auto
    thus "m \<le> 2 ^ (4 * n + 2)" by (metis edges_le)
  qed
  show ?thesis unfolding f_def using mem bdd by (rule cSup_upper)
qed

end
