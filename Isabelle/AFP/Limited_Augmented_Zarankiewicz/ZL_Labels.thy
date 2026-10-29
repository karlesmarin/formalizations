(*  Title:      ZL_Labels.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Admissibility of pairs in the limited augmented Zarankiewicz problem (Qi, Cui and Xu, Def. 2.1):
    the label lemma, the blocks lemma, vertical pairs, and at most one full row.
*)
theory ZL_Labels
  imports Main
begin

section \<open>Cells, conditions (C2) and (C3)\<close>

text \<open>A cell is a pair (row, column). \<open>Oc\<close> is the occupied set: the base \<open>E\<^sub>1\<close> together with both
  cells of every pair. Conditions (C2) and (C3) of Definition 2.1 of Qi, Cui and Xu, for a pair \<open>{c, d}\<close>;
  (C3) also applies to degenerate pairs (same row or same column).\<close>

definition C2 :: "(nat \<times> nat) set \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "C2 Oc c d \<longleftrightarrow> (fst c \<noteq> fst d \<and> snd c \<noteq> snd d \<longrightarrow> \<not> ((fst c, snd d) \<in> Oc \<and> (fst d, snd c) \<in> Oc))"

definition C3 :: "(nat \<times> nat) set \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "C3 Oc c d \<longleftrightarrow> \<not> (\<exists>k l. k \<noteq> fst c \<and> k \<noteq> fst d \<and> l \<noteq> snd c \<and> l \<noteq> snd d \<and>
      (k, l) \<in> Oc \<and> (k, snd c) \<in> Oc \<and> (k, snd d) \<in> Oc \<and> (fst c, l) \<in> Oc \<and> (fst d, l) \<in> Oc)"

definition supp :: "(nat \<times> nat) set \<Rightarrow> nat \<Rightarrow> nat set" where
  "supp Oc r = {j. (r, j) \<in> Oc}"

section \<open>The label lemma\<close>

text \<open>Every row carries a label containing its occupied support; any three distinct occupied columns of a row form
  a triple of the shadow \<open>H\<close>; the pair is compatible with the labels. Then the pair satisfies (C2) and (C3).
  This is the admissibility step of the realization in Theorem C of the paper.\<close>

lemma label_admissible:
  assumes lab: "\<And>r. supp Oc r \<subseteq> lab r"
    and tri: "\<And>k a b e. a \<in> supp Oc k \<Longrightarrow> b \<in> supp Oc k \<Longrightarrow> e \<in> supp Oc k \<Longrightarrow>
                a \<noteq> b \<Longrightarrow> a \<noteq> e \<Longrightarrow> b \<noteq> e \<Longrightarrow> {a, b, e} \<in> H"
    and rows: "fst c \<noteq> fst d"
    and vert: "snd c = snd d \<Longrightarrow> lab (fst c) \<inter> lab (fst d) = {snd c}"
    and diag2: "snd c \<noteq> snd d \<Longrightarrow> snd d \<notin> lab (fst c) \<or> snd c \<notin> lab (fst d)"
    and diag3: "snd c \<noteq> snd d \<Longrightarrow> \<forall>l \<in> lab (fst c) \<inter> lab (fst d) - {snd c, snd d}. {snd c, snd d, l} \<notin> H"
  shows "C2 Oc c d \<and> C3 Oc c d"
proof (rule conjI)
  show "C2 Oc c d"
    unfolding C2_def
  proof (intro impI notI)
    assume ne: "fst c \<noteq> fst d \<and> snd c \<noteq> snd d"
      and oc: "(fst c, snd d) \<in> Oc \<and> (fst d, snd c) \<in> Oc"
    have "snd d \<in> lab (fst c)" using lab oc unfolding supp_def by blast
    moreover have "snd c \<in> lab (fst d)" using lab oc unfolding supp_def by blast
    ultimately show False using diag2 ne by blast
  qed
  show "C3 Oc c d"
    unfolding C3_def
  proof (rule notI)
    assume "\<exists>k l. k \<noteq> fst c \<and> k \<noteq> fst d \<and> l \<noteq> snd c \<and> l \<noteq> snd d \<and>
      (k, l) \<in> Oc \<and> (k, snd c) \<in> Oc \<and> (k, snd d) \<in> Oc \<and> (fst c, l) \<in> Oc \<and> (fst d, l) \<in> Oc"
    then obtain k l where h: "k \<noteq> fst c" "k \<noteq> fst d" "l \<noteq> snd c" "l \<noteq> snd d"
      "(k, l) \<in> Oc" "(k, snd c) \<in> Oc" "(k, snd d) \<in> Oc" "(fst c, l) \<in> Oc" "(fst d, l) \<in> Oc"
      by blast
    have lc: "l \<in> lab (fst c)" using lab h(8) unfolding supp_def by blast
    have ld: "l \<in> lab (fst d)" using lab h(9) unfolding supp_def by blast
    show False
    proof (cases "snd c = snd d")
      case True
      then have "lab (fst c) \<inter> lab (fst d) = {snd c}" by (rule vert)
      then have "l = snd c" using lc ld by blast
      then show False using h(3) by simp
    next
      case False
      have s1: "snd c \<in> supp Oc k" and s2: "snd d \<in> supp Oc k" and s3: "l \<in> supp Oc k"
        using h unfolding supp_def by auto
      have "{snd c, snd d, l} \<in> H"
        by (rule tri[OF s1 s2 s3]) (use False h in auto)
      moreover have "{snd c, snd d, l} \<notin> H"
        using diag3[OF False] lc ld h(3,4) by blast
      ultimately show False by blast
    qed
  qed
qed

section \<open>The blocks lemma\<close>

text \<open>Columns are partitioned into blocks by \<open>blk\<close>; every row has a type of at most two blocks and its occupied
  support lies in those blocks; the pair joins an endpoint in a block of its row's type that the other type misses
  with an endpoint in a block of the other type that the first misses.\<close>

lemma blocks_admissible:
  assumes typ2: "\<And>r. card (typ r) \<le> 2" and fin: "\<And>r. finite (typ r)"
    and inside: "\<And>r j. j \<in> supp Oc r \<Longrightarrow> blk j \<in> typ r"
    and rows: "fst c \<noteq> fst d"
    and x: "blk (snd c) \<in> typ (fst c) - typ (fst d)"
    and y: "blk (snd d) \<in> typ (fst d) - typ (fst c)"
  shows "C2 Oc c d \<and> C3 Oc c d"
proof -
  have xa: "blk (snd c) \<in> typ (fst c)" "blk (snd c) \<notin> typ (fst d)" using x by auto
  have ya: "blk (snd d) \<in> typ (fst d)" "blk (snd d) \<notin> typ (fst c)" using y by auto
  show ?thesis
  proof (rule label_admissible[of Oc "\<lambda>r. {j. blk j \<in> typ r}" "{T. card (blk ` T) \<le> 2}" c d])
    fix r show "supp Oc r \<subseteq> {j. blk j \<in> typ r}" using inside by blast
  next
    fix k a b e
    assume "a \<in> supp Oc k" "b \<in> supp Oc k" "e \<in> supp Oc k"
    then have "blk ` {a, b, e} \<subseteq> typ k" using inside by auto
    then have "card (blk ` {a, b, e}) \<le> card (typ k)" by (rule card_mono[OF fin])
    also have "\<dots> \<le> 2" by (rule typ2)
    finally show "{a, b, e} \<in> {T. card (blk ` T) \<le> 2}" by simp
  next
    show "fst c \<noteq> fst d" by (rule rows)
  next
    assume "snd c = snd d"
    then show "{j. blk j \<in> typ (fst c)} \<inter> {j. blk j \<in> typ (fst d)} = {snd c}"
      using xa ya by simp
  next
    assume "snd c \<noteq> snd d"
    show "snd d \<notin> {j. blk j \<in> typ (fst c)} \<or> snd c \<notin> {j. blk j \<in> typ (fst d)}"
      using ya by simp
  next
    assume ne: "snd c \<noteq> snd d"
    show "\<forall>l\<in>{j. blk j \<in> typ (fst c)} \<inter> {j. blk j \<in> typ (fst d)} - {snd c, snd d}.
            {snd c, snd d, l} \<notin> {T. card (blk ` T) \<le> 2}"
    proof
      fix l assume l: "l \<in> {j. blk j \<in> typ (fst c)} \<inter> {j. blk j \<in> typ (fst d)} - {snd c, snd d}"
      then have lc: "blk l \<in> typ (fst c)" and ld: "blk l \<in> typ (fst d)" by auto
      have n1: "blk (snd c) \<noteq> blk (snd d)" using xa ya by auto
      have n2: "blk (snd c) \<noteq> blk l" using xa ld by auto
      have n3: "blk (snd d) \<noteq> blk l" using ya lc by auto
      have "card (blk ` {snd c, snd d, l}) = 3" using n1 n2 n3 by simp
      then show "{snd c, snd d, l} \<notin> {T. card (blk ` T) \<le> 2}" by simp
    qed
  qed
qed

section \<open>Vertical pairs and full rows in the regime \<open>m \<ge> n(n-1)/2\<close>\<close>

text \<open>Hypotheses describing a maximum base in the regime \<open>m \<ge> n(n-1)/2\<close>: every pair of distinct columns is
  covered by a row of the base, every row has a base cell and at most two (we only need: a base cell outside any
  given column of a non-base cell), all cells lie in columns \<open>< n\<close>, and every occupied cell outside the base
  belongs to a pair \<open>(c, d) \<in> P\<close>, all of whose cells are outside the base and satisfy (C2) and (C3).\<close>

lemma C2_sym: "C2 Oc c d = C2 Oc d c"
  unfolding C2_def by auto

lemma C3_sym: "C3 Oc c d = C3 Oc d c"
  unfolding C3_def by blast

lemma C2E:
  assumes "C2 Oc c d" "fst c \<noteq> fst d" "snd c \<noteq> snd d" "(fst c, snd d) \<in> Oc" "(fst d, snd c) \<in> Oc"
  shows False
  using assms unfolding C2_def by blast

lemma C3E:
  assumes "C3 Oc c d" "k \<noteq> fst c" "k \<noteq> fst d" "l \<noteq> snd c" "l \<noteq> snd d"
    "(k, l) \<in> Oc" "(k, snd c) \<in> Oc" "(k, snd d) \<in> Oc" "(fst c, l) \<in> Oc" "(fst d, l) \<in> Oc"
  shows False
  using assms unfolding C3_def by blast

lemma fresh2:
  assumes "3 \<le> (n::nat)"
  shows "\<exists>l<n. l \<noteq> a \<and> l \<noteq> b"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have sub: "{..<n} \<subseteq> {a, b}" by auto
  have "card {..<n} \<le> card {a, b}" by (rule card_mono) (simp_all add: sub)
  moreover have "card {a, b} \<le> 2" by (simp add: card_insert_if)
  ultimately show False using assms by simp
qed

locale max_base_regime =
  fixes n :: nat and E1 :: "(nat \<times> nat) set" and P :: "((nat \<times> nat) \<times> (nat \<times> nat)) set"
  assumes n3: "3 \<le> n"
    and cols: "\<And>c. c \<in> E1 \<Longrightarrow> snd c < n"
    and cover: "\<And>j l. j < n \<Longrightarrow> l < n \<Longrightarrow> j \<noteq> l \<Longrightarrow> \<exists>k. (k, j) \<in> E1 \<and> (k, l) \<in> E1"
    and has_base: "\<And>r j. (r, j) \<in> E1 \<union> {x. \<exists>y. (x, y) \<in> P \<or> (y, x) \<in> P} \<Longrightarrow> \<exists>a. (r, a) \<in> E1"
    and two_base: "\<And>r. card {j. (r, j) \<in> E1} \<le> 2"
    and pair_out: "\<And>c d. (c, d) \<in> P \<Longrightarrow> c \<notin> E1 \<and> d \<notin> E1 \<and> c \<noteq> d"
    and pair_cols: "\<And>c d. (c, d) \<in> P \<Longrightarrow> snd c < n \<and> snd d < n"
    and adm: "\<And>c d. (c, d) \<in> P \<Longrightarrow> C2 (E1 \<union> {x. \<exists>y. (x, y) \<in> P \<or> (y, x) \<in> P}) c d \<and>
                                       C3 (E1 \<union> {x. \<exists>y. (x, y) \<in> P \<or> (y, x) \<in> P}) c d"
begin

definition Occ :: "(nat \<times> nat) set" where
  "Occ = E1 \<union> {x. \<exists>y. (x, y) \<in> P \<or> (y, x) \<in> P}"

definition full :: "nat \<Rightarrow> bool" where
  "full r \<longleftrightarrow> (\<forall>j < n. (r, j) \<in> Occ)"

lemma vertical_pair:
  assumes "((i, j), (p, j)) \<in> P"
  shows "supp Occ i \<inter> supp Occ p \<inter> {..<n} = {j}"
proof -
  have out: "(i, j) \<notin> E1" "(p, j) \<notin> E1" "(i, j) \<noteq> (p, j)" using pair_out[OF assms] by auto
  have jn: "j < n" using pair_cols[OF assms] by simp
  have ci: "(i, j) \<in> Occ" using assms unfolding Occ_def by blast
  have cp: "(p, j) \<in> Occ" using assms unfolding Occ_def by blast
  have C3: "C3 Occ (i, j) (p, j)" using adm[OF assms] unfolding Occ_def by blast
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix l assume "l \<in> supp Occ i \<inter> supp Occ p \<inter> {..<n}"
    then have li: "(i, l) \<in> Occ" and lp: "(p, l) \<in> Occ" and ln: "l < n"
      unfolding supp_def by auto
    show "l \<in> {j}"
    proof (rule ccontr)
      assume "l \<notin> {j}"
      then have lj: "l \<noteq> j" by simp
      obtain k where k: "(k, j) \<in> E1" "(k, l) \<in> E1" using cover[OF jn ln lj[symmetric]] by blast
      have ki: "k \<noteq> i" and kp: "k \<noteq> p" using k(1) out by auto
      have "(k, l) \<in> Occ" "(k, j) \<in> Occ" using k unfolding Occ_def by auto
      then have "\<exists>k l. k \<noteq> fst (i, j) \<and> k \<noteq> fst (p, j) \<and> l \<noteq> snd (i, j) \<and> l \<noteq> snd (p, j) \<and>
        (k, l) \<in> Occ \<and> (k, snd (i, j)) \<in> Occ \<and> (k, snd (p, j)) \<in> Occ \<and>
        (fst (i, j), l) \<in> Occ \<and> (fst (p, j), l) \<in> Occ"
        using ki kp lj li lp by auto
      then show False using C3 unfolding C3_def by blast
    qed
  next
    fix l assume "l \<in> {j}"
    then have "l = j" by simp
    then show "l \<in> supp Occ i \<inter> supp Occ p \<inter> {..<n}" using ci cp jn unfolding supp_def by auto
  qed
qed

lemma E1_in_Occ: "x \<in> E1 \<Longrightarrow> x \<in> Occ"
  unfolding Occ_def by simp

lemma pair_adm:
  assumes "(c, d) \<in> P \<or> (d, c) \<in> P"
  shows "C2 Occ c d \<and> C3 Occ c d"
  using assms
proof (rule disjE)
  assume "(c, d) \<in> P"
  then show ?thesis using adm unfolding Occ_def by blast
next
  assume "(d, c) \<in> P"
  then have "C2 Occ d c \<and> C3 Occ d c" using adm unfolding Occ_def by blast
  then show ?thesis using C2_sym C3_sym by blast
qed

lemma exists_nonbase:
  obtains j where "j < n" "(F, j) \<notin> E1"
proof (rule ccontr)
  assume H: "\<not> thesis"
  let ?B = "{j. (F, j) \<in> E1}"
  have sub: "?B \<subseteq> {..<n}" using cols by force
  have "{..<n} \<subseteq> ?B"
  proof
    fix x assume "x \<in> {..<n}"
    then have xn: "x < n" by simp
    show "x \<in> ?B"
    proof (rule ccontr)
      assume "x \<notin> ?B"
      then have "(F, x) \<notin> E1" by simp
      with xn have thesis by (rule that)
      with H show False by blast
    qed
  qed
  then have "card {..<n} \<le> card ?B" by (rule card_mono[OF finite_subset[OF sub finite_lessThan]])
  moreover have "card ?B \<le> 2" by (rule two_base)
  ultimately show False using n3 by simp
qed

lemma key:
  assumes fF: "full F" and fG: "full G" and FG: "F \<noteq> G" and jn: "j < n"
    and pr: "((F, j), (P', q)) \<in> P \<or> ((P', q), (F, j)) \<in> P"
  shows False
proof -
  have out: "(F, j) \<notin> E1" "(P', q) \<notin> E1" "(F, j) \<noteq> (P', q)" using pair_out pr by blast+
  have qn: "q < n" using pair_cols pr by force
  have ad: "C2 Occ (F, j) (P', q) \<and> C3 Occ (F, j) (P', q)" by (rule pair_adm[OF pr])
  have fF': "\<And>x. x < n \<Longrightarrow> (F, x) \<in> Occ" using fF unfolding full_def by blast
  have fG': "\<And>x. x < n \<Longrightarrow> (G, x) \<in> Occ" using fG unfolding full_def by blast
  have GF: "G \<noteq> F" by (rule not_sym[OF FG])
  show False
  proof (cases "P' = F")
    case True
    with out(3) have qj: "q \<noteq> j" by auto
    obtain l where l: "l < n" "l \<noteq> j" "l \<noteq> q" using fresh2[OF n3] by blast
    show False
      by (rule C3E[OF ad[THEN conjunct2], of G l]) (use True GF l qj fF' fG' jn qn in simp_all)
  next
    case False
    note PF = False
    have FP: "F \<noteq> P'" by (rule not_sym[OF PF])
    show False
    proof (cases "q = j")
      case True
      have V: "supp Occ F \<inter> supp Occ P' \<inter> {..<n} = {j}"
        using pr
      proof (rule disjE)
        assume "((F, j), (P', q)) \<in> P"
        with True have "((F, j), (P', j)) \<in> P" by simp
        then show ?thesis by (rule vertical_pair)
      next
        assume "((P', q), (F, j)) \<in> P"
        with True have "((P', j), (F, j)) \<in> P" by simp
        then have "supp Occ P' \<inter> supp Occ F \<inter> {..<n} = {j}" by (rule vertical_pair)
        then show ?thesis by blast
      qed
      have pq: "(P', q) \<in> E1 \<union> {x. \<exists>y. (x, y) \<in> P \<or> (y, x) \<in> P}" using pr by blast
      obtain a where a: "(P', a) \<in> E1" using has_base[OF pq] by blast
      have aj: "a \<noteq> j" using a out(2) True by auto
      have an: "a < n" using cols[OF a] by simp
      have "a \<in> supp Occ F \<inter> supp Occ P' \<inter> {..<n}"
        using fF'[OF an] E1_in_Occ[OF a] an unfolding supp_def by auto
      then show False using V aj by simp
    next
      case False
      have Fq: "(F, q) \<in> Occ" by (rule fF'[OF qn])
      have Pj: "(P', j) \<notin> Occ"
      proof
        assume h: "(P', j) \<in> Occ"
        show False
          by (rule C2E[OF ad[THEN conjunct1]]) (use FP False Fq h in simp_all)
      qed
      have pq: "(P', q) \<in> E1 \<union> {x. \<exists>y. (x, y) \<in> P \<or> (y, x) \<in> P}" using pr by blast
      obtain a where a: "(P', a) \<in> E1" using has_base[OF pq] by blast
      have Pa: "(P', a) \<in> Occ" by (rule E1_in_Occ[OF a])
      have aj: "a \<noteq> j" using Pa Pj by auto
      have aq: "a \<noteq> q" using a out(2) by auto
      have an: "a < n" using cols[OF a] by simp
      have GP: "G \<noteq> P'" using fG'[OF jn] Pj by auto
      show False
        by (rule C3E[OF ad[THEN conjunct2], of G a]) (use GF GP aj aq Pa fF' fG' jn qn an in simp_all)
    qed
  qed
qed

lemma at_most_one_full_row:
  assumes "full F" and "full G"
  shows "F = G"
proof (rule ccontr)
  assume FG: "F \<noteq> G"
  obtain j where jn: "j < n" and nb: "(F, j) \<notin> E1" by (rule exists_nonbase)
  have "(F, j) \<in> Occ" using assms(1) jn unfolding full_def by blast
  then have "(F, j) \<in> {x. \<exists>y. (x, y) \<in> P \<or> (y, x) \<in> P}" using nb unfolding Occ_def by blast
  then obtain y where y: "((F, j), y) \<in> P \<or> (y, (F, j)) \<in> P" by blast
  obtain P' q where yy: "y = (P', q)" by (cases y)
  show False by (rule key[OF assms FG jn]) (use y yy in simp)
qed

end

end
