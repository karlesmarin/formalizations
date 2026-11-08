(*  Title:      ERT_Choosability.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín (the proofs). All rights reserved.
    Statement:  definitions and statement transcribed from google-deepmind/formal-conjectures
                (Apache License 2.0); they are not ours.
    License:    BSD
*)

theory ERT_Choosability
  imports Main
begin

section \<open>Erdos--Rubin--Taylor 1980: n(2) = 6\<close>

text \<open>Faithful transcription of the definitions of formal-conjectures
(ErdosProblems/629.lean, Wikipedia/OhbaConjecture.lean, FormalConjecturesForMathlib/.../List.lean).
Vertices are @{term "{..<m}"}; a graph is a relation \<open>E\<close> supported on them, symmetric, irreflexive;
colours are naturals; a list assignment gives a finite set of cardinality exactly \<open>k\<close> to each vertex.\<close>

definition sgraph :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "sgraph m E \<longleftrightarrow> (\<forall>u v. E u v \<longrightarrow> u < m \<and> v < m) \<and> (\<forall>u v. E u v \<longrightarrow> E v u) \<and> (\<forall>v. \<not> E v v)"

definition bipartite :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "bipartite m E \<longleftrightarrow> (\<exists>f::nat \<Rightarrow> nat. (\<forall>v<m. f v < 2) \<and> (\<forall>u v. E u v \<longrightarrow> f u \<noteq> f v))"

definition choosable :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "choosable m E k \<longleftrightarrow> (\<forall>L::nat \<Rightarrow> nat set. (\<forall>v<m. finite (L v) \<and> card (L v) = k) \<longrightarrow>
      (\<exists>c::nat \<Rightarrow> nat. (\<forall>v<m. c v \<in> L v) \<and> (\<forall>u v. E u v \<longrightarrow> c u \<noteq> c v)))"

definition list_chrom :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat" where
  "list_chrom m E = Inf {k. choosable m E k}"

definition n_choose :: "nat \<Rightarrow> nat" where
  "n_choose k = Inf {m. \<exists>E. sgraph m E \<and> bipartite m E \<and> k < list_chrom m E}"

subsection \<open>A criterion for choosability of bipartite graphs\<close>

lemma core_choose:
  assumes cover: "A \<union> B = {..<m}" and disj: "A \<inter> B = {}"
    and cross: "\<forall>u v. E u v \<longrightarrow> (u \<in> A \<and> v \<in> B) \<or> (u \<in> B \<and> v \<in> A)"
    and good: "\<forall>L::nat \<Rightarrow> nat set. (\<forall>v<m. finite (L v) \<and> card (L v) = k) \<longrightarrow>
        (\<exists>cA. (\<forall>a\<in>A. cA a \<in> L a) \<and> (\<forall>b\<in>B. \<not> L b \<subseteq> cA ` A))"
  shows "choosable m E k"
  unfolding choosable_def
proof (intro allI impI)
  fix L :: "nat \<Rightarrow> nat set"
  assume hL: "\<forall>v<m. finite (L v) \<and> card (L v) = k"
  obtain cA where cA1: "\<forall>a\<in>A. cA a \<in> L a" and cA2: "\<forall>b\<in>B. \<not> L b \<subseteq> cA ` A"
    using good hL by blast
  define c where "c v = (if v \<in> A then cA v else (SOME z. z \<in> L v \<and> z \<notin> cA ` A))" for v
  have cB: "b \<in> B \<Longrightarrow> c b \<in> L b \<and> c b \<notin> cA ` A" for b
  proof -
    assume hb: "b \<in> B"
    hence "b \<notin> A" using disj by blast
    from cA2 hb obtain z where "z \<in> L b" "z \<notin> cA ` A" by blast
    hence "\<exists>z. z \<in> L b \<and> z \<notin> cA ` A" by blast
    from someI_ex[OF this] show ?thesis using \<open>b \<notin> A\<close> by (simp add: c_def)
  qed
  have cAeq: "a \<in> A \<Longrightarrow> c a = cA a" for a by (simp add: c_def)
  have "\<forall>v<m. c v \<in> L v"
  proof (intro allI impI)
    fix v assume "v < m"
    hence "v \<in> A \<union> B" using cover by auto
    thus "c v \<in> L v"
    proof
      assume "v \<in> A" thus ?thesis using cAeq cA1 by simp
    next
      assume "v \<in> B" thus ?thesis using cB by blast
    qed
  qed
  moreover have "\<forall>u v. E u v \<longrightarrow> c u \<noteq> c v"
  proof (intro allI impI)
    fix u v assume "E u v"
    from cross[rule_format, OF this] show "c u \<noteq> c v"
    proof
      assume "u \<in> A \<and> v \<in> B"
      hence "c u = cA u" "c v \<notin> cA ` A" "u \<in> A" using cB cAeq by auto
      thus ?thesis by (metis imageI)
    next
      assume "u \<in> B \<and> v \<in> A"
      hence "c v = cA v" "c u \<notin> cA ` A" "v \<in> A" using cB cAeq by auto
      thus ?thesis by (metis imageI)
    qed
  qed
  ultimately show "\<exists>c. (\<forall>v<m. c v \<in> L v) \<and> (\<forall>u v. E u v \<longrightarrow> c u \<noteq> c v)" by blast
qed

lemma card2_sub_eq:
  assumes "finite S" "card S = 2" "S \<subseteq> {x, y}"
  shows "S = {x, y}"
proof (rule card_seteq[OF _ assms(3)])
  show "finite {x, y}" by simp
  show "card {x, y} \<le> card S" using assms(2) by (simp add: card_insert_if)
qed

lemma card2_not_sub1:
  assumes "finite S" "card S = 2"
  shows "\<not> S \<subseteq> {x}"
proof
  assume "S \<subseteq> {x}"
  from card_mono[OF _ this] have "card S \<le> 1" by simp
  thus False using assms(2) by simp
qed

subsection \<open>Two lists on one side, at most three vertices on the other\<close>

lemma pairs_lemma:
  assumes P: "finite P" "card P = 2" and Q: "finite Q" "card Q = 2"
    and B: "finite B" "card B \<le> 3" and M: "\<forall>b\<in>B. finite (M b) \<and> card (M b) = 2"
  shows "\<exists>x\<in>P. \<exists>y\<in>Q. \<forall>b\<in>B. \<not> M b \<subseteq> {x, y}"
proof (cases "P \<inter> Q = {}")
  case False
  then obtain x where xP: "x \<in> P" and xQ: "x \<in> Q" by blast
  have "\<forall>b\<in>B. \<not> M b \<subseteq> {x, x}"
    using M card2_not_sub1 by (metis insert_absorb2)
  with xP xQ show ?thesis by blast
next
  case True
  show ?thesis
  proof (rule ccontr)
    assume nt: "\<not> ?thesis"
    have neg: "\<forall>x\<in>P. \<forall>y\<in>Q. \<exists>b\<in>B. M b \<subseteq> {x, y}" using nt by blast
    have h: "\<forall>p\<in>P \<times> Q. \<exists>b. b \<in> B \<and> M b \<subseteq> {fst p, snd p}"
    proof (intro ballI)
      fix p assume pp: "p \<in> P \<times> Q"
      obtain x y where pe: "p = (x, y)" by (cases p)
      with pp have "x \<in> P" "y \<in> Q" by auto
      with neg have "\<exists>b\<in>B. M b \<subseteq> {x, y}" by blast
      thus "\<exists>b. b \<in> B \<and> M b \<subseteq> {fst p, snd p}" using pe by auto
    qed
    obtain g where g: "\<forall>p\<in>P \<times> Q. g p \<in> B \<and> M (g p) \<subseteq> {fst p, snd p}"
      using bchoice[OF h] by blast
    have inj: "inj_on g (P \<times> Q)"
    proof (rule inj_onI)
      fix p q assume pp: "p \<in> P \<times> Q" and qq: "q \<in> P \<times> Q" and gg: "g p = g q"
      obtain x y where p: "p = (x, y)" by (cases p)
      obtain x' y' where q: "q = (x', y')" by (cases q)
      have gp: "g p \<in> B \<and> M (g p) \<subseteq> {fst p, snd p}" using g pp by blast
      have gq: "g q \<in> B \<and> M (g q) \<subseteq> {fst q, snd q}" using g qq by blast
      define b where "b = g p"
      have bB: "b \<in> B" using gp by (simp add: b_def)
      have s1: "M b \<subseteq> {x, y}" using gp p by (simp add: b_def)
      have s2: "M b \<subseteq> {x', y'}" using gq q gg by (simp add: b_def)
      have Mb: "finite (M b)" "card (M b) = 2" using M bB by auto
      have e1: "M b = {x, y}" by (rule card2_sub_eq[OF Mb s1])
      have e2: "M b = {x', y'}" by (rule card2_sub_eq[OF Mb s2])
      have eq: "{x, y} = {x', y'}" using e1 e2 by simp
      have xP: "x \<in> P" and yQ: "y \<in> Q" and xP': "x' \<in> P" and yQ': "y' \<in> Q"
        using pp qq p q by auto
      have "x \<in> {x', y'}" using eq by auto
      hence "x = x' \<or> x = y'" by simp
      hence "x = x'" using xP yQ' True by auto
      moreover have "y \<in> {x', y'}" using eq by auto
      hence "y = x' \<or> y = y'" by simp
      hence "y = y'" using yQ xP' True by auto
      ultimately show "p = q" using p q by simp
    qed
    have sub: "g ` (P \<times> Q) \<subseteq> B" using g by auto
    have "card (P \<times> Q) \<le> card B" using card_inj_on_le[OF inj sub B(1)] .
    moreover have "card (P \<times> Q) = 4" using P Q by (simp add: card_cartesian_product)
    ultimately show False using B(2) by simp
  qed
qed

lemma K2m_choose:
  assumes cover: "A \<union> B = {..<m}" and disj: "A \<inter> B = {}"
    and cross: "\<forall>u v. E u v \<longrightarrow> (u \<in> A \<and> v \<in> B) \<or> (u \<in> B \<and> v \<in> A)"
    and cA: "card A = 2" and cB: "card B \<le> 3"
  shows "choosable m E 2"
proof (rule core_choose[OF cover disj cross])
  obtain a1 a2 where A: "A = {a1, a2}" and ne: "a1 \<noteq> a2" using cA by (auto simp: card_2_iff)
  have fB: "finite B" using cover by (metis finite_Un finite_lessThan)
  show "\<forall>L::nat \<Rightarrow> nat set. (\<forall>v<m. finite (L v) \<and> card (L v) = 2) \<longrightarrow>
        (\<exists>cA. (\<forall>a\<in>A. cA a \<in> L a) \<and> (\<forall>b\<in>B. \<not> L b \<subseteq> cA ` A))"
  proof (intro allI impI)
    fix L :: "nat \<Rightarrow> nat set"
    assume hL: "\<forall>v<m. finite (L v) \<and> card (L v) = 2"
    have a1m: "a1 < m" and a2m: "a2 < m" using A cover by auto
    have Bm: "\<forall>b\<in>B. finite (L b) \<and> card (L b) = 2" using hL cover by auto
    from pairs_lemma[where P = "L a1" and Q = "L a2" and B = B and M = L]
    obtain x y where xy: "x \<in> L a1" "y \<in> L a2" "\<forall>b\<in>B. \<not> L b \<subseteq> {x, y}"
      using hL a1m a2m fB cB Bm by blast
    define cA where "cA v = (if v = a1 then x else y)" for v
    have "cA ` A = {x, y}" using A ne by (auto simp: cA_def)
    moreover have "\<forall>a\<in>A. cA a \<in> L a" using A ne xy by (auto simp: cA_def)
    ultimately show "\<exists>cA. (\<forall>a\<in>A. cA a \<in> L a) \<and> (\<forall>b\<in>B. \<not> L b \<subseteq> cA ` A)"
      using xy(3) by metis
  qed
qed

lemma star_choose:
  assumes cover: "A \<union> B = {..<m}" and disj: "A \<inter> B = {}"
    and cross: "\<forall>u v. E u v \<longrightarrow> (u \<in> A \<and> v \<in> B) \<or> (u \<in> B \<and> v \<in> A)"
    and cA: "card A \<le> 1"
  shows "choosable m E 2"
proof (rule core_choose[OF cover disj cross])
  have fA: "finite A" using cover by (metis finite_Un finite_lessThan)
  show "\<forall>L::nat \<Rightarrow> nat set. (\<forall>v<m. finite (L v) \<and> card (L v) = 2) \<longrightarrow>
        (\<exists>cA. (\<forall>a\<in>A. cA a \<in> L a) \<and> (\<forall>b\<in>B. \<not> L b \<subseteq> cA ` A))"
  proof (intro allI impI)
    fix L :: "nat \<Rightarrow> nat set"
    assume hL: "\<forall>v<m. finite (L v) \<and> card (L v) = 2"
    have Bm: "\<forall>b\<in>B. finite (L b) \<and> card (L b) = 2" using hL cover by auto
    from cA fA have "A = {} \<or> (\<exists>a. A = {a})"
      by (metis card_0_eq le_Suc_eq card_1_singleton_iff le_zero_eq One_nat_def)
    thus "\<exists>cA. (\<forall>a\<in>A. cA a \<in> L a) \<and> (\<forall>b\<in>B. \<not> L b \<subseteq> cA ` A)"
    proof
      assume e: "A = {}"
      show ?thesis
      proof (intro exI[of _ "\<lambda>_. 0"] conjI ballI)
        fix a assume "a \<in> A" thus "(\<lambda>_. 0) a \<in> L a" using e by simp
      next
        fix b assume "b \<in> B"
        hence "finite (L b)" "card (L b) = 2" using Bm by auto
        thus "\<not> L b \<subseteq> (\<lambda>_. 0) ` A" using e by (auto simp: card_eq_0_iff)
      qed
    next
      assume "\<exists>a. A = {a}"
      then obtain a where ea: "A = {a}" by blast
      hence am: "a < m" using cover by auto
      with hL have "finite (L a)" "card (L a) = 2" by auto
      then obtain x where xa: "x \<in> L a" by (metis card_2_iff insertI1)
      show ?thesis
      proof (intro exI[of _ "\<lambda>_. x"] conjI ballI)
        fix a' assume "a' \<in> A" thus "(\<lambda>_. x) a' \<in> L a'" using ea xa by simp
      next
        fix b assume "b \<in> B"
        hence "finite (L b)" "card (L b) = 2" using Bm by auto
        thus "\<not> L b \<subseteq> (\<lambda>_. x) ` A" using ea card2_not_sub1 by simp
      qed
    qed
  qed
qed

subsection \<open>(b) Every bipartite graph with at most 5 vertices is 2-choosable\<close>

lemma bip_le5_choosable:
  assumes g: "sgraph m E" and b: "bipartite m E" and m5: "m \<le> 5"
  shows "choosable m E 2"
proof -
  obtain f :: "nat \<Rightarrow> nat" where f2: "\<forall>v<m. f v < 2" and fE: "\<forall>u v. E u v \<longrightarrow> f u \<noteq> f v"
    using b unfolding bipartite_def by blast
  define A where "A = {v. v < m \<and> f v = 0}"
  define B where "B = {v. v < m \<and> f v = 1}"
  have cover: "A \<union> B = {..<m}" using f2 unfolding A_def B_def by auto
  have disj: "A \<inter> B = {}" unfolding A_def B_def by auto
  have cross: "\<forall>u v. E u v \<longrightarrow> (u \<in> A \<and> v \<in> B) \<or> (u \<in> B \<and> v \<in> A)"
  proof (intro allI impI)
    fix u v assume e: "E u v"
    hence um: "u < m" and vm: "v < m" using g unfolding sgraph_def by auto
    have "f u < 2" "f v < 2" "f u \<noteq> f v" using f2 um vm fE e by auto
    thus "(u \<in> A \<and> v \<in> B) \<or> (u \<in> B \<and> v \<in> A)" using um vm unfolding A_def B_def by auto
  qed
  have cross': "\<forall>u v. E u v \<longrightarrow> (u \<in> B \<and> v \<in> A) \<or> (u \<in> A \<and> v \<in> B)" using cross by blast
  have fin: "finite A" "finite B" using cover by (metis finite_Un finite_lessThan)+
  have sum: "card A + card B = m" using card_Un_disjoint[OF fin disj] cover by simp
  have cover': "B \<union> A = {..<m}" using cover by auto
  have disj': "B \<inter> A = {}" using disj by auto
  show ?thesis
  proof (cases "card A \<le> 1")
    case True thus ?thesis using star_choose[OF cover disj cross] by blast
  next
    case False
    hence nA: "\<not> card A \<le> 1" .
    show ?thesis
    proof (cases "card B \<le> 1")
      case True thus ?thesis using star_choose[OF cover' disj' cross'] by blast
    next
      case False
      hence nB: "\<not> card B \<le> 1" .
      from nA nB m5 sum have "card A = 2 \<or> card B = 2" by arith
      thus ?thesis
      proof
        assume "card A = 2"
        with sum m5 have "card B \<le> 3" by arith
        thus ?thesis using K2m_choose[OF cover disj cross \<open>card A = 2\<close>] by blast
      next
        assume "card B = 2"
        with sum m5 have "card A \<le> 3" by arith
        thus ?thesis using K2m_choose[OF cover' disj' cross' \<open>card B = 2\<close>] by blast
      qed
    qed
  qed
qed

subsection \<open>(a) $K_{3,3}$ is not 2-choosable, but is 4-choosable\<close>

definition K33 :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "K33 u v \<longleftrightarrow> (u < 3 \<and> 3 \<le> v \<and> v < 6) \<or> (v < 3 \<and> 3 \<le> u \<and> u < 6)"

lemma K33_sgraph: "sgraph 6 K33"
  unfolding sgraph_def K33_def by auto

lemma K33_bipartite: "bipartite 6 K33"
  unfolding bipartite_def K33_def by (intro exI[of _ "\<lambda>v. if v < 3 then 0 else 1"]) auto

lemma K33_not_choosable_le2: "j \<le> 2 \<Longrightarrow> \<not> choosable 6 K33 j"
proof -
  assume "j \<le> 2"
  hence "j = 0 \<or> j = 1 \<or> j = 2" by arith
  thus ?thesis
  proof (elim disjE)
    assume j0: "j = 0"
    show ?thesis unfolding choosable_def
    proof
      assume h: "\<forall>L::nat \<Rightarrow> nat set. (\<forall>v<6. finite (L v) \<and> card (L v) = j) \<longrightarrow>
        (\<exists>c::nat \<Rightarrow> nat. (\<forall>v<6. c v \<in> L v) \<and> (\<forall>u v. K33 u v \<longrightarrow> c u \<noteq> c v))"
      have p: "\<forall>v<6. finite ({}::nat set) \<and> card ({}::nat set) = j" using j0 by simp
      from mp[OF spec[OF h, of "\<lambda>_. {}"] p] obtain c :: "nat \<Rightarrow> nat" where c0: "\<forall>v<6. c v \<in> {}" by blast
      from c0[rule_format, of 0] show False by simp
    qed
  next
    assume j1: "j = 1"
    show ?thesis unfolding choosable_def
    proof
      assume h: "\<forall>L::nat \<Rightarrow> nat set. (\<forall>v<6. finite (L v) \<and> card (L v) = j) \<longrightarrow>
        (\<exists>c::nat \<Rightarrow> nat. (\<forall>v<6. c v \<in> L v) \<and> (\<forall>u v. K33 u v \<longrightarrow> c u \<noteq> c v))"
      have p: "\<forall>v<6. finite ({0}::nat set) \<and> card ({0}::nat set) = j" using j1 by simp
      from mp[OF spec[OF h, of "\<lambda>_. {0}"] p]
      obtain c :: "nat \<Rightarrow> nat" where c1: "\<forall>v<6. c v \<in> {0}" and c2: "\<forall>u v. K33 u v \<longrightarrow> c u \<noteq> c v" by blast
      have z0: "c 0 = 0" and z3: "c 3 = 0" using c1 by auto
      have k: "K33 0 3" unfolding K33_def by simp
      have "c 0 \<noteq> c 3" using c2 k by blast
      thus False using z0 z3 by simp
    qed
  next
    assume "j = 2"
    define L :: "nat \<Rightarrow> nat set" where
      "L v = (if v mod 3 = 0 then {1, 2} else if v mod 3 = 1 then {1, 3} else {2, 3})" for v
    have "\<forall>v<6. finite (L v) \<and> card (L v) = 2" by (simp add: L_def)
    moreover have "\<not> (\<exists>c. (\<forall>v<6. c v \<in> L v) \<and> (\<forall>u v. K33 u v \<longrightarrow> c u \<noteq> c v))"
    proof
      assume "\<exists>c. (\<forall>v<6. c v \<in> L v) \<and> (\<forall>u v. K33 u v \<longrightarrow> c u \<noteq> c v)"
      then obtain c where hc: "\<forall>v<6. c v \<in> L v" and he: "\<forall>u v. K33 u v \<longrightarrow> c u \<noteq> c v" by blast
      have c0: "c 0 = 1 \<or> c 0 = 2" using hc[rule_format, of 0] by (simp add: L_def)
      have c1: "c 1 = 1 \<or> c 1 = 3" using hc[rule_format, of 1] by (simp add: L_def)
      have c2: "c 2 = 2 \<or> c 2 = 3" using hc[rule_format, of 2] by (simp add: L_def)
      have c3: "c 3 = 1 \<or> c 3 = 2" using hc[rule_format, of 3] by (simp add: L_def)
      have c4: "c 4 = 1 \<or> c 4 = 3" using hc[rule_format, of 4] by (simp add: L_def)
      have c5: "c 5 = 2 \<or> c 5 = 3" using hc[rule_format, of 5] by (simp add: L_def)
      have e: "\<forall>i<3. \<forall>j. 3 \<le> j \<and> j < 6 \<longrightarrow> c i \<noteq> c j" using he unfolding K33_def by auto
      have e03: "c 0 \<noteq> c 3" and e04: "c 0 \<noteq> c 4" and e05: "c 0 \<noteq> c 5"
        and e13: "c 1 \<noteq> c 3" and e14: "c 1 \<noteq> c 4" and e15: "c 1 \<noteq> c 5"
        and e23: "c 2 \<noteq> c 3" and e24: "c 2 \<noteq> c 4" and e25: "c 2 \<noteq> c 5"
        using e by auto
      from c0 c1 c2 c3 c4 c5 e03 e04 e05 e13 e14 e15 e23 e24 e25 show False by auto
    qed
    ultimately show ?thesis unfolding choosable_def \<open>j = 2\<close> by blast
  qed
qed

lemma K33_choosable4: "choosable 6 K33 4"
proof (rule core_choose[where A = "{0, 1, 2}" and B = "{3, 4, 5}"])
  show "{0, 1, 2} \<union> {3, 4, 5} = {..<(6::nat)}" by auto
  show "{0, 1, 2} \<inter> {3, 4, 5} = ({}::nat set)" by auto
  show "\<forall>u v. K33 u v \<longrightarrow> (u \<in> {0, 1, 2} \<and> v \<in> {3, 4, 5}) \<or> (u \<in> {3, 4, 5} \<and> v \<in> {0, 1, 2})"
    unfolding K33_def by auto
  show "\<forall>L::nat \<Rightarrow> nat set. (\<forall>v<6. finite (L v) \<and> card (L v) = 4) \<longrightarrow>
      (\<exists>cA. (\<forall>a\<in>{0, 1, 2}. cA a \<in> L a) \<and> (\<forall>b\<in>{3, 4, 5}. \<not> L b \<subseteq> cA ` {0, 1, 2}))"
  proof (intro allI impI)
    fix L :: "nat \<Rightarrow> nat set"
    assume hL: "\<forall>v<6. finite (L v) \<and> card (L v) = 4"
    define cA where "cA v = (SOME x. x \<in> L v)" for v
    have ne: "\<forall>v<6. L v \<noteq> {}" using hL by (metis card_eq_0_iff zero_neq_numeral)
    have "\<forall>a\<in>{0, 1, 2::nat}. cA a \<in> L a"
    proof (intro ballI)
      fix a assume "a \<in> {0, 1, 2::nat}"
      hence "a < 6" by auto
      with ne obtain y where "y \<in> L a" by blast
      thus "cA a \<in> L a" unfolding cA_def by (rule someI)
    qed
    moreover have "\<forall>b\<in>{3, 4, 5::nat}. \<not> L b \<subseteq> cA ` {0, 1, 2}"
    proof
      fix b assume bb: "b \<in> {3, 4, 5::nat}"
      show "\<not> L b \<subseteq> cA ` {0, 1, 2}"
      proof
        assume sub: "L b \<subseteq> cA ` {0, 1, 2}"
        have "card (cA ` {0, 1, 2::nat}) \<le> card {0, 1, 2::nat}" by (rule card_image_le) simp
        hence "card (cA ` {0, 1, 2::nat}) \<le> 3" by simp
        moreover have "card (L b) \<le> card (cA ` {0, 1, 2::nat})" using card_mono[OF _ sub] by simp
        moreover have "card (L b) = 4" using hL bb by auto
        ultimately show False by simp
      qed
    qed
    ultimately show "\<exists>cA. (\<forall>a\<in>{0, 1, 2}. cA a \<in> L a) \<and> (\<forall>b\<in>{3, 4, 5}. \<not> L b \<subseteq> cA ` {0, 1, 2})"
      by blast
  qed
qed

lemma K33_list_chrom_gt2: "2 < list_chrom 6 K33"
proof -
  have ne: "{k. choosable 6 K33 k} \<noteq> {}" using K33_choosable4 by auto
  from Inf_nat_def1[OF ne] have "choosable 6 K33 (list_chrom 6 K33)"
    unfolding list_chrom_def by simp
  with K33_not_choosable_le2 show ?thesis by (metis not_le_imp_less)
qed

lemma le5_not_in:
  assumes "m \<le> 5" "sgraph m E" "bipartite m E"
  shows "\<not> 2 < list_chrom m E"
proof -
  have "choosable m E 2" using bip_le5_choosable assms by blast
  hence "list_chrom m E \<le> 2" unfolding list_chrom_def by (intro cInf_lower) auto
  thus ?thesis by simp
qed

subsection \<open>(c) The theorem\<close>

theorem ert_n_two: "n_choose 2 = 6"
proof -
  let ?S = "{m. \<exists>E. sgraph m E \<and> bipartite m E \<and> 2 < list_chrom m E}"
  have in6: "6 \<in> ?S" using K33_sgraph K33_bipartite K33_list_chrom_gt2 by blast
  have ge: "\<forall>m\<in>?S. 6 \<le> m"
  proof
    fix m assume "m \<in> ?S"
    then obtain E where "sgraph m E" "bipartite m E" "2 < list_chrom m E" by blast
    thus "6 \<le> m" using le5_not_in[of m E] by (cases "m \<le> 5") auto
  qed
  have "Inf ?S \<le> 6" using in6 by (intro cInf_lower) auto
  moreover have "6 \<le> Inf ?S" using in6 ge by (intro cInf_greatest) auto
  ultimately show ?thesis unfolding n_choose_def by simp
qed

end
