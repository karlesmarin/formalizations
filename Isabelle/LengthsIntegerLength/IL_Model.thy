(*  Title:      IL_Model.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Integer length formula: the least number of integer squares is n + P + (z mod 2) for the graph model (lengths paper)
*)

theory IL_Model
  imports IL_Max
begin

section \<open>Disjoint unions of cycles and paths\<close>

text \<open>A component is a pair \<open>(cy, m)\<close>: a cycle with \<open>m \<ge> 3\<close> vertices if \<open>cy\<close>, otherwise a path with
\<open>m \<ge> 1\<close> vertices (a path with one vertex is an isolated vertex). The vertices of the union are the pairs
\<open>(c, k)\<close> with \<open>c\<close> a component index and \<open>k < m\<close>. The oriented matrix \<open>T0\<close> sends \<open>(c, k)\<close> to its successor.\<close>

definition okc :: "(bool \<times> nat) list \<Rightarrow> bool" where
  "okc cs \<longleftrightarrow> (\<forall>c < length cs. (fst (cs ! c) \<longrightarrow> 3 \<le> snd (cs ! c)) \<and> 1 \<le> snd (cs ! c))"

definition hn :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "hn cy m k \<longleftrightarrow> k < m \<and> (cy \<or> k + 1 < m)"

definition nxt :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nxt cy m k = (if cy \<and> k + 1 = m then 0 else k + 1)"

definition Vc :: "(bool \<times> nat) list \<Rightarrow> (nat \<times> nat) set" where
  "Vc cs = (SIGMA c:{..<length cs}. {..<snd (cs ! c)})"

definition T0 :: "(bool \<times> nat) list \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> int" where
  "T0 cs a b = (if fst a = fst b \<and> fst a < length cs \<and> hn (fst (cs ! fst a)) (snd (cs ! fst a)) (snd a)
      \<and> snd b = nxt (fst (cs ! fst a)) (snd (cs ! fst a)) (snd a) then 1 else 0)"

definition Ec :: "(bool \<times> nat) list \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "Ec cs a b \<longleftrightarrow> T0 cs a b \<noteq> 0 \<or> T0 cs b a \<noteq> 0"

definition Cz :: "(bool \<times> nat) list \<Rightarrow> nat set" where
  "Cz cs = {c \<in> {..<length cs}. \<not> fst (cs ! c) \<and> snd (cs ! c) = 1}"
definition Cp :: "(bool \<times> nat) list \<Rightarrow> nat set" where
  "Cp cs = {c \<in> {..<length cs}. \<not> fst (cs ! c) \<and> 2 \<le> snd (cs ! c)}"
definition Cn :: "(bool \<times> nat) list \<Rightarrow> nat set" where
  "Cn cs = {c \<in> {..<length cs}. \<not> fst (cs ! c)}"

lemma nxt_lt: "hn cy m k \<Longrightarrow> nxt cy m k < m"
  unfolding hn_def nxt_def by (auto split: if_splits)

lemma nxt_inj: "hn cy m k \<Longrightarrow> hn cy m k' \<Longrightarrow> (cy \<longrightarrow> 3 \<le> m) \<Longrightarrow> nxt cy m k = nxt cy m k' \<Longrightarrow> k = k'"
  unfolding hn_def nxt_def by (auto split: if_splits)

lemma nxt_not2: "hn cy m k \<Longrightarrow> hn cy m k' \<Longrightarrow> (cy \<longrightarrow> 3 \<le> m) \<Longrightarrow> nxt cy m k = k' \<Longrightarrow> nxt cy m k' = k \<Longrightarrow> False"
  unfolding hn_def nxt_def by (auto split: if_splits)

lemma okc_cy: "okc cs \<Longrightarrow> c < length cs \<Longrightarrow> fst (cs ! c) \<longrightarrow> 3 \<le> snd (cs ! c)"
  unfolding okc_def by blast

lemma okc_pos: "okc cs \<Longrightarrow> c < length cs \<Longrightarrow> 1 \<le> snd (cs ! c)"
  unfolding okc_def by blast

lemma Vc_mem: "a \<in> Vc cs \<longleftrightarrow> fst a < length cs \<and> snd a < snd (cs ! fst a)"
  unfolding Vc_def by (cases a) simp

lemma fin_Vc: "finite (Vc cs)"
  unfolding Vc_def by (rule finite_SigmaI) simp_all

lemma T0_nz: "T0 cs a b \<noteq> 0 \<longleftrightarrow> fst a = fst b \<and> fst a < length cs \<and>
    hn (fst (cs ! fst a)) (snd (cs ! fst a)) (snd a) \<and> snd b = nxt (fst (cs ! fst a)) (snd (cs ! fst a)) (snd a)"
  unfolding T0_def by (auto split: if_splits)

lemma T0_val: "T0 cs a b = 0 \<or> T0 cs a b = 1"
  unfolding T0_def by simp

lemma T0_no2:
  assumes ok: "okc cs" and x: "T0 cs a b \<noteq> 0" and y: "T0 cs b a \<noteq> 0"
  shows False
proof -
  have x': "fst a = fst b" "fst a < length cs" "hn (fst (cs ! fst a)) (snd (cs ! fst a)) (snd a)"
    "snd b = nxt (fst (cs ! fst a)) (snd (cs ! fst a)) (snd a)" using x unfolding T0_nz by auto
  have y': "fst b = fst a" "hn (fst (cs ! fst b)) (snd (cs ! fst b)) (snd b)"
    "snd a = nxt (fst (cs ! fst b)) (snd (cs ! fst b)) (snd b)" using y unfolding T0_nz by auto
  have e: "fst b = fst a" by (rule y'(1))
  have h2: "hn (fst (cs ! fst a)) (snd (cs ! fst a)) (snd b)" using y'(2) unfolding e .
  have n2: "snd a = nxt (fst (cs ! fst a)) (snd (cs ! fst a)) (snd b)" using y'(3) unfolding e .
  show False
    by (rule nxt_not2[OF x'(3) h2 okc_cy[OF ok x'(2)] x'(4)[symmetric] n2[symmetric]])
qed

lemma T0_supp:
  assumes x: "T0 cs a b \<noteq> 0"
  shows "a \<in> Vc cs \<and> b \<in> Vc cs"
proof -
  have x': "fst a = fst b" "fst a < length cs" "hn (fst (cs ! fst a)) (snd (cs ! fst a)) (snd a)"
    "snd b = nxt (fst (cs ! fst a)) (snd (cs ! fst a)) (snd a)" using x unfolding T0_nz by auto
  have sa: "snd a < snd (cs ! fst a)" using x'(3) unfolding hn_def by simp
  have sb: "snd b < snd (cs ! fst a)" using nxt_lt[OF x'(3)] x'(4) by simp
  have fb: "fst b = fst a" using x'(1) by simp
  have ca: "a \<in> Vc cs" unfolding Vc_mem using x'(2) sa by simp
  have cb: "b \<in> Vc cs" unfolding Vc_mem fb using x'(2) sb by simp
  show ?thesis using ca cb by simp
qed

lemma T0_col:
  assumes ok: "okc cs" and x: "T0 cs a c \<noteq> 0" and y: "T0 cs b c \<noteq> 0"
  shows "a = b"
proof -
  have x': "fst a = fst c" "fst a < length cs" "hn (fst (cs ! fst a)) (snd (cs ! fst a)) (snd a)"
    "snd c = nxt (fst (cs ! fst a)) (snd (cs ! fst a)) (snd a)" using x unfolding T0_nz by auto
  have y': "fst b = fst c" "hn (fst (cs ! fst b)) (snd (cs ! fst b)) (snd b)"
    "snd c = nxt (fst (cs ! fst b)) (snd (cs ! fst b)) (snd b)" using y unfolding T0_nz by auto
  have e: "fst b = fst a" using x'(1) y'(1) by simp
  have h2: "hn (fst (cs ! fst a)) (snd (cs ! fst a)) (snd b)" using y'(2) unfolding e .
  have n2: "snd c = nxt (fst (cs ! fst a)) (snd (cs ! fst a)) (snd b)" using y'(3) unfolding e .
  have "snd a = snd b" by (rule nxt_inj[OF x'(3) h2 okc_cy[OF ok x'(2)]]) (use x'(4) n2 in simp)
  thus "a = b" using e by (simp add: prod_eq_iff)
qed

lemma T0_row:
  assumes x: "T0 cs a b \<noteq> 0" and y: "T0 cs a c \<noteq> 0"
  shows "b = c"
  using x y unfolding T0_nz by (auto simp: prod_eq_iff)

lemma T0_psp:
  assumes ok: "okc cs"
  shows "psp (Vc cs) (T0 cs)"
  unfolding psp_def
proof (intro conjI)
  show "\<forall>i j. T0 cs i j \<noteq> 0 \<longrightarrow> i \<in> Vc cs \<and> j \<in> Vc cs" using T0_supp by blast
next
  show "\<forall>i j. T0 cs i j = 0 \<or> T0 cs i j = 1 \<or> T0 cs i j = -1"
  proof (intro allI)
    fix i j
    have "T0 cs i j = 0 \<or> T0 cs i j = 1" by (rule T0_val)
    thus "T0 cs i j = 0 \<or> T0 cs i j = 1 \<or> T0 cs i j = -1" by blast
  qed
next
  show "\<forall>i j k. T0 cs i j \<noteq> 0 \<longrightarrow> T0 cs i k \<noteq> 0 \<longrightarrow> j = k" using T0_row by blast
next
  show "\<forall>i j k. T0 cs i k \<noteq> 0 \<longrightarrow> T0 cs j k \<noteq> 0 \<longrightarrow> i = j" using T0_col[OF ok] by blast
qed

lemma T0_rep:
  assumes ok: "okc cs"
  shows "rep (Vc cs) (Ec cs) (T0 cs)"
  unfolding rep_def
proof (intro conjI ballI)
  show "psp (Vc cs) (T0 cs)" by (rule T0_psp[OF ok])
next
  fix a b
  have v1: "T0 cs a b = 0 \<or> T0 cs a b = 1" by (rule T0_val)
  have v2: "T0 cs b a = 0 \<or> T0 cs b a = 1" by (rule T0_val)
  have n2: "\<not> (T0 cs a b \<noteq> 0 \<and> T0 cs b a \<noteq> 0)" using T0_no2[OF ok] by blast
  show "T0 cs a b + T0 cs b a = (if Ec cs a b then 1 else 0)"
  proof (cases "Ec cs a b")
    case True
    hence "T0 cs a b \<noteq> 0 \<or> T0 cs b a \<noteq> 0" unfolding Ec_def .
    hence "T0 cs a b + T0 cs b a = 1" by (rule int01[OF v1 v2 n2])
    thus ?thesis using True by simp
  next
    case False
    hence "T0 cs a b = 0" "T0 cs b a = 0" unfolding Ec_def by auto
    thus ?thesis using False by simp
  qed
qed

lemma lgraph_Vc:
  assumes ok: "okc cs"
  shows "lgraph (Vc cs) (Ec cs)"
proof (unfold_locales)
  show "finite (Vc cs)" by (rule fin_Vc)
next
  fix i j assume "Ec cs i j" thus "Ec cs j i" unfolding Ec_def by blast
next
  fix i show "\<not> Ec cs i i"
  proof
    assume "Ec cs i i"
    hence h: "T0 cs i i \<noteq> 0" unfolding Ec_def by blast
    show False by (rule T0_no2[OF ok h h])
  qed
next
  fix i j assume "Ec cs i j"
  hence "T0 cs i j \<noteq> 0 \<or> T0 cs j i \<noteq> 0" unfolding Ec_def .
  thus "i \<in> Vc cs \<and> j \<in> Vc cs"
  proof
    assume "T0 cs i j \<noteq> 0" thus ?thesis by (rule T0_supp)
  next
    assume "T0 cs j i \<noteq> 0"
    hence "j \<in> Vc cs \<and> i \<in> Vc cs" by (rule T0_supp)
    thus ?thesis by simp
  qed
qed

end
