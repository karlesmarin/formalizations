(*  Title:      IL_Ext_Rep.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Integer length formula: the least number of integer squares is n + P + (z mod 2) for the graph model (lengths paper)
*)

theory IL_Ext_Rep
  imports Integer_Length
begin

section \<open>Pairing two free isolated vertices\<close>

definition ext :: "('v \<Rightarrow> 'v \<Rightarrow> int) \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> int" where
  "ext T i j a b = (if a = i \<and> b = j then 1 else if a = j \<and> b = i then -1 else T a b)"

lemma ext_1: assumes h: "a = i \<and> b = j" shows "ext T i j a b = 1"
  unfolding ext_def by (rule if_P[OF h])

lemma ext_2: assumes h1: "\<not> (a = i \<and> b = j)" and h2: "a = j \<and> b = i" shows "ext T i j a b = -1"
  unfolding ext_def by (subst if_not_P[OF h1], rule if_P[OF h2])

lemma ext_3: assumes h1: "\<not> (a = i \<and> b = j)" and h2: "\<not> (a = j \<and> b = i)" shows "ext T i j a b = T a b"
  unfolding ext_def by (subst if_not_P[OF h1], rule if_not_P[OF h2])

lemma ext_val:
  assumes v: "T a b = 0 \<or> T a b = 1 \<or> T a b = -1"
  shows "ext T i j a b = 0 \<or> ext T i j a b = 1 \<or> ext T i j a b = -1"
proof (cases "a = i \<and> b = j")
  case c1: True
  have "ext T i j a b = 1" by (rule ext_1[OF c1])
  thus ?thesis by (rule disjI2[OF disjI1])
next
  case c1: False
  show ?thesis
  proof (cases "a = j \<and> b = i")
    case c2: True
    have "ext T i j a b = -1" by (rule ext_2[OF c1 c2])
    thus ?thesis by (rule disjI2[OF disjI2])
  next
    case c2: False
    have e: "ext T i j a b = T a b" by (rule ext_3[OF c1 c2])
    show ?thesis using v unfolding e .
  qed
qed

context
  fixes T :: "'v \<Rightarrow> 'v \<Rightarrow> int" and i j :: 'v
  assumes ne: "i \<noteq> j"
    and i0: "\<And>k. T i k = 0" and i1: "\<And>k. T k i = 0"
    and j0: "\<And>k. T j k = 0" and j1: "\<And>k. T k j = 0"
begin

lemma T_away:
  assumes h: "T a b \<noteq> 0"
  shows "a \<noteq> i \<and> a \<noteq> j \<and> b \<noteq> i \<and> b \<noteq> j"
proof (intro conjI notI)
  assume e: "a = i"
  have "T a b = 0" unfolding e by (rule i0)
  thus False using h by (rule notE[rotated])
next
  assume e: "a = j"
  have "T a b = 0" unfolding e by (rule j0)
  thus False using h by (rule notE[rotated])
next
  assume e: "b = i"
  have "T a b = 0" unfolding e by (rule i1)
  thus False using h by (rule notE[rotated])
next
  assume e: "b = j"
  have "T a b = 0" unfolding e by (rule j1)
  thus False using h by (rule notE[rotated])
qed

lemma ext_nz_iff: "ext T i j a b \<noteq> 0 \<longleftrightarrow> T a b \<noteq> 0 \<or> (a = i \<and> b = j) \<or> (a = j \<and> b = i)"
proof (cases "a = i \<and> b = j")
  case c1: True
  have e: "ext T i j a b = 1" by (rule ext_1[OF c1])
  have n: "ext T i j a b \<noteq> 0" unfolding e by simp
  show ?thesis using n c1 by blast
next
  case c1: False
  show ?thesis
  proof (cases "a = j \<and> b = i")
    case c2: True
    have e: "ext T i j a b = -1" by (rule ext_2[OF c1 c2])
    have n: "ext T i j a b \<noteq> 0" unfolding e by simp
    show ?thesis using n c2 by blast
  next
    case c2: False
    have e: "ext T i j a b = T a b" by (rule ext_3[OF c1 c2])
    show ?thesis unfolding e using c1 c2 by blast
  qed
qed

lemma ext_supp:
  assumes h: "ext T i j a b \<noteq> 0"
  shows "(a = i \<and> b = j) \<or> (a = j \<and> b = i) \<or> (a \<noteq> i \<and> a \<noteq> j \<and> b \<noteq> i \<and> b \<noteq> j \<and> T a b \<noteq> 0)"
proof -
  have d: "T a b \<noteq> 0 \<or> (a = i \<and> b = j) \<or> (a = j \<and> b = i)" using h unfolding ext_nz_iff .
  show ?thesis
  proof (cases "T a b \<noteq> 0")
    case True
    have "a \<noteq> i \<and> a \<noteq> j \<and> b \<noteq> i \<and> b \<noteq> j" by (rule T_away[OF True])
    thus ?thesis using True by blast
  next
    case False
    thus ?thesis using d by blast
  qed
qed

lemma ext_row:
  assumes x: "ext T i j a b \<noteq> 0" and y: "ext T i j a c \<noteq> 0"
    and row: "T a b \<noteq> 0 \<Longrightarrow> T a c \<noteq> 0 \<Longrightarrow> b = c"
  shows "b = c"
proof (cases "a = i")
  case ai: True
  have nj: "a \<noteq> j" using ai ne by blast
  have "b = j" using ext_supp[OF x] ai nj by blast
  moreover have "c = j" using ext_supp[OF y] ai nj by blast
  ultimately show ?thesis by (rule trans[OF _ sym])
next
  case ai: False
  show ?thesis
  proof (cases "a = j")
    case aj: True
    have "b = i" using ext_supp[OF x] ai aj by blast
    moreover have "c = i" using ext_supp[OF y] ai aj by blast
    ultimately show ?thesis by (rule trans[OF _ sym])
  next
    case aj: False
    have "T a b \<noteq> 0" using ext_supp[OF x] ai aj by blast
    moreover have "T a c \<noteq> 0" using ext_supp[OF y] ai aj by blast
    ultimately show ?thesis by (rule row)
  qed
qed

lemma ext_col:
  assumes x: "ext T i j a c \<noteq> 0" and y: "ext T i j b c \<noteq> 0"
    and col: "T a c \<noteq> 0 \<Longrightarrow> T b c \<noteq> 0 \<Longrightarrow> a = b"
  shows "a = b"
proof (cases "c = j")
  case cj: True
  have ni: "c \<noteq> i" using cj ne by blast
  have "a = i" using ext_supp[OF x] cj ni by blast
  moreover have "b = i" using ext_supp[OF y] cj ni by blast
  ultimately show ?thesis by (rule trans[OF _ sym])
next
  case cj: False
  show ?thesis
  proof (cases "c = i")
    case ci: True
    have "a = j" using ext_supp[OF x] ci cj by blast
    moreover have "b = j" using ext_supp[OF y] ci cj by blast
    ultimately show ?thesis by (rule trans[OF _ sym])
  next
    case ci: False
    have "T a c \<noteq> 0" using ext_supp[OF x] ci cj by blast
    moreover have "T b c \<noteq> 0" using ext_supp[OF y] ci cj by blast
    ultimately show ?thesis by (rule col)
  qed
qed

end

context lgraph
begin

lemma ext_rep:
  assumes r: "rep V E T" and i: "i \<in> frs T" and j: "j \<in> frs T" and ne: "i \<noteq> j"
  shows "rep V E (ext T i j)"
proof -
  have iI: "i \<in> isoset" and jI: "j \<in> isoset" using i j unfolding frs_def by auto
  have iV: "i \<in> V" and jV: "j \<in> V" using iI jI unfolding isoset_def by auto
  have nEi: "\<And>k. \<not> E i k" and nEj: "\<And>k. \<not> E j k" using iI jI unfolding isoset_def by auto
  have i0: "\<And>k. T i k = 0" and i1: "\<And>k. T k i = 0" using i unfolding frs_def by auto
  have j0: "\<And>k. T j k = 0" and j1: "\<And>k. T k j = 0" using j unfolding frs_def by auto
  note S = ext_supp[OF ne i0 i1 j0 j1]
  have pA: "a \<in> V \<and> b \<in> V" if h0: "ext T i j a b \<noteq> 0" for a b
  proof -
    from S[OF h0] show "a \<in> V \<and> b \<in> V"
    proof (elim disjE)
      assume "a = i \<and> b = j" thus ?thesis using iV jV by blast
    next
      assume "a = j \<and> b = i" thus ?thesis using iV jV by blast
    next
      assume h: "a \<noteq> i \<and> a \<noteq> j \<and> b \<noteq> i \<and> b \<noteq> j \<and> T a b \<noteq> 0"
      hence "T a b \<noteq> 0" by blast
      thus ?thesis by (rule rep_supp[OF r])
    qed
  qed
  have pB: "\<And>a b. ext T i j a b = 0 \<or> ext T i j a b = 1 \<or> ext T i j a b = -1"
    by (rule ext_val, rule rep_val[OF r])
  have pC: "\<And>a b c. ext T i j a b \<noteq> 0 \<Longrightarrow> ext T i j a c \<noteq> 0 \<Longrightarrow> b = c"
    by (rule ext_row[OF ne i0 i1 j0 j1], assumption, assumption, rule rep_row[OF r])
  have pD: "\<And>a b c. ext T i j a c \<noteq> 0 \<Longrightarrow> ext T i j b c \<noteq> 0 \<Longrightarrow> a = b"
    by (rule ext_col[OF ne i0 i1 j0 j1], assumption, assumption, rule rep_col[OF r])
  have psp1: "psp V (ext T i j)"
    unfolding psp_def
  proof (intro conjI)
    show "\<forall>a b. ext T i j a b \<noteq> 0 \<longrightarrow> a \<in> V \<and> b \<in> V" using pA by blast
  next
    show "\<forall>a b. ext T i j a b = 0 \<or> ext T i j a b = 1 \<or> ext T i j a b = -1" using pB by blast
  next
    show "\<forall>a b c. ext T i j a b \<noteq> 0 \<longrightarrow> ext T i j a c \<noteq> 0 \<longrightarrow> b = c" using pC by blast
  next
    show "\<forall>a b c. ext T i j a c \<noteq> 0 \<longrightarrow> ext T i j b c \<noteq> 0 \<longrightarrow> a = b" using pD by blast
  qed
  have sum1: "\<And>a b. a \<in> V \<Longrightarrow> b \<in> V \<Longrightarrow>
      ext T i j a b + ext T i j b a = (if E a b then 1 else 0)"
  proof -
    fix a b assume aV: "a \<in> V" and bV: "b \<in> V"
    show "ext T i j a b + ext T i j b a = (if E a b then 1 else 0)"
    proof (cases "a = i \<and> b = j")
      case c1: True
      have nE: "\<not> E a b" using c1 nEi by blast
      have nc: "\<not> (b = i \<and> a = j)" using c1 ne by blast
      have c1': "b = j \<and> a = i" using c1 by blast
      have e1: "ext T i j a b = 1" by (rule ext_1[OF c1])
      have e2: "ext T i j b a = -1" by (rule ext_2[OF nc c1'])
      show ?thesis unfolding e1 e2 using nE by simp
    next
      case c1: False
      show ?thesis
      proof (cases "a = j \<and> b = i")
        case c2: True
        have nE: "\<not> E a b" using c2 nEj by blast
        have c2': "b = i \<and> a = j" using c2 by blast
        have e1: "ext T i j a b = -1" by (rule ext_2[OF c1 c2])
        have e2: "ext T i j b a = 1" by (rule ext_1[OF c2'])
        show ?thesis unfolding e1 e2 using nE by simp
      next
        case c2: False
        have c1': "\<not> (b = i \<and> a = j)" using c2 by blast
        have c2': "\<not> (b = j \<and> a = i)" using c1 by blast
        have e1: "ext T i j a b = T a b" by (rule ext_3[OF c1 c2])
        have e2: "ext T i j b a = T b a" by (rule ext_3[OF c1' c2'])
        show ?thesis unfolding e1 e2 by (rule rep_sum[OF r aV bV])
      qed
    qed
  qed
  show ?thesis unfolding rep_def using psp1 sum1 by blast
qed

end

end
