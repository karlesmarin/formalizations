(*  Title:      Integer_Length.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Integer length formula: the least number of integer squares is n + P + (z mod 2) for the graph model (lengths paper)
*)

theory Integer_Length
  imports Main "HOL-Library.Product_Lexorder"
begin

text \<open>Integer length of a graph of maximum degree at most two, in finite combinatorics.
An integer representation is a signed partial permutation matrix \<open>T\<close> (every row and every column has
at most one nonzero entry, and the entries are \<open>0\<close>, \<open>1\<close>, \<open>-1\<close>) with \<open>T + T\<^sup>T = A\<^sub>G\<close>. The number of squares
is \<open>2 n - nnz T\<close>. We prove: \<open>nnz T \<le> |E| + 2 \<lfloor>z/2\<rfloor>\<close> with \<open>z\<close> the number of isolated vertices, the matching
construction, and the closed formula for a disjoint union of cycles and paths.\<close>

section \<open>Auxiliary facts on pairs\<close>

lemma swap_mem: "(i, j) \<in> prod.swap ` S \<longleftrightarrow> (j, i) \<in> S"
proof
  assume "(i, j) \<in> prod.swap ` S"
  then obtain q where q: "q \<in> S" "(i, j) = prod.swap q" by blast
  thus "(j, i) \<in> S" by (cases q) auto
next
  assume "(j, i) \<in> S"
  hence "prod.swap (j, i) \<in> prod.swap ` S" by (rule imageI)
  thus "(i, j) \<in> prod.swap ` S" by simp
qed

lemma inj_swap_on: "inj_on prod.swap A"
  by (rule inj_onI) (metis swap_swap)

text \<open>Arithmetic helpers on plain variables.\<close>

lemma int_edge:
  fixes x y :: int
  assumes "x = 0 \<or> x = 1 \<or> x = -1" "y = 0 \<or> y = 1 \<or> y = -1" "x + y = 1"
  shows "(x = 1 \<and> y = 0) \<or> (x = 0 \<and> y = 1)"
  using assms by presburger

lemma int_neg: fixes x y :: int assumes "x + y = 0" shows "y = - x"
  using assms by presburger

lemma int_nz: fixes x y :: int assumes "x + y = 0" "x \<noteq> 0" shows "y \<noteq> 0"
  using assms by presburger

lemma int_self: fixes x :: int assumes "x + x = 0" "x \<noteq> 0" shows False
  using assms by presburger

lemma int01:
  fixes x y :: int
  assumes "x = 0 \<or> x = 1" "y = 0 \<or> y = 1" "\<not> (x \<noteq> 0 \<and> y \<noteq> 0)" "x \<noteq> 0 \<or> y \<noteq> 0"
  shows "x + y = 1"
  using assms by presburger

lemma nat_bound:
  fixes n a b ne z k :: nat
  assumes "n = a + b" "2 * a = ne" "b \<le> z" "b = 2 * k"
  shows "2 * n \<le> ne + 4 * (z div 2)"
  using assms by presburger

lemma nat_max:
  fixes a b ne z :: nat
  assumes "2 * a = ne" "2 * b \<le> ne + 4 * (z div 2)"
  shows "b \<le> a + 2 * (z div 2)"
  using assms by presburger

lemma nat_fin_eq:
  fixes t t0 z cn n p :: nat
  assumes "t = t0 + 2 * (z div 2)" "t0 + cn = n" "cn = p + z"
  shows "t + (n + p + z mod 2) = 2 * n"
  using assms by presburger

lemma nat_fin_le:
  fixes t t0 z cn n p :: nat
  assumes "t \<le> t0 + 2 * (z div 2)" "t0 + cn = n" "cn = p + z"
  shows "t + (n + p + z mod 2) \<le> 2 * n"
  using assms by presburger

lemma nat_ge2: fixes m :: nat assumes "1 \<le> m" "m \<noteq> 1" shows "2 \<le> m"
  using assms by presburger

lemma nat_c: fixes x y k :: nat assumes "x = 0" "x = y - 1" "2 * Suc k \<le> y" shows False
  using assms by arith

lemma nat_ite:
  fixes m :: nat and cy :: bool
  assumes "1 \<le> m"
  shows "(if cy then m else m - 1) + (if \<not> cy then 1 else 0) = m"
proof (cases cy)
  case True
  thus ?thesis by simp
next
  case False
  have e: "m - 1 + 1 = m" using assms by arith
  show ?thesis using False e by simp
qed

lemma sum_ind:
  "finite A \<Longrightarrow> (\<Sum>x\<in>A. if P x then (1::nat) else 0) = card {x \<in> A. P x}"
proof (induction rule: finite_induct)
  case empty
  show ?case by simp
next
  case (insert a A)
  have fS: "finite {x \<in> A. P x}" using insert.hyps(1) by simp
  have nS: "a \<notin> {x \<in> A. P x}" using insert.hyps(2) by simp
  show ?case
  proof (cases "P a")
    case True
    hence "{x \<in> insert a A. P x} = insert a {x \<in> A. P x}" by auto
    thus ?thesis using True insert.hyps insert.IH fS nS by (simp add: card_insert_disjoint)
  next
    case False
    hence "{x \<in> insert a A. P x} = {x \<in> A. P x}" by auto
    thus ?thesis using False insert.hyps insert.IH by simp
  qed
qed

section \<open>Signed partial permutations and representations\<close>

definition psp :: "'v set \<Rightarrow> ('v \<Rightarrow> 'v \<Rightarrow> int) \<Rightarrow> bool" where
  "psp V T \<longleftrightarrow> (\<forall>i j. T i j \<noteq> 0 \<longrightarrow> i \<in> V \<and> j \<in> V)
    \<and> (\<forall>i j. T i j = 0 \<or> T i j = 1 \<or> T i j = -1)
    \<and> (\<forall>i j k. T i j \<noteq> 0 \<longrightarrow> T i k \<noteq> 0 \<longrightarrow> j = k)
    \<and> (\<forall>i j k. T i k \<noteq> 0 \<longrightarrow> T j k \<noteq> 0 \<longrightarrow> i = j)"

definition rep :: "'v set \<Rightarrow> ('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> ('v \<Rightarrow> 'v \<Rightarrow> int) \<Rightarrow> bool" where
  "rep V E T \<longleftrightarrow> psp V T \<and> (\<forall>i\<in>V. \<forall>j\<in>V. T i j + T j i = (if E i j then 1 else 0))"

definition nnz :: "('v \<Rightarrow> 'v \<Rightarrow> int) \<Rightarrow> nat" where
  "nnz T = card {p. T (fst p) (snd p) \<noteq> 0}"

lemma rep_psp: "rep V E T \<Longrightarrow> psp V T"
  unfolding rep_def by blast

lemma rep_row: "rep V E T \<Longrightarrow> T a b \<noteq> 0 \<Longrightarrow> T a c \<noteq> 0 \<Longrightarrow> b = c"
  unfolding rep_def psp_def by blast

lemma rep_col: "rep V E T \<Longrightarrow> T a c \<noteq> 0 \<Longrightarrow> T b c \<noteq> 0 \<Longrightarrow> a = b"
  unfolding rep_def psp_def by blast

lemma rep_val: "rep V E T \<Longrightarrow> T a b = 0 \<or> T a b = 1 \<or> T a b = -1"
  unfolding rep_def psp_def by blast

lemma rep_supp: "rep V E T \<Longrightarrow> T a b \<noteq> 0 \<Longrightarrow> a \<in> V \<and> b \<in> V"
  unfolding rep_def psp_def by blast

lemma rep_sum: "rep V E T \<Longrightarrow> a \<in> V \<Longrightarrow> b \<in> V \<Longrightarrow> T a b + T b a = (if E a b then 1 else 0)"
  unfolding rep_def by blast

locale lgraph =
  fixes V :: "'v::linorder set" and E :: "'v \<Rightarrow> 'v \<Rightarrow> bool"
  assumes Efin: "finite V"
    and Esym: "\<And>i j. E i j \<Longrightarrow> E j i"
    and Eirr: "\<And>i. \<not> E i i"
    and Esub: "\<And>i j. E i j \<Longrightarrow> i \<in> V \<and> j \<in> V"
begin

definition ne :: nat where "ne = card {p. E (fst p) (snd p)}"
definition isoset :: "'v set" where "isoset = {i \<in> V. \<forall>j. \<not> E i j}"
definition nz :: nat where "nz = card isoset"
definition frs :: "('v \<Rightarrow> 'v \<Rightarrow> int) \<Rightarrow> 'v set" where
  "frs T = {i \<in> isoset. (\<forall>k. T i k = 0) \<and> (\<forall>k. T k i = 0)}"

lemma fin_VV: "finite (V \<times> V)" using Efin by simp

lemma fin_isoset: "finite isoset"
  by (rule finite_subset[OF _ Efin]) (auto simp: isoset_def)

lemma fin_supp:
  assumes "rep V E T"
  shows "finite {p. T (fst p) (snd p) \<noteq> 0}"
proof (rule finite_subset[OF _ fin_VV], rule subsetI)
  fix p assume "p \<in> {p. T (fst p) (snd p) \<noteq> 0}"
  hence "T (fst p) (snd p) \<noteq> 0" by simp
  from rep_supp[OF assms this] show "p \<in> V \<times> V" by (simp add: mem_Times_iff)
qed

lemma edge_cases:
  assumes r: "rep V E T" and e: "E i j"
  shows "(T i j = 1 \<and> T j i = 0) \<or> (T i j = 0 \<and> T j i = 1)"
proof -
  from e have ij: "i \<in> V" "j \<in> V" using Esub by auto
  have s: "T i j + T j i = 1" using rep_sum[OF r ij] e by simp
  have a: "T i j = 0 \<or> T i j = 1 \<or> T i j = -1" by (rule rep_val[OF r])
  have b: "T j i = 0 \<or> T j i = 1 \<or> T j i = -1" by (rule rep_val[OF r])
  show ?thesis by (rule int_edge[OF a b s])
qed

lemma NX_prop:
  assumes r: "rep V E T" and h1: "T i j \<noteq> 0" and h2: "\<not> E i j"
  shows "T j i = - T i j" "T j i \<noteq> 0" "i \<noteq> j" "\<not> E j i"
proof -
  from rep_supp[OF r h1] have ij: "i \<in> V" "j \<in> V" by auto
  have s: "T i j + T j i = 0" using rep_sum[OF r ij] h2 by simp
  show "T j i = - T i j" by (rule int_neg[OF s])
  show "T j i \<noteq> 0" by (rule int_nz[OF s h1])
  show "i \<noteq> j"
  proof
    assume eq: "i = j"
    have "T i i + T i i = 0" using s eq by metis
    moreover have "T i i \<noteq> 0" using h1 eq by metis
    ultimately show False by (rule int_self)
  qed
  show "\<not> E j i" using h2 Esym by blast
qed

lemma NX_iso:
  assumes r: "rep V E T" and h1: "T i j \<noteq> 0" and h2: "\<not> E i j"
  shows "i \<in> isoset"
proof -
  have iV: "i \<in> V" using rep_supp[OF r h1] by simp
  have tji: "T j i \<noteq> 0" using NX_prop[OF r h1 h2] by simp
  have "\<forall>k. \<not> E i k"
  proof (intro allI notI)
    fix k assume ek: "E i k"
    from edge_cases[OF r ek] show False
    proof
      assume "T i k = 1 \<and> T k i = 0"
      hence tik: "T i k \<noteq> 0" by simp
      from rep_row[OF r h1 tik] have "j = k" .
      thus False using h2 ek by simp
    next
      assume "T i k = 0 \<and> T k i = 1"
      hence tki: "T k i \<noteq> 0" by simp
      from rep_col[OF r tki tji] have "k = j" .
      thus False using h2 ek by simp
    qed
  qed
  thus ?thesis unfolding isoset_def using iV by simp
qed

lemma card_NE:
  assumes r: "rep V E T"
  shows "2 * card {p. T (fst p) (snd p) \<noteq> 0 \<and> E (fst p) (snd p)} = ne"
proof -
  let ?N = "{p. T (fst p) (snd p) \<noteq> 0 \<and> E (fst p) (snd p)}"
  have fN: "finite ?N" by (rule finite_subset[OF _ fin_supp[OF r]]) auto
  have un0: "((i, j) \<in> {p. E (fst p) (snd p)}) \<longleftrightarrow> ((i, j) \<in> ?N \<union> prod.swap ` ?N)" for i j
  proof -
    show "((i, j) \<in> {p. E (fst p) (snd p)}) \<longleftrightarrow> ((i, j) \<in> ?N \<union> prod.swap ` ?N)"
    proof
      assume "(i, j) \<in> {p. E (fst p) (snd p)}"
      hence e: "E i j" by simp
      from edge_cases[OF r e] show "(i, j) \<in> ?N \<union> prod.swap ` ?N"
      proof
        assume "T i j = 1 \<and> T j i = 0"
        thus ?thesis using e by simp
      next
        assume h: "T i j = 0 \<and> T j i = 1"
        have "(j, i) \<in> ?N" using h Esym[OF e] by simp
        hence "(i, j) \<in> prod.swap ` ?N" by (simp add: swap_mem)
        thus ?thesis by simp
      qed
    next
      assume "(i, j) \<in> ?N \<union> prod.swap ` ?N"
      thus "(i, j) \<in> {p. E (fst p) (snd p)}"
      proof
        assume "(i, j) \<in> ?N" thus ?thesis by simp
      next
        assume "(i, j) \<in> prod.swap ` ?N"
        hence "(j, i) \<in> ?N" by (simp add: swap_mem)
        hence "E j i" by simp
        thus ?thesis using Esym by simp
      qed
    qed
  qed
  have un: "{p. E (fst p) (snd p)} = ?N \<union> prod.swap ` ?N"
  proof (rule set_eqI)
    fix p show "p \<in> {p. E (fst p) (snd p)} \<longleftrightarrow> p \<in> ?N \<union> prod.swap ` ?N"
      using un0[of "fst p" "snd p"] by simp
  qed
  have dis: "?N \<inter> prod.swap ` ?N = {}"
  proof (rule equals0I)
    fix p assume h: "p \<in> ?N \<inter> prod.swap ` ?N"
    obtain i j where p: "p = (i, j)" by (cases p) auto
    have h2: "(i, j) \<in> ?N \<inter> prod.swap ` ?N" using h p by metis
    hence a: "T i j \<noteq> 0" "E i j" by auto
    from h2 have "(i, j) \<in> prod.swap ` ?N" by simp
    hence "(j, i) \<in> ?N" by (simp add: swap_mem)
    hence b: "T j i \<noteq> 0" by simp
    from edge_cases[OF r a(2)] a(1) b show False by auto
  qed
  have "ne = card (?N \<union> prod.swap ` ?N)" by (simp only: ne_def un)
  also have "\<dots> = card ?N + card (prod.swap ` ?N)"
    by (rule card_Un_disjoint[OF fN finite_imageI[OF fN] dis])
  also have "card (prod.swap ` ?N) = card ?N" by (rule card_image[OF inj_swap_on])
  finally show ?thesis by simp
qed

lemma NX_card:
  assumes r: "rep V E T"
  shows "card {p. T (fst p) (snd p) \<noteq> 0 \<and> \<not> E (fst p) (snd p)} \<le> nz"
    and "even (card {p. T (fst p) (snd p) \<noteq> 0 \<and> \<not> E (fst p) (snd p)})"
proof -
  let ?X = "{p. T (fst p) (snd p) \<noteq> 0 \<and> \<not> E (fst p) (snd p)}"
  have fX: "finite ?X" by (rule finite_subset[OF _ fin_supp[OF r]]) auto
  have inj: "inj_on fst ?X"
  proof (rule inj_onI)
    fix p q assume pX: "p \<in> ?X" and qX: "q \<in> ?X" and f: "fst p = fst q"
    have a: "T (fst p) (snd p) \<noteq> 0" using pX by simp
    have b0: "T (fst q) (snd q) \<noteq> 0" using qX by simp
    have b: "T (fst p) (snd q) \<noteq> 0" using b0 f by simp
    have "snd p = snd q" by (rule rep_row[OF r a b])
    thus "p = q" using f by (simp add: prod_eq_iff)
  qed
  have sub: "fst ` ?X \<subseteq> isoset"
  proof
    fix i assume "i \<in> fst ` ?X"
    then obtain p where "p \<in> ?X" "i = fst p" by blast
    thus "i \<in> isoset" using NX_iso[OF r] by auto
  qed
  have "card ?X = card (fst ` ?X)" by (rule card_image[OF inj, symmetric])
  also have "\<dots> \<le> card isoset" by (rule card_mono[OF fin_isoset sub])
  finally show "card ?X \<le> nz" unfolding nz_def .
  have nei: "fst p \<noteq> snd p" if "p \<in> ?X" for p
  proof -
    from that have "T (fst p) (snd p) \<noteq> 0" "\<not> E (fst p) (snd p)" by auto
    from NX_prop(3)[OF r this] show "fst p \<noteq> snd p" .
  qed
  have Xsw: "(j, i) \<in> ?X" if "(i, j) \<in> ?X" for i j
  proof -
    from that have h: "T i j \<noteq> 0" "\<not> E i j" by auto
    from NX_prop[OF r h] show "(j, i) \<in> ?X" by simp
  qed
  let ?L = "{p \<in> ?X. fst p < snd p}"
  let ?G = "{p \<in> ?X. snd p < fst p}"
  have fL: "finite ?L" by (rule finite_subset[OF _ fX]) auto
  have fG: "finite ?G" by (rule finite_subset[OF _ fX]) auto
  have un: "?X = ?L \<union> ?G"
  proof (rule set_eqI)
    fix p show "p \<in> ?X \<longleftrightarrow> p \<in> ?L \<union> ?G"
    proof
      assume pX: "p \<in> ?X"
      hence "fst p \<noteq> snd p" by (rule nei)
      thus "p \<in> ?L \<union> ?G" using pX by (auto simp: neq_iff)
    next
      assume "p \<in> ?L \<union> ?G" thus "p \<in> ?X" by auto
    qed
  qed
  have dis: "?L \<inter> ?G = {}" by auto
  have gl: "?G = prod.swap ` ?L"
  proof (rule set_eqI)
    fix p :: "'v \<times> 'v"
    obtain i j where p: "p = (i, j)" by (cases p) auto
    show "p \<in> ?G \<longleftrightarrow> p \<in> prod.swap ` ?L"
    proof (cases "(i, j) \<in> ?X")
      case True
      hence "(j, i) \<in> ?X" by (rule Xsw)
      thus ?thesis using True p by (auto simp: swap_mem)
    next
      case False
      hence "(j, i) \<notin> ?X" using Xsw by blast
      thus ?thesis using False p by (auto simp: swap_mem)
    qed
  qed
  have a1: "card ?X = card (?L \<union> ?G)" by (rule arg_cong[where f = card, OF un])
  have a2: "card (?L \<union> ?G) = card ?L + card ?G" by (rule card_Un_disjoint[OF fL fG dis])
  have a3: "card ?G = card ?L" by (subst gl) (rule card_image[OF inj_swap_on])
  have "card ?X = 2 * card ?L" using a1 a2 a3 by simp
  thus "even (card ?X)" by simp
qed

lemma nnz_split:
  assumes r: "rep V E T"
  shows "nnz T = card {p. T (fst p) (snd p) \<noteq> 0 \<and> E (fst p) (snd p)}
    + card {p. T (fst p) (snd p) \<noteq> 0 \<and> \<not> E (fst p) (snd p)}"
proof -
  let ?A = "{p. T (fst p) (snd p) \<noteq> 0 \<and> E (fst p) (snd p)}"
  let ?B = "{p. T (fst p) (snd p) \<noteq> 0 \<and> \<not> E (fst p) (snd p)}"
  have f: "finite {p. T (fst p) (snd p) \<noteq> 0}" by (rule fin_supp[OF r])
  have fA: "finite ?A" by (rule finite_subset[OF _ f]) auto
  have fB: "finite ?B" by (rule finite_subset[OF _ f]) auto
  have eq: "{p. T (fst p) (snd p) \<noteq> 0} = ?A \<union> ?B" by auto
  have dis: "?A \<inter> ?B = {}" by auto
  show ?thesis unfolding nnz_def eq by (rule card_Un_disjoint[OF fA fB dis])
qed

theorem nnz_bound:
  assumes r: "rep V E T"
  shows "2 * nnz T \<le> ne + 4 * (nz div 2)"
proof -
  have s: "nnz T = card {p. T (fst p) (snd p) \<noteq> 0 \<and> E (fst p) (snd p)}
    + card {p. T (fst p) (snd p) \<noteq> 0 \<and> \<not> E (fst p) (snd p)}" by (rule nnz_split[OF r])
  have e: "2 * card {p. T (fst p) (snd p) \<noteq> 0 \<and> E (fst p) (snd p)} = ne" by (rule card_NE[OF r])
  have le: "card {p. T (fst p) (snd p) \<noteq> 0 \<and> \<not> E (fst p) (snd p)} \<le> nz" by (rule NX_card(1)[OF r])
  obtain k where k: "card {p. T (fst p) (snd p) \<noteq> 0 \<and> \<not> E (fst p) (snd p)} = 2 * k"
    using NX_card(2)[OF r] by (auto elim: evenE)
  show ?thesis by (rule nat_bound[OF s e le k])
qed

corollary nnz_supported:
  assumes r: "rep V E T" and sup: "\<And>i j. T i j \<noteq> 0 \<Longrightarrow> E i j"
  shows "2 * nnz T = ne"
proof -
  have "{p. T (fst p) (snd p) \<noteq> 0 \<and> \<not> E (fst p) (snd p)} = {}" using sup by auto
  hence z: "card {p. T (fst p) (snd p) \<noteq> 0 \<and> \<not> E (fst p) (snd p)} = 0" by (simp only: card.empty)
  have s: "nnz T = card {p. T (fst p) (snd p) \<noteq> 0 \<and> E (fst p) (snd p)}
    + card {p. T (fst p) (snd p) \<noteq> 0 \<and> \<not> E (fst p) (snd p)}" by (rule nnz_split[OF r])
  have e: "2 * card {p. T (fst p) (snd p) \<noteq> 0 \<and> E (fst p) (snd p)} = ne" by (rule card_NE[OF r])
  show ?thesis using s z e by simp
qed


end
end
