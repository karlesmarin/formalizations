(*  Title:      ZL_Canonical.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    The combinatorial steps of the slope of the canonical base: the two (C3) witnesses, the counting
    step through the critical threshold of the graph of the pairs, and the module attaining the slope.
*)
theory ZL_Canonical
  imports ZL_Labels Graph_Threshold
begin

text \<open>The canonical base of the paper has all the ones of its singleton rows in one anchor column, here column
  \<open>0\<close>. The slope theorem for the canonical base says that the largest number of pairs on it is
  \<open>\<kappa>\<^sub>n m + O(1)\<close> with \<open>\<kappa>\<^sub>n = \<lfloor>(n-1)\<^sup>2/4\<rfloor>/(n-1)\<close>. Its proof has three combinatorial steps, proved here:
  the two (C3) witnesses that make every frequent label independent in the graph of the pairs; the counting step
  that reduces the number of pairs to the critical threshold of that graph, bounded by Hof's theorem; and the
  admissibility of the module that attains the slope. The asymptotic bookkeeping (rare labels, special rows,
  filler rows) is not formalized.\<close>

section \<open>The two (C3) witnesses\<close>

text \<open>A pair inside one row \<open>r\<close> is excluded as soon as another row \<open>r''\<close> carries the anchor and both
  columns of the pair.\<close>

lemma canonical_not_horizontal:
  assumes "r'' \<noteq> r" "j \<noteq> 0" "q \<noteq> 0"
    and "(r'', 0) \<in> Oc" "(r'', j) \<in> Oc" "(r'', q) \<in> Oc" "(r, 0) \<in> Oc"
  shows "\<not> C3 Oc (r, j) (r, q)"
  using assms unfolding C3_def by fastforce

text \<open>A pair between two anchored rows \<open>r\<close>, \<open>r'\<close> is excluded as soon as a third row carries the anchor
  and both columns of the pair: a frequent label cannot contain both columns of a remaining pair.\<close>

lemma canonical_label_indep:
  assumes "r'' \<noteq> r" "r'' \<noteq> r'" "j \<noteq> 0" "q \<noteq> 0"
    and "(r'', 0) \<in> Oc" "(r'', j) \<in> Oc" "(r'', q) \<in> Oc" "(r, 0) \<in> Oc" "(r', 0) \<in> Oc"
  shows "\<not> C3 Oc (r, j) (r', q)"
  using assms unfolding C3_def by fastforce

section \<open>The counting step\<close>

text \<open>A pair is a pair of cells \<open>(c, d)\<close>, a cell is \<open>(row, column)\<close>. The graph of the pairs joins the
  columns of the two cells of each pair.\<close>

definition pgraph :: "(('r \<times> 'n) \<times> ('r \<times> 'n)) set \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> bool" where
  "pgraph P j q \<longleftrightarrow> (\<exists>c d. (c, d) \<in> P \<and> ((snd c = j \<and> snd d = q) \<or> (snd c = q \<and> snd d = j)))"

text \<open>If the cells of the pairs are pairwise distinct, every cell lies in the label of its row, and every
  label is independent in the graph of the pairs, then the number of pairs is at most the number of rows times
  \<open>\<lfloor>k\<^sup>2/4\<rfloor>/k\<close>, with \<open>k\<close> the number of columns. Proof: charge every pair to the weights of its two
  columns under the fractional cover of Hof's theorem.\<close>

theorem canonical_count:
  fixes R :: "'r set" and L :: "'r \<Rightarrow> 'n::finite set" and P :: "(('r \<times> 'n) \<times> ('r \<times> 'n)) set"
  assumes finR: "finite R" and finP: "finite P"
    and rows: "\<And>c d. (c, d) \<in> P \<Longrightarrow> fst c \<in> R \<and> fst d \<in> R"
    and lab: "\<And>c d. (c, d) \<in> P \<Longrightarrow> snd c \<in> L (fst c) \<and> snd d \<in> L (fst d)"
    and ndeg: "\<And>c d. (c, d) \<in> P \<Longrightarrow> c \<noteq> d"
    and disj: "\<And>x y. x \<in> P \<Longrightarrow> y \<in> P \<Longrightarrow> x \<noteq> y \<Longrightarrow> {fst x, snd x} \<inter> {fst y, snd y} = {}"
    and ind: "\<And>r. r \<in> R \<Longrightarrow> indep (pgraph P) (L r)"
  shows "real (card P) \<le> real (card R) * (real (CARD('n)\<^sup>2 div 4) / real CARD('n))"
proof -
  define B where "B = real (CARD('n)\<^sup>2 div 4) / real CARD('n)"
  obtain p :: "real^'n" where cov: "fcover (pgraph P) p"
    and bnd: "\<forall>I. indep (pgraph P) I \<longrightarrow> (\<Sum>v\<in>I. p $ v) \<le> B"
    using graph_threshold_bound[of "pgraph P"] unfolding B_def by blast
  have pos: "\<And>v. 0 \<le> p $ v" using cov by (simp add: fcover_def)
  define f where "f x = p $ snd x" for x :: "'r \<times> 'n"
  define C where "C = (\<Union>x\<in>P. {fst x, snd x})"
  have one: "1 \<le> f (fst x) + f (snd x)" if "x \<in> P" for x
  proof -
    obtain c d where x: "x = (c, d)" by (cases x)
    have "pgraph P (snd c) (snd d)" using that x unfolding pgraph_def by blast
    then show ?thesis using cov x unfolding fcover_def f_def by simp
  qed
  have "real (card P) = (\<Sum>x\<in>P. 1)" by simp
  also have "\<dots> \<le> (\<Sum>x\<in>P. f (fst x) + f (snd x))" by (rule sum_mono) (rule one)
  also have "\<dots> = (\<Sum>x\<in>P. \<Sum>y\<in>{fst x, snd x}. f y)"
  proof (rule sum.cong[OF refl])
    fix x assume "x \<in> P"
    then have "fst x \<noteq> snd x" using ndeg by (cases x) auto
    then show "f (fst x) + f (snd x) = (\<Sum>y\<in>{fst x, snd x}. f y)" by simp
  qed
  also have "\<dots> = (\<Sum>y\<in>C. f y)"
    unfolding C_def by (rule sum.UNION_disjoint[symmetric]) (use finP disj in auto)
  also have "\<dots> \<le> (\<Sum>y\<in>Sigma R L. f y)"
  proof (rule sum_mono2)
    show "finite (Sigma R L)" using finR by (simp add: finite_SigmaI)
    show "C \<subseteq> Sigma R L"
    proof
      fix y assume "y \<in> C"
      then obtain x where x: "x \<in> P" and y: "y = fst x \<or> y = snd x" unfolding C_def by blast
      obtain c d where cd: "x = (c, d)" by (cases x)
      have "fst c \<in> R" "fst d \<in> R" "snd c \<in> L (fst c)" "snd d \<in> L (fst d)"
        using rows[of c d] lab[of c d] x cd by auto
      then show "y \<in> Sigma R L" using y cd by (cases c, cases d) auto
    qed
    show "\<And>y. y \<in> Sigma R L - C \<Longrightarrow> 0 \<le> f y" using pos unfolding f_def by simp
  qed
  also have "\<dots> = (\<Sum>r\<in>R. \<Sum>v\<in>L r. p $ v)"
  proof -
    have "(\<Sum>r\<in>R. \<Sum>v\<in>L r. p $ v) = (\<Sum>(r, v)\<in>Sigma R L. p $ v)"
      using finR by (rule sum.Sigma) simp
    then show ?thesis by (simp add: f_def split_def)
  qed
  also have "\<dots> \<le> (\<Sum>r\<in>R. B)" by (rule sum_mono) (use bnd ind in blast)
  also have "\<dots> = real (card R) * B" by simp
  finally show ?thesis unfolding B_def .
qed

section \<open>The module that attains the slope\<close>

text \<open>Rows of \<open>RX\<close> carry the anchor and columns of \<open>X\<close>, rows of \<open>RY\<close> the anchor and columns of \<open>Y\<close>;
  every other row has at most two occupied cells (the special rows). Then every pair joining a cell of an
  \<open>RX\<close> row in \<open>X\<close> with a cell of an \<open>RY\<close> row in \<open>Y\<close> satisfies (C2) and (C3). Corollary of the block lemma
  with three blocks: the anchor, \<open>X\<close> and \<open>Y\<close>.\<close>

lemma canonical_module_admissible:
  fixes X Y RX RY :: "nat set"
  assumes XY: "X \<inter> Y = {}" and anc: "0 \<notin> X" "0 \<notin> Y" and RXY: "RX \<inter> RY = {}"
    and sx: "\<And>r. r \<in> RX \<Longrightarrow> supp Oc r \<subseteq> insert 0 X"
    and sy: "\<And>r. r \<in> RY \<Longrightarrow> supp Oc r \<subseteq> insert 0 Y"
    and other: "\<And>r. r \<notin> RX \<Longrightarrow> r \<notin> RY \<Longrightarrow> finite (supp Oc r) \<and> card (supp Oc r) \<le> 2"
    and c: "fst c \<in> RX" "snd c \<in> X" and d: "fst d \<in> RY" "snd d \<in> Y"
  shows "C2 Oc c d \<and> C3 Oc c d"
proof -
  define blk :: "nat \<Rightarrow> nat" where "blk j = (if j \<in> X then 1 else if j \<in> Y then 2 else 0)" for j
  define tp :: "nat \<Rightarrow> nat set" where
    "tp r = (if r \<in> RX then {0, 1} else if r \<in> RY then {0, 2} else blk ` supp Oc r)" for r
  show ?thesis
  proof (rule blocks_admissible)
    fix r show "card (tp r) \<le> 2"
    proof (cases "r \<in> RX \<or> r \<in> RY")
      case True then show ?thesis unfolding tp_def by (auto simp: card_insert_if)
    next
      case False
      then have nx: "r \<notin> RX" and ny: "r \<notin> RY" by auto
      have "card (blk ` supp Oc r) \<le> card (supp Oc r)" using other[OF nx ny] by (simp add: card_image_le)
      also have "\<dots> \<le> 2" using other[OF nx ny] by simp
      finally show ?thesis using nx ny unfolding tp_def by simp
    qed
  next
    fix r show "finite (tp r)" using other unfolding tp_def by auto
  next
    fix r j assume j: "j \<in> supp Oc r"
    show "blk j \<in> tp r"
    proof (cases "r \<in> RX")
      case True then show ?thesis using sx[OF True] j anc unfolding tp_def blk_def by auto
    next
      case nx: False
      show ?thesis
      proof (cases "r \<in> RY")
        case True then show ?thesis using sy[OF True] j anc XY nx unfolding tp_def blk_def by auto
      next
        case False then show ?thesis using j nx unfolding tp_def by auto
      qed
    qed
  next
    show "fst c \<noteq> fst d" using c d RXY by auto
  next
    show "blk (snd c) \<in> tp (fst c) - tp (fst d)" using c d RXY unfolding tp_def blk_def by auto
  next
    show "blk (snd d) \<in> tp (fst d) - tp (fst c)" using c d RXY XY unfolding tp_def blk_def by auto
  qed
qed

end
